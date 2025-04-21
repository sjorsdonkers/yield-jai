logx :: (root: *Code_Node) {
    debug_builder: String_Builder;
    print_expression(*debug_builder, root);
    log("%", builder_to_string(*debug_builder));
}

Coroutinator :: struct {
    Coroutine: Type;
    next : Code;
}

// Works but, inconvenient to insert `yoo as it cannot be redefined, could take name as an argument
yielder :: (resumable: $R, arguments:..Any, call:= #caller_code) #expand {
    YieldProc :: #run,stallable into_yielding(resumable);
    `yoo := init(YieldProc);

    yoo.arguments = #insert -> string {
        builder: String_Builder;
        append(*builder, ".{");
        root := compiler_get_nodes(call).(*Code_Procedure_Call);
        print_arguments(*builder, array_view(root.arguments_unsorted, 1), false);
        append(*builder, "};");
        return builder_to_string(*builder);
    };
}

init :: ($yielding: Coroutinator) -> $COROUTINE #modify {
    COROUTINE = yielding.Coroutine;
    return true;
} {
    return.{next=#insert #run yielding.next};
}

yield :: (return_value: s64) #expand {
    `return return_value;
}

Co_Status :: enum { YIELD; RETURN; IMPLEMENTATION_ERROR; }
Coroutine :: struct (Args: Type, State: Type, Output: Type) {
    arguments : Args;
    state   : State;
    position: s64;
    next : (*Coroutine(Args, State, Output)) -> Co_Status, Output;
}
next :: (yielding: *$T/Coroutine) -> Co_Status, T.Output {
    s, o := yielding.next(yielding);
    return s, o;
}

for_expansion :: (routine: Coroutine, body: Code, flags: For_Flags) #expand {
    index := 0;
    while true {
        defer index += 1;
        `it_index := index;
        status, `it := next(*routine);
        assert(status != .IMPLEMENTATION_ERROR, "Coroutine returned IMPLEMENTATION_ERROR");

        #insert body;

        if status == .RETURN then break;
    }
}

into_yielding :: (proc: $T) -> Coroutinator #expand #compile_time {
    return into_yielding_impl(code_of(proc));
}

into_yielding_impl :: ($code: Code) -> Coroutinator #compile_time {
    Args   :: #run,stallable extract_arguments(code);
    State  :: #run extract_state(code);
    Output :: #run extract_output(code);

    new_code := #run -> Code {
        root, nodes := compiler_get_nodes(code);
        assert(root.kind == .PROCEDURE_HEADER, "%", root.*);
        header := root.(*Code_Procedure_Header);
        original_returns := header.returns;
        {
            // Set coroutine as first and only argument. The original arguments should be held in the state and using-ed in the proc
            self_code := #code self: *COROUTINE;
            self_decl := compiler_get_nodes(self_code);
            assert(self_decl.kind == .DECLARATION, "%", self_decl.kind);

            arguments: [..] *Code_Declaration;
            array_add(*arguments, self_decl.(*Code_Declaration));
            header.arguments = arguments;

            // Add Co_Status as first return value
            status_code := #code status:Co_Status;
            status_decl := compiler_get_nodes(status_code);
            assert(status_decl.kind == .DECLARATION, "%", status_decl.kind);

            returns: [..] *Code_Declaration;
            array_add(*returns, status_decl.(*Code_Declaration));
            for header.returns array_add(*returns, it);
            header.returns = returns;
        }

        top_statements: [..]*Code_Node;
        array_add(*top_statements, compiler_get_nodes(#code using self.arguments;));
        array_add(*top_statements, compiler_get_nodes(#code using self.state;));

        // Create `while true if self.position == {`
        loop_node, cases_block := position_switch_node();
        array_add(*top_statements, loop_node);

        cases: [..]*Code_Node;
        add_case_default(*cases); // Needed for the always yield case, not sure if we want that

        sub_block := Block_Process.{original = header.body_or_null.block, name = ""};
        sub_block.set_me_to_case_id = 0;
        next_available_case_id := 1;

        while has_more(sub_block) {
            new_block, exit, case_id := process_block(*sub_block, *next_available_case_id);
            assert(case_id != -1);
            add_case(*cases, case_id, new_block);
        }
        cases_block.statements = cases;

        array_add(*top_statements, default_return(original_returns));
        header.body_or_null.block.statements = top_statements;

        // Debug
        logx(root);

        return compiler_get_code(root);
    }
    return Coroutinator.{Coroutine(Args, State, Output), new_code};
}

Block_Exit :: enum { END; NEW_CASE; }

Block_Process :: struct {
    name             : string;
    original         : *Code_Block;
    statement_index  := 0;
    current_sub_block: *Block_Process; // Can be null
    waiting_sub_block: *Block_Process; // Can be null
    deferred_statements: [..]*Code_Node;

    set_me_to_case_id := -1;
    after_goto_case_id:= -1;
    original_is_processed := false;
    is_expansion := false;
}

new_sub_block :: (block: *Code_Block, name: string) -> *Block_Process {
    sub_block := New(Block_Process);
    sub_block.original = block;
    sub_block.name = name;
    return sub_block;
}

using_state :: (name: string) -> *Code_Using {
    root := compiler_get_nodes(#code using tmp;).(*Code_Using);
    ident := root.expression.(*Code_Ident);
    ident.name = name;
    return root;
}

has_more :: (self: Block_Process) -> bool {
    res :=  (self.statement_index < self.original.statements.count)
        || self.current_sub_block != null
        || self.waiting_sub_block != null
        || self.after_goto_case_id != -1
        || self.deferred_statements.count > 0;
    return res;
}

process_block :: (self: *Block_Process, next_available_case_id: *s64) -> *Code_Block, Block_Exit, s64 { //original_block to take statements from should modify this such that remaining statements can be put into the next positions block)
    new_block := New(Code_Block);
    new_block.* = self.original.*;

    return_new_block :: (exit: Block_Exit, new_set_me_to_case_id:=-1) #expand {
        `new_block.statements = `statements;
        case_id := `self.set_me_to_case_id;
        `self.set_me_to_case_id = new_set_me_to_case_id;
        `return `new_block, exit, case_id;
    }
    take_case_id :: (next_available_case_id: *s64) -> s64 {
        case_id := next_available_case_id.*;
        next_available_case_id.* += 1;
        return case_id;
    }

    statements : [..]*Code_Node;
    // Add a using statement for the state of the current block
    // This makes it so that we do not have to dot prefix every state variable
    // Since nested block states are using-ed as well, we do not need to prefix them either and just use the name of the current block
    if self.name then array_add(*statements, using_state(self.name));

    // If we have waiting sub blocks, but no current one, we make the waiting one current
    if self.current_sub_block == null {
        self.current_sub_block, self.waiting_sub_block = self.waiting_sub_block, null;
    }

    while has_more(self) {
        // If we have a sub block we process that first
        if self.current_sub_block != null {
            // Sub blocks are always resuming a previously started yielded from block
            if self.current_sub_block.original_is_processed { // This is mostly just an optimization to prevent unnecessary splits before while loops
                array_add(*statements, ..self.current_sub_block.original.statements);

                // We do not use after_goto_case_id atm, the creator can add the statement..for now
                defer self.current_sub_block = null;
                new_block.statements = statements;
                return new_block, .NEW_CASE, self.current_sub_block.set_me_to_case_id;
            }

            sub_block, sub_exit, sub_case_id := process_block(self.current_sub_block, next_available_case_id);
            array_add(*statements, sub_block);
            assert(sub_case_id != -1);

            if !has_more(self.current_sub_block) {
                // Is this when we yield/return as the last statement in a sub block?
                // assert(self.current_sub_block.set_me_to_case_id == -1, "% - %", self.current_sub_block.set_me_to_case_id, sub_case_id); // ??
                self.current_sub_block = null;
            }
            if sub_exit == .END {
                // We dropped of the end of a nested block, so we take over the case id
                // However, we we may have started the sub block ourselves in which case it's ID are the same
                // assert(self.set_me_to_case_id == -1 || self.set_me_to_case_id == sub_case_id, "%-%", self.set_me_to_case_id, sub_case_id);
                self.set_me_to_case_id = sub_case_id;
                continue;
            } else {
                // The sub block yielded so we just return what it told us
                new_block.statements = statements;
                return new_block, sub_exit, sub_case_id;
            }
        }

        // We may be at the end of the block, but still need to write the after goto statement, deferred statements
        if self.statement_index >= self.original.statements.count {
            assert(self.after_goto_case_id != -1 || self.deferred_statements.count > 0);

            // Place each deferred statement at the end of the block
            // Currently we do not support yielding from a deferred statement
            // Note: defer is executed after evaluating all statements of the return block
            //       returned locals mutated in the defer are not reflected in the return value
            //       if defer returns it self that return wins, but the original return statements are still evaluated
            //       if multiple defers return, all return expressions are evaluated, the first defers return wins
            array_add(*statements, ..self.deferred_statements);
            array_reset(*self.deferred_statements);

            if self.after_goto_case_id != -1 {
                array_add(*statements, set_position_node(self.after_goto_case_id));
                self.after_goto_case_id = -1;
                return_new_block(.NEW_CASE); // If we have a after goto we need to end the case as this the end of for example an if or loop block
            }
            break;
        }

        stmnt := self.original.statements[self.statement_index];
        defer self.statement_index += 1;

        if stmnt.kind == {
        case .RETURN;
            ret_node := stmnt.(*Code_Return);
            if self.is_expansion && !(ret_node.return_flags & .IS_BACKTICKED) {
                assert(false, "Not backticked return in expansion is not yet supported");
            }
            // Insert deferred statements
            array_add(*statements, ..self.deferred_statements);
            array_reset(*self.deferred_statements);

            array_add(*statements, set_position_node(0));
            array_add(*statements, return_with_costatus(ret_node));

            self.after_goto_case_id = -1; // Since we are returning there is nowhere we need to go after
            unreachable_case_id := take_case_id(next_available_case_id); // TODO prevent unreachable_case_id from being inserted
            return_new_block(.NEW_CASE, unreachable_case_id);
        case .PROCEDURE_CALL;
            call := stmnt.(*Code_Procedure_Call);
            // Replace yield(..) calls
            if call.procedure_expression.kind == .IDENT
            && "yield" == call.procedure_expression.(*Code_Ident).name {
                resume_case_id := take_case_id(next_available_case_id);
                array_add(*statements, set_position_node(resume_case_id));
                array_add(*statements, convert_yield_to_return(call));

                return_new_block(.NEW_CASE, resume_case_id);
            }

            // Expand macro expansions if they contain yield/return statements
            if call.macro_expansion_block != null {
                assert(self.current_sub_block == null);
                scope_name := tprint("expand_%", self.statement_index);
                self.current_sub_block = new_sub_block(call.macro_expansion_block, scope_name);

                // Set the call argument values to the expand state
                // We need to set the call arguments from the current scope to prevent getting current literals used in the assignment shadowed
                // expand_2.bob = bob;
                header := call.resolved_procedure_expression.(*Code_Procedure_Header);
                for value_code: call.arguments_sorted {
                    arg := header.arguments[it_index].(*Code_Declaration); // We are assuming the order of call and procedure args is the same

                    arg_assignment := compiler_get_nodes(#code scope.procarg = callarg).(*Code_Binary_Operator);
                    target := arg_assignment.left.(*Code_Binary_Operator);
                    target.left.(*Code_Ident).name = scope_name;
                    target.right.(*Code_Ident).name = arg.name;
                    arg_assignment.right = value_code;
                    array_add(*statements, arg_assignment);
                }

                // Remove all backticks from identifiers (not declarations defer, return, push_context)
                remove_backticks_from_idents(self.current_sub_block.original); // @speed can we do this after processing the block?

                self.current_sub_block.is_expansion = true;
                block, exit, case_id := process_block(self.current_sub_block, next_available_case_id);
                assert(case_id == -1);
                array_add(*statements, block);
                if exit == .END {
                    // No yield or return inside the expansion we cannot add the normal block as we need to process backticked
                    self.current_sub_block = null;
                    continue;
                } else {
                    // The expansion yielded so we need to add the part we parsed and proceed with the remaining statements
                    return_new_block(exit, self.current_sub_block.set_me_to_case_id);
                }
            }
        case .DECLARATION;
            assigment := convert_declaration_to_assignment(stmnt.(*Code_Declaration));
            if assigment then array_add(*statements, assigment);
            continue; // TODO compound declarations
        case .BLOCK;
            assert(self.current_sub_block == null);
            self.current_sub_block = new_sub_block(stmnt.(*Code_Block), tprint("block_%", self.statement_index));
            block, exit, case_id  := process_block(self.current_sub_block, next_available_case_id);
            assert(case_id == -1);
            array_add(*statements, block);
            if exit == .END {
                // No yield or return in the block, we still use the processed one as it may have backticked declarations
                self.current_sub_block = null;
                continue;
            } else {
                // The block yielded so we need to add the part we parsed and proceed with the remaining statements
                return_new_block(exit, self.current_sub_block.set_me_to_case_id);
            }
        case .DEFER;
            // Since we may end the scope early we need to physically move the deferred statements to the end of the block
            array_add(*self.deferred_statements, stmnt);
            continue;
        case .IF;
            if_block := stmnt.(*Code_If);

            // case 0;     code before if
            //             if condition {
            //                 then code until goto 1
            //             } else {
            //                 else code until goto 3
            //             }
            //             yield 4;
            // case 1;     code in then after 1st yield
            //             yield 2;
            // case 2;     code in then after 2nd yield till end
            //             yield 4
            // case 3;     code in else after yield till end
            //             yield 4
            // case 4;     code after if

            // Do then block
            then_exit := Block_Exit.END;
            if if_block.then_block != null {
                assert(self.current_sub_block == null);
                self.current_sub_block = new_sub_block(if_block.then_block, tprint("then_%", self.statement_index));
                then_block, then_exit=, then_case_id := process_block(self.current_sub_block, next_available_case_id);
                assert(then_case_id == -1);
                if_block.then_block = then_block;
                if then_exit == .END then self.current_sub_block = null;
            }

            // Do else block
            else_exit := Block_Exit.END;
            if if_block.else_block != null {
                assert(self.waiting_sub_block == null);
                self.waiting_sub_block = new_sub_block(if_block.else_block, tprint("else_%", self.statement_index));
                else_block, else_exit=, else_case_id := process_block(self.waiting_sub_block, next_available_case_id);
                assert(else_case_id == -1);
                if_block.else_block = else_block;
                if else_exit == .END then self.waiting_sub_block = null;
            }

            array_add(*statements, if_block);
            if then_exit == .END && else_exit == .END {
                continue;
            }

            // We create a case ID (4) such that both branching blocks can jump to the same position
            after_if_case_id := take_case_id(next_available_case_id);
            array_add(*statements, set_position_node(after_if_case_id));
            if self.current_sub_block then self.current_sub_block.after_goto_case_id = after_if_case_id;
            if self.waiting_sub_block then self.waiting_sub_block.after_goto_case_id = after_if_case_id;

            return_new_block(.NEW_CASE, after_if_case_id);
        case .WHILE;
            while_stmnt := stmnt.(*Code_While);

            // case 0;
            //      code before while
            //      goto 1
            // case 1;
            //      if while condition {
            //          code until goto 2
            //      }
            //      goto 4
            // case 2;
            //      code in while after 1st yield
            //      goto 3 // Goto to next pos in the same block
            // case 3;
            //      code in while after 2nd yield until end of while block
            //      goto 1 // Goto loop start if we reached the end of the loop block
            // case 4;
            //      code after while

            assert(self.current_sub_block == null && self.waiting_sub_block == null);
            self.waiting_sub_block = new_sub_block(while_stmnt.block, tprint("while_%", self.statement_index));
            body_block, while_exit, while_case_id := process_block(self.waiting_sub_block, next_available_case_id);
            assert(while_case_id == -1);

            if while_exit == .END {
                while_stmnt.block = body_block; // Needed as declaration may have been backticked
                array_add(*statements, while_stmnt);
                self.waiting_sub_block = null;
                continue;
            }
            /// CASE 0 ///
            // If the while block contains any yield or return we turn it into an if statement
            // Before doing so we need to end the current case as we do not want to re-execute that code
            loop_start_case_id  := take_case_id(next_available_case_id);
            after_while_case_id := take_case_id(next_available_case_id);
            array_add(*statements, set_position_node(loop_start_case_id));
            array_add(*statements, compiler_get_nodes(#code continue)); // We need to continue to prevent the execution of any code of higher blocks

            /// CASE 2 / 3 / ... should eventually always loop back to 1 ///
            self.waiting_sub_block.after_goto_case_id = loop_start_case_id;

            /// CASE 1 ///
            // Set it as the current sub-block
            {
                if_node           := New(Code_If);
                if_node.kind       = .IF;
                if_node.condition  = while_stmnt.condition;
                if_node.then_block = body_block;

                while_statements: [..]*Code_Node;
                array_add(*while_statements, if_node);
                array_add(*while_statements, set_position_node(after_while_case_id));
                // We end this case here as we do not want to execute code after the while loop until the loop has completed

                temp_block           := New(Code_Block);
                temp_block.*          = self.original.*;
                temp_block.statements = while_statements;

                self.current_sub_block                       = new_sub_block(temp_block, "");
                self.current_sub_block.set_me_to_case_id     = loop_start_case_id;
                self.current_sub_block.original_is_processed = true;
            }

            /// CASE 4 continues from the this Block_Process with after_while_case_id ///
            return_new_block(.NEW_CASE, after_while_case_id);
        case .FOR;
            for_stmnt := stmnt.(*Code_For);
            assert(self.current_sub_block == null);

            // There are 3 types of for loops: range based (for 0..5), array based (for array) and for_expansions.

            // for_expansion
            if for_stmnt.macro_expansion_procedure_call {
                call := for_stmnt.macro_expansion_procedure_call;
                // for_expansion are very different from range or array for loops.
                // for expansions are somewhat like normal expansion calls with a couple of differences. The looping (if any) happens somewhere later inside the expansion.
                // Some of the differences are: a for_expansion has the argument assignment statements already put inside the body, so we do not need to do that here.
                // However to avoid a copy the iterable is "extracted" during desugaring. Extract code may not exist so we need to replace it.
                // The other main issue is that we don't seem to get any help renaming the variables
                self.current_sub_block = new_sub_block(call.macro_expansion_block, tprint("for_%", self.statement_index));
                remove_backticks_from_idents(self.current_sub_block.original);

                // The first 3 statements in the block are magically the arguments to the for_expansion,
                // we know that these are always: (Iterable, Body, Flags)
                // Iterable is put there as a Code_Extract node, which we may not use, so we need to replace the right hand side of the assignment.
                // Code_Extract is likely used to avoid unnecessary copies of the iterable.
                iterable := compiler_get_nodes(#code (iter).*).(*Code_Unary_Operator); // A copy since we cannot extract
                iterable.subexpression = call.arguments_sorted[0];
                iterable.subexpression.node_flags |= .IS_PARENTHESIZED;
                self.current_sub_block.original.statements[0].(*Code_Declaration).expression = iterable;

                // The block is parsed just like a normal expansion, there is on last difference relating to renaming of it / it_index.
                // When the loop body code is insert we need to make sure it and it_index are assigned inside the loop body to variables of the expected names.
                // Like `value := it;`. We could solve that by 1. assigning them in a block previous to de the body code, 2. In a block that is the parent of the body code, or 3. In the body code itself.
                // TODO renaming
                // TODO change if non it/it_index backticked variables are imported as like in normal expansion
                self.current_sub_block.is_expansion = true;
                block, exit, case_id := process_block(self.current_sub_block, next_available_case_id);
                assert(case_id == -1);
                array_add(*statements, block);
                if exit == .END {
                    // No yield or return in the loop
                    self.current_sub_block = null;
                    continue;
                } else {
                    // The loop yielded so we added the part we parsed and proceed with the remaining statements
                    return_new_block(exit, self.current_sub_block.set_me_to_case_id);
                }
            }


            // We currently just do a hacky solutions for ranges and arrays that reuse the while implementation
            // Currently it will create 2 extra cases and an extra nested block due to the hacky implementation

            // local = 0;
            // {
            //     it := 0; // TODO need to be careful that often it is just a copy instead of the actual iteration variable
            //     while it <= 1{
            //         defer it += 1; <----------------- This is an issue since it changes the index of all statements
            //         yield(local);
            //         local += 1;
            //     }
            // }

            for_statements: [..]*Code_Node;
            it_decl := compiler_get_nodes(#code it := 0).(*Code_Declaration);
            it_decl.name = for_stmnt.ident_it.name;
            it_decl.expression = for_stmnt.iteration_expression;
            array_add(*for_statements, it_decl); // TODO it_index

            while_stmnt := New(Code_While);
            while_stmnt.kind = .WHILE;

            while_stmnt.block = for_stmnt.block;
            block_statements_with_defer: [..]*Code_Node;
            defer_increment_node := compiler_get_nodes(#code defer it += 1;).(*Code_Defer);
            defer_increment_node.block.statements[0].(*Code_Binary_Operator).left = for_stmnt.ident_it;
            array_add(*block_statements_with_defer, defer_increment_node);
            array_add(*block_statements_with_defer, ..for_stmnt.block.statements);
            while_stmnt.block.statements = block_statements_with_defer;

            while_condition := compiler_get_nodes(#code it <= 1).(*Code_Binary_Operator);
            while_condition.left = for_stmnt.ident_it;
            while_condition.right = for_stmnt.iteration_expression_right;
            while_stmnt.condition = while_condition;
            array_add(*for_statements, while_stmnt);

            for_block  := New(Code_Block);
            for_block.* = self.original.*;
            for_block.statements = for_statements;

            for_start_case_id := take_case_id(next_available_case_id);
            after_for_case_id := take_case_id(next_available_case_id);
            self.current_sub_block = new_sub_block(for_block, tprint("for_%", self.statement_index));
            self.current_sub_block.set_me_to_case_id  = for_start_case_id;
            self.current_sub_block.after_goto_case_id = after_for_case_id;

            array_add(*statements, set_position_node(for_start_case_id));
            array_add(*statements, compiler_get_nodes(#code continue));

            return_new_block(.NEW_CASE, after_for_case_id);
        case .DIRECTIVE_INSERT;
            insert_code := stmnt.(*Code_Directive_Insert);
            // We should insert the code if it contains a yield statement
            // TODO scope, break, continue, remove, internal, expression
            if !(insert_code.is_internal || insert_code.scope_redirection || insert_code.break_replacement || insert_code.continue_replacement || insert_code.remove_replacement) {
                // We just replace the insert statement and re-evaluate the statement
                self.original.statements[self.statement_index] = insert_code.expansion;
                self.statement_index -= 1; // Needed as it is going to be defer incremented
                continue;
            }

        }

        array_add(*statements, stmnt);
    }

    return_new_block(.END);
}

// Remove all backticks from identifiers (not declarations, defer, return, push_context)
// We do not do declarations as they NEED to be transformed to assignments in which case they also loose the backtick
// If a backticked declaration remains that is a bug
remove_backticks_from_idents :: (node: *Code_Node) {
    pointers: [..] *Code_Node;
    get_recursive_nodes_breadth_first(node, *pointers);
    for pointers {
        if it.kind == .IDENT then it.(*Code_Ident).flags &= ~.HAS_SCOPE_MODIFIER;
    }
}

position_switch_node :: () -> *Code_Node, *Code_Block {
    switch_code := #code while true if self.position == {
    };
    while_node := compiler_get_nodes(switch_code).(*Code_While);
    switch_node := while_node.block.statements[0].(*Code_If);
    return while_node, switch_node.then_block;
}

add_case :: (cases: *[..]*Code_Node, position: s64, then_block: *Code_Block) {
    case_code: Code;
    {
        case_code = #code case -1;
    }
    case_node := compiler_get_nodes(case_code).(*Code_Case);
    case_node.condition.(*Code_Literal)._s64 = position;
    case_node.then_block = then_block;

    array_add(cases, case_node);
}

// Adds a case that resets the position to 0 if no other case is matched;
// This should probably be only b `case cases.count;`, it's kinda hacky regardless and likely to change
add_case_default :: (cases: *[..]*Code_Node) {
    case_code: Code;
    {
        case_code = #code case; self.position = 0;
    }
    case_node := compiler_get_nodes(case_code).(*Code_Case);
    array_add(cases, case_node);
}

// Add return .IMPLEMENTATION_ERROR with defaulted args;
default_return :: (returns: []*Code_Declaration) -> *Code_Block {
    block_code := #code {};
    block_node := compiler_get_nodes(block_code).(*Code_Block);

    statements : [..]*Code_Node;

    for returns {
        decl := New(Code_Declaration);
        decl.* = it.*;
        decl.name = tprint("ret_%", it_index);
        array_add(*statements, decl);
    }

    return_code_0 := #code return .IMPLEMENTATION_ERROR; // TODO make proper loop
    return_node_0 := compiler_get_nodes(return_code_0).(*Code_Return);
    return_code_1 := #code return .IMPLEMENTATION_ERROR, ret_0;
    return_node_1 := compiler_get_nodes(return_code_1).(*Code_Return);
    return_code_2 := #code return .IMPLEMENTATION_ERROR, ret_0, ret_1;
    return_node_2 := compiler_get_nodes(return_code_2).(*Code_Return);
    return_code_3 := #code return .IMPLEMENTATION_ERROR, ret_0, ret_1, ret_2;
    return_node_3 := compiler_get_nodes(return_code_3).(*Code_Return);

    if returns.count == {
    case 0; array_add(*statements, return_node_0);
    case 1; array_add(*statements, return_node_1);
    case 2; array_add(*statements, return_node_2);
    case 3; array_add(*statements, return_node_3);
    case; assert(false);
    }

    block_node.statements = statements;

    return block_node;
}

set_position_node :: (position: s64) -> *Code_Node {
    set_code := #code self.position = 0;
    root := compiler_get_nodes(set_code).(*Code_Binary_Operator);
    assert(root.kind == .BINARY_OPERATOR, "%", root.kind);
    assert(root.right.kind == .LITERAL, "%", root.right.kind);
    root.right.(*Code_Literal)._s64 = position;
    return root;
}

// Add .RETURN to every return statement;
return_with_costatus :: (it_return: Code_Return) -> *Code_Return {
    return_code := #code return .RETURN;
    return_node := compiler_get_nodes(return_code).(*Code_Return);

    arguments_unsorted:  [..] Code_Argument;
    arguments_sorted:    [..] *Code_Node;

    assert(return_node.arguments_sorted.count == 0); // TODO Arguments_sorted is not used or so.. Note: it_return.arguments_sorted > 0
    array_add(*arguments_unsorted, return_node.arguments_unsorted[0]);
    for it_return.arguments_unsorted array_add(*arguments_unsorted, it);
    return_node.arguments_unsorted = arguments_unsorted;

    return return_node;
}

// Change yields to returns like: yield(5); to return .YIELD, 5;
convert_yield_to_return :: (yield_call: *Code_Procedure_Call) -> *Code_Return {
    yield_code := #code return .YIELD;
    yield_node := compiler_get_nodes(yield_code).(*Code_Return);

    arguments_unsorted:  [..] Code_Argument;
    arguments_sorted:    [..] *Code_Node;

    // What about arguments_sorted?
    array_add(*arguments_unsorted, yield_node.arguments_unsorted[0]);
    for yield_call.arguments_unsorted array_add(*arguments_unsorted, it);
    yield_node.arguments_unsorted = arguments_unsorted;

    return yield_node;
}

// Change `local := 42` to `local = 42`
// Returns null if the type is not given a value (expression)
convert_declaration_to_assignment :: (declaration: *Code_Declaration) -> *Code_Node {
    if declaration.flags & .IS_CONSTANT then return declaration;
    assert(declaration.name != "");
    if declaration.expression == null   then return null;

    ident := New(Code_Ident);
    ident.name = declaration.name;

    assignment := New(Code_Binary_Operator);
    assignment.kind = .BINARY_OPERATOR;
    assignment.operator_type = #char "=";
    assignment.left = ident;
    assignment.right = declaration.expression;

    return assignment;
}

extract_output :: ($code: Code) -> Type #compile_time {
    root, nodes := compiler_get_nodes(code);
    assert(root.kind == .PROCEDURE_HEADER, "%", root.*);

    header := root.(*Code_Procedure_Header);
    assert(header.returns.count == 1);
    return get_type(header.returns[0].type_inst.result);
}

extract_arguments :: ($code: Code) -> Type #compile_time {
    #insert -> Code {
        root := compiler_get_nodes(code); assert(root.kind == .PROCEDURE_HEADER, "%", root.*);
        header := root.(*Code_Procedure_Header); assert(header.body_or_null != null);

        type_root, type_nodes := compiler_get_nodes(#code Co_args :: struct {});
        for type_nodes if it.kind == .BLOCK {
            block := it.(*Code_Block);
            statements: [..]*Code_Node;
            for header.arguments {
                array_add(*statements, it.(*Code_Node));
            }
            block.statements = statements;
        }
        return compiler_get_code(type_root);
    };
    return Co_args;
}

extract_state :: ($code: Code) -> Type #compile_time {
    type_only_decl :: (decl: *Code_Declaration) -> *Code_Node {
        if decl.flags & .IS_CONSTANT {
            // root := compiler_get_nodes(#code name :: 6).(*Code_Declaration);
            return decl;
        }
        if decl.type_inst {
            // We have the Code_Type_Instantiation so we it is easy to build the declaration
            root := compiler_get_nodes(#code name: i32).(*Code_Declaration); // flags?
            root.name = decl.name;
            root.type_inst = decl.type_inst;
            return root;
        }

        // We want to modify code from `val := 7` to `val: i32`
        // We have the Type_Info -> type -> "TheType" available but we need a Code_Type_Instantiation
        insert_type := compiler_get_nodes(#code #insert "the_name: TheType").(*Code_Directive_Insert);
        insert_type.expression.(*Code_Literal)._string = tprint("%: %;", decl.name, get_type(decl.type));
        return insert_type;
    }
    add_state_members :: (statements: *[..]*Code_Node, node: *Code_Node, index:=-1) {
        add_nest :: (name: string, statements: *[..]*Code_Node, it: *Code_Node, it_index:=-1) {
            block_statements: [..]*Code_Node;
            add_state_members(*block_statements, it, it_index);

            root := compiler_get_nodes(#code nest_name: struct {}).(*Code_Declaration);
            root.name = name;
            root.type_inst.type_valued_expression.(*Code_Struct).block.statements = block_statements;
            array_add(statements, root);
        }
        if node.kind == {
        case .BLOCK;
            block := node.(*Code_Block);
            for block.members {
                assert(it.kind == .DECLARATION);
                member := it.(*Code_Declaration);
                if member.flags & .IS_CONSTANT then continue; // TODO need to be in there too, might be better to use code instead of string
                // Backticked declarations from expansions should only be added at the call site's block where it is imported
                if member.flags & .HAS_SCOPE_MODIFIER && !(member.flags & (.IS_IMPORTED | .IS_ITERATOR)) then continue;

                array_add(statements, type_only_decl(xx it));
            }

            for block.statements {
                if it.kind == .BLOCK {
                    add_nest(tprint("block_%", it_index), statements, it, it_index);
                } else {
                    add_state_members(statements, it, it_index);
                }
            }
        case .IF;
            if_block := node.(*Code_If);
            if if_block.then_block != null {
                add_nest(tprint("then_%", index), statements, if_block.then_block);
            }
            if if_block.else_block != null {
                add_nest(tprint("else_%", index), statements, if_block.else_block);
            }
        case .WHILE;
            add_nest(tprint("while_%", index), statements, node.(*Code_While).block);
        case .FOR;
            for_stmnt := node.(*Code_For);

            for_statements: [..]*Code_Node;
            if for_stmnt.macro_expansion_procedure_call {
                add_state_members(*for_statements, for_stmnt.macro_expansion_procedure_call.macro_expansion_block);
            } else {
                // This works for range and arrays, but not for_expansions which have void types
                if for_stmnt.ident_decl array_add(*for_statements, type_only_decl(for_stmnt.ident_decl));
                if for_stmnt.index_decl array_add(*for_statements, type_only_decl(for_stmnt.index_decl));

                add_nest("while_1", *for_statements, for_stmnt.block); // TODO remember what the 1 was for
            }

            root := compiler_get_nodes(#code nest_name: struct {}).(*Code_Declaration);
            root.name = tprint("for_%", index);
            root.type_inst.type_valued_expression.(*Code_Struct).block.statements = for_statements;
            array_add(statements, root);
        case .PROCEDURE_CALL;
            call := node.(*Code_Procedure_Call);
            if call.macro_expansion_block == null then return;
            if call.procedure_expression.kind == .IDENT
                && "yield" == call.procedure_expression.(*Code_Ident).name then return;

            expand_statements: [..]*Code_Node;
            // The arguments of the expansion need to be captured in the state
            // TODO using arguments causes the members to be inserted as .IS_IMPORTED
            // Since we need the same value to be accessible both ways we should instead have them only the using in the state, not the members.
            assert(call.resolved_procedure_expression.kind == .PROCEDURE_HEADER);
            header := call.resolved_procedure_expression.(*Code_Procedure_Header);
            for header.arguments array_add(*expand_statements, type_only_decl(it));

            add_state_members(*expand_statements, call.macro_expansion_block);

            root := compiler_get_nodes(#code nest_name: struct {}).(*Code_Declaration);
            root.name = tprint("expand_%", index);
            root.type_inst.type_valued_expression.(*Code_Struct).block.statements = expand_statements;
            array_add(statements, root);
        case .DIRECTIVE_INSERT;
            insert_code := node.(*Code_Directive_Insert);
            // When generating the code we need to insert the code as it may contain a yield or return.
            // This is specifically important when the the yield is for the body of a for_expansion.
            // - When the scope is `internal` we should not make a new scope
            // - If the insert is in a redirected scope, I have no idea what to do
            // - Break, continue, and remove should not be allowed to yield for now.
            // - expression?
            if !(insert_code.is_internal || insert_code.scope_redirection || insert_code.break_replacement || insert_code.continue_replacement || insert_code.remove_replacement) {

                if insert_code.expansion.kind == .BLOCK {
                    add_nest(tprint("block_%", index +1), statements, insert_code.expansion, index); // +1 is a hack as for will insert a defer causing this to move down 1
                } else {
                    add_state_members(statements, insert_code.expansion, index);
                }
            }
        }
    }
    Co_state :: #insert #run,stallable -> Code {
        root, nodes := compiler_get_nodes(code); assert(root.kind == .PROCEDURE_HEADER, "%", root.*);
        header := root.(*Code_Procedure_Header); assert(header.body_or_null != null);

        struct_root := compiler_get_nodes(#code struct {}).(*Code_Struct);

        statements: [..]*Code_Node;
        add_state_members(*statements, header.body_or_null.block);
        struct_root.block.statements = statements;

        log("State:\n%", struct_root.kind);
        logx(struct_root);
        log("");

        return compiler_get_code(struct_root);
    };
    return Co_state;
}

#scope_file
#import "Basic";
#import "Compiler";
#import "Program_Print";
#import "Print_Vars";
#import "Code_Visit";

explain_for :: (for_stmnt: *Code_For) {
    log("===========================================");

    log("For iteration_expression - %", for_stmnt.iteration_expression != null);
    if for_stmnt.iteration_expression       logx(for_stmnt.iteration_expression);
    log("For iteration_expression_right - %", for_stmnt.iteration_expression_right != null);
    if for_stmnt.iteration_expression_right logx(for_stmnt.iteration_expression_right);
    log("For block - %", for_stmnt.block != null);
    if for_stmnt.block {
        logx(for_stmnt.block);
        log("Block members:");
        for for_stmnt.block.members {
            log("- %: %;", it.(*Code_Declaration).name, get_type(it.(*Code_Declaration).type));
        }
        log("Block statements:");
        for for_stmnt.block.statements {
            if it.kind == .DECLARATION {
                log("- % %", it.(*Code_Declaration).name, get_type(it.(*Code_Declaration).type));
                logx(it); // why do it and it_index not show up, any special flags?

            } else {
                log("- %", it.*);
            }
        }
    }
    log("For ident_it - %", for_stmnt.ident_it != null);
    if for_stmnt.ident_it                   logx(for_stmnt.ident_it);
    log("For ident_it_index - %", for_stmnt.ident_it_index != null);
    if for_stmnt.ident_it_index             logx(for_stmnt.ident_it_index);
    log("For ident_decl - %", for_stmnt.ident_decl != null);
    if for_stmnt.ident_decl                 logx(for_stmnt.ident_decl);
    log("For index_decl - %", for_stmnt.index_decl != null);
    if for_stmnt.index_decl                 logx(for_stmnt.index_decl);
    log("For want_replacement_for_expansion - %", for_stmnt.want_replacement_for_expansion != null);
    if for_stmnt.want_replacement_for_expansion logx(for_stmnt.want_replacement_for_expansion);
    log("For want_pointer_expression - %", for_stmnt.want_pointer_expression != null);
    if for_stmnt.want_pointer_expression    logx(for_stmnt.want_pointer_expression);
    log("For want_reverse_expression - %", for_stmnt.want_reverse_expression != null);
    if for_stmnt.want_reverse_expression    logx(for_stmnt.want_reverse_expression);
    log("For for_flags: %", for_stmnt.for_flags);
    log("For macro_expansion_procedure_call - %", for_stmnt.macro_expansion_procedure_call != null);
    if for_stmnt.macro_expansion_procedure_call {
        logx(for_stmnt.macro_expansion_procedure_call);
        log("\nMacro expansion block");
        logx(for_stmnt.macro_expansion_procedure_call.macro_expansion_block);
        log("Macro block members:");
        for for_stmnt.macro_expansion_procedure_call.macro_expansion_block.members {
            log("- % % // %", it.(*Code_Declaration).name, get_type(it.(*Code_Declaration).type), it.(*Code_Declaration).flags);
        }
        log("Macro block statements:");
        for for_stmnt.macro_expansion_procedure_call.macro_expansion_block.statements {
            if it.kind == .DECLARATION {
                log("- % % // %", it.(*Code_Declaration).name, get_type(it.(*Code_Declaration).type), it.(*Code_Declaration).flags);
                logx(it);
            } else {
                log("- %", it.*);
                explain_for(xx it);
            }
        }
    }
    log("===========================================");
}
