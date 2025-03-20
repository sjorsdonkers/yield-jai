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
        // add_case_default(*cases); // Probably not needed
        active_case_id         := 0;
        next_available_case_id := 1;
        current_case_block     := add_case(*cases, active_case_id);

        statements: [..] *Code_Node;
        assert(header.body_or_null != null);

        sub_block := Block_Process.{original = header.body_or_null.block};
        while sub_block.statement_index < sub_block.original.statements.count {
            new_block, exit := process_block(*sub_block, *next_available_case_id);
            if new_block.statements.count > 0 { // 0 since no using state statement
                array_add(*statements, ..new_block.statements);
            }
            if exit != .END {
                current_case_block.statements = statements;
                statements = [..]*Code_Node.{};
                active_case_id += 1;
                current_case_block = add_case(*cases, active_case_id);
            }
        }
        if statements.count == 0 {
            cases.count -= 1;
        } else {
            current_case_block.statements = statements;
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
    original: *Code_Block;
    statement_index := 0;
    current_sub_block: *Block_Process; // Can be null
    waiting_else_block: *Block_Process; // Can be null
    name: string;

    set_me_to_case_id : *s64;
    after_goto_case_id:= -1;
    inline_statements:= false;
}

using_state :: (name: string) -> *Code_Using {
    root := compiler_get_nodes(#code using tmp;).(*Code_Using);
    ident := root.expression.(*Code_Ident);
    ident.name = name;
    return root;
}

has_more :: (block: Block_Process) -> bool {
    res :=  (block.statement_index < block.original.statements.count)
        || block.current_sub_block != null
        || block.waiting_else_block != null;
    // assert(!res || block.after_goto_case_id == -1);
    return res;
}

process_block :: (self: *Block_Process, next_available_case_id: *s64) -> *Code_Block, Block_Exit { //original_block to take statements from should modify this such that remaining statements can be put into the next positions block)
    new_block := New(Code_Block);
    new_block.* = self.original.*;

    statements : [..]*Code_Node;
    if self.name then array_add(*statements, using_state(self.name));

    if self.current_sub_block == null
        && self.waiting_else_block != null {
            self.current_sub_block = self.waiting_else_block;
            self.waiting_else_block = null;
    }

    while has_more(self) {
        if self.current_sub_block != null {
            if self.current_sub_block.inline_statements {
                array_add(*statements, ..self.current_sub_block.original.statements);
                new_block.statements = statements; // TODO Not sure if we need to copy here, do we need the using statement?
                self.current_sub_block = null;
                return new_block, .NEW_CASE; // always returnyield here is not clear from inline name
            }

            sub_block, sub_exit := process_block(self.current_sub_block, next_available_case_id);
            if sub_block.statements.count > 1 { // 1 for using state statement
                array_add(*statements, sub_block);
            }

            after_goto_case_id := self.current_sub_block.after_goto_case_id;
            if !has_more(self.current_sub_block) {
                self.current_sub_block = null;
            }

            if sub_exit != .END {
                new_block.statements = statements;
                return new_block, sub_exit;
            }
            if after_goto_case_id != -1 {
                array_add(*statements, set_position_node(after_goto_case_id));
                new_block.statements = statements;
                return new_block, .NEW_CASE;
            }
            continue;
        }

        stmnt := self.original.statements[self.statement_index];
        defer self.statement_index += 1;

        if stmnt.kind == {
        case .RETURN;
            array_add(*statements, set_position_node(0));
            array_add(*statements, return_with_costatus(stmnt.(*Code_Return)));

            new_block.statements = statements;
            return new_block, .NEW_CASE;
        case .PROCEDURE_CALL;
            call := stmnt.(*Code_Procedure_Call);
            if call.procedure_expression.kind == .IDENT
            && "yield" == call.procedure_expression.(*Code_Ident).name {
                array_add(*statements, set_position_node(next_available_case_id.*));
                next_available_case_id.* += 1;
                array_add(*statements, convert_yield_to_return(call));

                new_block.statements = statements;
                return new_block, .NEW_CASE;
            }
        case .DECLARATION;
            array_add(*statements, convert_declaration_to_assignment(stmnt.(*Code_Declaration)));
            continue; // TODO compound declarations
        case .BLOCK;
            assert(self.current_sub_block == null);
            self.current_sub_block = New(Block_Process);
            self.current_sub_block.original = stmnt.(*Code_Block);
            self.current_sub_block.name = tprint("block_%", self.statement_index);
            continue;
        case .IF;
            if_block := stmnt.(*Code_If);

            // Do then block
            assert(self.current_sub_block == null);
            assert(if_block.then_block != null); // TBD is then optional? Like in `y := ifx x > 5 else 2;`
            self.current_sub_block = New(Block_Process);
            self.current_sub_block.original = if_block.then_block;
            self.current_sub_block.name = tprint("then_%", self.statement_index);

            then_block, then_exit := process_block(self.current_sub_block, next_available_case_id);
            if_block.then_block = then_block;
            if !has_more(self.current_sub_block) {
                self.current_sub_block = null;
            }

            // Do else block
            else_exit := Block_Exit.END;
            if if_block.else_block != null {
                assert(self.waiting_else_block == null);
                self.waiting_else_block = New(Block_Process);
                self.waiting_else_block.original = if_block.else_block;
                self.waiting_else_block.name = tprint("else_%", self.statement_index);

                else_block:, else_exit = process_block(self.waiting_else_block, next_available_case_id);
                if_block.else_block = else_block;
                if !has_more(self.waiting_else_block) {
                    self.waiting_else_block = null;
                }
            }

            array_add(*statements, if_block);
            if then_exit != .END || else_exit != .END {
                array_add(*statements, set_position_node(next_available_case_id.*));
                // should waiting be moved to current block if that is null?
                if self.current_sub_block then self.current_sub_block.after_goto_case_id = next_available_case_id.*;
                if self.waiting_else_block then self.waiting_else_block.after_goto_case_id = next_available_case_id.*;

                // We start a new case here such that both branches can jump to the same position
                next_available_case_id.* += 1;
                new_block.statements = statements;
                return new_block, then_exit;
            }
            continue;
        case .WHILE;
            assert(self.current_sub_block == null);
            assert(self.waiting_else_block == null);

            while_block := stmnt.(*Code_While);
            self.waiting_else_block = New(Block_Process);
            self.waiting_else_block.original = while_block.block;
            self.waiting_else_block.name = tprint("while_%", self.statement_index);

            // Reserve a case id for the while loop
            reserved_case_id:= next_available_case_id.*;
            next_available_case_id.* += 1;

            body_block, while_exit := process_block(self.waiting_else_block, next_available_case_id);
            if !has_more(self.waiting_else_block) {
                self.waiting_else_block = null;
            }

            if while_exit == .END {
                // The while loop does not contain any yields or returns so we can just add it as a normal while loop
                array_add(*statements, while_block);
                // No new cases were added, so we give back the reserved id
                assert(next_available_case_id.* == reserved_case_id + 1);
                next_available_case_id.* = reserved_case_id;
                continue;
            }
            // HMM we want to give the stack down to the leaves such that the leaf can start a new case a just write the code as below
            //

            // case 0;
            //      code before while
            //      yield 1
            // case 1;
            //      if while condition {
            //          code until yield 2
            //      }
            //      yield 4
            // case 2;
            //      code in while after 1st yield
            //      yield 3 // yield to next pos if has_more code
            // case 3;
            //      code in while after 2nd yield until end of while block
            //      yield 1 // yield to loop start if we reached the end of the loop block
            // case 4;
            //      code after while

            // If this contains a yield or return we turn it into an if statement
            // Before doing so we need to end the current case as we do not want to re-execute that code
            // NOTE the id has already been updated by the while_body so the body continuation should be before the while body
            array_add(*statements, set_position_node(reserved_case_id));
            self.waiting_else_block.after_goto_case_id = reserved_case_id;
            log("Reserved case id: %", reserved_case_id);

            // WE ARE HERE!!!
            // Make block add these statements below
            // Set it as the current sub-block (be sad about the extra nested block we add here), may be add inline flag later
            // prevent sub_block from being reprocessed, may use same inline flag
            if_node := New(Code_If);
            if_node.kind = .IF;
            if_node.condition = while_block.condition;
            if_node.then_block = body_block;

            while_statements: [..]*Code_Node;
            array_add(*while_statements, if_node);
            // // We need to end this case here as we do not want to execute code after the while loop until the loop has completed
            position_node, id_ptr := set_position_node(next_available_case_id.*);
            array_add(*while_statements, position_node);
            assert(self.set_me_to_case_id == null);
            self.set_me_to_case_id = id_ptr;
            next_available_case_id.* += 1;

            temp_block := New(Code_Block);
            temp_block.* = self.original.*;
            temp_block.statements = while_statements;

            self.current_sub_block = New(Block_Process);
            self.current_sub_block.original = temp_block;
            self.current_sub_block.inline_statements = true;

            new_block.statements = statements;
            return new_block, while_exit;
        }

        array_add(*statements, stmnt);
    }

    new_block.statements = statements;
    return new_block, .END;
}

position_switch_node :: () -> *Code_Node, *Code_Block {
    switch_code := #code while true if self.position == {
    };
    while_node := compiler_get_nodes(switch_code).(*Code_While);
    switch_node := while_node.block.statements[0].(*Code_If);
    return while_node, switch_node.then_block;
}

add_case :: (cases: *[..]*Code_Node, position: s64) -> *Code_Block {
    case_code: Code;
    {
        case_code = #code case -1;
    }
    case_node := compiler_get_nodes(case_code).(*Code_Case);
    case_node.condition.(*Code_Literal)._s64 = position;

    array_add(cases, case_node);
    return case_node.then_block;
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

// TODO update to not take position but take pointer to _s64 such that it can be set in the future
set_position_node :: (position: s64) -> *Code_Node, *s64 {
    set_code := #code self.position = 0;
    root, nodes := compiler_get_nodes(set_code);
    for nodes if it.kind == .LITERAL {
        it.(*Code_Literal)._s64 = position;
        return root, *it.(*Code_Literal)._s64;
    }
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
convert_declaration_to_assignment :: (declaration: *Code_Declaration) -> *Code_Node {
    if declaration.flags & .IS_CONSTANT {
        return declaration;
    }
    assert(declaration.name != "");
    assert(declaration.expression != null);

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
    Co_state :: struct {
        #insert -> string {
            root, nodes := compiler_get_nodes(code); assert(root.kind == .PROCEDURE_HEADER, "%", root.*);
            header := root.(*Code_Procedure_Header); assert(header.body_or_null != null);

            print_block_members :: (builder: *String_Builder, block: *Code_Block) {
                for block.members {
                    print_to_builder(builder, "%: %;\n", it.name, get_type(it.type));
                }
                for block.statements {
                    if it.kind == {
                    case .BLOCK;
                        sub_block := it.(*Code_Block);
                        print_to_builder(builder, "block_%: struct {\n", it_index); // The name is used to `using` the state in the procedure [also shadowing is allowed]
                        print_block_members(builder, sub_block);
                        print_to_builder(builder, "};\n");
                    case .IF;
                        if_block := it.(*Code_If);
                        print_to_builder(builder, "then_%: struct {\n", it_index);
                        print_block_members(builder, if_block.then_block);
                        print_to_builder(builder, "};\n");

                        if if_block.else_block != null {
                            print_to_builder(builder, "else_%: struct {\n", it_index);
                            print_block_members(builder, if_block.else_block);
                            print_to_builder(builder, "};\n");
                        }
                    case .WHILE;
                        while_block := it.(*Code_While);
                        print_to_builder(builder, "while_%: struct {\n", it_index);
                        print_block_members(builder, while_block.block);
                        print_to_builder(builder, "};\n");
                    }
                }
            }
            builder: String_Builder;
            print_block_members(*builder, header.body_or_null.block);
            return builder_to_string(*builder);
        }
    }
    return Co_state;
}

#scope_file
#import "Basic";
#import "Compiler";
#import "Program_Print";
