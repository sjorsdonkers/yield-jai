logx :: (root: *Code_Node) {
    debug_builder: String_Builder;
    print_expression(*debug_builder, root);
    log("%", builder_to_string(*debug_builder));
}

Co_Status :: enum { YIELD; RETURN; IMPLEMENTATION_ERROR; }
Coroutine :: struct (State: Type, Output: Type) {
    state   : State;
    position: s64;
    next : (*Coroutine(State, Output)) -> Co_Status, Output;
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

into_yielding :: ($code: Code) -> Coroutinator #compile_time {
    State  :: #run extract_state(code);
    Output :: #run extract_output(code);

    new_code := #run -> Code {
        root, nodes := compiler_get_nodes(code);
        assert(root.kind == .PROCEDURE_HEADER, "%", root.*);
        header := root.(*Code_Procedure_Header);
        original_returns := header.returns;
        {
            // Add coroutine as first argument
            self_code := #code self: *COROUTINE;
            self_decl := compiler_get_nodes(self_code);
            assert(self_decl.kind == .DECLARATION, "%", self_decl.kind);

            arguments: [..] *Code_Declaration;
            array_add(*arguments, self_decl.(*Code_Declaration));
            for header.arguments array_add(*arguments, it);
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
        array_add(*top_statements, compiler_get_nodes(#code using self.state;));

        loop_node, cases_block := position_switch_node();
        array_add(*top_statements, loop_node);

        cases: [..]*Code_Node;
        add_case_default(*cases);
        current_case_block := add_case(*cases, 0);
        next_position := 1; //return this from add_case?

        statements: [..] *Code_Node;
        assert(header.body_or_null != null);

        sub_block := Block_Process.{original = header.body_or_null.block};
        while sub_block.statement_index < sub_block.original.statements.count {
            new_block, exit := process_block(*sub_block, *next_position);
            if new_block.statements.count > 0 { // 0 since no using state statement
                array_add(*statements, ..new_block.statements);
            }
            if exit != .END {
                current_case_block.statements = statements;
                statements = [..]*Code_Node.{};
                current_case_block = add_case(*cases, next_position);
                next_position += 1;
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
    return Coroutinator.{Coroutine(State, Output), new_code};
}

Block_Exit :: enum { END; RETURN; YIELD; }

Block_Process :: struct {
    original: *Code_Block;
    statement_index := 0;
    current_sub_block: *Block_Process; // Can be null
    name: string;
}

using_state :: (name: string) -> *Code_Using {
    root := compiler_get_nodes(#code using tmp;).(*Code_Using);
    ident := root.expression.(*Code_Ident);
    ident.name = name;
    return root;
}

process_block :: (original: *Block_Process, next_position: *s64) -> *Code_Block, Block_Exit { //original_block to take statements from should modify this such that remaining statements can be put into the next positions block)
    new_block := New(Code_Block);
    new_block.* = original.original.*;

    statements : [..]*Code_Node;
    if original.name then array_add(*statements, using_state(original.name));

    for original.statement_index..original.original.statements.count-1 {
        original.statement_index += 1; // Usually we want to increment, sometimes we reverse this for cases like BLOCK
        stmnt := original.original.statements[it];

        if stmnt.kind == {
        case .RETURN;
            array_add(*statements, set_position_node(0));
            array_add(*statements, return_with_costatus(stmnt.(*Code_Return)));

            new_block.statements = statements;
            return new_block, .RETURN;
        case .PROCEDURE_CALL;
            call := stmnt.(*Code_Procedure_Call);
            if call.procedure_expression.kind == .IDENT
            && "yield" == call.procedure_expression.(*Code_Ident).name {
                array_add(*statements, set_position_node(next_position.*));
                array_add(*statements, convert_yield_to_return(call));

                new_block.statements = statements;
                return new_block, .YIELD;
            }
        case .DECLARATION;
            array_add(*statements, convert_declaration_to_assignment(stmnt.(*Code_Declaration)));
            continue; // TODO compound declarations
        case .BLOCK;
            if original.current_sub_block == null {
                original.current_sub_block = New(Block_Process);
                original.current_sub_block.original = stmnt.(*Code_Block);
                original.current_sub_block.name = tprint("block_%", original.statement_index - 1);
            }

            sub_block, sub_exit := process_block(original.current_sub_block, next_position);
            if sub_block.statements.count > 1 { // 1 for using state statement
                array_add(*statements, sub_block);
            }

            if original.current_sub_block.statement_index < original.current_sub_block.original.statements.count {
                original.statement_index -= 1; // We are not be done with this block after this, so make sure we revisit it next time
            }

            new_block.statements = statements;
            return new_block, sub_exit;
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

set_position_node :: (position: s64) -> *Code_Node {
    set_code := #code self.position = 0;
    root, nodes := compiler_get_nodes(set_code);
    for nodes if it.kind == .LITERAL {
        it.(*Code_Literal)._s64 = position;
    }
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

extract_state :: ($code: Code) -> Type #compile_time {
    Co_state :: struct {
        #insert -> string {
            root, nodes := compiler_get_nodes(code); assert(root.kind == .PROCEDURE_HEADER, "%", root.*);
            header := root.(*Code_Procedure_Header); assert(header.body_or_null != null);

            print_block_members :: (builder: *String_Builder, block: *Code_Block) {
                for block.members {
                    print_to_builder(builder, "%: %;\n", it.name, get_type(it.type));
                }
                for block.statements if it.kind == .BLOCK {
                    sub_block := it.(*Code_Block);
                    print_to_builder(builder, "block_%: struct {\n", it_index); // The name is used to `using` the state in the procedure [also shadowing is allowed]
                    print_block_members(builder, sub_block);
                    print_to_builder(builder, "};\n");
                }
            }
            builder: String_Builder;
            print_block_members(*builder, header.body_or_null.block);
            return builder_to_string(*builder);
        }
    }
    return Co_state;
}

Coroutinator :: struct {
    Coroutine: Type;
    next : Code;
}

init :: ($yielding: Coroutinator) -> $COROUTINE #modify {
    COROUTINE = yielding.Coroutine;
    return true;
} {
    return.{next=#insert #run yielding.next};
}

gen :: () -> s64 {
    iota := 0;
    while true {
        yield(iota);
        iota += 1;
    }
}
cogen :: (self: *Coroutine(s64, s64)) -> Co_Status, s64 {
    a := 17.;
    defer self.state += 1;
    return .YIELD, self.state;
}

mynext :: (self: *Coroutine(s64, s64)) -> Co_Status, s64 {
    for self.state..2 {
        print("state: %\n", self.state);

        output := self.state;
        self.state += 1;
        return .YIELD, output;
    }
    return .RETURN, -1;
};

my_proc :: () -> s64 {
    for 0..2 {
        print("it: %\n", it);
        yield(it);
    }
    return -1;
}



yield :: (return_value: s64) #expand {
    `return return_value;
}

// #add_context toml_custom_type_to_value := default_custom_type_to_value;

#scope_file
#import "Basic";
#import "Compiler";
#import "Program_Print";
