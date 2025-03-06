// Header does not go into body
// Procedure goes into arguments, etc, but not into ancillary information like overloads.
// No block.parent, or members! jst statements.


// get_subexpressions is here so that you can use it as a building block
// if you want something different than the kinds of traversal
// provided in this file. It just gives you what the sub-expression
// pointers are for any particular node, so you can recurse or
// iterate into them, or ... whatever.

maybe_array_add :: inline (array: *[..] **Code_Node, item: **Code_Node) #no_abc {
    if item.* inline array_add(array, item);
}

get_subexpressions :: (node: *Code_Node, pointers: *[..] **Code_Node) {
    using Code_Node.Kind;

    // This is an exceptions that probably needs to be turned into acustomization point.
    // This is needed so that we do not replace members of structs that happen to have the same name as a local.
    // When changing the code from local = 42 to self.state.local = 42, we do not want to change the identifier other.local to other.self.state.local.
    if node.kind == BINARY_OPERATOR {
        using c := cast(*Code_Binary_Operator) node;
        if c.operator_type == #char "." {
          array_add(pointers, *left);
          return;
        }
    }
    // End of exception.


    A :: (ident: Code) #expand { // @Speed: This is supposed to avoid the 'if' but we have a problem, so it is back in.
        if (#insert ident).*  inline array_add(pointers, (#insert ident).(**Code_Node));
    }

    M :: (ident: Code) #expand {
        if (#insert ident).*  inline maybe_array_add(pointers, (#insert ident).(**Code_Node));
    }

    if #complete node.kind == {
      case UNINITIALIZED;  // Should not happen!

      case BLOCK;
        c := cast(*Code_Block) node;
        for * c.statements A(it);
        // array_add(pointers, ..c.statements);  // Can't use A here because of the .. ; hmm!!

      case LITERAL;

      case IDENT;

      case UNARY_OPERATOR;
        c := cast(*Code_Unary_Operator) node;
        array_add(pointers, *c.subexpression);

      case BINARY_OPERATOR;
        using c := cast(*Code_Binary_Operator) node;
        A(*left);
        M(*right);

      case PROCEDURE_BODY;
        using c := cast(*Code_Procedure_Body) node;
        A(*block);

      case PROCEDURE_CALL;
        call := cast(*Code_Procedure_Call) node;
        A(*call.procedure_expression);
        for * call.arguments_unsorted {
            A(*it.expression);
        }

        M(*call.macro_expansion_block);

      case CONTEXT;
      case WHILE;
        using c := cast(*Code_While) node;
        A(*condition);
        A(*block);

      case IF;
        using c := cast(*Code_If) node;
        A(*condition);
        A(*then_block);
        M(*else_block);

      case LOOP_CONTROL;
        c := cast(*Code_Loop_Control) node;
        A(*c.target_ident);

      case CASE;
        using c := cast(*Code_Case) node;
        A(*condition);
        A(*then_block);

      case RETURN;
        c := cast(*Code_Return) node;
        for c.arguments_unsorted A(*it.expression);

      case FOR;
        using c := cast(*Code_For) node;
        A(*iteration_expression);
        M(*iteration_expression_right);
        A(*block);
        M(*want_pointer_expression);
        M(*want_reverse_expression);
        M(*want_replacement_for_expansion);

      case TYPE_DEFINITION;

      case TYPE_INSTANTIATION;
        using c := cast(*Code_Type_Instantiation) node;
        M(*pointer_to);
        M(*type_directive_target);
        M(*array_element_type);
        M(*array_dimension);

      case ENUM;
        using c := cast(*Code_Enum) node;
        array_add(pointers, *c.block.(*Code_Node));

      case PROCEDURE_HEADER;
        using c := cast(*Code_Procedure_Header) node;
        for * arguments array_add(pointers, it.(**Code_Node));
        for * returns   array_add(pointers, it.(**Code_Node));
        for * notes     array_add(pointers, it.(**Code_Node));

      case STRUCT;
        using c := cast(*Code_Struct) node;
        A(*block);
        for * notes A(it);

      case COMMA_SEPARATED_ARGUMENTS;
        c := cast(*Code_Comma_Separated_Arguments) node;
        for * c.arguments array_add(pointers, * it.node);

      case EXTRACT;

      case DIRECTIVE_BYTES;
        using c := cast(*Code_Directive_Bytes) node;
        A(*expression);

      case MAKE_VARARGS;
        c := cast(*Code_Make_Varargs) node;
        for * c.expressions A(it);

      case DECLARATION;
        using c := cast(*Code_Declaration) node;
        M(*type_inst);
        M(*expression);
        M(*alignment_expression);
        for * notes M(it);

      case RESOLVED_OVERLOAD;
        using c := cast(*Code_Resolved_Overload) node;
        A(*result);
        A(*source_expression);

      case CAST;
        using c := cast(*Code_Cast) node;
        A(*target_type);
        A(*expression);

      case DIRECTIVE_IMPORT;
        using c := cast(*Code_Directive_Import) node;
        M(*module_parameters_call);
        M(*program_parameters_call);

      case DIRECTIVE_THIS;
      case DIRECTIVE_THROUGH;
      case DIRECTIVE_LOAD;

      case DIRECTIVE_RUN;
        using c := cast(*Code_Directive_Run) node;
        A(*procedure);
        M(*procedure.body_or_null);

      case DIRECTIVE_CODE;
        c := cast(*Code_Directive_Code) node;
        if c.expression array_add(pointers, *c.expression);  // c.expression could be null if this is #code,null!

      case DIRECTIVE_POKE_NAME;
        c := cast(*Code_Directive_Poke_Name) node;
      case ASM;
        c := cast(*Code_Asm) node;
      case DIRECTIVE_BAKE;
        c := cast(*Code_Directive_Bake) node;
        array_add(pointers, *c.procedure_call.(*Code_Node));
      case DIRECTIVE_MODIFY;
        c := cast(*Code_Directive_Modify) node;
        A(*c.block);

      case DIRECTIVE_LIBRARY;

      case TYPE_QUERY;
        using c := cast(*Code_Type_Query) node;
        M(*type_to_query);

      case EXPRESSION_QUERY;
        using c := cast(*Code_Expression_Query) node;
        M(*expression_to_query);

      case PUSH_CONTEXT;
        using c := cast(*Code_Push_Context) node;
        A(*to_push);
        A(*block);

      case NOTE;
        c := cast(*Code_Note) node;

      case DIRECTIVE_PLACE;
      case DIRECTIVE_SCOPE;
      case DIRECTIVE_LOCATION;
        using c := cast(*Code_Directive_Location) node;
        M(*expression);

      case DIRECTIVE_MODULE_PARAMETERS;
        using c := cast(*Code_Directive_Module_Parameters) node;
        M(*module_parameters);
        M(*program_parameters);

      case DIRECTIVE_ADD_CONTEXT;
//        c := cast(*Code_Directive_Add_Context) node;

      case DIRECTIVE_COMPILE_TIME;

      case COMPOUND_DECLARATION;
        using c := cast(*Code_Compound_Declaration) node;
        M(*comma_separated_assignment);
        array_add(pointers, *c.declaration_properties.(*Code_Node));
        M(*alignment_expression);
        for * c.notes array_add(pointers, it.(**Code_Node));

      case DEFER;
        using c := cast(*Code_Defer) node;
        A(*block);

      case USING;
        using c := cast(*Code_Using) node;
        A(*expression);

      case PLACEHOLDER;

      case DIRECTIVE_INSERT;
        using c := cast(*Code_Directive_Insert) node;
        A(*expression);

      case DIRECTIVE_PROCEDURE_NAME;
        using c := cast(*Code_Directive_Procedure_Name) node;
        A(*argument);

      case DIRECTIVE_WILDCARD;

      case DIRECTIVE_EXISTS;
        using c := cast(*Code_Directive_Exists) node;
        A(*query_expression);
        A(*sync_expression);

      case DIRECTIVE_CONTEXT_TYPE;
    }
}

// Collect all subexpressions, recursively, breadth_first traversal.
get_recursive_nodes_breadth_first :: (node: **Code_Node, pointers: *[..] **Code_Node) {
    cursor := pointers.count;

    array_add(pointers, node);

    while cursor < pointers.count {
        sub := pointers.*[cursor].*;
        get_subexpressions(sub, pointers);
        cursor += 1;
    }
}

get_recursive_nodes_depth_first :: (node: **Code_Node, pointers: *[..] **Code_Node) {
    stack: [..] **Code_Node;
    stack.allocator = temp;

    array_add(*stack, node);
    while stack.count {
        sub := pop(*stack);
        array_add(pointers, sub);
        get_subexpressions(sub.*, *stack);
    }
}

replace_all_ident :: (root: *Code_Node, target_name: string, replacement: *Code_Node) {
    pointers: [..] **Code_Node;
    pointers.allocator = temp;
    get_recursive_nodes_breadth_first(*root, *pointers);

    for pointers {
        if it.*.kind == .IDENT && it.*.(*Code_Ident).name == target_name {
            it.* = replacement;
        }
    }
}

#scope_module
#import "Compiler";
#import "Basic";
