# DONE for runtime
- Code_Scope_Entry
- Code_Type_Instantiation
- Code_Enum
- Code_Directive_Through
- Code_Directive_Place
- Code_Directive_Procedure_Name
- Code_Directive_Load
- Code_Directive_Bytes
- Code_Directive_Code
- Code_Directive_Poke_Name
- Code_Directive_Location
- Code_Directive_Library
- Code_Directive_Wildcard
- Code_Directive_Exists
- Code_Struct
- Code_Using
- Code_Asm
- Code_Note
- Code_Procedure_Header
- Code_Procedure_Body
- Code_Type_Query
- Code_Expression_Query
- Code_Unary_Operator
- Code_Binary_Operator
- Code_Directive_Run
- Code_Directive_Import
- Code_Directive_Modify
- Code_Directive_Scope
- Code_Directive_Module_Parameters
- Code_Directive_Bake

# MAYBE DONE
- Code_Argument
- Code_Block
- Code_Ident
  1. resolved_declaration
- Code_Resolved_Overload


# WIP
- Code_Return  
  1. ifx like in statements
  1. Backticked
  1. Quick lambda
- Code_While  
  1. Code_Loop_Control
  1. named while
  1. ifx like in condition
- Code_Procedure_Call
  1. ifx like in arguments
  1. varargs
  1. macro_expansion_block
    1. `defer
    1. `push_context
    1. return values (unbackticked)
    1. unbackticked yield?
    1. procedure header constants block?
    1. const arguments
    1. usinged param (should be using in struct, member now gets imported to block scope, we do not want that)
  1. context_modification
- Code_Declaration
  1. ifx like in expression
  1. IS_CONSTANT in state!!
  1. HAS_SCOPE_MODIFIER (Remove requirement to always rewrite sub-blocks just to remove any potential backticks)
  1. IS_UNINITIALIZED
  1. IS_ITERATOR
  1. using-ed 
- Code_If
  1. ifx like in condition
  1. MARKED_AS_COMPLETE
Code_Defer
  1. yields inside deferred block
Code_For
  1. Do not rename after loop body code has been shadowed
  1. support multiple inserts of loop body code
  1. non-it/it_index backticked statements
  1. by pointer and other flags
- Code_Directive_Insert
  1. scope
  1. break, continue, remove
  1. internal?
  1. only insert when needed

# TODO

Code_Compound_Declaration
Code_Literal
- Code_Struct_Literal_Info
- Code_Array_Literal_Info
- Code_Pointer_Literal_Info  

Code_Cast
Code_Case
Code_Comma_Separated_Argument
Code_Comma_Separated_Arguments
Code_Extract
Code_Make_Varargs
Code_Loop_Control
Code_Type_Definition
Code_Placeholder

Code_Directive_Add_Context
Code_Directive_Context_Type
Code_Context
Code_Push_Context

# Remove state for code blocks that do not contain yield/return at any level
# Propagate is_expansion for unbackticked return in nested block


# Compiler
Need *Type_info or type -> Code_Type_Instantiation for: `val := 7` to `val: i32`
Naming error? `Code_For.ident_decl` -> `Code_For.it_decl`
Code_Case.owning_if always null ?
