let grammar = {|
# Facet Language Grammar (EBNF)

## program
```
program ::= top_item*
top_item ::= fn_def | struct_def | trait_def | impl_def
```

## top-level items
```
fn_def ::= "fn" ID opt_lifetime_params "(" params ")" "->" ty opt_where_outlives "{" block "}"
struct_def ::= "struct" ID opt_generic_params opt_trait_bounds "{" struct_field ("," struct_field)* "}"
trait_def ::= "trait" ID opt_generic_params opt_trait_bounds ";"
impl_def ::= "impl" opt_generic_params ID opt_type_args "for" ty ";"
struct_field ::= opt_mut ID ":" ty
trait_bound ::= ID ":" trait_ref ("+" trait_ref)*
trait_ref ::= ID opt_type_args
```

## generic params and bounds
```
opt_lifetime_params ::= ""
                      | "<" LIFETIME ("," LIFETIME)* ">"
opt_generic_params ::= ""
                     | "<" generic_param ("," generic_param)* ">"
generic_param ::= LIFETIME | ID
opt_trait_bounds ::= ""
                   | "where" trait_bound ("," trait_bound)*
```

## params
```
params ::= ""
         | param ("," param)*
```

## param
```
param ::= opt_mut ID ":" ty
```

## opt_mut
```
opt_mut ::= ""
          | "mut"
```

## block
```
block ::= stmt+ expr
        | stmt+
        | expr
```

## stmt
```
stmt ::= let_stmt ";"
       | atom_expr ";"
```

## let_stmt
```
let_stmt ::= "let" opt_mut var_name ":" ty "=" expr
           | "let" opt_mut var_name "=" expr
```

## var_name
```
var_name ::= ID
           | "_"
```

## expr
```
expr ::= atom_expr
       | "let" opt_mut var_name ":" ty "=" expr "in" expr
       | "let" opt_mut var_name "=" expr "in" expr
```

## atom_expr
```
atom_expr ::= "()"
            | INT_LIT
            | FLOAT_LIT
            | "true"
            | "false"
            | place
            | ID "{" struct_literal_field ("," struct_literal_field)* "}"
            | ID "<" type_arg ("," type_arg)* ">" "{" struct_literal_field ("," struct_literal_field)* "}"
            | "(" "drop" expr ")"
            | "(" "replace" place atom_expr ")"
            | "(" place "=" atom_expr ")"
            | "(" "&" place ")"
            | "(" "&" "mut" place ")"
            | "(" "*" expr ")"
            | "(" ID atom_expr* ")"
            | "if" atom_expr "{" block "}" "else" "{" block "}"
            | "if" atom_expr "{" block "}"
```

## place
```
place ::= place_base ("." ID)*
place_base ::= ID
             | "*" place
struct_literal_field ::= ID "=" expr
```

## ty
```
ty ::= "affine"       ty_core
     | "linear"       ty_core
     | "unrestricted" ty_core
```

## ty_core
```
ty_core ::= "isize"
           | "f64"
           | "bool"
           | "()"
           | ID opt_type_args
           | "&" ty
           | "&" "mut" ty
           | "&" LIFETIME ty
           | "&" LIFETIME "mut" ty
           | "fn" "(" ty_list ")" "->" ty
           | "for" "<" LIFETIME ("," LIFETIME)* ">" "fn" "(" ty_list ")" "->" ty opt_where_outlives
```

## ty_list
```
ty_list ::= ""
          | ty ("," ty)*
opt_type_args ::= ""
                | "<" type_arg ("," type_arg)* ">"
type_arg ::= LIFETIME | ty
```

## Literals
```
INT_LIT   ::= ["-"] digit+
FLOAT_LIT ::= ["-"] digit+ "." digit+
ID        ::= (alpha | "_") (alpha | digit | "_")*
LIFETIME  ::= "'" alpha (alpha | digit | "_")*
```

## Reserved words
`fn`, `let`, `in`, `mut`, `drop`, `replace`, `affine`, `linear`,
`unrestricted`, `isize`, `f64`, `bool`, `true`, `false`, `if`, `else`,
`struct`, `trait`, `impl`, `for`, `where`
|}

let print_grammar () = print_string grammar
