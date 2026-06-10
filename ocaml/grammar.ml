let grammar = {|
# Facet Language Grammar (EBNF)

## program
```
program ::= top_item*
top_item ::= fn_def | struct_def | enum_def | trait_def | impl_def | use_def | mod_def
```

## top-level items
```
fn_def ::= opt_pub "fn" ID opt_generic_params "(" params ")" "->" ty opt_fn_where_clause "{" block "}"
struct_def ::= opt_pub "struct" ID opt_generic_params opt_trait_bounds "{" struct_field ("," struct_field)* "}"
enum_def ::= opt_pub "enum" ID opt_generic_params opt_fn_where_clause "{" enum_variant ("," enum_variant)* "}"
trait_def ::= opt_pub "trait" ID opt_generic_params opt_trait_bounds ";"
            | opt_pub "trait" ID opt_generic_params opt_trait_bounds "{" trait_item* "}"
trait_item ::= "type" ID ";"
             | method_sig ";"
method_sig ::= "fn" ID opt_generic_params "(" surface_params ")" "->" surface_ty opt_trait_bounds
impl_def ::= "impl" opt_generic_params path opt_type_args "for" ty ";"
           | "impl" opt_generic_params path opt_type_args "for" ty "{" impl_item* "}"
impl_item ::= "type" ID "=" surface_ty ";"
            | "fn" ID opt_generic_params "(" surface_params ")" "->" surface_ty opt_trait_bounds "{" block "}"
use_def ::= "use" path opt_use_alias ";"
opt_use_alias ::= "" | "as" ID
mod_def ::= opt_pub "mod" ID "{" top_item* "}"
          | opt_pub "mod" ID ";"
opt_pub ::= "" | "pub"
struct_field ::= opt_mut ID ":" ty
enum_variant ::= ID
               | ID "(" ty ("," ty)* ")"
trait_bound ::= ID ":" trait_ref ("+" trait_ref)*
trait_ref ::= path opt_type_args
surface_trait_ref ::= path opt_surface_type_args
opt_fn_where_clause ::= ""
                      | "where" fn_where_item ("," fn_where_item)*
fn_where_item ::= trait_bound | outlives_constraint
```

## generic params and bounds
```
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
surface_params ::= ""
                 | surface_param ("," surface_param)*
```

## param
```
param ::= opt_mut ID ":" ty
surface_param ::= opt_mut ID ":" surface_ty
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
       | "let" "rec" opt_rec_captures rec_fn_def ("and" rec_fn_def)* "in" expr

rec_fn_def ::= ID "(" params ")" "->" ty "{" block "}"
opt_rec_captures ::= ""
                   | "[" capture_list "]"
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
            | qualified_path "{" struct_literal_field ("," struct_literal_field)* "}"
            | ID "<" type_arg ("," type_arg)* ">" "{" struct_literal_field ("," struct_literal_field)* "}"
            | qualified_path "(" [atom_expr ("," atom_expr)*] ")"
            | "(" path opt_type_args atom_expr* ")"  (* direct calls and short UFCS: (Trait::method receiver args) *)
            | ID "::" ID "<" type_arg ("," type_arg)* ">" "(" [atom_expr ("," atom_expr)*] ")"
            | ID "<" type_arg ("," type_arg)* ">" "::" ID "(" [atom_expr ("," atom_expr)*] ")"
            | qualified_path "<" type_arg ("," type_arg)* ">" "::" ID "(" [atom_expr ("," atom_expr)*] ")"
            | ID "<" type_arg ("," type_arg)* ">" "::" ID "<" type_arg ("," type_arg)* ">" "(" [atom_expr ("," atom_expr)*] ")"
            | qualified_path "<" type_arg ("," type_arg)* ">" "::" ID "<" type_arg ("," type_arg)* ">" "(" [atom_expr ("," atom_expr)*] ")"
            | "(" "<" ty "as" trait_ref ">" "::" ID opt_type_args atom_expr* ")"
            | "match" match_scrut "{" match_branch ("," match_branch)* [","] "}"
            | "(" "drop" expr ")"
            | "(" "replace" place atom_expr ")"
            | "(" place "=" atom_expr ")"
            | "(" "&" place ")"
            | "(" "&" "mut" place ")"
            | "(" "*" expr ")"
            | "if" atom_expr "{" block "}" "else" "{" block "}"
            | "if" atom_expr "{" block "}"
            | "closure" "[" capture_list "]" "(" params ")" "->" ty "{" block "}"
```

## place
```
place ::= place_base ("." ID)*
place_base ::= ID
             | "*" place
path ::= ID | qualified_path
qualified_path ::= ID "::" ID ("::" ID)*
struct_literal_field ::= ID "=" expr
match_branch ::= ID "=>" expr
match_scrut ::= place
              | "(" expr ")"
capture_list ::= ""
               | ID ("," ID)*
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
           | path opt_type_args
           | "<" ty "as" trait_ref ">" "::" ID
           | "Self" "::" ID
           | "&" ty
           | "&" "mut" ty
           | "&" LIFETIME ty
           | "&" LIFETIME "mut" ty
           | "fn" "(" ty_list ")" "->" ty
           | "closure" "<" LIFETIME ">" "(" ty_list ")" "->" ty
           | "for" "<" LIFETIME ("," LIFETIME)* ">" "fn" "(" ty_list ")" "->" ty opt_where_outlives
           | "for" "<" ID ("," ID)* ">" "fn" "(" ty_list ")" "->" ty opt_trait_bounds
```

## ty_list
```
ty_list ::= ""
          | ty ("," ty)*
opt_type_args ::= ""
                | "<" type_arg ("," type_arg)* ">"
type_arg ::= LIFETIME | ty
```

## surface_ty
```
surface_ty ::= opt_usage surface_ty_core
opt_usage ::= "" | "affine" | "linear" | "unrestricted"
surface_ty_core ::= "isize"
                  | "f64"
                  | "bool"
                  | "()"
                  | path opt_surface_type_args
                  | "<" surface_ty "as" surface_trait_ref ">" "::" ID
                  | "Self" "::" ID
                  | "&" surface_ty
                  | "&" "mut" surface_ty
                  | "&" LIFETIME surface_ty
                  | "&" LIFETIME "mut" surface_ty
                  | "fn" "(" surface_ty_list ")" "->" surface_ty
                  | "closure" "<" LIFETIME ">" "(" surface_ty_list ")" "->" surface_ty
surface_ty_list ::= ""
                  | surface_ty ("," surface_ty)*
opt_surface_type_args ::= ""
                        | "<" surface_type_arg ("," surface_type_arg)* ">"
surface_type_arg ::= LIFETIME | surface_ty
```

## Literals
```
INT_LIT   ::= ["-"] digit+
FLOAT_LIT ::= ["-"] digit+ "." digit+
ID        ::= (alpha | "_") (alpha | digit | "_")*
LIFETIME  ::= "'" alpha (alpha | digit | "_")*
```

## Reserved words
`fn`, `let`, `rec`, `and`, `in`, `mut`, `drop`, `replace`, `affine`, `linear`,
`unrestricted`, `isize`, `f64`, `bool`, `true`, `false`, `if`, `else`,
`struct`, `enum`, `trait`, `impl`, `mod`, `pub`, `use`, `as`, `for`, `where`, `closure`, `match`
|}

let print_grammar () = print_string grammar
