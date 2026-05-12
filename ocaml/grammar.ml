let grammar = {|
# Facet Language Grammar (EBNF)

## program
```
program ::= fn_def*
```

## fn_def
```
fn_def ::= "fn" ID opt_lifetime_params "(" params ")" "->" ty opt_where_outlives "{" block "}"
```

## opt_lifetime_params
```
opt_lifetime_params ::= ""
                      | "<" LIFETIME ("," LIFETIME)* ">"
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
            | ID
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
place ::= ID
        | "*" place
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
           | "&" ty
           | "&" "mut" ty
           | "&" LIFETIME ty
           | "&" LIFETIME "mut" ty
           | "fn" "(" ty_list ")" "->" ty
```

## ty_list
```
ty_list ::= ""
          | ty ("," ty)*
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
`unrestricted`, `isize`, `f64`, `if`, `else`, `true`, `false`, `bool`, `where`
|}

let print_grammar () = print_string grammar
