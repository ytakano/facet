let grammar = {|
# Facet Language Grammar (EBNF)

## program
```
program ::= fn_def*
```

## fn_def
```
fn_def ::= "fn" ID "(" params ")" "->" ty "{" block "}"
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
            | ID
            | "(" "drop" expr ")"
            | "(" "replace" ID atom_expr ")"
            | "(" ID atom_expr* ")"
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
           | "()"
           | "&" ty
           | "&" "mut" ty
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
```

## Reserved words
`fn`, `let`, `in`, `mut`, `drop`, `replace`, `affine`, `linear`,
`unrestricted`, `isize`, `f64`
|}

let print_grammar () = print_string grammar
