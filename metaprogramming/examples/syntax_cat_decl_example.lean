declare_syntax_cat           imp_program
syntax "skip"              : imp_program
syntax ident ":=" imp_expr : imp_program

syntax imp_program ";;" imp_program : imp_program

syntax "if" imp_expr "then" imp_program "else" imp_program "fi" : imp_program
syntax "while" imp_expr "do" imp_program "od" : imp_program
