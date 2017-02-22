
(* The type of tokens. *)

type token = 
  | WHILE
  | VGL
  | VAR
  | THEN
  | SEMI
  | RPAREN
  | RCRO
  | RBR
  | PRINT
  | PLUS
  | OR
  | NOT
  | NEWLINE
  | NEQ
  | MULT
  | MINUS
  | LT
  | LPAREN
  | LE
  | LCRO
  | LBR
  | IF
  | IDENT of (Ast.ident)
  | GT
  | GE
  | FOR
  | EXIT
  | EQ
  | EOF
  | END
  | ELSE
  | DIV
  | CONST_INT of (int)
  | CONST_BOOL of (bool)
  | BEGIN
  | ASSIGN
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.prog)
