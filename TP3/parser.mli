
(* The type of tokens. *)

type token = 
  | WHILE
  | VAR
  | THEN
  | SEMI
  | RPAREN
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
  | IF
  | IDENT of (string)
  | GT
  | GE
  | EXIT
  | EQ
  | EOF
  | END
  | ELSE
  | DIV
  | CONST_INT of (int)
  | CONST_BOOL of (bool)
  | BEGIN
  | ASSI
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.prog)
