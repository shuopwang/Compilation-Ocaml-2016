
(* The type of tokens. *)

type token = 
  | UMINUS
  | THEN
  | RPAR
  | PLUS
  | OR
  | NOT
  | NEQ
  | MULT
  | MINUS
  | LT
  | LPAR
  | LE
  | INT of (int)
  | IF
  | GT
  | GE
  | EQ
  | EOF
  | ELSE
  | DIV
  | BOOL of (bool)
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val toplevel_expr: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.expr)
