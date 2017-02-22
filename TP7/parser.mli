
(* The type of tokens. *)

type token = 
  | WHILE
  | VAR
  | TO
  | THEN
  | SEMI
  | RPAREN
  | RETURN
  | RBRACKET
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
  | LBRACKET
  | INT
  | IF
  | IDENT of (Ast.ident)
  | GT
  | GE
  | FUN
  | FOR
  | EXIT
  | EQ
  | EOF
  | END
  | ELSE
  | DIV
  | CONST_INT of (int)
  | CONST_BOOL of (bool)
  | COMMA
  | COLON
  | BOOL
  | BEGIN
  | ASSIGN
  | ARRAY
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.prog)
