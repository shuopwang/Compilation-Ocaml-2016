# 1 "lexer.mll"
 

  open Lexing
  open Parser
  open Ast

  let lexical_error s =
    failwith ("Lexical error : " ^ s)
    
  let comment_cpt = ref 0      

  let keyword_or_ident =
    let h = Hashtbl.create 17 in
    List.iter (fun (s, k) -> Hashtbl.add h s k)
      [ "true",  CONST_BOOL(true);
	"false", CONST_BOOL(false);
	"not",   NOT;
	"if",    IF;
	"then",  THEN;
	"else",  ELSE;
	"var",   VAR;
	"print", PRINT;
	"newline", NEWLINE;
	"exit",  EXIT;
	"begin", BEGIN;
	"end",   END;
	"while", WHILE;
	"fun",   FUN;
	"return", RETURN;
      ]	;
    fun s ->
      try  Hashtbl.find h s
      with Not_found -> IDENT s
	

# 38 "lexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base = 
   "\000\000\230\255\231\255\232\255\233\255\234\255\235\255\002\000\
    \001\000\001\000\003\000\004\000\005\000\006\000\245\255\246\255\
    \247\255\248\255\249\255\078\000\020\000\004\000\002\000\255\255\
    \253\255\244\255\243\255\241\255\239\255\238\255\237\255\236\255\
    \038\000\252\255\253\255\038\000\039\000\255\255\254\255";
  Lexing.lex_backtrk = 
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\024\000\
    \024\000\024\000\015\000\013\000\024\000\024\000\255\255\255\255\
    \255\255\255\255\255\255\004\000\003\000\005\000\001\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\002\000\002\000\255\255\255\255";
  Lexing.lex_default = 
   "\002\000\000\000\000\000\000\000\000\000\000\000\000\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\000\000\000\000\
    \000\000\000\000\000\000\255\255\255\255\255\255\255\255\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \034\000\000\000\000\000\255\255\255\255\000\000\000\000";
  Lexing.lex_trans = 
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\022\000\023\000\022\000\000\000\022\000\000\000\022\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \022\000\012\000\022\000\000\000\000\000\000\000\009\000\029\000\
    \021\000\018\000\015\000\016\000\003\000\017\000\024\000\014\000\
    \020\000\020\000\020\000\020\000\020\000\020\000\020\000\020\000\
    \020\000\020\000\007\000\006\000\010\000\013\000\011\000\031\000\
    \028\000\027\000\026\000\025\000\020\000\020\000\020\000\020\000\
    \020\000\020\000\020\000\020\000\020\000\020\000\036\000\038\000\
    \035\000\037\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\005\000\000\000\004\000\000\000\000\000\
    \000\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\000\000\008\000\030\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\000\000\000\000\000\000\000\000\019\000\000\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\033\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000";
  Lexing.lex_check = 
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\022\000\255\255\000\000\255\255\022\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\022\000\255\255\255\255\255\255\000\000\009\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\021\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\007\000\
    \010\000\011\000\012\000\013\000\020\000\020\000\020\000\020\000\
    \020\000\020\000\020\000\020\000\020\000\020\000\032\000\035\000\
    \032\000\036\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\000\000\255\255\000\000\255\255\255\255\
    \255\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\255\255\000\000\008\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\255\255\255\255\255\255\255\255\019\000\255\255\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\032\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255";
  Lexing.lex_base_code = 
   "";
  Lexing.lex_backtrk_code = 
   "";
  Lexing.lex_default_code = 
   "";
  Lexing.lex_trans_code = 
   "";
  Lexing.lex_check_code = 
   "";
  Lexing.lex_code = 
   "";
}

let rec token lexbuf =
    __ocaml_lex_token_rec lexbuf 0
and __ocaml_lex_token_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 43 "lexer.mll"
      ( new_line lexbuf; token lexbuf )
# 165 "lexer.ml"

  | 1 ->
# 45 "lexer.mll"
      ( token lexbuf )
# 170 "lexer.ml"

  | 2 ->
# 47 "lexer.mll"
      ( incr comment_cpt; comment lexbuf; token lexbuf )
# 175 "lexer.ml"

  | 3 ->
# 49 "lexer.mll"
      ( CONST_INT (int_of_string (lexeme lexbuf)) )
# 180 "lexer.ml"

  | 4 ->
# 51 "lexer.mll"
      ( keyword_or_ident (lexeme lexbuf) )
# 185 "lexer.ml"

  | 5 ->
# 53 "lexer.mll"
      ( LPAREN )
# 190 "lexer.ml"

  | 6 ->
# 55 "lexer.mll"
      ( RPAREN )
# 195 "lexer.ml"

  | 7 ->
# 57 "lexer.mll"
      ( MINUS )
# 200 "lexer.ml"

  | 8 ->
# 59 "lexer.mll"
      ( PLUS )
# 205 "lexer.ml"

  | 9 ->
# 61 "lexer.mll"
      ( MULT )
# 210 "lexer.ml"

  | 10 ->
# 63 "lexer.mll"
      ( DIV )
# 215 "lexer.ml"

  | 11 ->
# 65 "lexer.mll"
      ( EQ )
# 220 "lexer.ml"

  | 12 ->
# 67 "lexer.mll"
      ( NEQ )
# 225 "lexer.ml"

  | 13 ->
# 69 "lexer.mll"
      ( GT )
# 230 "lexer.ml"

  | 14 ->
# 71 "lexer.mll"
      ( GE )
# 235 "lexer.ml"

  | 15 ->
# 73 "lexer.mll"
      ( LT )
# 240 "lexer.ml"

  | 16 ->
# 75 "lexer.mll"
      ( LE )
# 245 "lexer.ml"

  | 17 ->
# 77 "lexer.mll"
      ( AND )
# 250 "lexer.ml"

  | 18 ->
# 79 "lexer.mll"
      ( OR )
# 255 "lexer.ml"

  | 19 ->
# 81 "lexer.mll"
      ( ASSIGN )
# 260 "lexer.ml"

  | 20 ->
# 83 "lexer.mll"
      ( SEMI )
# 265 "lexer.ml"

  | 21 ->
# 85 "lexer.mll"
      ( LBRACKET )
# 270 "lexer.ml"

  | 22 ->
# 87 "lexer.mll"
      ( RBRACKET )
# 275 "lexer.ml"

  | 23 ->
# 89 "lexer.mll"
      ( COMMA )
# 280 "lexer.ml"

  | 24 ->
# 92 "lexer.mll"
      ( lexical_error (lexeme lexbuf) )
# 285 "lexer.ml"

  | 25 ->
# 94 "lexer.mll"
      ( EOF )
# 290 "lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; 
      __ocaml_lex_token_rec lexbuf __ocaml_lex_state

and comment lexbuf =
    __ocaml_lex_comment_rec lexbuf 32
and __ocaml_lex_comment_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 98 "lexer.mll"
      ( incr comment_cpt; comment lexbuf )
# 302 "lexer.ml"

  | 1 ->
# 100 "lexer.mll"
      ( decr comment_cpt; if !comment_cpt > 0 then comment lexbuf )
# 307 "lexer.ml"

  | 2 ->
# 102 "lexer.mll"
      ( comment lexbuf )
# 312 "lexer.ml"

  | 3 ->
# 104 "lexer.mll"
      ( lexical_error "unterminated comment" )
# 317 "lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; 
      __ocaml_lex_comment_rec lexbuf __ocaml_lex_state

;;
