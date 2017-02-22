
module Basics = struct
  
  exception Error
  
  type token = 
    | WHILE
    | VAR
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
    | IF
    | IDENT of (Ast.ident)
    | GT
    | GE
    | FUN
    | EXIT
    | EQ
    | EOF
    | END
    | ELSE
    | DIV
    | CONST_INT of (int)
    | CONST_BOOL of (bool)
    | COMMA
    | BEGIN
    | ASSIGN
    | AND
  
end

include Basics

let _eRR =
  Basics.Error

type _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  _menhir_token: token;
  mutable _menhir_error: bool
}

and _menhir_state = 
  | MenhirState101
  | MenhirState99
  | MenhirState98
  | MenhirState95
  | MenhirState89
  | MenhirState85
  | MenhirState83
  | MenhirState79
  | MenhirState78
  | MenhirState75
  | MenhirState73
  | MenhirState72
  | MenhirState71
  | MenhirState67
  | MenhirState66
  | MenhirState64
  | MenhirState63
  | MenhirState59
  | MenhirState58
  | MenhirState57
  | MenhirState56
  | MenhirState54
  | MenhirState52
  | MenhirState51
  | MenhirState50
  | MenhirState49
  | MenhirState48
  | MenhirState47
  | MenhirState45
  | MenhirState44
  | MenhirState43
  | MenhirState42
  | MenhirState41
  | MenhirState40
  | MenhirState39
  | MenhirState38
  | MenhirState37
  | MenhirState36
  | MenhirState35
  | MenhirState34
  | MenhirState33
  | MenhirState30
  | MenhirState29
  | MenhirState28
  | MenhirState27
  | MenhirState26
  | MenhirState25
  | MenhirState24
  | MenhirState23
  | MenhirState21
  | MenhirState20
  | MenhirState19
  | MenhirState18
  | MenhirState17
  | MenhirState16
  | MenhirState15
  | MenhirState8
  | MenhirState6
  | MenhirState5
  | MenhirState4
  | MenhirState3
  | MenhirState2
  | MenhirState1
  | MenhirState0
  

  open Astcommon
  open Ast

  let current_pos () =
    Parsing.symbol_start_pos (),
    Parsing.symbol_end_pos ()


let rec _menhir_reduce25 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.call) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (c : (Ast.call))) = _menhir_stack in
    let _v : (Ast.expr) =                                            ( Ecall c             ) in
    _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce24 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr * Ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (f : (Ast.expr * Ast.expr))) = _menhir_stack in
    let _v : (Ast.expr) =                          ( let e1, e2 = f in Egetarr (e1, e2)    ) in
    _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_separated_nonempty_list_COMMA_expr_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.expr list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState8 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (x : (Ast.expr list)) = _v in
        let _v : (Ast.expr list) =     ( x ) in
        _menhir_goto_loption_separated_nonempty_list_COMMA_expr__ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (Ast.expr list)) = _v in
        let ((_menhir_stack, _menhir_s, (x : (Ast.expr))), _) = _menhir_stack in
        let _2 = () in
        let _v : (Ast.expr list) =     ( x :: xs ) in
        _menhir_goto_separated_nonempty_list_COMMA_expr_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run16 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState16

and _menhir_run23 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState23
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState23
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState23
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState23
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState23
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState23

and _menhir_run25 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState25
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState25
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState25
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState25
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState25
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState25

and _menhir_run18 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState18

and _menhir_run27 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState27
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState27
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState27
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState27
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState27
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState27

and _menhir_run33 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState33

and _menhir_run35 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState35 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState35 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState35 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState35
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState35
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState35
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState35
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState35
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState35

and _menhir_run20 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState20

and _menhir_run37 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState37 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState37 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState37 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState37
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState37
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState37
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState37
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState37
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState37

and _menhir_run39 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState39

and _menhir_run41 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState41
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState41
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState41
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState41
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState41
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState41

and _menhir_run29 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState29
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState29
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState29
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState29
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState29
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState29

and _menhir_run43 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState43 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState43 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState43 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState43
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState43
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState43
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState43
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState43
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState43

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.fprintf Pervasives.stderr "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_goto_loption_separated_nonempty_list_COMMA_expr__ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.expr list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (id : (Ast.ident))), _, (xs0 : (Ast.expr list))) = _menhir_stack in
        let _4 = () in
        let _2 = () in
        let _v : (Ast.call) = let params =
          let xs = xs0 in
              ( xs )
        in
                                                   ( id, params          ) in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        (match _menhir_s with
        | MenhirState1 | MenhirState98 | MenhirState78 | MenhirState71 | MenhirState73 | MenhirState66 | MenhirState63 | MenhirState2 | MenhirState3 | MenhirState4 | MenhirState5 | MenhirState6 | MenhirState48 | MenhirState50 | MenhirState8 | MenhirState45 | MenhirState16 | MenhirState18 | MenhirState20 | MenhirState23 | MenhirState43 | MenhirState41 | MenhirState39 | MenhirState37 | MenhirState35 | MenhirState33 | MenhirState25 | MenhirState27 | MenhirState29 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            _menhir_reduce25 _menhir_env (Obj.magic _menhir_stack)
        | MenhirState0 | MenhirState59 | MenhirState95 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | SEMI ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (c : (Ast.call))) = _menhir_stack in
                let _2 = () in
                let _v : (Ast.instr) =                                       ( Icall c             ) in
                _menhir_goto_instr _menhir_env _menhir_stack _menhir_s _v
            | AND | DIV | EQ | GE | GT | LBRACKET | LE | LT | MINUS | MULT | NEQ | OR | PLUS ->
                _menhir_reduce25 _menhir_env (Obj.magic _menhir_stack)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            _menhir_fail ())
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_separated_nonempty_list_COMMA_IDENT_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.ident list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState85 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (Ast.ident list)) = _v in
        let (_menhir_stack, _menhir_s, (x : (Ast.ident))) = _menhir_stack in
        let _2 = () in
        let _v : (Ast.ident list) =     ( x :: xs ) in
        _menhir_goto_separated_nonempty_list_COMMA_IDENT_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState83 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (x : (Ast.ident list)) = _v in
        let _v : (Ast.ident list) =     ( x ) in
        _menhir_goto_loption_separated_nonempty_list_COMMA_IDENT__ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_expr : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState45 | MenhirState8 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState15
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState15 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CONST_BOOL _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _v
            | CONST_INT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _v
            | IDENT _v ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _v
            | IF ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState45
            | LBRACKET ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState45
            | LPAREN ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState45
            | MINUS ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState45
            | NOT ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState45
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState45)
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState15
        | EQ ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState15
        | GE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState15
        | GT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState15
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState15
        | LE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState15
        | LT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState15
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState15
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState15
        | NEQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState15
        | OR ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState15
        | PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState15
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (x : (Ast.expr))) = _menhir_stack in
            let _v : (Ast.expr list) =     ( [ x ] ) in
            _menhir_goto_separated_nonempty_list_COMMA_expr_ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState15)
    | MenhirState16 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState17
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState17
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState17
        | AND | BEGIN | COMMA | ELSE | EQ | GE | GT | LE | LT | MINUS | NEQ | OR | PLUS | RBRACKET | RPAREN | SEMI | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _10 = () in
            let _v : (Ast.expr) = let op =
              let _1 = _10 in
                      ( Plus  )
            in
                                                       ( Ebinop (op, e1, e2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState17)
    | MenhirState18 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState19
        | AND | BEGIN | COMMA | DIV | ELSE | EQ | GE | GT | LE | LT | MINUS | MULT | NEQ | OR | PLUS | RBRACKET | RPAREN | SEMI | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _10 = () in
            let _v : (Ast.expr) = let op =
              let _1 = _10 in
                      ( Mult  )
            in
                                                       ( Ebinop (op, e1, e2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState19)
    | MenhirState20 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | EQ ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | GE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | GT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | LE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | LT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | NEQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | OR ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | RBRACKET ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState21 in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _v : (Ast.expr * Ast.expr) =                                            ( (e1, e2)            ) in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            (match _menhir_s with
            | MenhirState98 | MenhirState78 | MenhirState73 | MenhirState71 | MenhirState66 | MenhirState63 | MenhirState1 | MenhirState2 | MenhirState3 | MenhirState4 | MenhirState5 | MenhirState50 | MenhirState48 | MenhirState6 | MenhirState45 | MenhirState43 | MenhirState41 | MenhirState39 | MenhirState37 | MenhirState35 | MenhirState33 | MenhirState29 | MenhirState27 | MenhirState25 | MenhirState23 | MenhirState20 | MenhirState18 | MenhirState16 | MenhirState8 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                _menhir_reduce24 _menhir_env (Obj.magic _menhir_stack)
            | MenhirState0 | MenhirState59 | MenhirState95 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | ASSIGN ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | CONST_BOOL _v ->
                        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _v
                    | CONST_INT _v ->
                        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _v
                    | IDENT _v ->
                        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _v
                    | IF ->
                        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState98
                    | LBRACKET ->
                        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState98
                    | LPAREN ->
                        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState98
                    | MINUS ->
                        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState98
                    | NOT ->
                        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState98
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState98)
                | AND | DIV | EQ | GE | GT | LBRACKET | LE | LT | MINUS | MULT | NEQ | OR | PLUS ->
                    _menhir_reduce24 _menhir_env (Obj.magic _menhir_stack)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                _menhir_fail ())
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState21)
    | MenhirState23 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState24
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState24
        | EQ ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState24
        | GE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState24
        | GT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState24
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState24
        | LE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState24
        | LT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState24
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState24
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState24
        | NEQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState24
        | PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState24
        | BEGIN | COMMA | ELSE | OR | RBRACKET | RPAREN | SEMI | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _10 = () in
            let _v : (Ast.expr) = let op =
              let _1 = _10 in
                      ( Or    )
            in
                                                       ( Ebinop (op, e1, e2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState24)
    | MenhirState25 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState26
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState26
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState26
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState26
        | PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState26
        | AND | BEGIN | COMMA | ELSE | EQ | GE | GT | LE | LT | NEQ | OR | RBRACKET | RPAREN | SEMI | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _10 = () in
            let _v : (Ast.expr) = let op =
              let _1 = _10 in
                      ( Neq   )
            in
                                                       ( Ebinop (op, e1, e2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState26)
    | MenhirState27 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | AND | BEGIN | COMMA | ELSE | EQ | GE | GT | LE | LT | MINUS | NEQ | OR | PLUS | RBRACKET | RPAREN | SEMI | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _10 = () in
            let _v : (Ast.expr) = let op =
              let _1 = _10 in
                      ( Minus )
            in
                                                       ( Ebinop (op, e1, e2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState28)
    | MenhirState29 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | AND | BEGIN | COMMA | DIV | ELSE | EQ | GE | GT | LE | LT | MINUS | MULT | NEQ | OR | PLUS | RBRACKET | RPAREN | SEMI | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _10 = () in
            let _v : (Ast.expr) = let op =
              let _1 = _10 in
                      ( Div   )
            in
                                                       ( Ebinop (op, e1, e2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState30)
    | MenhirState33 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | AND | BEGIN | COMMA | ELSE | EQ | GE | GT | LE | LT | NEQ | OR | RBRACKET | RPAREN | SEMI | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _10 = () in
            let _v : (Ast.expr) = let op =
              let _1 = _10 in
                      ( Lt    )
            in
                                                       ( Ebinop (op, e1, e2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState34)
    | MenhirState35 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | AND | BEGIN | COMMA | ELSE | EQ | GE | GT | LE | LT | NEQ | OR | RBRACKET | RPAREN | SEMI | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _10 = () in
            let _v : (Ast.expr) = let op =
              let _1 = _10 in
                      ( Le    )
            in
                                                       ( Ebinop (op, e1, e2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState36)
    | MenhirState37 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | AND | BEGIN | COMMA | ELSE | EQ | GE | GT | LE | LT | NEQ | OR | RBRACKET | RPAREN | SEMI | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _10 = () in
            let _v : (Ast.expr) = let op =
              let _1 = _10 in
                      ( Gt    )
            in
                                                       ( Ebinop (op, e1, e2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState38)
    | MenhirState39 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | AND | BEGIN | COMMA | ELSE | EQ | GE | GT | LE | LT | NEQ | OR | RBRACKET | RPAREN | SEMI | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _10 = () in
            let _v : (Ast.expr) = let op =
              let _1 = _10 in
                      ( Ge    )
            in
                                                       ( Ebinop (op, e1, e2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState40)
    | MenhirState41 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | AND | BEGIN | COMMA | ELSE | EQ | GE | GT | LE | LT | NEQ | OR | RBRACKET | RPAREN | SEMI | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _10 = () in
            let _v : (Ast.expr) = let op =
              let _1 = _10 in
                      ( Eq    )
            in
                                                       ( Ebinop (op, e1, e2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState42)
    | MenhirState43 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | EQ ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | GE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | GT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | LE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | LT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | NEQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | AND | BEGIN | COMMA | ELSE | OR | RBRACKET | RPAREN | SEMI | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _10 = () in
            let _v : (Ast.expr) = let op =
              let _1 = _10 in
                      ( And   )
            in
                                                       ( Ebinop (op, e1, e2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState44)
    | MenhirState6 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState47
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState47
        | EQ ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState47
        | GE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState47
        | GT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState47
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState47
        | LE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState47
        | LT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState47
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState47
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState47
        | NEQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState47
        | OR ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState47
        | PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState47
        | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState47 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CONST_BOOL _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _v
            | CONST_INT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _v
            | IDENT _v ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _v
            | IF ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState48
            | LBRACKET ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState48
            | LPAREN ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState48
            | MINUS ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState48
            | NOT ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState48
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState48)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState47)
    | MenhirState73 | MenhirState48 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | ELSE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState49 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CONST_BOOL _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v
            | CONST_INT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v
            | IDENT _v ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v
            | IF ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState50
            | LBRACKET ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState50
            | LPAREN ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState50
            | MINUS ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState50
            | NOT ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState50
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState50)
        | EQ ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | GE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | GT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | LE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | LT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | NEQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | OR ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState49)
    | MenhirState50 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState51
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState51
        | EQ ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState51
        | GE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState51
        | GT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState51
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState51
        | LE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState51
        | LT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState51
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState51
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState51
        | NEQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState51
        | OR ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState51
        | PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState51
        | BEGIN | COMMA | ELSE | RBRACKET | RPAREN | SEMI | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((((((_menhir_stack, _menhir_s), _, (c : (Ast.expr))), _), _, (e1 : (Ast.expr))), _), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : (Ast.expr) =                                            ( Eif (c, e1, e2)     ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState51)
    | MenhirState5 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | EQ ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | GE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | GT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | LE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | LT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | NEQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | OR ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | RBRACKET ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState52 in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (e : (Ast.expr))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Ast.expr) =                                            ( Enewarr e           ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState52)
    | MenhirState4 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | EQ ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | GE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | GT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | LE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | LT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | NEQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | OR ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState54 in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (s : (Ast.expr))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Ast.expr) =                                            ( s                   ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState54)
    | MenhirState3 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | AND | BEGIN | COMMA | ELSE | EQ | GE | GT | LE | LT | MINUS | NEQ | OR | PLUS | RBRACKET | RPAREN | SEMI | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (e : (Ast.expr))) = _menhir_stack in
            let _10 = () in
            let _v : (Ast.expr) = let op =
              let _1 = _10 in
                      ( Uminus )
            in
                                                       ( Eunop (op, e)       ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState56)
    | MenhirState2 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState57
        | EQ ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState57
        | GE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState57
        | GT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState57
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState57
        | LE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState57
        | LT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState57
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState57
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState57
        | NEQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState57
        | PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState57
        | AND | BEGIN | COMMA | ELSE | OR | RBRACKET | RPAREN | SEMI | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (e : (Ast.expr))) = _menhir_stack in
            let _10 = () in
            let _v : (Ast.expr) = let op =
              let _1 = _10 in
                      ( Not    )
            in
                                                       ( Eunop (op, e)       ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState57)
    | MenhirState1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BEGIN ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | EQ ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | GE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | GT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | LE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | LT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | NEQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | OR ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState58)
    | MenhirState63 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | EQ ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | GE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | GT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | LE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | LT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | NEQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | OR ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState64 in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (e : (Ast.expr))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Ast.instr) =                                       ( Ireturn e           ) in
            _menhir_goto_instr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState64)
    | MenhirState66 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | EQ ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | GE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | GT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | LE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | LT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | NEQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | OR ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState67 in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (e : (Ast.expr))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Ast.instr) =                                       ( Iprint e            ) in
            _menhir_goto_instr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState67)
    | MenhirState71 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | EQ ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | GE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | GT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | LE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | LT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | NEQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | OR ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState72 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BEGIN ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState73
            | CONST_BOOL _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _v
            | CONST_INT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _v
            | IDENT _v ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _v
            | IF ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState73
            | LBRACKET ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState73
            | LPAREN ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState73
            | MINUS ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState73
            | NOT ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState73
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState73)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState72)
    | MenhirState78 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | EQ ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | GE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | GT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | LE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | LT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | NEQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | OR ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState79 in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (id : (Ast.ident))), _, (e : (Ast.expr))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _v : (Ast.instr) =                                       ( Iassign (id, e)     ) in
            _menhir_goto_instr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState79)
    | MenhirState98 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState99
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState99
        | EQ ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState99
        | GE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState99
        | GT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState99
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState99
        | LE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState99
        | LT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState99
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState99
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState99
        | NEQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState99
        | OR ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState99
        | PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState99
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState99 in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (f : (Ast.expr * Ast.expr))), _, (e : (Ast.expr))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _v : (Ast.instr) =                     ( let e1, e2 = f in Isetarr (e1, e2, e) ) in
            _menhir_goto_instr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState99)
    | MenhirState0 | MenhirState59 | MenhirState95 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState101
        | DIV ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState101
        | EQ ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState101
        | GE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState101
        | GT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState101
        | LBRACKET ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState101
        | LE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState101
        | LT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState101
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState101
        | MULT ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState101
        | NEQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState101
        | OR ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState101
        | PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState101
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState101)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_instr_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.prog) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState59 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | END ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (instrs : (Ast.prog))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Ast.block) =                                       ( instrs           ) in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            (match _menhir_s with
            | MenhirState73 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | ELSE ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | BEGIN ->
                        _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState75
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState75)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | MenhirState75 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (((((_menhir_stack, _menhir_s), _, (c : (Ast.expr))), _), _, (b1 : (Ast.block))), _, (b2 : (Ast.block))) = _menhir_stack in
                let _5 = () in
                let _3 = () in
                let _1 = () in
                let _v : (Ast.instr) =                                       ( Iif (c, b1, b2)     ) in
                _menhir_goto_instr _menhir_env _menhir_stack _menhir_s _v
            | MenhirState89 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((((_menhir_stack, _menhir_s), (id : (Ast.ident))), _, (xs0 : (Ast.ident list))), _, (b : (Ast.block))) = _menhir_stack in
                let _5 = () in
                let _3 = () in
                let _1 = () in
                let _v : (Ast.instr) = let params =
                  let xs = xs0 in
                      ( xs )
                in
                                                      ( Idecl_fun (id, params, b) ) in
                _menhir_goto_instr _menhir_env _menhir_stack _menhir_s _v
            | MenhirState0 | MenhirState59 | MenhirState95 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (b : (Ast.block))) = _menhir_stack in
                let _v : (Ast.instr) =                                       ( Iblock b            ) in
                _menhir_goto_instr _menhir_env _menhir_stack _menhir_s _v
            | MenhirState58 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (((_menhir_stack, _menhir_s), _, (e : (Ast.expr))), _, (b : (Ast.block))) = _menhir_stack in
                let _1 = () in
                let _v : (Ast.instr) =                                       ( Iwhile (e, b)       ) in
                _menhir_goto_instr _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                _menhir_fail ())
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState95 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Ast.instr))), _, (xs : (Ast.prog))) = _menhir_stack in
        let _v : (Ast.prog) =     ( x :: xs ) in
        _menhir_goto_list_instr_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EOF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (instrs : (Ast.prog))) = _menhir_stack in
            let _2 = () in
            let _v : (Ast.prog) =                           ( instrs ) in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_1 : (Ast.prog)) = _v in
            Obj.magic _1
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce6 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.ident) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (id : (Ast.ident))) = _menhir_stack in
    let _v : (Ast.expr) =                                            ( Eident id           ) in
    _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run8 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.ident) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState8 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState8 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState8 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState8
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState8
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState8
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState8
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState8
    | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState8 in
        let _v : (Ast.expr list) =     ( [] ) in
        _menhir_goto_loption_separated_nonempty_list_COMMA_expr__ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState8

and _menhir_run6 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState6
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState6
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState6
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState6
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState6
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState6

and _menhir_run7 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.ident) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack)
    | AND | BEGIN | COMMA | DIV | ELSE | EQ | GE | GT | LBRACKET | LE | LT | MINUS | MULT | NEQ | OR | PLUS | RBRACKET | RPAREN | SEMI | THEN ->
        _menhir_reduce6 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_loption_separated_nonempty_list_COMMA_IDENT__ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.ident list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BEGIN ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState89
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState89)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run84 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.ident) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COMMA ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IDENT _v ->
            _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState85)
    | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (x : (Ast.ident))) = _menhir_stack in
        let _v : (Ast.ident list) =     ( [ x ] ) in
        _menhir_goto_separated_nonempty_list_COMMA_IDENT_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_instr : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.instr) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BEGIN ->
        _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _v
    | EXIT ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | FUN ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | IDENT _v ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _v
    | IF ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | NEWLINE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | PRINT ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | RETURN ->
        _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | VAR ->
        _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | WHILE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | END | EOF ->
        _menhir_reduce39 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState95

and _menhir_goto_const : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (c : (Ast.expr)) = _v in
    let _v : (Ast.expr) =                                            ( c                   ) in
    _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState101 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState99 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState98 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState95 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState89 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState85 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState83 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState79 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState78 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState73 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState72 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState71 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState67 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState66 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState64 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState63 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState59 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState58 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState57 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState56 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState54 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState52 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState51 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState50 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState49 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState48 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState47 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState44 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState43 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState42 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState41 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState39 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState38 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState37 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState36 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState35 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState34 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState33 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState30 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState29 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState28 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState27 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState26 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState25 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState24 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState23 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState21 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState20 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState19 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState18 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState16 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState15 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState8 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState6 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState5 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState4 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState3 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState2 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_reduce39 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Ast.prog) =     ( [] ) in
    _menhir_goto_list_instr_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState1 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState1 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState1 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState1

and _menhir_run60 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | IDENT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), (id : (Ast.ident))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Ast.instr) =                                       ( Idecl_var id        ) in
            _menhir_goto_instr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run63 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState63
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState63
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState63
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState63
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState63
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState63

and _menhir_run66 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState66 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState66 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState66 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState66
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState66
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState66
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState66
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState66
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState66

and _menhir_run2 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState2 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState2 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState2 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState2
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState2
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState2
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState2
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState2
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState2

and _menhir_run69 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | SEMI ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _2 = () in
        let _1 = () in
        let _v : (Ast.instr) =                                       ( Inewline            ) in
        _menhir_goto_instr _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run3 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState3
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState3
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState3
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState3
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState3
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState3

and _menhir_run4 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState4 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState4 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState4 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState4
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState4
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState4
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState4
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState4
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState4

and _menhir_run5 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState5 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState5 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState5 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState5

and _menhir_run71 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState71

and _menhir_run77 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.ident) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASSIGN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | CONST_BOOL _v ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
        | CONST_INT _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
        | IDENT _v ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
        | IF ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | LBRACKET ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | LPAREN ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | MINUS ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | NOT ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState78)
    | LPAREN ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack)
    | AND | DIV | EQ | GE | GT | LBRACKET | LE | LT | MINUS | MULT | NEQ | OR | PLUS ->
        _menhir_reduce6 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run81 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | IDENT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | IDENT _v ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState83 _v
            | RPAREN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_s = MenhirState83 in
                let _v : (Ast.ident list) =     ( [] ) in
                _menhir_goto_loption_separated_nonempty_list_COMMA_IDENT__ _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState83)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run91 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | SEMI ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _2 = () in
        let _1 = () in
        let _v : (Ast.instr) =                                       ( Iexit               ) in
        _menhir_goto_instr _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run9 : _menhir_env -> 'ttv_tail -> _menhir_state -> (int) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (i : (int)) = _v in
    let _v : (Ast.expr) =                ( Econst (Cint i)  ) in
    _menhir_goto_const _menhir_env _menhir_stack _menhir_s _v

and _menhir_run10 : _menhir_env -> 'ttv_tail -> _menhir_state -> (bool) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (b : (bool)) = _v in
    let _v : (Ast.expr) =                ( Econst (Cbool b) ) in
    _menhir_goto_const _menhir_env _menhir_stack _menhir_s _v

and _menhir_run59 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BEGIN ->
        _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState59
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _v
    | EXIT ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState59
    | FUN ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState59
    | IDENT _v ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _v
    | IF ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState59
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState59
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState59
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState59
    | NEWLINE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState59
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState59
    | PRINT ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState59
    | RETURN ->
        _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState59
    | VAR ->
        _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState59
    | WHILE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState59
    | END ->
        _menhir_reduce39 _menhir_env (Obj.magic _menhir_stack) MenhirState59
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState59

and _menhir_discard : _menhir_env -> _menhir_env =
  fun _menhir_env ->
    let lexer = _menhir_env._menhir_lexer in
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = lexer lexbuf in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    }

and prog : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.prog) =
  fun lexer lexbuf ->
    let _menhir_env = let _tok = Obj.magic () in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    } in
    Obj.magic (let _menhir_stack = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BEGIN ->
        _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | CONST_BOOL _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | CONST_INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | EXIT ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | FUN ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | IDENT _v ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | IF ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LBRACKET ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | NEWLINE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | PRINT ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | RETURN ->
        _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | VAR ->
        _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | WHILE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | EOF ->
        _menhir_reduce39 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0)
  

