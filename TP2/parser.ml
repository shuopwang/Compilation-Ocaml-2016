
module Basics = struct
  
  exception Error
  
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
  | MenhirState35
  | MenhirState33
  | MenhirState31
  | MenhirState29
  | MenhirState27
  | MenhirState25
  | MenhirState23
  | MenhirState21
  | MenhirState19
  | MenhirState17
  | MenhirState15
  | MenhirState12
  | MenhirState10
  | MenhirState8
  | MenhirState3
  | MenhirState1
  | MenhirState0
  

  open Ast

  (* Vous pouvez insérer ici du code Caml pour définir des fonctions
     ou des variables qui seront utilisées dans les actions sémantiques. *)


let rec _menhir_run7 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (_menhir_stack, _menhir_s, (e1 : (Ast.expr))) = _menhir_stack in
    let _2 = () in
    let _v : (Ast.expr) =                     (Eunop(Uminus,e1)) in
    _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run10 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState10 _v
    | EOF ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState10
    | IF ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState10
    | INT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState10 _v
    | LPAR ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState10
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState10

and _menhir_run12 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState12 _v
    | EOF ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState12
    | IF ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState12
    | INT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState12 _v
    | LPAR ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState12
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState12

and _menhir_run14 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (_menhir_stack, _menhir_s, (e1 : (Ast.expr))) = _menhir_stack in
    let _2 = () in
    let _v : (Ast.expr) =                  (Eunop(Not,e1)) in
    _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run15 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState15 _v
    | EOF ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState15
    | IF ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState15
    | INT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState15 _v
    | LPAR ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState15
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState15

and _menhir_run33 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _v
    | EOF ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | IF ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | INT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _v
    | LPAR ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState33

and _menhir_run27 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _v
    | EOF ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState27
    | IF ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState27
    | INT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _v
    | LPAR ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState27
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState27

and _menhir_run17 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _v
    | EOF ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState17
    | IF ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState17
    | INT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _v
    | LPAR ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState17
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState17

and _menhir_run19 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState19 _v
    | EOF ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState19
    | IF ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState19
    | INT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState19 _v
    | LPAR ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState19
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState19

and _menhir_run21 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState21 _v
    | EOF ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState21
    | IF ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState21
    | INT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState21 _v
    | LPAR ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState21
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState21

and _menhir_run23 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _v
    | EOF ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState23
    | IF ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState23
    | INT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _v
    | LPAR ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState23
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState23

and _menhir_run25 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _v
    | EOF ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState25
    | IF ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState25
    | INT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _v
    | LPAR ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState25
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState25

and _menhir_run31 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState31 _v
    | EOF ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | IF ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | INT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState31 _v
    | LPAR ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState31

and _menhir_run29 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _v
    | EOF ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState29
    | IF ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState29
    | INT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _v
    | LPAR ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState29
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState29

and _menhir_goto_expr : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState3 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack)
        | MULT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack)
        | NEQ ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack)
        | NOT ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack)
        | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOL _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState8 _v
            | EOF ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState8
            | IF ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState8
            | INT _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState8 _v
            | LPAR ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState8
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState8)
        | UMINUS ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState8 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack)
        | ELSE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOL _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState35 _v
            | EOF ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState35
            | IF ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState35
            | INT _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState35 _v
            | LPAR ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState35
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState35)
        | EQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack)
        | MULT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack)
        | NEQ ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack)
        | NOT ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack)
        | UMINUS ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState10 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack)
        | NEQ ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack)
        | NOT ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack)
        | UMINUS ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack)
        | ELSE | EOF | MULT | PLUS | RPAR | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _2 = () in
            let _v : (Ast.expr) =                             (Ebinop(Plus,e1,e2)) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState12 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack)
        | NEQ ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack)
        | NOT ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack)
        | UMINUS ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack)
        | AND | DIV | ELSE | EOF | MINUS | MULT | OR | PLUS | RPAR | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _2 = () in
            let _v : (Ast.expr) =                           (Ebinop(Or,e1,e2)) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState15 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | NOT ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack)
        | UMINUS ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack)
        | AND | DIV | ELSE | EOF | EQ | GE | GT | LE | LT | MINUS | MULT | NEQ | OR | PLUS | RPAR | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _2 = () in
            let _v : (Ast.expr) =                            (Ebinop(Neq,e1,e2)) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | NOT ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack)
        | UMINUS ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack)
        | AND | DIV | ELSE | EOF | EQ | GE | GT | LE | LT | MINUS | MULT | NEQ | OR | PLUS | RPAR | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _2 = () in
            let _v : (Ast.expr) =                           (Ebinop(Lt,e1,e2)) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState19 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | NOT ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack)
        | UMINUS ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack)
        | AND | DIV | ELSE | EOF | EQ | GE | GT | LE | LT | MINUS | MULT | NEQ | OR | PLUS | RPAR | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _2 = () in
            let _v : (Ast.expr) =                           (Ebinop(Le,e1,e2)) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState21 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | NOT ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack)
        | UMINUS ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack)
        | AND | DIV | ELSE | EOF | EQ | GE | GT | LE | LT | MINUS | MULT | NEQ | OR | PLUS | RPAR | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _2 = () in
            let _v : (Ast.expr) =                           (Ebinop(Gt,e1,e2)) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState23 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | NOT ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack)
        | UMINUS ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack)
        | AND | DIV | ELSE | EOF | EQ | GE | GT | LE | LT | MINUS | MULT | NEQ | OR | PLUS | RPAR | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _2 = () in
            let _v : (Ast.expr) =                           (Ebinop(Ge,e1,e2)) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState25 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | NOT ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack)
        | UMINUS ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack)
        | AND | DIV | ELSE | EOF | EQ | GE | GT | LE | LT | MINUS | MULT | NEQ | OR | PLUS | RPAR | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _2 = () in
            let _v : (Ast.expr) =                           (Ebinop(Eq,e1,e2)) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState27 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack)
        | NEQ ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack)
        | NOT ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack)
        | UMINUS ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack)
        | DIV | ELSE | EOF | MINUS | MULT | PLUS | RPAR | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _2 = () in
            let _v : (Ast.expr) =                              (Ebinop(Minus,e1,e2)) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState29 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack)
        | NEQ ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack)
        | NOT ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack)
        | UMINUS ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack)
        | AND | DIV | ELSE | EOF | MINUS | MULT | OR | PLUS | RPAR | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _2 = () in
            let _v : (Ast.expr) =                            (Ebinop(And,e1,e2)) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState31 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack)
        | NEQ ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack)
        | NOT ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack)
        | UMINUS ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack)
        | DIV | ELSE | EOF | MINUS | MULT | PLUS | RPAR | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _2 = () in
            let _v : (Ast.expr) =                            (Ebinop(Div,e1,e2)) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState33 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack)
        | NEQ ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack)
        | NOT ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack)
        | UMINUS ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack)
        | ELSE | EOF | MULT | PLUS | RPAR | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _, (e2 : (Ast.expr))) = _menhir_stack in
            let _2 = () in
            let _v : (Ast.expr) =                             (Ebinop(Mult,e1,e2)) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState35 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), _, (e1 : (Ast.expr))), _, (e2 : (Ast.expr))), _, (e3 : (Ast.expr))) = _menhir_stack in
        let _5 = () in
        let _3 = () in
        let _1 = () in
        let _v : (Ast.expr) =                                                (Eif(e1,e2,e3)) in
        _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack)
        | MULT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack)
        | NEQ ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack)
        | NOT ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack)
        | RPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (e : (Ast.expr))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Ast.expr) =                      ( e ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | UMINUS ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | AND ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack)
        | EOF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (e : (Ast.expr))) = _menhir_stack in
            let _2 = () in
            let _v : (Ast.expr) =               ( e ) in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_1 : (Ast.expr)) = _v in
            Obj.magic _1
        | EQ ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack)
        | MULT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack)
        | NEQ ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack)
        | NOT ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack)
        | UMINUS ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState35 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState33 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState31 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState29 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState27 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState25 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState23 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState21 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState19 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState15 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState12 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState10 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState8 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState3 ->
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

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState1 _v
    | EOF ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | IF ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | INT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState1 _v
    | LPAR ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState1

and _menhir_run2 : _menhir_env -> 'ttv_tail -> _menhir_state -> (int) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (i : (int)) = _v in
    let _v : (Ast.expr) =           (Econst (Cint i)) in
    _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run3 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _v
    | EOF ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState3
    | IF ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState3
    | INT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _v
    | LPAR ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState3
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState3

and _menhir_run4 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Ast.expr) =       ( failwith "Unlikely" ) in
    _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run5 : _menhir_env -> 'ttv_tail -> _menhir_state -> (bool) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (b : (bool)) = _v in
    let _v : (Ast.expr) =           (Econst(Cbool b)) in
    _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v

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

and toplevel_expr : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.expr) =
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
    | BOOL _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | EOF ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | IF ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | INT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | LPAR ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0)
  

