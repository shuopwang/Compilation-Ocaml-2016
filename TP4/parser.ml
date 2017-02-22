
module Basics = struct
  
  exception Error
  
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
  | MenhirState99
  | MenhirState98
  | MenhirState95
  | MenhirState92
  | MenhirState91
  | MenhirState89
  | MenhirState88
  | MenhirState87
  | MenhirState85
  | MenhirState80
  | MenhirState79
  | MenhirState78
  | MenhirState77
  | MenhirState76
  | MenhirState75
  | MenhirState74
  | MenhirState72
  | MenhirState69
  | MenhirState68
  | MenhirState63
  | MenhirState62
  | MenhirState61
  | MenhirState57
  | MenhirState56
  | MenhirState55
  | MenhirState54
  | MenhirState50
  | MenhirState49
  | MenhirState48
  | MenhirState47
  | MenhirState45
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
  | MenhirState32
  | MenhirState31
  | MenhirState30
  | MenhirState29
  | MenhirState27
  | MenhirState26
  | MenhirState25
  | MenhirState24
  | MenhirState23
  | MenhirState22
  | MenhirState21
  | MenhirState20
  | MenhirState18
  | MenhirState17
  | MenhirState16
  | MenhirState15
  | MenhirState14
  | MenhirState13
  | MenhirState12
  | MenhirState11
  | MenhirState10
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
  let rec calu_number (d:expr list) :int=
  		match d with
  		|e1::r ->(1+(calu_number r)) 
  		|[] ->0
  let rec agssi_table (id:ident)(d:expr list) (i:int) : instr list=
  		match d with
  		|e1::r -> (Isetarr (Eident id, Econst (Cint i), e1))::(agssi_table id  r (i+1) )
  		|[] ->[]
  		
  let init_table (id:ident) (d:expr list) :instr=
  		let num=calu_number d in 
         Iassign (id, Enewarr (Econst (Cint (num))))
  let make_table (id: ident) (d: expr list) : instr =
		Iblock ((Idecl_var (id))::(init_table id d )::(agssi_table id d 0))
  let instr_table (il:instr list):instr=
  		Iblock il
  let decag (id:ident)(e:expr)(il: instr list):instr =
  		let list_expr=(List.append [(Idecl_var id);(Iassign(id,e))] il) in 
  		Iblock (list_expr)

   

let rec _menhir_goto_donne : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.expr list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState57 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s, (e : (Ast.expr))), _), _, (d : (Ast.expr list))) = _menhir_stack in
        let _2 = () in
        let _v : (Ast.expr list) =                           (e::d) in
        _menhir_goto_donne _menhir_env _menhir_stack _menhir_s _v
    | MenhirState55 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RBR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | SEMI ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | BEGIN ->
                    _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState61
                | CONST_BOOL _v ->
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _v
                | CONST_INT _v ->
                    _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _v
                | EXIT ->
                    _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState61
                | FOR ->
                    _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState61
                | IDENT _v ->
                    _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _v
                | IF ->
                    _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState61
                | LCRO ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState61
                | LPAREN ->
                    _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState61
                | MINUS ->
                    _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState61
                | NEWLINE ->
                    _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState61
                | NOT ->
                    _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState61
                | PRINT ->
                    _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState61
                | VAR ->
                    _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState61
                | WHILE ->
                    _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState61
                | END | EOF ->
                    _menhir_reduce38 _menhir_env (Obj.magic _menhir_stack) MenhirState61
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState61)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState69 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RBR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | SEMI ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | BEGIN ->
                    _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState72
                | CONST_BOOL _v ->
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _v
                | CONST_INT _v ->
                    _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _v
                | EXIT ->
                    _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState72
                | FOR ->
                    _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState72
                | IDENT _v ->
                    _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _v
                | IF ->
                    _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState72
                | LCRO ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState72
                | LPAREN ->
                    _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState72
                | MINUS ->
                    _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState72
                | NEWLINE ->
                    _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState72
                | NOT ->
                    _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState72
                | PRINT ->
                    _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState72
                | VAR ->
                    _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState72
                | WHILE ->
                    _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState72
                | END | EOF ->
                    _menhir_reduce38 _menhir_env (Obj.magic _menhir_stack) MenhirState72
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState72)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce25 : _menhir_env -> ((('ttv_tail * _menhir_state * (Ast.expr)) * _menhir_state) * _menhir_state * (Ast.expr)) * _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let ((((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _), _, (e2 : (Ast.expr))), _) = _menhir_stack in
    let _4 = () in
    let _2 = () in
    let _v : (Ast.expr) =                                     ( Egetarr(e1,e2)		 ) in
    _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run13 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState13 _v
    | CONST_INT _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState13 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState13 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState13
    | LCRO ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState13
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState13
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState13
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState13
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState13

and _menhir_run20 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
    | CONST_INT _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | LCRO ->
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

and _menhir_run22 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _v
    | CONST_INT _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState22
    | LCRO ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState22
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState22
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState22
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState22
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState22

and _menhir_run15 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState15 _v
    | CONST_INT _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState15 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState15 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState15
    | LCRO ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState15
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState15
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState15
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState15
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState15

and _menhir_run24 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _v
    | CONST_INT _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | LCRO ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState24

and _menhir_run29 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _v
    | CONST_INT _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState29
    | LCRO ->
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

and _menhir_run31 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState31 _v
    | CONST_INT _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState31 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState31 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LCRO ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState31

and _menhir_run17 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _v
    | CONST_INT _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState17
    | LCRO ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState17
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState17
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState17
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState17
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState17

and _menhir_run33 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _v
    | CONST_INT _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LCRO ->
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
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState35 _v
    | CONST_INT _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState35 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState35 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState35
    | LCRO ->
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

and _menhir_run37 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState37 _v
    | CONST_INT _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState37 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState37 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState37
    | LCRO ->
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

and _menhir_run26 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState26 _v
    | CONST_INT _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState26 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState26 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState26
    | LCRO ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState26
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState26
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState26
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState26
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState26

and _menhir_run39 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.expr) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _v
    | CONST_INT _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LCRO ->
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

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.fprintf Pervasives.stderr "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_goto_expr : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState6 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | EQ ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | GE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | GT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | LE ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | LT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | NEQ ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | OR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState10 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CONST_BOOL _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState11 _v
            | CONST_INT _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState11 _v
            | IDENT _v ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState11 _v
            | IF ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState11
            | LCRO ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState11
            | LPAREN ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState11
            | MINUS ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState11
            | NOT ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState11
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState11)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState10)
    | MenhirState11 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState12
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState12
        | ELSE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState12 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CONST_BOOL _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _v
            | CONST_INT _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _v
            | IDENT _v ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _v
            | IF ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState41
            | LCRO ->
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
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState41)
        | EQ ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState12
        | GE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState12
        | GT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState12
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState12
        | LE ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState12
        | LT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState12
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState12
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState12
        | NEQ ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState12
        | OR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState12
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState12
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState12)
    | MenhirState13 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | AND | BEGIN | ELSE | EQ | GE | GT | LE | LT | MINUS | NEQ | OR | PLUS | RBR | RCRO | RPAREN | SEMI | THEN | VGL ->
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState14)
    | MenhirState15 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | AND | BEGIN | DIV | ELSE | EQ | GE | GT | LE | LT | MINUS | MULT | NEQ | OR | PLUS | RBR | RCRO | RPAREN | SEMI | THEN | VGL ->
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState16)
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | EQ ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | GE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | GT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | LE ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | LT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | NEQ ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | OR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | RCRO ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState18 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            _menhir_reduce25 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState18)
    | MenhirState20 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | EQ ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | GE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | GT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | LE ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | LT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | NEQ ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | BEGIN | ELSE | OR | RBR | RCRO | RPAREN | SEMI | THEN | VGL ->
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState21)
    | MenhirState22 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState23
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState23
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState23
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState23
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState23
        | AND | BEGIN | ELSE | EQ | GE | GT | LE | LT | NEQ | OR | RBR | RCRO | RPAREN | SEMI | THEN | VGL ->
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState23)
    | MenhirState24 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState25
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState25
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState25
        | AND | BEGIN | ELSE | EQ | GE | GT | LE | LT | MINUS | NEQ | OR | PLUS | RBR | RCRO | RPAREN | SEMI | THEN | VGL ->
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState25)
    | MenhirState26 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState27
        | AND | BEGIN | DIV | ELSE | EQ | GE | GT | LE | LT | MINUS | MULT | NEQ | OR | PLUS | RBR | RCRO | RPAREN | SEMI | THEN | VGL ->
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState27)
    | MenhirState29 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | AND | BEGIN | ELSE | EQ | GE | GT | LE | LT | NEQ | OR | RBR | RCRO | RPAREN | SEMI | THEN | VGL ->
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState30)
    | MenhirState31 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | AND | BEGIN | ELSE | EQ | GE | GT | LE | LT | NEQ | OR | RBR | RCRO | RPAREN | SEMI | THEN | VGL ->
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState32)
    | MenhirState33 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | AND | BEGIN | ELSE | EQ | GE | GT | LE | LT | NEQ | OR | RBR | RCRO | RPAREN | SEMI | THEN | VGL ->
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState34)
    | MenhirState35 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | AND | BEGIN | ELSE | EQ | GE | GT | LE | LT | NEQ | OR | RBR | RCRO | RPAREN | SEMI | THEN | VGL ->
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState36)
    | MenhirState37 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | AND | BEGIN | ELSE | EQ | GE | GT | LE | LT | NEQ | OR | RBR | RCRO | RPAREN | SEMI | THEN | VGL ->
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState38)
    | MenhirState39 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | EQ ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | GE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | GT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | LE ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | LT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | NEQ ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | AND | BEGIN | ELSE | OR | RBR | RCRO | RPAREN | SEMI | THEN | VGL ->
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState40)
    | MenhirState41 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | EQ ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | GE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | GT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | LE ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | LT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | NEQ ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | OR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BEGIN | ELSE | RBR | RCRO | RPAREN | SEMI | THEN | VGL ->
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState42)
    | MenhirState5 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState43
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState43
        | EQ ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState43
        | GE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState43
        | GT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState43
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState43
        | LE ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState43
        | LT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState43
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState43
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState43
        | NEQ ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState43
        | OR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState43
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState43
        | RCRO ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState43 in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (e : (Ast.expr))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Ast.expr) =                            ( Enewarr(e) 		 ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState43)
    | MenhirState4 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState45
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState45
        | EQ ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState45
        | GE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState45
        | GT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState45
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState45
        | LE ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState45
        | LT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState45
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState45
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState45
        | NEQ ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState45
        | OR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState45
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState45
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState45 in
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState45)
    | MenhirState3 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState47
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState47
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState47
        | AND | BEGIN | ELSE | EQ | GE | GT | LE | LT | MINUS | NEQ | OR | PLUS | RBR | RCRO | RPAREN | SEMI | THEN | VGL ->
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState47)
    | MenhirState2 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | EQ ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | GE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | GT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | LE ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | LT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | NEQ ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | AND | BEGIN | ELSE | OR | RBR | RCRO | RPAREN | SEMI | THEN | VGL ->
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState48)
    | MenhirState1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | BEGIN ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | EQ ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | GE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | GT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | LE ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | LT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | NEQ ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | OR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState49
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState49)
    | MenhirState69 | MenhirState57 | MenhirState55 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | EQ ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | GE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | GT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | LE ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | LT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | NEQ ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | OR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | VGL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState56 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CONST_BOOL _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState57 _v
            | CONST_INT _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState57 _v
            | IDENT _v ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState57 _v
            | IF ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState57
            | LCRO ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState57
            | LPAREN ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState57
            | MINUS ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState57
            | NOT ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState57
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState57)
        | RBR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (e : (Ast.expr))) = _menhir_stack in
            let _v : (Ast.expr list) =                        ([e]) in
            _menhir_goto_donne _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState56)
    | MenhirState62 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState63
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState63
        | EQ ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState63
        | GE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState63
        | GT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState63
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState63
        | LE ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState63
        | LT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState63
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState63
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState63
        | NEQ ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState63
        | OR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState63
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState63
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState63 in
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState63)
    | MenhirState74 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | EQ ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | GE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | GT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | LE ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | LT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | NEQ ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | OR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState75 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CONST_BOOL _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _v
            | CONST_INT _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _v
            | IDENT _v ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _v
            | IF ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState76
            | LCRO ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState76
            | LPAREN ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState76
            | MINUS ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState76
            | NOT ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState76
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState76)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState75)
    | MenhirState76 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState77
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState77
        | EQ ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState77
        | GE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState77
        | GT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState77
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState77
        | LE ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState77
        | LT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState77
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState77
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState77
        | NEQ ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState77
        | OR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState77
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState77
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState77 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CONST_BOOL _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
            | CONST_INT _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
            | IDENT _v ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
            | IF ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState78
            | LCRO ->
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
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState77)
    | MenhirState78 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | EQ ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | GE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | GT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | LE ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | LT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | NEQ ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | OR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState79 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BEGIN ->
                _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState80
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState80)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState79)
    | MenhirState0 | MenhirState50 | MenhirState99 | MenhirState61 | MenhirState72 | MenhirState85 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState87
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState87
        | EQ ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState87
        | GE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState87
        | GT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState87
        | LCRO ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState87 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CONST_BOOL _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _v
            | CONST_INT _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _v
            | IDENT _v ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _v
            | IF ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState88
            | LCRO ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState88
            | LPAREN ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState88
            | MINUS ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState88
            | NOT ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState88
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState88)
        | LE ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState87
        | LT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState87
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState87
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState87
        | NEQ ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState87
        | OR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState87
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState87
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState87)
    | MenhirState88 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState89
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState89
        | EQ ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState89
        | GE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState89
        | GT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState89
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState89
        | LE ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState89
        | LT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState89
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState89
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState89
        | NEQ ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState89
        | OR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState89
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState89
        | RCRO ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState89 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ASSIGN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | CONST_BOOL _v ->
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v
                | CONST_INT _v ->
                    _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v
                | IDENT _v ->
                    _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v
                | IF ->
                    _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState91
                | LCRO ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState91
                | LPAREN ->
                    _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState91
                | MINUS ->
                    _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState91
                | NOT ->
                    _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState91
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState91)
            | AND | DIV | EQ | GE | GT | LCRO | LE | LT | MINUS | MULT | NEQ | OR | PLUS ->
                _menhir_reduce25 _menhir_env (Obj.magic _menhir_stack)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState89)
    | MenhirState91 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState92
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState92
        | EQ ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState92
        | GE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState92
        | GT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState92
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState92
        | LE ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState92
        | LT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState92
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState92
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState92
        | NEQ ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState92
        | OR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState92
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState92
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState92 in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((((_menhir_stack, _menhir_s, (e1 : (Ast.expr))), _), _, (e2 : (Ast.expr))), _), _, (e3 : (Ast.expr))) = _menhir_stack in
            let _7 = () in
            let _5 = () in
            let _4 = () in
            let _2 = () in
            let _v : (Ast.instr) =                                                 ( Isetarr(e1,e2,e3)) in
            _menhir_goto_instr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState92)
    | MenhirState68 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState95
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState95
        | EQ ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState95
        | GE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState95
        | GT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState95
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState95
        | LE ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState95
        | LT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState95
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState95
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState95
        | NEQ ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState95
        | OR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState95
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState95
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState95 in
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState95)
    | MenhirState54 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | DIV ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | EQ ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | GE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | GT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | LCRO ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | LE ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | LT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | MINUS ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | MULT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | NEQ ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | OR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | PLUS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState98 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BEGIN ->
                _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState99
            | CONST_BOOL _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState99 _v
            | CONST_INT _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState99 _v
            | EXIT ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState99
            | FOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState99
            | IDENT _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState99 _v
            | IF ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState99
            | LCRO ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState99
            | LPAREN ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState99
            | MINUS ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState99
            | NEWLINE ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState99
            | NOT ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState99
            | PRINT ->
                _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState99
            | VAR ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState99
            | WHILE ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState99
            | END | EOF ->
                _menhir_reduce38 _menhir_env (Obj.magic _menhir_stack) MenhirState99
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState99)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState98)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_instr_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.prog) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState72 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s, (id : (Ast.ident))), _), _, (d : (Ast.expr list))), _, (instr : (Ast.prog))) = _menhir_stack in
        let _6 = () in
        let _5 = () in
        let _3 = () in
        let _2 = () in
        let _v : (Ast.instr) =            ( instr_table (agssi_table id d 0)  ) in
        _menhir_goto_instr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState85 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Ast.instr))), _, (xs : (Ast.prog))) = _menhir_stack in
        let _v : (Ast.prog) =     ( x :: xs ) in
        _menhir_goto_list_instr_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState61 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((_menhir_stack, _menhir_s), (id : (Ast.ident))), _), _, (d : (Ast.expr list))), _, (instrs : (Ast.prog))) = _menhir_stack in
        let _7 = () in
        let _6 = () in
        let _4 = () in
        let _3 = () in
        let _1 = () in
        let _v : (Ast.instr) =            ( make_table id d  	) in
        _menhir_goto_instr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState99 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((_menhir_stack, _menhir_s), (id : (Ast.ident))), _, (e : (Ast.expr))), _), _, (instr : (Ast.prog))) = _menhir_stack in
        let _5 = () in
        let _3 = () in
        let _1 = () in
        let _v : (Ast.instr) =            (	decag id e 	instr	) in
        _menhir_goto_instr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState50 ->
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
            (match _menhir_s with
            | MenhirState80 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (b : (Ast.block)) = _v in
                let (((((((_menhir_stack, _menhir_s), _, (e1 : (Ast.expr))), _), _, (e2 : (Ast.expr))), _), _, (e3 : (Ast.expr))), _) = _menhir_stack in
                let _8 = () in
                let _6 = () in
                let _4 = () in
                let _2 = () in
                let _1 = () in
                let _v : (Ast.instr) =                  ( Ifor(e1,e2,e3,b)			) in
                _menhir_goto_instr _menhir_env _menhir_stack _menhir_s _v
            | MenhirState0 | MenhirState50 | MenhirState99 | MenhirState61 | MenhirState72 | MenhirState85 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (b : (Ast.block)) = _v in
                let _v : (Ast.instr) =                                       ( Iblock b            ) in
                _menhir_goto_instr _menhir_env _menhir_stack _menhir_s _v
            | MenhirState49 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (b : (Ast.block)) = _v in
                let ((_menhir_stack, _menhir_s), _, (e : (Ast.expr))) = _menhir_stack in
                let _1 = () in
                let _v : (Ast.instr) =                                      ( Iwhile(e,b)		    ) in
                _menhir_goto_instr _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                _menhir_fail ())
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

and _menhir_reduce7 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.ident) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (id : (Ast.ident))) = _menhir_stack in
    let _v : (Ast.expr) =                                            ( Eident id           ) in
    _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run7 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.ident) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce7 _menhir_env (Obj.magic _menhir_stack)

and _menhir_goto_instr : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.instr) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BEGIN ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | CONST_BOOL _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _v
    | CONST_INT _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _v
    | EXIT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | FOR ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | IDENT _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | LCRO ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | NEWLINE ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | PRINT ->
        _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | VAR ->
        _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | WHILE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | END | EOF ->
        _menhir_reduce38 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState85

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
    | MenhirState99 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState98 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState95 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState92 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState91 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState89 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState88 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState87 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState85 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState80 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState79 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState78 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState77 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState76 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState74 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState72 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState69 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState68 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState63 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState62 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState61 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState57 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState56 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState55 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState54 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
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
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState47 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState43 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
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
    | MenhirState32 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState31 ->
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
    | MenhirState27 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState26 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState25 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState24 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState23 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState22 ->
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
    | MenhirState18 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState16 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState15 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState14 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState13 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState12 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState11 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState10 ->
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

and _menhir_reduce38 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState1 _v
    | CONST_INT _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState1 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState1 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LCRO ->
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

and _menhir_run51 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | ASSIGN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CONST_BOOL _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _v
            | CONST_INT _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _v
            | IDENT _v ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _v
            | IF ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState54
            | LBR ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_s = MenhirState54 in
                let _menhir_stack = (_menhir_stack, _menhir_s) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | CONST_BOOL _v ->
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState55 _v
                | CONST_INT _v ->
                    _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState55 _v
                | IDENT _v ->
                    _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState55 _v
                | IF ->
                    _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState55
                | LCRO ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState55
                | LPAREN ->
                    _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState55
                | MINUS ->
                    _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState55
                | NOT ->
                    _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState55
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState55)
            | LCRO ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState54
            | LPAREN ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState54
            | MINUS ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState54
            | NOT ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState54
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState54)
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

and _menhir_run62 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState62 _v
    | CONST_INT _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState62 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState62 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState62
    | LCRO ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState62
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState62
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState62
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState62
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState62

and _menhir_run2 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState2 _v
    | CONST_INT _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState2 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState2 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState2
    | LCRO ->
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

and _menhir_run65 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _v
    | CONST_INT _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState3
    | LCRO ->
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
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState4 _v
    | CONST_INT _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState4 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState4 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState4
    | LCRO ->
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
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState5 _v
    | CONST_INT _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState5 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState5 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | LCRO ->
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

and _menhir_run6 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONST_BOOL _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _v
    | CONST_INT _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _v
    | IDENT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState6
    | LCRO ->
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

and _menhir_run67 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.ident) -> 'ttv_return =
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
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v
        | CONST_INT _v ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v
        | IDENT _v ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v
        | IF ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | LBR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState68 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CONST_BOOL _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _v
            | CONST_INT _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _v
            | IDENT _v ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _v
            | IF ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState69
            | LCRO ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState69
            | LPAREN ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState69
            | MINUS ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState69
            | NOT ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState69
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState69)
        | LCRO ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | LPAREN ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | MINUS ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | NOT ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState68)
    | AND | DIV | EQ | GE | GT | LCRO | LE | LT | MINUS | MULT | NEQ | OR | PLUS ->
        _menhir_reduce7 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run73 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | CONST_BOOL _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
        | CONST_INT _v ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
        | IDENT _v ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
        | IF ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | LCRO ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | LPAREN ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | MINUS ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | NOT ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState74)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run82 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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

and _menhir_run8 : _menhir_env -> 'ttv_tail -> _menhir_state -> (int) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (i : (int)) = _v in
    let _v : (Ast.expr) =                ( Econst (Cint i)  ) in
    _menhir_goto_const _menhir_env _menhir_stack _menhir_s _v

and _menhir_run9 : _menhir_env -> 'ttv_tail -> _menhir_state -> (bool) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (b : (bool)) = _v in
    let _v : (Ast.expr) =                ( Econst (Cbool b) ) in
    _menhir_goto_const _menhir_env _menhir_stack _menhir_s _v

and _menhir_run50 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BEGIN ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState50
    | CONST_BOOL _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v
    | CONST_INT _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v
    | EXIT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState50
    | FOR ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState50
    | IDENT _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState50
    | LCRO ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState50
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState50
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState50
    | NEWLINE ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState50
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState50
    | PRINT ->
        _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState50
    | VAR ->
        _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState50
    | WHILE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState50
    | END ->
        _menhir_reduce38 _menhir_env (Obj.magic _menhir_stack) MenhirState50
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState50

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
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | CONST_BOOL _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | CONST_INT _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | EXIT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | FOR ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | IDENT _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | IF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LCRO ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LPAREN ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | MINUS ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | NEWLINE ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | PRINT ->
        _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | VAR ->
        _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | WHILE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | EOF ->
        _menhir_reduce38 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0)
  

