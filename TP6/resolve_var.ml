open Astcommon
open Ast
open Printf

module Env = Map.Make(String)
type var_env = Astv.var Env.t
type fun_env = Astv.fname Env.t


module Vset = Set.Make(struct type t = Astv.var let compare = compare end)
type var_set = Vset.t

module Funset = Set.Make(struct type t = Astv.fun_descr let compare = compare end)
type fun_set = Funset.t
    
let new_svar : ident -> Astv.var =
  let c = ref 0 in
  fun (id: ident) -> incr c; Astv.Static_var (!c, id)

let new_fun : ident -> Astv.fname =
  let c = ref 0 in
  fun (id: ident) -> incr c; Astv.Function (!c, id)

    
let rec resolve_expr (env: var_env) (fenv: fun_env) :
    Ast.expr -> Astv.expr = function
  | Econst c ->
    Astv.Econst c
      
  | Eident id ->
    Astv.Evar (Env.find id env)
      
  | Eunop (op, e) ->
    Astv.Eunop (op, resolve_expr env fenv e)
      
  | Ebinop (binop, e1, e2) ->
    Astv.Ebinop (binop, resolve_expr env fenv e1, resolve_expr env fenv e2)
      
  | Eif (e1, e2, e3) ->
    Astv.Eif (resolve_expr env fenv e1, resolve_expr env fenv e2, resolve_expr env fenv e3)

  | Enewarr e ->
    Astv.Enewarr (resolve_expr env fenv e)

  | Egetarr (a, i) ->
    Astv.Egetarr (resolve_expr env fenv a, resolve_expr env fenv i)

  | Ecall c ->
    (* On propose ici de faire appel à une fonction spécifique pour résoudre
       les appels. Cette fonction servira également dans le cas [Icall]. *)
    Astv.Ecall (resolve_call env fenv c)

(* Fonction pour la résolution des identifiants au niveau d'un appel de
   fonction. *)
and resolve_call (env: var_env) (fenv: fun_env) ((f, args): Ast.call) :
    Astv.call =
    let rec expr_list env fenv args=match args with
    |[] ->[]
    | arg1::arglist->resolve_expr env fenv arg1 :: expr_list env fenv arglist
    in
    Env.find f fenv , expr_list env fenv args
        
let add_par env params=
    let rec addpar env i=function
    | [] -> env
    | par::r-> let env =Env.add par (Astv.Param (!i,par)) env in 
            i:=!i+1;
            addpar env i r 
      in addpar env (ref 0) params

let rec resolve_instr (env: var_env) (fenv: fun_env) (nxt_local: int) :
    Ast.instr -> Astv.instr option * var_set * fun_set * var_env * fun_env * int =
  function
    | Idecl_var id    ->
      let var, nxt_local = if nxt_local < 0
	then new_svar id, nxt_local
	else Astv.Local_var (nxt_local, id), nxt_local + 1
      in
      None, Vset.singleton var, Funset.empty, Env.add id var env, fenv, nxt_local

    | Idecl_fun (id, params, b) ->
      add_par env params;
      let fun_var = new_fun id in 
      let blk, vset, fset, nxt_local = resolve_block env fenv nxt_local b in
      let fundecal={ Astv.name = fun_var ; Astv.body = blk ; Astv.nb_locals = nxt_local} in
      None, vset,Funset.singleton fundecal, env , Env.add id fun_var fenv,(-1)
      
    | Iassign (id, e) ->
      let svar = Env.find id env
      and e    = resolve_expr env fenv e
      in
      Some (Astv.Iassign (svar, e)), Vset.empty, Funset.empty, env, fenv, nxt_local

    | Isetarr (a, i, e) ->
      let a = resolve_expr env fenv a
      and i = resolve_expr env fenv i
      and e = resolve_expr env fenv e
      in
      Some (Astv.Isetarr (a, i, e)), Vset.empty, Funset.empty, env, fenv, nxt_local

    | Iblock b ->
      let is, vset, fset, _ = resolve_block env fenv nxt_local b in
      Some (Astv.Iblock is), vset, fset, env, fenv, nxt_local
	
    | Iwhile (c, is) ->
      let c  = resolve_expr env fenv c
      and is, vset, fset, _ = resolve_block env fenv nxt_local is
      in
      Some (Astv.Iwhile(c, is)), vset, fset, env, fenv, nxt_local

    (* Construction ajoutée aujourd'hui. *) 
    | Iif (c, is1, is2) ->
      let c = resolve_expr env fenv c
      and is1, vset1, fset1, _ = resolve_block env fenv nxt_local is1
      and is2, vset2, fset2, _ = resolve_block env fenv nxt_local is2
      in
      Some (Astv.Iif(c, is1, is2)),
      Vset.union vset1 vset2,
      Funset.union fset1 fset2,
      env, fenv, nxt_local
	
    | Iprint e ->
      Some (Astv.Iprint (resolve_expr env fenv e)), Vset.empty, Funset.empty, env, fenv, nxt_local

    | Inewline ->
      Some Astv.Inewline, Vset.empty, Funset.empty, env, fenv, nxt_local

    | Icall c ->
      Some (Astv.Icall (resolve_call env fenv c)), Vset.empty, Funset.empty, env, fenv, nxt_local
	
    | Ireturn e ->
      Some (Astv.Ireturn (resolve_expr env fenv e)),Vset.empty,Funset.empty,env,fenv,nxt_local

    | Iexit    ->
      Some Astv.Iexit, Vset.empty, Funset.empty, env, fenv, nxt_local

	
and resolve_block (env: var_env) (fenv: fun_env) (nxt_local: int) :
    Ast.instr list -> Astv.block * var_set * fun_set * int = function
  | [] -> [], Vset.empty, Funset.empty, nxt_local
  | i::is ->
    let i, vs1, fs1, env, fenv, nxt_local = resolve_instr env fenv nxt_local i in
    let is, vs2, fs2, nxt_local = resolve_block env fenv nxt_local is in
    let is = match i with
      | None -> is
      | Some i -> i :: is
    in
    is, Vset.union vs1 vs2, Funset.union fs1 fs2, nxt_local
      
let resolve_prog (p: Ast.prog) : Astv.prog =
  let is, vset, fset, _ = resolve_block Env.empty Env.empty (-1) p in
  { Astv.instrs = is;
    Astv.svars = Vset.elements vset;
    Astv.funs = Funset.elements fset; }
