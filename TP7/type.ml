open Astcommon
open Astt

let mk_texpr e t = { expr=e; ty=t }

let rec check_types ty1 ty2 = match ty1, ty2 with
  | Tint, Tint -> ()
  (* Certains des autres cas sont à autoriser,
     d'autres doivent lever une exception. *)
  | Tbool, Tbool -> ()
  | Tarr a1, Tarr a2 -> check_types a1 a2
  | Tint, _ ->failwith "error: not the same type type the first is int"
  | Tbool,_ ->failwith "error: not the same type the first is bool "
  | _,_-> failwith "error: the different type"
  
let rec type_expr = function
  | Astv.Econst c ->
    let ty = match c with
      | Cint _  -> Tint
      | Cbool _ -> Tbool
    in
    mk_texpr (Econst c) ty
      
  | Astv.Eunop (op, e) ->
    let e  = type_expr e in
    let ty = match op with
      | Uminus -> check_types Tint  e.ty; Tint
      | Not    -> check_types Tbool e.ty; Tbool
    in
    mk_texpr (Eunop(op, e)) ty

  | Astv.Evar  var ->
      let ty=match  var with
     | Astv.Static_var   (_,_,ty1)->ty1
     | Astv.Param      (_,_,ty2)->ty2
     | Astv.Local_var  (_,_,ty3)->ty3
      in
     mk_texpr (Evar (var)) ty

  | Astv.Ebinop  (binop,e1,e2)->
    let e1 = type_expr e1 in
    let e2 = type_expr e2 in
    let ty= match binop with
    | Plus | Minus | Mult | Div ->check_types e1.ty Tint;check_types e1.ty e2.ty; Tint
    | And  | Or -> check_types e1.ty Tbool ;check_types e1.ty e2.ty; Tbool
    | Eq   | Neq   | Lt   | Le  | Gt | Ge ->  check_types e1.ty Tint;check_types e1.ty e2.ty; Tbool
    in
    mk_texpr (Ebinop (binop,e1,e2)) ty

  | Astv.Eif   (e1,e2,e3) ->
   let e1= type_expr e1 in
   let e2= type_expr e2 in 
   let e3 =type_expr e3 in 
   check_types e1.ty Tbool;
   check_types e2.ty e3.ty;
   mk_texpr (Eif (e1,e2,e3)) e2.ty

  | Astv.Enewarr (ty,e1)->
    let e1=type_expr e1 in
    check_types e1.ty ty;
    mk_texpr (Enewarr (ty,e1)) ty

  | Astv.Egetarr (e1,e2)->
   let e1= type_expr e1 in 
   let e2= type_expr e2 in
   check_types e2.ty Tint;
   mk_texpr (Egetarr (e1,e2)) e1.ty
  | Astv.Ecall  (f,params) ->
    let fty=match f with
    Astv.Function(_,_,fty) ->fty
    in
    let ty=match fty.return_ty with
    | Some t -> t
    | _ -> failwith "The function is voids"
  in
    mk_texpr (Ecall (f,(type_call (f,params)))) ty
      
      
and type_call (f, params) =
   List.map type_expr params
  
(* [ret] est le type éventuel attendu lors d'une instruction [return]. *)
let rec type_block ret b =
  List.map (type_instr ret) b

and type_instr ret = function
  | Astv.Iblock b ->
    let b = type_block ret b in
    Iblock b

  | Astv.Iwhile (e, b) ->
    let e = type_expr  e
    and b = type_block ret b
    in
    check_types Tbool e.ty;
    Iwhile (e, b)
  | Astv.Inewline -> Inewline

  | Astv.Iassign  (var,e)->
   let ty=match var with
     | Static_var   (_,_,ty1)->ty1
     | Param      (_,_,ty2)->ty2
     | Local_var  (_,_,ty3)->ty3
   in 
   let e= type_expr e in 
   check_types ty e.ty;
   Iassign (var,e)

  | Astv.Isetarr   (e1,e2,e3)-> 
  let e1= type_expr e1 in 
  let e2= type_expr e2 in 
  let e3= type_expr e3 in 
  check_types e2.ty Tint;
  check_types e1.ty e3.ty;
  Isetarr (e1,e2,e3)

  | Astv.Iif       (e,b1,b2)-> 
    let e=type_expr e in
    let b1= type_block ret b1 in
    let b2= type_block ret b2 in
    check_types Tbool e.ty;
    Iif (e,b1,b2)
  | Astv.Iprint    e-> 
      let e=type_expr e in 
      check_types e.ty Tint;
      Iprint (e)
  | Astv.Ireturn   e-> 
        Ireturn (type_expr e)
  | Astv.Icall   (f,params)-> Icall(f,(type_call (f,params)))
  | Astv.Iexit -> Iexit

let type_fun_descr fdescr =
  let ret = match fdescr.Astv.name with
      Astv.Function (_, _, fty) -> fty.return_ty
  in
  { name  = fdescr.Astv.name;
    body  = type_block ret fdescr.Astv.body;
    lvars = fdescr.Astv.lvars }
    
let type_prog p =
  let instrs = type_block None p.Astv.instrs
  and funs   = List.map type_fun_descr p.Astv.funs
  in
  { instrs = instrs;
    svars  = p.Astv.svars;
    funs   = funs }
