open Astcommon
open Astv

let mk_unop op e =
  match op, e with
    | Uminus, Econst (Cint i) -> Econst (Cint (-i))

    | Not, Econst (Cbool b)   -> Econst (Cbool (not b))

    | _, _ -> Eunop (op, e)

(* Deux cas triviaux sont donnés consistant aux cas, 
   (soient c1 et c2 deux constantes différentes) :
 * c1 = c1 ou c1 <> c2 qui donnent true
 * c1 = c2 ou c1 <> c1 qui donnent false
 * 
 * Le reste est à faire.
 *)
let mk_binop op e1 e2 =
  match op, e1, e2 with
    (* Tests d'égalité. *)
    | (Eq | Neq), Econst c1, Econst c2 ->
      let op = match op with
	| Eq  -> ( = )
	| Neq -> ( <> )
	| _ -> assert false
      in Econst (Cbool (op c1 c2))
      
    (* A compléter : arithmétique, comaparaisons d'entiers etc. *)
    | (Ge |Gt|Le|Lt), Econst c1, Econst c2->
      let op=match op with
      | Ge -> ( >= )
      | Gt -> ( > )
      | Le -> ( <= )
      | Lt -> ( < )
      | _ -> assert false
          in Econst (Cbool (op c1 c2))

(* Il faut transformer chaque expression en une expression optimisée si possible
 *
 * Les cas correspondant à une constante et une variable
 * (aucune optimisation possible) et le cas d'un opérateur unaire sont donnés.
 * 
 * Le reste est à faire.
*)
let rec fold_constants_expr e = match e with
  | Econst _ | Evar _ -> e
    
  | Eunop (op, e) -> mk_unop op (fold_constants_expr e)
    
  | Ebinop (op,e1,e2) -> mk_binop op (fold_constants_expr e1) (fold_constants_expr e2)

  | Eif (e1,e2,e3)-> fold_constants_expr e1;
                    fold_constants_expr e2;
                  fold_constants_expr e3
  | Enewarr e1-> fold_constants_expr e1
  | Egetarr (e1,e2)-> fold_constants_expr e1; fold_constants_expr e2
(* De la même manière que pour les expressions, il faut optimiser 
 * les instructions qui peuvent l'être en optimisant les expressions
 * les composant. *)
let rec fold_constants_instr = function
  | Iassign (v, e) -> Iassign (v, fold_constants_expr e)

  | Iblock b -> Iblock (fold_constants_block b)

  | Isetarr (e1,e2,e3)-> Isetarr (fold_constants_expr e1,fold_constants_expr e2, fold_constants_expr e3)

  | Iwhile (e1,b)->Iwhile (fold_constants_expr e1, fold_constants_block b)

  | Iprint e -> Iprint (fold_constants_expr e)

  | Ireturn e -> Ireturn (fold_constants_expr e) 

  | Iif (e,b1,b2) -> Iif (fold_constants_expr e,fold_constants_block b1,fold_constants_block b2)

and fold_constants_block b = List.map fold_constants_instr b

let fold_constants (p: prog) =
  { p with instrs = fold_constants_block p.instrs;
    funs   = List.map
      (fun f -> { f with body = fold_constants_block f.body })
      p.funs
  }
