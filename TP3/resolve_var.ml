open Astcommon
open Ast
open Printf


(* Définition d'un type pour les environnements associant des variables [Astv.var]
   à des chaînes de caractères. Vous disposez en particulier de la constante
   [Env.empty] qui désigne un environnement vide ainsi que des fonctions :

   Env.find : string -> var_env  -> Astv.var
   ... qui renvoie la variable associée à une chaîne de caractères.

   Env.add  : string -> Astv.var -> var_env  -> var_env
   ... qui renvoie un nouvel environnement, étendu d'une association.
*)
module Env = Map.Make(String)
type var_env = Astv.var Env.t
  (*
  var_env is a Env, it include Astv.var 
  type var = Static_var of int * Ast.ident
  and Env.t
  *)
    
(* Définition d'un type pour les ensembles de variables [Astv.var].
   Vous disposez en particulier de la constante [Vset.empty] qui désigne un
   ensemble vide ainsi que des fonctions :

   Vset.singleton : Astv.var -> var_set
   ... qui construit un ensemble contenant une unique variable.

   Vset.union : var_set -> var_set -> var_set
   ... qui renvoie l'union de deux ensembles.
*)
module Vset = Set.Make(struct type t = Astv.var let compare = compare end)
type var_set = Vset.t

  (*
  l'ensemble de Astv.var
  type var = Static_var of int * Ast.ident
  *)

    
(* Création d'une nouvelle variable à partir d'un identifiant.
   Remarque : faire apparaître l'identifiant dans la définition n'est pas
   nécessaire. Nous le proposons ici pour faciliter le débogage de votre
   compilateur. *)
let new_svar : ident -> Astv.var =
  let c = ref 0 in
  fun (id: ident) -> incr c; Astv.Static_var (!c, id)

    
(* Transformation d'une expression [Ast.expr] en une expression [Astv.expr],
   en utilisant un environnement [env] pour convertir les identifiants en
   variables. *)
let rec resolve_expr (env: var_env) : Ast.expr -> Astv.expr = function
  (* Une constante est directement traduite en la même constante. *)
  | Econst c ->
    Astv.Econst c
  (* Cas à compléter : Eident, Eunop, Ebinop, Eif. *) 
  | Eident i -> Astv.Evar(Env.find i env)
  | Eunop (unop,ex) -> Astv.Eunop (unop,resolve_expr env ex)
  | Ebinop (op,ex1,ex2) -> Astv.Ebinop (op,resolve_expr env ex1,resolve_expr env ex2)
  | Eif (ex1,ex2,ex3) -> Astv.Eif (resolve_expr env ex1,resolve_expr env ex2,resolve_expr env ex3)
  | _ -> failwith "Not implemented"

    
(* Transformation d'une instruction [Ast.instr] en une instruction [Astv.instr].
   Un appel [resolve_instr env i] renvoie trois éléments :
   1/ Une instruction [Astv.instr] optionnelle, qui sera [None] si l'instruction
      [i] n'a pas d'équivalent dans [Astv.instr], et [Some i'] sinon.
   2/ L'ensemble des variables introduites par cette expression.
   3/ Une mise à jour de l'environnement [env].
*)
let rec resolve_instr (env: var_env) :
    Ast.instr -> Astv.instr option * var_set * var_env
  = function
    (* L'instruction [Ast.Iexit] est directement traduite en [Astv.Iexit].
       Aucune variable n'est introduite par cette instruction, et l'environnement
       n'est pas modifié. De même pour [Ast.Inewline]. *)
    | Iexit    -> Some Astv.Iexit, Vset.empty, env
    | Inewline -> Some Astv.Inewline, Vset.empty, env
    (* [Ast.Iprint] est traité comme les deux cas précédents, mais il faut en
       plus transformer l'expression [e]. *)
    | Iprint e -> Some (Astv.Iprint (resolve_expr env e)), Vset.empty, env

    (* Cas à compléter : Idecl_var, Iassign, Iblock, Iwhile *)
    | Idecl_var ident->let c= new_svar ident in 
                              None,
                              Vset.singleton c,(*je sais pas si correct*)
                              Env.add ident c env 
    | Iassign (ident,expr)->  let c = (Env.find ident env) in 
                              Some (Astv.Iassign (c,resolve_expr env (expr))),
                              Vset.empty, env
    | Iblock (block) ->let (blk,set)=resolve_block env block in
                              Some (Astv.Iblock (blk)),set,env

    | Iwhile (expr,block) ->let ex1=resolve_expr env expr in
                            let (blk,set)=resolve_block env block in
                              Some (Iwhile (ex1,blk)),set,env
    
    | _ -> failwith "Not implemented"

(* Suggestion : utilisez une fonction auxiliaire pour le traitement des blocs
   d'instructions. Selon le type proposé ici, cette fonction peut renvoyer
   le bloc transformé ainsi que l'ensemble des variables introduites dans le
   bloc. En revanche, il n'est pas nécessaire ici de renvoyer un environnement
   modifié, car les variables introduites dans le bloc ne sont pas visibles
   de l'extérieur. *)
and resolve_block (env: var_env) :Ast.instr list -> Astv.block * var_set =
      function
     | [] -> [], Vset.empty
     | ex::blk ->
    let ex, vset1, env = resolve_instr env ex in
    let blk, vset2 = resolve_block env blk in

    let block=match ex with
      | None -> blk
      | Some ex -> ex :: blk
     in 
     block, Vset.union vset1 vset2
  
    
(* Transformation d'un programme [Ast.prog] en un programme [Astv.prog]. *)
let resolve_prog (p: Ast.prog) : Astv.prog =
  let is, vset = resolve_block Env.empty p in
  { Astv.instrs = is; Astv.svars = Vset.elements vset }
  
