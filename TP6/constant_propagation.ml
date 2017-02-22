open Astcommon
open Astv

module Venv = Map.Make (struct type t = Astv.var let compare = compare end)

type reaching_defs = One of expr | More

(* L'environnement de type def_env associe à une variable le fait
   qu'elle ait une ou plusieurs valeurs possibles (si aucune, la variable
   n'appraraît pas dans l'environnement) *)
type def_env = reaching_defs Venv.t

(* Type des annotations :
 * def_in : ensemble des définitions visibles à un point de programme
 * par exemple :
 *   var x;
 *   x := 3;
 *   var y;
 *   if x < 0 then y := -1 else y := 1;
 *      ici, on a (def_in  = [x -> One 3]; 
 *                 def_out = [x -> One 3; y -> More])
 *)
type def_annot = { mutable def_in: def_env;
                   mutable def_out: def_env }

(* Type principal associant à chaque instruction une annotation 
   de type def_annot. *)
type annot_instr = { i: a_instr;
                     annot: def_annot}

and a_block = annot_instr list

and a_instr =
  | Aassign   of var  * expr
  | Asetarr   of expr * expr  * expr
  | Ablock    of a_block
  | Awhile    of expr * a_block
  | Aif       of expr * a_block * a_block
  | Aprint    of expr
  | Anewline
  | Areturn   of expr
  | Acall     of call
  | Aexit

(* Associe à chaque variable de la liste le fait qu'elle peut être
   associée à plusieurs valeurs. Cette fonction est utilisée dans le cas 
   d'un appel de fonction où on considère, pour commencer, qu'à la sortie 
   d'une fonction on ne peut rien prévoir sur la valeur des variables 
   du programme. *)
let fuzzy_defs vars =
  List.fold_right (fun v env -> Venv.add v More env) vars Venv.empty
    
(* Fonction transformant une instruction de type Astv.instr en
   une instruction annotée donc de type annot*)
let annot_instr i =
  { i = i; annot = { def_in = Venv.empty; def_out = Venv.empty } }
    
let rec init_instr = function
  | Iassign (v, e)    -> annot_instr (Aassign (v, e))
  | Iblock b          -> annot_instr (Ablock (init_block b))
  | Isetarr (e1,e2,e3)  -> annot_instr (Asetarr (e1,e2,e3))
  | Iwhile (e,b)   -> annot_instr (Awhile (e,init_block b)) 
  (* Construction ajoutée aujourd'hui. *)
  | Iif (e,b1,b2)     -> annot_instr (Aif (e,(init_block b1),(init_block b2)))
  | Iprint e         -> annot_instr (Aprint e)
  | Inewline      -> annot_instr (Anewline)
  | Ireturn  e    -> annot_instr (Areturn e)
  | Icall  call -> annot_instr (Acall call)
  | Iexit   ->annot_instr (Aexit)
  |  _ -> failwith "mal formel"
    
and init_block b = List.map init_instr b

(* Cette fonction sera à utiliser avec la fonction Map.Make.merge
   dans les cas nécessaires. *)
let merge_rule _ o1 o2 = match o1, o2 with
  | None, None -> None
  | None, Some d | Some d, None -> Some d
  (* Raffinement possible à introduire :
     si deux définitions identiques, ne pas crier à l'ambiguïté.
  *)
  | Some _, Some _ -> Some More
    
let rec propagate_instr vars pred_out a =
  (* Initialement, le dictionnaire def_in est le même que le dictionnaire 
     def_out de l'instruction précédente (ceci reste vrai sauf pour les boucles) *)
  a.annot.def_in <- pred_out;
  begin
    match a.i with
      | Ablock b          -> a.annot.def_out <- propagate_block vars pred_out b

      | Awhile (_, b)     ->
        (* On fait deux passes dans la boucle. Entre les deux on redéfinit
	   le dictionnaire d'entrée en y ajoutant ce qui avait été produit
	   en sortie du premier tour.
	   Conjecture : grâce à notre approximation de l'ensemble des
	   définitions on a atteint le point fixe.
	   Bien sûr, vous pouvez le démontrer.
        *)
        a.annot.def_out <- propagate_block vars pred_out b;
        a.annot.def_in <- a.annot.def_out;
        a.annot.def_out <- propagate_block vars pred_out b        
      | Aif (_, b1, b2)   ->
        (* Après le if, on fait l'union, en invalidant les variables définies
	   des deux côtés.
        *)
        a.annot.def_out <- propagate_block vars pred_out b1;
        a.annot.def_out <- propagate_block vars pred_out b2
          
      (* Appel de fonction, version de base : tout le dictionnaire est invalidé.
	 Il faut construire un dictionnaire indiquant [More] pour toutes les
	 variables, même celles pas encore touchées.
	 La fonction [fuzzy_defs] construit ce dictionnaire à partir de la
	 liste des variables connues.
	 Remarque : dans l'état actuel des définitions on ne sait pas construire
	 cette liste pour les fonctions, l'ensemble des variables locales
	 n'étant pas enregistré dans l'AST.
      *)
    
      | Acall _           -> a.annot.def_out <- fuzzy_defs vars
      | Asetarr   (e1, e2, e3)-> failwith "not compele Asetarr"
      | Aprint    e -> failwith "not compele Aprint"(*a.annot.def_out <-*)
      | Areturn   e -> failwith "not compele Areturn"

  end;
  (* On a besoin du dictionnaire de sortie pour l'instruction suivante *)
  a.annot.def_out
	
and propagate_block vars pred_out l =
  List.fold_left (fun p_out i -> propagate_instr vars p_out i) pred_out l
    
let rec strip_a annot = strip_i annot.annot.def_in annot.i

and strip_b block = List.map strip_a block

and strip_i defs  = function
  | Aassign (v, e)    -> Iassign (v, strip_e defs e)
  | Asetarr  (e1,e2,e3) -> Isetarr (strip_e defs e1, strip_e defs e2, strip_e defs e3)
  | Ablock  b -> Iblock (strip_b b)
  | Awhile  (e,b)  ->Iwhile (strip_e defs e, strip_b b)
  | Aif     (e,b1,b2) -> Iif (strip_e defs e, strip_b b1, strip_b b2)
  | Aprint   e ->Iprint (strip_e defs e)
  | Anewline -> Inewline
  | Areturn   e -> Ireturn (strip_e defs e)
  | Acall   call -> Icall (strip_call defs call)
  | Aexit -> Iexit
  |_ ->failwith " mal forme"

    
and strip_e defs e = match e with
  | Econst _ -> e
  | Evar var ->failwith "not compele Evar"  
      (* Dans cette version simple, on ne fait la substitution que si la valeur
	 substituée est une constante. On pourrait aller plus loin et inspecter
	 la valeur donnée par l'unique définition, en regardant notamment si
	 elle est suffisamment simple ou simplifiable pour que la substitution
	 soit intéressante (on ne veut surtout pas inliner une valeur dont
	 le calcul demande d'aller lire plusieurs variables).
	 Ici quoiqu'il arrive, interaction forte avec l'autre optimisation
	 du jour.
      *)
         
  | Eunop (unop,e1) -> failwith "not compele Eunop"(*Eunop (unop, strip_e e1) *)
  | Ebinop (binop,e1,e2) ->failwith "not compele Ebinop"(* Ebinop (binop, strip_e e1, strip_e e2)*)
  | Eif    (e1,e2,e3) -> failwith "not compele Eif" (*Eif (strip_e e1,strip_e e2,strip_e e3)*)
  | Enewarr e ->failwith "not compele Enewarr"  (* Enewarr (strip_e e) *)
  | Egetarr (e1,e2)-> failwith "not compele Egetarr" (* Egetarr (strip_e e1,strip_e e2) *)
  | Ecall  call -> Ecall(strip_call defs call)   
and strip_call defs (f, args) = f, List.map (strip_e defs) args
    
(* Pour rester correct vis-à-vis du problème de la connaissance de l'ensemble
   des variables locales d'une fonction, cette première version n'optimise
   que le corps du programme. *)
let propagate_constants prog =
  let a_prog = init_block prog.instrs in
  let _ = propagate_block prog.svars Venv.empty a_prog in
  let result = strip_b a_prog in
  { instrs = result; svars = prog.svars; funs = prog.funs }
