open Astcommon
open Astv
  
let push: int -> unit =
  Printf.printf "  sub $sp, $sp, 4\n  sw $a%d, 0($sp)\n"

let pop: int -> unit =
  Printf.printf "  lw $a%d, 0($sp)\n  add $sp, $sp, 4\n"

let new_label : unit -> string =
  let c = ref 0 in
  fun () -> incr c; Printf.sprintf "__label__%05i" !c

(* Association d'une étiquette à une variable statique. *)
let get_label : Astv.var -> string = function
  | Astv.Static_var (n, id) -> Printf.sprintf "__var__%05i__%s" n id
  
let rec generate_expr (e : Astv.expr) : unit = 
  match e with
      
    | Econst (Cint i)  -> Printf.printf "  li $a0, %d\n" i
    (* On représente [true] par l'entier [1] et [false] par l'entier [0]. *)
    | Econst (Cbool b) -> Printf.printf "  li $a0, %d\n" (if b then 1 else 0)

    | Evar var -> Printf.printf "  la $a0, %s\n  lw $a0, 0($a0)\n" (get_label var)

    (* Le [-] unaire est directement représenté par [neg].
       Pour la négation logique, on traduit [Not e] par [1 - e]. *)
    | Eunop (Uminus, e) ->
      generate_expr e;
      Printf.printf "  neg $a0, $a0\n"
    | Eunop (Not, e) ->
      generate_expr e;
      Printf.printf "  li $a1, 1\n  sub $a0, $a1, $a0\n"
      
    | Ebinop ((Plus | Mult) as op, Econst (Cint i), e)
    | Ebinop ((Plus | Mult | Minus | Div) as op, e, Econst (Cint i))
	when -32768 <= i && i < 32768 ->
      generate_expr e;
      let op = match op with
	| Plus -> "add"
	| Mult -> "mul"
	| Minus -> "sub"
	| Div  -> "div"
	| _    -> assert false
      in
      Printf.printf "  %s $a0, $a0, %d\n" op i
	
    | Ebinop (op, e1, e2) ->
      generate_expr e1;
      push 0;
      generate_expr e2;
      pop 1;
      let op = match op with
	| Plus -> "add"
	| Mult -> "mul"
	| Minus -> "sub"
	| Div  -> "div"
	(* Les autres opérateurs binaires correspondent directement
	   à des instructions MIPS. *)
	| Eq   -> "seq"
	| Neq  -> "sne"
	| Lt   -> "slt"
	| Le   -> "sle"
	| Gt   -> "sgt"
	| Ge   -> "sge"
	| And  -> "and"
	| Or   -> "or"
      in
      Printf.printf "  %s $a0, $a1, $a0\n" op

    | Eif (c, e_then, e_else) ->
      (* Création de deux étiquettes pour le début et la fin du bloc "else". *)
      let else_label = new_label()
      and end_label  = new_label()
      in
      (* Évaluation de la condition. *)
      generate_expr c;
      (* Si le résultat est [false], c'est-à-dire [0], sauter au bloc "else". *)
      Printf.printf "  beqz $a0, %s\n" else_label;
      (* ... sinon, on passe à l'instruction suivante, qui est le bloc "then". *)
      generate_expr e_then;
      (* À la fin du bloc "then", sauter à la fin du branchement. *)
      Printf.printf "  b %s\n" end_label;
      (* Début du bloc "else". *)
      Printf.printf "%s:\n" else_label;
      generate_expr e_else;
      (* Fin du branchement. *)
      Printf.printf "%s:\n" end_label

	
(* Génération de code pour les blocs. *)
let rec generate_instr : instr -> unit = function
  (* Calcul de l'expression, puis appel système d'affichage. *)
  | Iprint e ->
    generate_expr e;
    Printf.printf "  li $v0, 1\n  syscall\n"
      
  (* Appel système pour l'affichage du caractère '\n' *)
  | Inewline ->
    Printf.printf "  li $v0, 11\n  li $a0, 10\n  syscall\n"
       
  (* Appel système de fin du programme. *)
  | Iexit ->
    Printf.printf "  li $v0, 10\n  syscall\n"

  (* Cas à compléter : Iassign, Iblock, Iwhile.
     Rappel : Idecl_var a disparu dans [Astv]. *)
  | Iassign (var,expr)-> generate_expr expr;
                         Printf.printf "  la $a1, %s\n  sw $a0, 0($a1)\n" (get_label var)
  | Iblock b -> generate_block b;
  | Iwhile (expr,b)-> begin let while_label = new_label()
                          and end_label  = new_label()
                          in
                          Printf.printf " %s:\n"  while_label;
                          generate_expr expr;
                          Printf.printf "  beqz $a0, %s\n" end_label;
                          generate_block b; 
                          Printf.printf "  b %s\n" while_label;
                          Printf.printf "%s:\n" end_label;
                        end
  | _ -> failwith "Not implemented"
  and generate_block ( b: block ) : unit= 
  List.iter generate_instr b


    
(* Génération du code assembleur du programme complet. 
   Vous devez y définir une partie [.text] contenant le programme lui-même,
   mais aussi une partie [.data] définissant les variables. *)
let generate_prog (p : Astv.prog) : unit =
  (*generer du code pour p.instrs*)
  List.iter generate_instr p.instrs;
  (*declarer des donnees pour p.svar*)
  let strings=List.map get_label p.svars in
  List.iter (fun s-> Printf.printf "%s\n" s) strings;

