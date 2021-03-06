open Astcommon
open Astv
open Printf
  
let push: int -> unit =
  printf "  sub $sp, $sp, 4\n  sw $a%d, 0($sp)\n"

let peek: int -> unit =
  printf "  lw $a%d, 0($sp)\n"

let pop: int -> unit =
  printf "  lw $a%d, 0($sp)\n  add $sp, $sp, 4\n"

let new_label : unit -> string =
  let c = ref 0 in
  fun () -> incr c; sprintf "__label__%05i" !c

let get_label : Astv.var -> string = function
  | Astv.Static_var (n, id) -> sprintf "__var__%05i__%s" n id
let get_loc :Astv.expr ->int= function
  | Econst (Cint i) -> i
  | _ -> 0

let max = ref 0 (*pour le max_loc *)

let flag = true(*test si'il est out_of_mermoire*)

let i = ref 1 (*l'indice de chaque tableau*)
 
let a =ref 1

 let hello : Astv.expr -> bool=function
      | Enewarr e->true
      | _ -> false

let rec generate_expr (e : Astv.expr) : unit = 
  match e with
      
    | Econst (Cint i)  -> printf "  li $a0, %d\n" i
    | Econst (Cbool b) -> printf "  li $a0, %d\n" (if b then 1 else 0)

    (* On charge l'adresse de la variable avec [la] puis on lit la valeur à
       cette adresse avec [lw]. L'étiquette de la variable est donnée par la
       fonction [get_label]. *)
    | Evar var -> printf "  la $a0, %s\n  lw $a0, 0($a0)\n" (get_label var)

    | Eunop (Uminus, e) ->
      generate_expr e;
      printf "  neg $a0, $a0\n"
    | Eunop (Not, e) ->
      generate_expr e;
      printf "  li $a1, 1\n  sub $a0, $a1, $a0\n"
      
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
      printf "  %s $a0, $a0, %d\n" op i
	
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
	| Eq   -> "seq"
	| Neq  -> "sne"
	| Lt   -> "slt"
	| Le   -> "sle"
	| Gt   -> "sgt"
	| Ge   -> "sge"
	| And  -> "and"
	| Or   -> "or"
      in
      printf "  %s $a0, $a1, $a0\n" op

    | Eif (c, e_then, e_else) ->
      let else_label = new_label()
      and end_label  = new_label()
      in
      generate_expr c;
      printf "  beqz $a0, %s\n" else_label;
      generate_expr e_then;
      printf "  b %s\n" end_label;
      printf "%s:\n" else_label;
      generate_expr e_else;
      printf "%s:\n" end_label

    | Enewarr e -> begin 
                    generate_expr e;
                    push 0;
                    max :=get_loc e;
                    i := !i +1;
                    printf " add $a0, $a0, 1\n";
                    printf " sll $a0, $a0, 4\n jal malloc\n";
                    pop 1;
                  end
(*create a tableau*)
    | Egetarr (a, i) ->
                      generate_expr a;push 0;
                      generate_expr i;pop 1;
                      printf "  lw $a2, 0($a1)\n";
                      printf "  bge $a0, $a2, out_of_memory \n";
                      printf "  add $a0, $a0, 1\n";
                      printf "  mul $a0, $a0, 4\n";
                      printf "  add $a0, $a0, $a1\n";
                      printf "  lw $a0, 0($a0)\n"  

 (*renouvie le value du tablea a[i]*)     

let rec generate_instr : instr -> unit = function
  
  | Iassign (var, e) ->
    (* Affectation : d'abord calcul de l'expression [e], puis mise à jour de la
       variable. L'adresse de la variable est obtenue avec [la] et l'étiquette
       donnée par [get_label], puis la mise à jour est effectuée avec [sw]. *)
    if flag=true
    then 
    begin
    generate_expr e; 
    printf "  la $a1, %s\n  sw $a0, 0($a1)\n" (get_label var)
    end
    else
    printf "\n"(*this time we need to changed the value of a[i]*)
  | Isetarr (a, i, e) -> 
    if flag=true
     then begin     
                      generate_expr a;
                      push 0;
                      generate_expr i;
                      pop 1;
                      printf "  lw $a2, 0($a1)\n";
                      printf "  bge $a0, $a2, out_of_memory \n";
                      printf "  add $a0, $a0, 1\n";
                      printf "  mul $a0, $a0, 4\n";
                      printf "  add $a0, $a0, $a1\n";
                      push 0;
                      generate_expr e;
                      pop 1;
                      printf " sw $a0, 0($a1)\n"
          end
      else
      printf "\n"
  | Iblock b      ->if flag =true
                then generate_block b

  | Iwhile (expr,b)-> if flag =true
                     then begin
                      let while_label = new_label()
                          and end_label  = new_label()
                          in
                          printf "%s:\n" while_label;
                          generate_expr expr;
                          printf "  beqz $a0, %s\n" end_label;
                          generate_block b; 
                          printf "  b %s\n" while_label;
                          printf "%s:\n" end_label;
                          end
  | Ifor (e1,e2,e3,b)-> if flag=true
                      then begin
                        generate_expr e1;
                        generate_expr e2;
                        generate_block b;
                        generate_expr e3;
                      end
  | Iprint e ->
    if flag =true 
    then begin generate_expr e;
    printf "  li $v0, 1\n  syscall\n"
      end
    else
    printf "\n"
  | Inewline ->
    printf "  li $v0, 11\n  li $a0, 10\n  syscall\n"
      
  | Iexit ->
    printf "  li $v0, 10\n  syscall\n"

(* Pour générer le code d'un bloc, on se contente d'appliquer la génération
   consécutivement à toutes les instructions du bloc. *)
and generate_block (b: block) : unit =
  List.iter generate_instr b



let init () = printf "
  li  $a0, 1024       # Appel système sbrk pour réserver 1024 octets.
  li  $v0, 9
  syscall

  la  $a0, nxt_loc    # L'appel système a placé dans $v0 l'adresse de début
  sw  $v0, 0($a0)     # de la zone réservée, à sauvegarder dans nxt_loc.

  add $v0, $v0, 1024  # Calcul de max_loc, 1024 octets plus loin.
  la  $a0, max_loc   
  sw  $v0, 0($a0)
                      # Initialisation terminée.

"

let system_vars () = printf "
nxt_loc:
  .word 0
max_loc:
  .word 0
"

let built_ins () = printf "
end_exec:                       # Fin de l'exécution
  li $v0, 10
  syscall

malloc:
  la   $v0, nxt_loc             # Sauvegarde de l'adresse de début de bloc
  lw   $v1, 0($v0)

  add  $a1, $v1, $a0            # Calcul de l'adresse de fin...
  la   $a2, max_loc
  lw   $a2, 0($a2)
  bgt  $a1, $a2, out_of_memory  # ... et arrêt en cas de dépassement

  sw   $a1, 0($v0)              # Sinon confirmation de l'allocation
  move $a0, $v1
  jr   $ra                      # et retour au point d'appel

out_of_memory:                  # Affichage d'un message d'erreur
  la $a0, __const_out_of_memory
  li $v0, 4
  syscall
  b end_exec
"

let constants () = printf "
__const_out_of_memory:
  .asciiz \"out of memory\"
"

let generate_prog (p : Astv.prog) : unit =
  (* Le code. *)  
  printf "  .text\nmain:\n";
  (* 1. Initialisation. *)
  init ();
  (* 2. Le programme lui-même. *)
  List.iter generate_instr p.instrs;
  (* 3. Les fonctions primitives. *)
  built_ins ();

  (* Les données. *)
  printf "  .data\n";
  (* 1. Les variables utilisées par les primitives. *)
  system_vars ();
  constants ();
  (* 2. Les variables de l'utilisateur. *)
  List.iter (fun var -> printf "%s:\n  .word 0\n" (get_label var)) p.svars
