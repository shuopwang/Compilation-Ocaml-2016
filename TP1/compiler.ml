open Ast
open Printf

(* Les fonctions [push] et [pop] prennent en argument un numéro de registre [i]
   et affichent le code correspondant à 
   [push] : placer sur la pile la valeur contenue dans le registre [$ai]
   [pop]  : transférer dans [$ai] la valeur présente au sommet de la pile
*)
let push: int -> unit =
  printf "  sub $sp, $sp, 4\n  sw $a%d, 0($sp)\n"

let pop: int -> unit =
  printf "  lw $a%d, 0($sp)\n  add $sp, $sp, 4\n"

    
(* Création d'une nouvelle étiquette pour les branchements. *)
let new_label : unit -> string =
  let c = ref 0 in
  fun () -> incr c; sprintf "__label__%05i" !c

    
(* Compilation des expressions.
   Le code produit place le résultat dans le registre [$a0]. *)
let rec compile_expr (e : Ast.expr) (n:int): unit = 
  match e with
      (* Constante : on charge directement la valeur dans le registre. *)
     | Econst c ->
      begin match c with
      | Cint i  -> printf "  li $a%d, %d\n"n i
      | Cbool b -> if b
              then 
              printf "  li $a%d,1\n" n
            else
              printf "  li $a%d,0\n" n
      end

      (* Opération arithmétique dont l'un des opérandes peut être utilisé
	 directement (sans passer par un registre).
	 Il faut que cet opérande soit une constante sur 16 bits signée.
	 Elle peut être le deuxième opérande de n'importe quelle opération
	 arithmétique, ou le premier opérande d'une opération commutative
	 (addition ou multiplication). *)
    | Ebinop ((Plus | Mult) as op, Econst (Cint i), e)
    | Ebinop ((Plus | Mult | Minus | Div) as op, e, Econst (Cint i))
	when -32768 <= i && i < 32768 ->
      (* On calcule d'abord l'opérande qui n'est pas immédiat. *)
      compile_expr e n;
      (* Puis on effectue l'opération. *)
      let op = match op with
	| Plus  -> "add"
	| Mult  -> "mul"
	| Minus -> "sub"
	| Div   -> "div"
	| _     -> assert false
      in
      printf "  %s $a%d, $a%d, %d\n"  op n n i

      (* Opération arithmétique ordinaire *)
    | Ebinop (op, e1, e2) ->
      (* 1. on calcule le résultat du premier opérande *)
      compile_expr e1 n;
      (* 2. on le sauvegarde sur la pile *)
      push 0;
      (* 3. on calcule le résultat du deuxième opérande *)
      compile_expr e2 (n+1);
      (* 4. on récupère sur la pile le premier résultat *)
      pop 1;
      (* 5. on effectue l'opération *)
      let op = match op with
	| Plus -> "add"
	| Mult -> "mul"
	| Minus -> "sub"
	| Div  -> "div"
  | Eq -> "beq"
  | Neq -> "bne"
  | Lt -> "blt"
  | Le -> "ble"
  | Gt -> "bgt"
  | Ge -> "bge"
  | And -> "and"
  | Or -> "or"
  | _    -> failwith "Not implemented"
      in
      if  op="add"||op="mul"||op="div"||op="sub"||op="beq"||op="bne"||op="blt"||op="ble"||op="bgt"||op="bge"
        then printf " %s $a0, $a1, $a0\n" op
      else if op ="and"
      then printf "  beq $a0, 1, continue\n  li $v0, 1\n  syscall\n  li $v0, 10\n  syscall\ncontinue:\n  %s $a0, $a1, $a0\n" op
        else if op ="or"
        then printf "  beq $a0, 0, continue\n  li $v0, 1\n  syscall\n  li $v0, 10\n  syscall\ncontinue:\n  %s $a0, $a1, $a0\n" op
       
    (* À vous de jouer ! *)
    | Eunop(unop,ex1)->
        compile_expr ex1 n;
       begin
           match unop with
      | Uminus->
          printf "neg $a0, $a0\n"
      | Not -> 
        printf "  not $a0, $a0\n" 
      | _ -> failwith "Not implemented"
       end
    |Eif(ex1,ex2,ex3) ->
          compile_expr ex1 n;
          let string=new_label()in
          printf "  beq $a0, .%sElse\n" string;
          compile_expr ex2 n;
          printf "  b         .%s\n" string;
          printf ".%sElse:\n" string;
          compile_expr ex3 n;
          printf ".%s:\n" string;
    | _ -> failwith "Not implemented"


(* Compilation d'une expression à la racine : on affiche d'abord le préambule,
   puis le code correspondant à l'expression, et enfin le code d'affichage et
   d'arrêt du programme. *)
let compile_toplevel_expr (e: Ast.expr) : unit =
  printf ".text\nmain:\n";
  compile_expr e 0;
  printf "  jal    print_int\n";
  printf "  li $v0, 1\n  syscall\n  li $v0, 10\n  syscall\n"
