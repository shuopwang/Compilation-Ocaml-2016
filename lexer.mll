{
  open Lexing
  open Parser
  open Ast


  (* Vous pouvez insÃ©rer ici du code Caml pour dÃ©finir des fonctions
     ou des variables qui seront utilisÃ©es dans les actions sÃ©mantiques. *)
  
  (*ajouter*)
  let level = ref 0 ;;

}

let digit  = ['0'-'9']
let number = digit+


rule token = parse
  | '\n' (* Actions en cas de retour Ã  la ligne :
      1. enregistrer le changement de ligne dans le tampon [lexbuf]
      (utile pour localiser les erreurs)
      2. relancer l'analyse en rappelant la fonction [token] sur [lexbuf]
   *)
      { new_line lexbuf; token lexbuf }

      
  |[' ' '\t']
      { token lexbuf }

  (*1.2 commentaires imbriqués*)
  | "(*" { comment lexbuf; token lexbuf }
    (* on commecnce le comment
      *)

  | eof  (* Fin de fichier : Ã©mission du lexÃ¨me [EOF] *)
       { EOF }
  | number 
      {INT(int_of_string (lexeme (* Lexing.lexbuf -> string*) lexbuf))}
      (*les parentenese*)
  | '(' {LPAR}
  | ')' {RPAR}
    (*les operations basics*)
  | '+' { PLUS }
  | '-' { MINUS }
  | '*' { MULT }
  | '/' { DIV }
 
(*les symbloes booleens et les comparaisons*)

  | "&&" {AND}
  | "||"  {OR}
  
  |"=="{EQ}
  |"!=" {NEQ}
  | '<' { LT }
  | '>' { GT }
  |"<=" {LE}
  |">=" {GE}

  |"not" {NOT}
  |"-" {UMINUS}
  (*les mots-cles*)
  |"if" {IF}
  |"then" {THEN}
  |"else" {ELSE}
   (*----ajout the constantes booleenes --*) 
  |"true"  {BOOL(true)}
  |"false" {BOOL(false)}

  | _
      { failwith "Lexical error" }
      
and comment = parse 
  | "*)" { () }
  | "(*" { comment lexbuf; comment lexbuf}
  |  _ { comment lexbuf }
  | eof { failwith "commentaire non terminé" }
      

