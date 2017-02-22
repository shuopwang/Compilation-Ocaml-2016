%{

  open Ast

  (* Vous pouvez insérer ici du code Caml pour définir des fonctions
     ou des variables qui seront utilisées dans les actions sémantiques. *)

%}

(* Définition des lexèmes. *)
%token EOF
%token <int>INT
%token <bool>BOOL
(*les operateurs*)
%token LPAR RPAR PLUS MINUS MULT DIV AND OR 
%token EQ NEQ LT LE GT GE
%token NOT UMINUS
%token IF THEN ELSE
		   
(* Règles d'associativité et de priorité. *)
%left PLUS MULT
%left DIV MINUS
%left AND OR
%left EQ NEQ LT LE GT GE
%right NOT UMINUS
%nonassoc ELSE




(* Symbole de départ et type de la valeur produite par l'action sémantique. *)
%start toplevel_expr
%type <Ast.expr> toplevel_expr

%%

(* Règles. *)

toplevel_expr:
(* Expression à la racine : une expression [expr] dont on notera [e] la valeur
   sémantique, suivie du symbole [EOF].
   La valeur sémantique associée est la valeur [e] de l'expression.
*)
| e=expr; EOF { e }
;

expr:
| i = INT {Econst (Cint i)}
|b = BOOL {Econst(Cbool b)}
| LPAR; e=expr; RPAR { e }

|e1 = expr; PLUS; e2 = expr {Ebinop(Plus,e1,e2)}
|e1 = expr; MINUS; e2 = expr {Ebinop(Minus,e1,e2)}
|e1 = expr; MULT; e2 = expr {Ebinop(Mult,e1,e2)}
|e1 = expr; DIV; e2 = expr {Ebinop(Div,e1,e2)}

|e1 = expr; AND; e2 = expr {Ebinop(And,e1,e2)}
|e1 = expr; OR; e2 = expr {Ebinop(Or,e1,e2)}

|e1 = expr; LT; e2 = expr {Ebinop(Lt,e1,e2)}
|e1 = expr; GT; e2 = expr {Ebinop(Gt,e1,e2)}
|e1 = expr; LE; e2 = expr {Ebinop(Le,e1,e2)}
|e1 = expr; GE; e2 = expr {Ebinop(Ge,e1,e2)}
|e1 = expr; NEQ; e2 = expr {Ebinop(Neq,e1,e2)}
|e1 = expr; EQ; e2 = expr {Ebinop(Eq,e1,e2)}

|e1 = expr; UMINUS; {Eunop(Uminus,e1)}
|e1 = expr; NOT; {Eunop(Not,e1)}

|IF; e1 = expr; THEN; e2 = expr ELSE e3 = expr {Eif(e1,e2,e3)}

| EOF { failwith "Unlikely" }
;;
