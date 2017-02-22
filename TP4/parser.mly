%{

  open Astcommon
  open Ast

  let current_pos () =
    Parsing.symbol_start_pos (),
    Parsing.symbol_end_pos ()
  let rec calu_number (d:expr list) :int=
  		match d with
  		|e1::r ->(1+(calu_number r)) 
  		|[] ->0
  let rec agssi_table (id:ident)(d:expr list) (i:int) : instr list=
  		match d with
  		|e1::r -> (Isetarr (Eident id, Econst (Cint i), e1))::(agssi_table id  r (i+1) )
  		|[] ->[]
  		
  let init_table (id:ident) (d:expr list) :instr=
  		let num=calu_number d in 
         Iassign (id, Enewarr (Econst (Cint (num))))
  let make_table (id: ident) (d: expr list) : instr =
		Iblock ((Idecl_var (id))::(init_table id d )::(agssi_table id d 0))
  let instr_table (il:instr list):instr=
  		Iblock il
  let decag (id:ident)(e:expr)(il: instr list):instr =
  		let list_expr=(List.append [(Idecl_var id);(Iassign(id,e))] il) in 
  		Iblock (list_expr)

   
%}

%token <int> CONST_INT
%token PLUS MINUS MULT DIV
%token <bool> CONST_BOOL
%token AND OR NOT
%token EQ NEQ
%token GE GT LE LT
%token IF THEN ELSE
%token LPAREN RPAREN
%token LCRO RCRO
%token LBR RBR
%token <Ast.ident> IDENT
%token VAR ASSIGN
%token PRINT NEWLINE EXIT
%token SEMI VGL
%token BEGIN END WHILE FOR
%token EOF

%nonassoc ELSE
%left OR
%left AND
%left NOT
%left EQ NEQ GE GT LE LT
%left PLUS MINUS
%left MULT DIV

%start prog
%type <Ast.prog> prog

%%

prog:
| instrs=list(instr); EOF { instrs }
;
  
block:
| BEGIN; instrs=list(instr); END      { instrs           }
;
  
instr:
| VAR; id=IDENT; SEMI                 { Idecl_var id        }

| id=IDENT; ASSIGN; e=expr; SEMI      { Iassign (id, e)     }
| PRINT; e=expr; SEMI                 { Iprint e            }
| b=block                             { Iblock b            }
| WHILE;e=expr;b=block;			           { Iwhile(e,b)		    }

| FOR;
  LPAREN;e1=expr;SEMI;e2=expr;SEMI;e3=expr;RPAREN;
		b=block;					  { Ifor(e1,e2,e3,b)			}
| VAR; id=IDENT; ASSIGN; LBR;d=donne; RBR; SEMI ;instrs=list(instr)
									  { make_table id d  	}
| id=IDENT;ASSIGN;LBR;d=donne;RBR;SEMI;instr=list(instr)
									  { instr_table (agssi_table id d 0)  }
| VAR;id=IDENT;ASSIGN;e=expr;SEMI;instr=list(instr)
									  {	decag id e 	instr	}
| NEWLINE; SEMI                       { Inewline            }
| EXIT; SEMI                          { Iexit               }
| e1=expr;LCRO;e2=expr;RCRO;ASSIGN;e3=expr;SEMI { Isetarr(e1,e2,e3)}
;

donne:
| e=expr;VGL;d=donne						{e::d}
| e=expr									      {[e]}	
;
expr:
| c=const                                  { c                   }
| id=IDENT                                 { Eident id           }
| LPAREN; s=expr; RPAREN                   { s                   }
| op=unop; e=expr                          { Eunop (op, e)       }
| e1=expr; op=binop; e2=expr               { Ebinop (op, e1, e2) }
| IF; c=expr; THEN; e1=expr; ELSE; e2=expr { Eif (c, e1, e2)     }
| LCRO;e=expr;RCRO						   { Enewarr(e) 		 }
| e1=expr;LCRO; e2=expr; RCRO;			   { Egetarr(e1,e2)		 }
;

const:
| i=CONST_INT  { Econst (Cint i)  }
| b=CONST_BOOL { Econst (Cbool b) }
;

%inline binop:
| PLUS  { Plus  }
| MINUS { Minus }
| MULT  { Mult  }
| DIV   { Div   }
| AND   { And   }
| OR    { Or    }
| EQ    { Eq    }
| NEQ   { Neq   }
| LT    { Lt    }
| LE    { Le    }
| GT    { Gt    }
| GE    { Ge    }
;

%inline unop:
| MINUS { Uminus }
| NOT   { Not    }
;
