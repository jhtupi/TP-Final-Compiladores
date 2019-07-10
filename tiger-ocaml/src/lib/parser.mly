// parser.mly

%{
  open Absyn
%}

%token <int>           INT
%token <string>        STR
%token <Symbol.symbol> ID
%token                 FOR WHILE BREAK LET IN NIL TO END
%token                 FUNCTION VAR TYPE ARRAY IF THEN ELSE DO OF
%token                 LPAREN "(" RPAREN ")"
%token                 LBRACK "[" RBRACK "]"
%token                 LBRACE "{" RBRACE "}"
%token                 DOT "." COLON ":" COMMA "," SEMI ";"
%token                 PLUS "+" MINUS "-" TIMES "*" DIV "/"
%token                 EQ "=" NE "<>"
%token                 LT "<" LE "<=" GT ">" GE ">="
%token                 AND "&" OR "|"
%token                 ASSIGN ":="
%token                 EOF


%nonassoc AND OR
%nonassoc EQ NE LT LE GT GE
%left PLUS MINUS
%left TIMES DIV

%start <Absyn.lexp>    program

%%

program:
 | x=exp EOF                             {x}

exp:
 | NIL                                   	{$loc, NilExp}
 | x=INT                                 	{$loc, IntExp x}
 | x=STR                                 	{$loc, StringExp x}
 | t=ID "[" n=exp "]" OF x=exp           	{$loc, ArrayExp (t, n, x)}
 | i=ID LBRACE e=record_exps RBRACE			{$loc, RecordExp (i, e)}
 | x=var                                 	{$loc, VarExp x}
 | x=var ":=" e=exp        					{$loc, AssignExp (x,e)}
 | f=ID "(" p=option_exps ")"				{$loc, CallExp (f, p)} 
 | x=exp o=binop y=exp                   	{$loc, OpExp (o, x, y)}
 | IF x=exp THEN y=exp	z=option_exp		{$loc, IfExp (x, y, z)}
 | WHILE x=exp DO y=exp					 	{$loc, WhileExp (x, y)}
 | FOR x=ID ASSIGN y=exp TO z=exp DO w=exp	{$loc, ForExp (x, y, z, w)}
 | BREAK									{$loc, BreakExp}
 | "(" es=exps ")"                       	{$loc, SeqExp es}
 | LET ds=decs IN es=exps END            	{$loc, LetExp (ds, ($loc(es), SeqExp es))}

%inline binop:
 | "+"                                   {PlusOp}
 | "-"                                   {MinusOp}
 | "*"                                   {TimesOp}
 | "/"                                   {DivideOp}
 | "="                                   {EqOp}
 | "<>"                                  {NeOp}
 | "<"                                   {LtOp}
 | ">"                                   {GtOp}
 | "<="                                  {LeOp}
 | ">="                                  {GeOp}
 | "&"                                   {AndOp}
 | "|"                                   {OrOp}


option_exp: (* else do IfThenElse *)
 | opt=option(e=exp ELSE {e})       {opt}

option_exps: (* parâmetros da chamada de função*)
 | opt=separated_list(",",e=exp {e})   {opt}


exps:
 | es=separated_list(";", exp)           {es}

record_exps: (* Para o RecordExp *)
 | l=separated_list(",", rec_exp) 		 {l}

rec_exp:
 | i=ID "=" e=exp 						 {($loc, (i, e))}

(*var = lvalue*)
var:
 | v=ID                                  {$loc, SimpleVar v}
 | v=var "." i=ID						 {$loc, FieldVar (v, i)}
 | v=var "[" e=exp "]"					 {$loc, SubscriptVar (v, e)}

decs:
 | ds=list(dec)                          {ds}

dec:
 | d=vardec                              {$loc, d}
 | d=list(functiondec)			 	     {$loc, MutualFunctionDecs d}
 | d=mutualtypedecs                      {$loc, d}

vardec:
 | VAR v=ID ":" t=type_constraint ":=" e=exp {VarDec (v, t, e)}

functiondec:
  | FUNCTION v=ID "(" t=tyfields ")" ret=type_constraint ASSIGN x=exp	{($loc, (v, t, ret, x))}
  (*type constraint é um símbolo NT opcional do retorno do tipo da função*)

mutualtypedecs:
 | ds=nonempty_list(typedec)             {MutualTypeDecs ds}

typedec:
 | TYPE t=ID "=" ty=ty                   {$loc, (t, ty)}

type_constraint:
 | c=option(":" t=ID {$loc(t), t})       {c}

ty:
 | ty=ID                                 {$loc, NameTy ty}
 | LBRACE t=tyfields RBRACE				 {$loc, RecordTy t}
 | ARRAY OF t=ID						 {$loc, ArrayTy ($loc(t), t)}

tyfields:
 | ls=separated_list(",", typefield)		{ls}

typefield:
 | campo=ID ":" tipo=ID   					{$loc, (campo, tipo)}
