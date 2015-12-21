%{
open Modules
open Transformation_frm
open Except
%}

%token ERR
%token <int> AG
%token <string> PROP
%token NEG EVENT ALWAYS NEXT UNTIL
%token AND  OR  IMPLIES  EQUIV  RELEASE 
%token VIRG PVIRG
%token LPAR RPAR 
%token LANGLE RANGLE LCROC RCROC
%token EOF
%left UNTIL RELEASE
%right EQUIV
%left IMPLIES
%left OR
%left AND
%nonassoc LANGLE RANGLE LCROC RCROC
%nonassoc NEG
%nonassoc EVENT ALWAYS NEXT 
%start main
%type <Modules.State_Formulae.t> main
%%

main: 
	exprs EOF   { $1 }  
;

exprs: 
| state PVIRG exprs { State_Formulae.add (transform_fnn $1) $3 }
| state { State_Formulae.singleton (transform_fnn $1) }
;

state:
| PROP	{ Prop $1 }
| NEG state   { Neg $2 }
| LPAR state RPAR  { $2 } 
| state AND state  { And($1,$3) }
| state OR state   { Or($1,$3) }
| state IMPLIES state { Imply($1,$3) }
| state EQUIV state { Equiv($1,$3)  }
/* traitement des coalitions vides */ 
| LANGLE RANGLE LPAR path RPAR  { Coal(Agents.empty,$4) }
| LANGLE RANGLE path  { Coal(Agents.empty,$3) }
| LCROC RCROC LPAR path RPAR { CoCoal(Agents.empty,$4) }
| LCROC RCROC path  { CoCoal(Agents.empty,$3) }
/* -- */
| LANGLE agents RANGLE LPAR path RPAR { Coal($2,$5) } 
| LANGLE agents RANGLE path { Coal($2,$4) }
| LCROC agents RCROC LPAR path RPAR  { CoCoal($2,$5) }
| LCROC agents RCROC path  { CoCoal($2,$4) }
| error    { (Except.parse_error "state" ; Top)}
;

path:
| NEG path   {NegP $2 }
| ALWAYS path { Always $2 }
| NEXT path { Next $2 }
| EVENT path { Event $2 }
| path UNTIL path { Until($1,$3) }
| LPAR path RPAR  { $2 }
| path AND path  { AndP($1,$3) }
| path OR path   { OrP($1,$3) }
| path IMPLIES path { ImplyP($1,$3) }
| path EQUIV path { EquivP($1,$3)  }
| path RELEASE path { Release($1,$3) }
| PROP	{State( Prop $1 )}
/* traitement des coalitions vides */ 
| LANGLE RANGLE LPAR path RPAR  { State(Coal(Agents.empty,$4) )}
| LANGLE RANGLE path  {State( Coal(Agents.empty,$3) )}
| LCROC RCROC LPAR path RPAR { State (CoCoal(Agents.empty,$4)) }
| LCROC RCROC path  { State (CoCoal(Agents.empty,$3)) }
/* -- */
| LANGLE agents RANGLE LPAR path RPAR { State (Coal($2,$5)) } 
| LANGLE agents RANGLE path { State (Coal($2,$4)) }
| LCROC agents RCROC LPAR path RPAR  { State (CoCoal($2,$5)) }
| LCROC agents RCROC path  { State (CoCoal($2,$4)) }
| error    { (Except.parse_error "path" ; State(Top)) }
;


agents:
| agent VIRG agents { Agents.add $1 $3 }
| agent	{ Agents.singleton $1 }
| error    { parse_error "agents"; Agents.empty }
;

agent:
| AG { $1 }
| error    { parse_error "agent"; 0  }
;
