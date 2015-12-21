{
  open Parser_formula  	(* the type token is defined in parser.mli *)
  exception Error
}


	let chiffre = ['0'-'9']+
	let alpha = ['a'-'z']['a'-'z''0'-'9']*
	let space = [' ''\n''\t']

rule token = parse
| ';'             {PVIRG}
| '(' 						{LPAR}
| ')' 						{RPAR}
| "<<" 						{LANGLE}
| ">>" 						{RANGLE}
| "[["            {LCROC}
| "]]"            {RCROC}
| '~' 						{NEG}
| "/\\" 					{AND}
| "&&" 					  {AND}
| "\\/" 					{OR}
| "||" 					  {OR}
| "->" 						{IMPLIES}
| "<->"           {EQUIV}
| 'F'  						{EVENT} 
| 'G'	 					  {ALWAYS}
| 'X'  						{NEXT}
| 'U'  						{UNTIL}
| 'R'             {RELEASE}
| ','  						{VIRG}  (* ou skip? *)
| chiffre as lxm  {AG (int_of_string lxm)}
| alpha as lxm 		{PROP lxm}
| eof  						{EOF}
| space  				  {token lexbuf}
| ""  						{raise Error}
