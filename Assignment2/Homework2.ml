
(*Definition of dfa and all it ausiliarity functions*)
type state = int
type symbol = char
type transition = int * symbol * int 

type	dfa	=		
		{	states	:	state	list;	
      sigma	:	symbol	list;	
      start	:	state;	
      transitions	:	transition	list;	
      accepting	:	state	list;
    }	

let	states	(dfa	:	dfa)	=	dfa.states;;

let	explode	s	=	
  let	rec	expl i	l	=	
				if	i	<	0	then	l	else	
						expl	(i	-	1)	(s.[i]	::	l)	in		(*	s.[i]	returns	the	ith	element	of	s	as	a	char	*)	
  expl	(String.length	s	-	1)	[];;	(*	String.length	s	returns	the	length	of	s						*)	
                                  
let	rec	contains	e	l	=		
		match	l	with	
		|	[]	->	false	
		|	hd::tl	->	if	hd	=	e	then	true	else	contains	e	tl;;

let checkAccepts str dfa =
    (* Get the list of symbols. *)
  let symbols = explode str in
        (* If I'm at state {state}, where do I go on {symbol}? *)
  let transition state symbol =
    let rec find_state l = match l with
      | (s1,sym,s2)::tl -> if (s1 = state && symbol = sym) then s2 
          else find_state tl
      | _ -> failwith "no next state" 
    in find_state dfa.transitions in
  let final_state = let rec h symbol_list = match symbol_list with
      | [hd] -> (transition dfa.start hd)
      | hd::tl -> (transition (h tl) hd)
      | _ -> failwith "empty list of symbols"
    in h (List.rev symbols) in 
  if (contains final_state dfa.accepting) then true
  else false;;


(*Policy not read after write*)
let	phi_not_r_after_w	:	dfa	=		
  {	 
    states	=	[0;1;2];	
    sigma	=	['r';'w';'c'];	
    start	=	0;	
    transitions	=	
      [(0,'r',0);(0,'w',1);(0,'c',0);	
       (1,'r',2);(1,'w',1);(1,'c',1);
       (2,'r',2);(2,'w',2);(1,'c',2)];	
    accepting	=	[0;1]	
  };;


(*Definition not write*)
let phi_not_write : dfa =
  {
    states	=	[0;1];	
    sigma	=	['r';'w';'c'];	
    start	=	0;	
    transitions	=	
      [(0,'r',0);(0,'w',1);(0,'c',0);	
       (1,'r',1);(1,'w',1);(1,'c',1)];	
    accepting	=	[0]	
  }
  
(*Definition not Connect*)
let phi_not_connect : dfa =
  {
    states	=	[0;1];	
    sigma	=	['r';'w';'c'];	
    start	=	0;	
    transitions	=	
      [(0,'r',0);(0,'w',0);(0,'c',1);	
       (1,'r',1);(1,'w',1);(1,'c',1)];	
    accepting	=	[0]	
  }



(*push sullo stack*)
let push stack vall =match stack with 
  |[] -> [vall]
  |x::xs -> vall::x::xs;;

(*top stack*)
let top stack = match stack with 
    [x] ->  x 
  |x::xs -> x
  |_-> failwith "the stack is empty";;

(*function isnotempty stack*)
let isnotempty stack = match stack with 
    [] -> false
  |_-> true ;;





(*Definition of the language and eval *)

type expr =
  | CstI of int
  | CstB of bool
  | Var of string
  | Let of string * expr * expr
  | Prim of string * expr * expr
  | If of expr * expr * expr
  | Fun of string * expr 
  | Call of expr * expr
  | Letrec of string * expr * expr
  | Read of string
  | Write of string *expr
  | Connect of string
  | Policy of dfa * expr


type 'v env = (string * 'v) list;;


let rec lookup env x =
  match env with
  | [] -> failwith (x ^ " not found")
  | (y, v)::r -> if x=y then v else lookup r x;;


type value =
  | Int of int
  | Closure of string * expr * value env
  | RecClosure of string * string * expr * value env
                    

let rec  eval st  (eta:string) (e : expr) (env : value env) : value*string =
  match e with
  | CstI i -> (Int i,eta)
  | CstB b -> (Int (if b then 1 else 0),eta)
  | Var x -> (lookup env x, eta)
  | Read s -> let eta1 = eta^"r" in  if((isnotempty st)) then let flag = checkAccepts eta1 (top st) in begin match flag with 
      | true -> (Int 1, eta1)
      | false ->  failwith "the history does not respect the policy"
    end
    else  (*altrimenti ritorno solo il valore*) (Int 1,eta1)

  | Write (s,s1) -> let eta1 = eta^"w" in  if((isnotempty st)) then let flag = checkAccepts eta1 (top st) in begin match flag with 
      | true -> (Int 2, eta1)
      | false ->  failwith "the history does not respect the policy"
    end
    else  (*altrimenti ritorno solo il valore*) (Int 2,eta1)
  | Connect s -> let eta1 = eta^"c" in  if((isnotempty st)) then let flag = checkAccepts eta1 (top st) in begin match flag with 
      | true -> (Int 3, eta1)
      | false -> failwith "the history does not respect the policy"
    end
    else  (*altrimenti ritorno solo il valore*) (Int 3,eta1)

  | Policy(dfa, e1 )->  let s1 = push st dfa in let (v1,eta1) = eval s1 eta e1 env in let flag1 = checkAccepts eta1 (top s1) in begin match flag1 with
      |true ->  (v1,eta1)
      |false -> failwith "the history does not respect the policy"
    end
  | Prim(ope, e1, e2) -> 
      let (v1, eta) = eval st eta e1 env  in
      let (v2, eta) = eval st eta e2 env  in
      begin
        match (ope, v1, v2) with 
        | ("*", Int i1, Int i2) -> (Int (i1 * i2),eta)
        | ("+", Int i1, Int i2) -> (Int (i1 + i2),eta)
        | ("-", Int i1, Int i2) -> (Int (i1 - i2),eta)
        | ("=", Int i1, Int i2) -> (Int (if i1 = i2 then 1 else 0),eta)
        | ("<", Int i1, Int i2) -> (Int (if i1 < i2 then 1 else 0),eta)
        | _ -> failwith "unknown primiRve or wrong type"
      end
  | Let(x, eRhs, letBody) ->
      let (xVal,eta') = eval st eta eRhs env in
      let letEnv = (x, xVal) :: env in eval st eta' letBody letEnv
  |If(e1, e2, e3) ->
      begin
        match eval st eta e1 env with
        | (Int 0,eta') -> eval st eta' e3 env
        | (Int _,eta') -> eval st eta' e2 env
        | _ -> failwith "eval st eta If"
      end
  | Fun(x,fBody) -> (Closure(x, fBody, env),eta) 
  | Call(eFun, eArg) ->
      let (fClosure,_) = eval st eta eFun env in
      begin
        match fClosure with
        | Closure (x, fBody, fDeclEnv) ->
            let (xVal,eta') = eval st eta eArg env in
            let fBodyEnv = (x, xVal) :: fDeclEnv
            in eval st eta' fBody fBodyEnv
        |RecClosure (g,arg,fBody,fDecenv)->
            let (xVal,eta') = eval st eta eArg env in 
            let rEnv =  (g,fClosure)::fDecenv in
            let aEnv = (arg,xVal)::rEnv in 
            eval st eta' fBody aEnv

        | _ -> failwith "eval st eta Call: not a function"
      end
  | Letrec(f, funDef, letBody) ->
      match funDef with
      |Fun(i, fBody) -> let env1 = (f,(RecClosure(f, i, fBody, env)))::env in
          eval st eta letBody env1 
      | _ -> failwith("non functional def");;



(*------------------Albero di sintassi astratta-----------------*)


(*Factorial function !n: testing the recursion *)
let e3 = Letrec(
    "fact", 
    Fun("y", If( Prim("=", Var("y"), CstI(0)), CstI(1),  Prim("*",Var("y"),Call(Var("fact"), Prim("-", Var("y"), CstI(1)))))),
    Call(Var("fact"),CstI(10)));;


(*Read after write without the policy*)
let e4 = Let("x", Write("C:file.txt", CstI(1)), Read("C:newfile.txt"));;


(*Recursion with R/W Access*)
let e5 = Letrec(
    "readn", 
    Fun("y", If( Prim("=", Var("y"), CstI(0)), CstI(1),  Prim("*", Let("x", Write("C:file.txt", CstI(1)), Read("C:newfile.txt")),Call(Var("readn"), Prim("-", Var("y"), CstI(1)))))),
    Call(Var("readn"),CstI(5)));;

(*This history doesn't respect*)
let e6 = Let("x", Write("C:/home/alessandro/file.txt",CstI(1)), Let("y", Read("ciao"), Policy(phi_not_r_after_w, Read("ciao"))) );;

(*This history respect*)
let e7 = Let("x", Read("C:/home/alessandro/file.txt"), Let("y", Write("ciao", CstI(1)), Policy(phi_not_r_after_w, Write("ciao",CstI(1)))));;

(*Policy inside the policy| all the access are done*) 
let e8 = Let ("x", Write("C:/home",CstI(256)), Policy(phi_not_r_after_w, Let("z", Policy(phi_not_connect, CstI(4)), Policy(phi_not_r_after_w, Connect("C")) )));;


eval [] "" e8 [];;