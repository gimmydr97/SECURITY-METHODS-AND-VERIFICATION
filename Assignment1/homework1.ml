type permission = string list (* lista di permessi relativi ad una funzione*)

type expr =
  | CstI of int
  | CstB of bool
  | Var of string
  | Let of string * expr * expr
  | Prim of string * expr * expr
  | Read of string (*simulazione di lettura da un file*)
  | Write of string * string (*simulazione di scrittura di una stringa su di un file*)
  | If of expr * expr * expr
  | Fun of permission * string * expr 
  | Call of expr * expr



type 'v env = (string * 'v) list;;

type value =
  | Int of int
  | Closure of string * expr * value env 

type  stack = permission list;; (* costrutto che rappresenta una stack come lista di liste di permessi*)

let push stack (vall:permission) =match stack with (* f. a. che fa la push sullo stack di permessi *)
  |[] -> [vall]
  |x::xs -> vall::x::xs;;

(* f. a.che fa l'intersezione di due liste*)
let rec pairintersect l1 l2 = match l1 with [] -> [] 
                                          |h1::t1 -> (match l2 with [] -> [] 
                                                                  |h2::t2 when h1 < h2 -> pairintersect t1 l2
                                                                  |h2::t2 when h1 > h2 -> pairintersect l1 t2
                                                                  |h2::t2 -> (match pairintersect t1 t2 with [] -> [h1]
                                                                                                           | h3::t3 as l when h3 = h1 -> l
                                                                                                           | h3::t3 as l -> h1::l));;

(* f. a. che fa l'interseione delle liste sullo stack di permessi*)
let rec intersect stack = match stack with 
  |[]->[] 
  |l::[]->l     
  |l1::l2::ls-> intersect((pairintersect l1 l2)::ls);;

(*f. a. che controlla de un elemento appartiene ad una lista*)
let rec member lista element = match lista with 
  |[] -> false
  |x::xs -> if((compare x element) == 0) then true else member xs element;;

let rec lookup env x =
  match env with
  | [] -> failwith (x ^ " not found")
  | (y, v)::r -> if x=y then v else lookup r x;;


let rec eval (s:stack) (e : expr) (env : value env) : value =
  match e with
  | CstI i -> Int i
  | CstB b -> Int (if b then 1 else 0)
  | Var x -> lookup env x

  (*  casi in cui si valuta un expr di Read o Write 
  e quindi bisognerà effettuare i controlli dei permessi sull'interezione dello stack di permessi*)
  | Read file -> if ((member (intersect s) "read")==true) then Int(1) else failwith "permission denied" 
  | Write (file,e1) -> if ((member (intersect s) "write")==true) then Int(1) else failwith "permission denied"

  | Prim(ope, e1, e2) ->
      let v1 = eval s e1 env in
      let v2 = eval s e2 env in
      begin
        match (ope, v1, v2) with
        | ("*", Int i1, Int i2) -> Int (i1 * i2)
        | ("+", Int i1, Int i2) -> Int (i1 + i2)
        | ("-", Int i1, Int i2) -> Int (i1 - i2)
        | ("=", Int i1, Int i2) -> Int (if i1 = i2 then 1 else 0)
        | ("<", Int i1, Int i2) -> Int (if i1 < i2 then 1 else 0)
        | _ -> failwith "unknown primiRve or wrong type"
      end
  | Let(x, eRhs, letBody) ->
      begin
        match eRhs with 
        (* ogniqualvolta si fa il Let di una funzione si aggiorna lo stack 
        dei permessi con la lista dei permessi della funzione in questione *)
        |Fun(p,y,fbody)-> let newstack = push s p in 
            let xVal = eval newstack eRhs env in
            let letEnv = (x, xVal) :: env in eval newstack letBody letEnv

        |_-> let xVal = eval s eRhs env in
            let letEnv = (x, xVal) :: env in eval s letBody letEnv
      end
  |If(e1, e2, e3) ->
      begin
        match eval s e1 env with
        | Int 0 -> eval s e3 env
        | Int _ -> eval s e2 env 
        | _ -> failwith "eval If"
      end
  (* controllo preliminare sulla giusta apposizione dei permessi relativi ad una funzione *)
  | Fun(perm,x,fBody) -> 
      begin 
        match perm with
        |[] -> Closure(x, fBody, env)
        |["read";"write"] -> Closure(x, fBody, env)
        |["read"] ->Closure(x, fBody, env)
        |["write"] -> Closure(x, fBody, env)
        |_-> failwith "wrong sintax : on permission"
      end    
  | Call(eFun, eArg) ->
      let fClosure = eval s eFun env in
      begin
        match fClosure with
        | Closure (x, fBody, fDeclEnv) -> 
            let xVal = eval s eArg env in
            let fBodyEnv = (x, xVal) :: fDeclEnv
            in eval s fBody fBodyEnv
        | _ -> failwith "eval Call: not a function"
      end;;
(* caso di dichiarazione di funzione con errata apposizione dei permessi*)
let es0 = Let ("fun", Fun(["pippo"],"y", Prim("+",Var("y"), Var("y"))), Call(Var("fun"),CstI(2)));;

(* caso di chiamata a buon fine di una funzione con permessi*)
let es1 = Let ("fun", Fun(["read"], "x", Read("file")), Call(Var("fun"),CstI(2)));;

(* caso di chimata non andata a buon fine di una funzione con permessi *)
let es2 = Let ("fun", Fun(["write"], "x", Read("file")), Call(Var("fun"),CstI(2)));;

(* caso di chiamata di concatenazione di funzioni con permessi andata a buon fine *)
let es3 = Let ("f", Fun(["read";"write"],"y", Prim("*",Var("y"), Var("y"))), Let("g",Fun(["write"],"z", Write("file","ciao")), Call(Var("f"),Call(Var("g"),CstI(2)))));;

(* caso di chiamata di concatenazione di funzioni con permessi non andata a buon fine *)
let es4 = Let ("f", Fun(["read"],"y", Prim("*",Var("y"), Var("y"))), Let("g",Fun(["write"],"z", Write("file","ciao")), Call(Var("f"),Call(Var("g"),CstI(2)))));;


eval [] es0 [];;
(*
eval [] es1 [];;
eval [] es2 [];;
eval [] es3 [];;
eval [] es4 [];;
*)
