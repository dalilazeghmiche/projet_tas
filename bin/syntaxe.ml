


(* Termes *)
type pterm = Var of string | App of pterm * pterm | Abs of string * pterm | N of int | Add of pterm * pterm 
(* Types *) 
type ptype = Var of string | Arr of ptype * ptype | Nat 
(* Environnements de typage *) 
type env = (string * ptype) list 
(* Listes d'équations *) 
type equa = (ptype * ptype) list
(* pretty printer de termes*)     
let rec print_term (t : pterm) : string =
  match t with
    Var x -> x
    | App (t1, t2) -> "(" ^ (print_term t1) ^" "^ (print_term t2) ^ ")"
    | Abs (x, t) -> "(fun "^ x ^" -> " ^ (print_term t) ^")" 
    | N n -> string_of_int n
    | Add (t1, t2) -> "(" ^ (print_term t1) ^" + "^ (print_term t2) ^ ")"
(* pretty printer de types*)                    
let rec print_type (t : ptype) : string =
  match t with
    Var x -> x
  | Arr (t1, t2) -> "(" ^ (print_type t1) ^" -> "^ (print_type t2) ^")"
  | Nat -> "Nat" 
