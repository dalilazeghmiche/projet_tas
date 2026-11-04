


(* Termes *)
type pterm = Var of string | App of pterm * pterm | Abs of string * pterm | N of int | Add of pterm * pterm 
  | Sub of pterm * pterm                  (* soustraction *)
  | Nil                                   (* liste vide [] *)
  | Cons of pterm * pterm                 (* cons e l : ajoute e en tête de l *)
  | Hd of pterm                           (* tête d'une liste *)
  | Tl of pterm                           (* queue d'une liste *)
  | IfZero of pterm * pterm * pterm       (* ifzero c then a else b *)
  | IfEmpty of pterm * pterm * pterm      (* ifempty c then a else b *)
  | Fix of pterm                          (* fix (fun phi -> M) *)
  | Let of string * pterm * pterm         (* let x = e1 in e2 *)
  (* partie 4 : traits impératifs *)
  | Unit                                  (* la valeur unit () *)
  | Region of int                         (* une région (case mémoire) rho_n *)
  | Ref of pterm                          (* ref e : création de région *)
  | Deref of pterm                        (* !e : déréférencement *)
  | Assign of pterm * pterm               (* e1 := e2 : assignement *)
(* Types *) 
type ptype = Var of string | Arr of ptype * ptype | Nat
  | Liste of ptype                 (* [T] *)
  | Forall of string list * ptype  (* forall X1 … Xk. T *) 
  (* partie 4 *)
  | TUnit                                 (* le type unit *)
  | TRef of ptype                         (* Ref T : région contenant des valeurs de type T *)
  | Weak of string list * ptype           (* weak X1 ... Xk. T  (polymorphisme faible) *)
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
    | Sub (t1, t2) -> "(" ^ (print_term t1) ^ " - " ^ (print_term t2) ^ ")"
    | Nil -> "[]"
    | Cons (t1, t2) -> "(" ^ (print_term t1) ^ " :: " ^ (print_term t2) ^ ")"
    | Hd t -> "(hd " ^ (print_term t) ^ ")"
    | Tl t -> "(tl " ^ (print_term t) ^ ")"
    | IfZero (c, a, b) -> "(ifzero " ^ (print_term c) ^ " then " ^ (print_term a)
                        ^ " else " ^ (print_term b) ^ ")"
    | IfEmpty (c, a, b) -> "(ifempty " ^ (print_term c) ^ " then " ^ (print_term a)
                         ^ " else " ^ (print_term b) ^ ")"
    | Fix t -> "(fix " ^ (print_term t) ^ ")"
    | Let (x, e1, e2) -> "(let " ^ x ^ " = " ^ (print_term e1) ^ " in " ^ (print_term e2) ^ ")"
    | Unit -> "()"
    | Region n -> "rho" ^ (string_of_int n)
    | Ref t -> "(ref " ^ (print_term t) ^ ")"
    | Deref t -> "!" ^ (print_term t)
    | Assign (t1, t2) -> "(" ^ (print_term t1) ^ " := " ^ (print_term t2) ^ ")"

(* pretty printer de types*)                    
let rec print_type (t : ptype) : string =
  match t with
    Var x -> x
  | Arr (t1, t2) -> "(" ^ (print_type t1) ^" -> "^ (print_type t2) ^")"
  | Nat -> "Nat" 
  | Liste t -> "[" ^ (print_type t) ^ "]"
  | Forall (vs, t) -> "(forall " ^ (String.concat " " vs) ^ ". " ^ (print_type t) ^ ")"
  | TUnit -> "Unit"
  | TRef t -> "(Ref " ^ (print_type t) ^ ")"
  | Weak (vs, t) -> "(weak " ^ (String.concat " " vs) ^ ". " ^ (print_type t) ^ ")"
