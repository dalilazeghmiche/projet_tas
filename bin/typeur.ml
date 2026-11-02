open Syntaxe



(* générateur de noms frais de variables de types *)
let compteur_var : int ref = ref 0                    

let nouvelle_var () : string = compteur_var := !compteur_var + 1; 
  "T"^(string_of_int !compteur_var)


exception VarPasTrouve
exception Echec_unif of string

 
(* nombre maximum d'étapes d'unification (timeout) *)
let fuel_defaut : int = 10000
 
(* cherche le type d'une variable dans un environnement *)
let rec cherche_type (v : string) (e : env) : ptype =
  match e with
  | [] -> raise VarPasTrouve
  | (v1, t1) :: _ when v1 = v -> t1
  | _ :: q -> cherche_type v q
 
(* ---------- opérations sur les types ---------- *)
 
(* vérificateur d'occurence : la variable v apparaît-elle (libre) dans t ? *)
let rec appartient_type (v : string) (t : ptype) : bool =
  match t with
  | Var v1 -> v1 = v
  | Arr (t1, t2) -> (appartient_type v t1) || (appartient_type v t2)
  | Nat -> false
  | Liste t1 -> appartient_type v t1
  | Forall (vs, t1) -> not (List.mem v vs) && appartient_type v t1
 
(* remplace la variable v par le type t0 dans le type t *)
let rec substitue_type (t : ptype) (v : string) (t0 : ptype) : ptype =
  match t with
  | Var v1 -> if v1 = v then t0 else Var v1
  | Arr (t1, t2) -> Arr (substitue_type t1 v t0, substitue_type t2 v t0)
  | Nat -> Nat
  | Liste t1 -> Liste (substitue_type t1 v t0)
  | Forall (vs, t1) -> if List.mem v vs then Forall (vs, t1)   (* v est liée ici *)
                       else Forall (vs, substitue_type t1 v t0)
 
(* remplace la variable v par le type t0 dans une liste d'équations *)
let substitue_type_partout (e : equa) (v : string) (t0 : ptype) : equa =
  List.map (fun (x, y) -> (substitue_type x v t0, substitue_type y v t0)) e
 
(* variables de type libres d'un type (sans doublons) *)
let rec variables_type (t : ptype) : string list =
  match t with
  | Var v -> [v]
  | Arr (t1, t2) -> List.sort_uniq compare ((variables_type t1) @ (variables_type t2))
  | Nat -> []
  | Liste t1 -> variables_type t1
  | Forall (vs, t1) -> List.filter (fun v -> not (List.mem v vs)) (variables_type t1)
 
(* "barendregtisation" et ouverture d'un forall :
   forall X1..Xk. T  devient  T où chaque Xi est remplacé par une variable fraîche *)
let ouvre (vs : string list) (t : ptype) : ptype =
  List.fold_left (fun acc v -> substitue_type acc v (Var (nouvelle_var ()))) t vs
 
(* ---------- substitutions ---------- *)
 
(* une substitution associe des variables de type à des types :
   c'est la solution d'un système d'équations *)
type substitution = (string * ptype) list
 
(* applique une substitution à un type *)
let applique_subst (s : substitution) (t : ptype) : ptype =
  List.fold_left (fun acc (v, tv) -> substitue_type acc v tv) t s
 
(* ---------- unification ---------- *)
 
(* résout un système d'équations ; renvoie la substitution solution
   s    : substitution déjà trouvée
   fuel : nombre maximum d'étapes (timeout) *)
let rec unifie (eqs : equa) (s : substitution) (fuel : int) : substitution =
  if fuel <= 0 then raise (Echec_unif "timeout de l'unification") else
  match eqs with
  (* plus d'équations : succès *)
  | [] -> s
  (* deux types égaux : on supprime l'équation *)
  | (t1, t2) :: reste when t1 = t2 -> unifie reste s (fuel - 1)
  (* un forall : on le renomme (barendregtisation) puis on l'ouvre *)
  | (Forall (vs, t1), t2) :: reste -> unifie ((ouvre vs t1, t2) :: reste) s (fuel - 1)
  | (t1, Forall (vs, t2)) :: reste -> unifie ((t1, ouvre vs t2) :: reste) s (fuel - 1)
  (* une variable d'un côté : occur check, puis on remplace la variable partout *)
  | (Var x, t) :: reste | (t, Var x) :: reste ->
      if appartient_type x t then
        raise (Echec_unif ("occurence de " ^ x ^ " dans " ^ (print_type t)))
      else
        let s' = (x, t) :: List.map (fun (y, ty) -> (y, substitue_type ty x t)) s in
        unifie (substitue_type_partout reste x t) s' (fuel - 1)
  (* deux flèches : on décompose *)
  | (Arr (t1, t2), Arr (t3, t4)) :: reste -> unifie ((t1, t3) :: (t2, t4) :: reste) s (fuel - 1)
  (* deux listes : on égalise le type des éléments *)
  | (Liste t1, Liste t2) :: reste -> unifie ((t1, t2) :: reste) s (fuel - 1)
  (* constructeurs différents : échec *)
  | (t1, t2) :: _ ->
      raise (Echec_unif ("type " ^ (print_type t1) ^ " non-unifiable avec " ^ (print_type t2)))
 
(* ---------- généralisation ---------- *)
 
(* variables de type libres d'un environnement *)
let variables_env (e : env) : string list =
  List.concat_map (fun (_, t) -> variables_type t) e
 
(* généralise t : ajoute un forall pour chaque variable libre de t
   qui n'apparaît pas dans l'environnement e *)
let generalise (t : ptype) (e : env) : ptype =
  let libres_env = variables_env e in
  let vs = List.filter (fun v -> not (List.mem v libres_env)) (variables_type t) in
  if vs = [] then t else Forall (vs, t)
 
(* ---------- génération d'équations ---------- *)
 
(* génère les équations qui disent que le terme te a le type ty dans l'environnement e *)
let rec genere_equa (te : pterm) (ty : ptype) (e : env) : equa =
  match te with
  (* ----- partie 2 ----- *)
  | Var v -> [(ty, cherche_type v e)]
  | App (t1, t2) ->
      let ta = Var (nouvelle_var ()) in
      (genere_equa t1 (Arr (ta, ty)) e) @ (genere_equa t2 ta e)
  | Abs (x, t) ->
      let ta = Var (nouvelle_var ()) and tr = Var (nouvelle_var ()) in
      (ty, Arr (ta, tr)) :: (genere_equa t tr ((x, ta) :: e))
  | N _ -> [(ty, Nat)]
  (* ----- partie 3 : entiers ----- *)
  | Add (t1, t2) | Sub (t1, t2) ->
      (* + et - : Nat -> Nat -> Nat *)
      (ty, Nat) :: ((genere_equa t1 Nat e) @ (genere_equa t2 Nat e))
  (* ----- partie 3 : listes ----- *)
  | Nil ->
      (* [] : [X] pour un X frais *)
      [(ty, Liste (Var (nouvelle_var ())))]
  | Cons (t1, t2) ->
      (* cons : X -> [X] -> [X] *)
      let x = Var (nouvelle_var ()) in
      (ty, Liste x) :: ((genere_equa t1 x e) @ (genere_equa t2 (Liste x) e))
  | Hd t1 ->
      (* hd : [X] -> X *)
      let x = Var (nouvelle_var ()) in
      (ty, x) :: (genere_equa t1 (Liste x) e)
  | Tl t1 ->
      (* tl : [X] -> [X] *)
      let x = Var (nouvelle_var ()) in
      (ty, Liste x) :: (genere_equa t1 (Liste x) e)
  (* ----- partie 3 : branchements ----- *)
  | IfZero (c, a, b) ->
      (* la condition est un entier, les deux branches ont le type cible *)
      (genere_equa c Nat e) @ (genere_equa a ty e) @ (genere_equa b ty e)
  | IfEmpty (c, a, b) ->
      (* la condition est une liste, les deux branches ont le type cible *)
      let x = Var (nouvelle_var ()) in
      (genere_equa c (Liste x) e) @ (genere_equa a ty e) @ (genere_equa b ty e)
  (* ----- partie 3 : point fixe ----- *)
    | Fix t1 ->
      (* règle (Fix) du cours : fix (fun phi -> M) : T -> U
         le type est forcément un type fonctionnel, et M : (T -> U) -> (T -> U) *)
      let ta = Var (nouvelle_var ()) and tr = Var (nouvelle_var ()) in
      (ty, Arr (ta, tr)) :: (genere_equa t1 (Arr (ty, ty)) e)
  (* ----- partie 3 : let polymorphe ----- *)
  | Let (x, e1, e2) ->
      (* 1. on type e1 : équations + unification *)
      let t0 = Var (nouvelle_var ()) in
      let eq1 = genere_equa e1 t0 e in
      let s = unifie eq1 [] fuel_defaut in
      let t0' = applique_subst s t0 in
      (* 2. on généralise son type (on applique d'abord la solution à l'environnement) *)
      let e' = List.map (fun (y, t) -> (y, applique_subst s t)) e in
      let sigma = generalise t0' e' in
      (* 3. on type e2 avec x : sigma ; on garde eq1 pour ne pas perdre
            les contraintes que e1 impose aux variables de l'environnement *)
      eq1 @ (genere_equa e2 ty ((x, sigma) :: e))
 
(* ---------- inférence ---------- *)
 
(* variables d'un type dans leur ordre d'apparition (sans doublons) *)
let variables_ordre (t : ptype) : string list =
  let rec parcours (t : ptype) (vu : string list) : string list =
    match t with
    | Var v -> if List.mem v vu then vu else vu @ [v]
    | Arr (t1, t2) -> parcours t2 (parcours t1 vu)
    | Nat -> vu
    | Liste t1 -> parcours t1 vu
    | Forall (_, t1) -> parcours t1 vu
  in parcours t []
 
(* renomme les variables d'un type en a, b, c... pour un affichage lisible *)
let renomme_lisible (t : ptype) : ptype =
  let vs = variables_ordre t in
  let lettres = List.mapi (fun i v -> (v, Var (String.make 1 (Char.chr (97 + (i mod 26)))))) vs in
  applique_subst lettres t
 
(* infère le type d'un terme (lève Echec_unif ou VarPasTrouve en cas d'échec) *)
let typeur (t : pterm) (fuel : int) : ptype =
  let but = Var (nouvelle_var ()) in
  let s = unifie (genere_equa t but []) [] fuel in
  applique_subst s but
 
(* enchaîne génération d'équations et unification, avec un timeout *)
let inference_fuel (t : pterm) (fuel : int) : string =
  try
    let res = typeur t fuel in
    (print_term t) ^ " ***TYPABLE*** avec le type " ^ (print_type (renomme_lisible res))
  with
  | Echec_unif bla -> (print_term t) ^ " ***PAS TYPABLE*** : " ^ bla
  | VarPasTrouve -> (print_term t) ^ " ***PAS TYPABLE*** : variable libre (non liee)"
 
(* inférence avec le timeout par défaut *)
let inference (t : pterm) : string = inference_fuel t fuel_defaut


(* renvoie le type d'un terme sous forme de chaîne, ou "PAS TYPABLE"
   (utilisée par les tests automatiques) *)
let type_de (t : pterm) : string =
  try print_type (renomme_lisible (typeur t fuel_defaut))
  with Echec_unif _ | VarPasTrouve -> "PAS TYPABLE"
 