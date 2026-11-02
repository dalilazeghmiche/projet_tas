open Syntaxe


(*=========== PARTIE 2.2 ET 3.2: SEMANTIQUE ===================*)

(* générateur de noms frais pour les variables de termes *)

let compteur_var_t : int ref = ref 0
let nouvelle_var_t () : string = 
  compteur_var_t := !compteur_var_t +1;
  "_x" ^ (string_of_int !compteur_var_t)

(* renvoie la liste des variables libres d'un terme *)
let rec variables_libres (t : pterm) : string list =
  match t with
  | Var x -> [x]
  | Abs (x, m) -> List.filter (fun y -> y <> x) (variables_libres m)
  | App (m, n) | Add (m, n) | Sub (m, n) | Cons (m, n) ->
      (variables_libres m) @ (variables_libres n)
  | N _ | Nil -> []
  | Hd m | Tl m | Fix m -> variables_libres m
  | IfZero (c, a, b) | IfEmpty (c, a, b) ->
      (variables_libres c) @ (variables_libres a) @ (variables_libres b)
  | Let (x, e1, e2) ->
      (* x est liée dans e2, mais pas dans e1 *)
      (variables_libres e1) @ (List.filter (fun y -> y <> x) (variables_libres e2))


(* tire un nom frais, et recommence tant que le nom fait partie de la liste interdite *)
let rec nom_frais (interdits : string list) : string =
  let v = nouvelle_var_t () in
  if List.mem v interdits then nom_frais interdits else v

  (* alpha-conversion qui évite les noms de la liste interdits
   rn : liste (ancien nom, nouveau nom) des variables liées au-dessus *)
let rec alphaconv_evite (t : pterm) (rn : (string * string) list) (interdits : string list) : pterm =
  let ac (u : pterm) : pterm = alphaconv_evite u rn interdits in
  match t with
  | Var x -> (match List.assoc_opt x rn with
              | Some x' -> Var x'
              | None -> Var x)
  | Abs (x, m) -> let x' = nom_frais interdits in
                  Abs (x', alphaconv_evite m ((x, x') :: rn) interdits)
  | App (m, n) -> App (ac m, ac n)
  | N k -> N k
  | Add (m, n) -> Add (ac m, ac n)
  | Sub (m, n) -> Sub (ac m, ac n)
  | Nil -> Nil
  | Cons (m, n) -> Cons (ac m, ac n)
  | Hd m -> Hd (ac m)
  | Tl m -> Tl (ac m)
  | IfZero (c, a, b) -> IfZero (ac c, ac a, ac b)
  | IfEmpty (c, a, b) -> IfEmpty (ac c, ac a, ac b)
  | Fix m -> Fix (ac m)
  | Let (x, e1, e2) ->
      (* e1 est hors de la portée de x ; x est renommé dans e2 *)
      let x' = nom_frais interdits in
      Let (x', ac e1, alphaconv_evite e2 ((x, x') :: rn) interdits)
 
(* alpha-conversion (convention de Barendregt) : les variables liées
   deviennent fraîches, distinctes entre elles ET des variables libres de t *)
let alphaconv (t : pterm) (rn : (string * string) list) : pterm =
  alphaconv_evite t rn (variables_libres t)
                  


(* substitution : remplace la variable x par le terme n dans le terme m
   (calcule m[n/x]) *)
let rec substitution (x : string) (n : pterm) (m : pterm) : pterm =
  let sub = substitution x n in
  match m with
  | Var y -> if y = x then n else Var y
  | Abs (y, corps) -> if y = x then Abs (y, corps)
                      else Abs (y, sub corps)
  | App (m1, m2) -> App (sub m1, sub m2)
  | N k -> N k
  | Add (m1, m2) -> Add (sub m1, sub m2)
  | Sub (m1, m2) -> Sub (sub m1, sub m2)
  | Nil -> Nil
  | Cons (m1, m2) -> Cons (sub m1, sub m2)
  | Hd m1 -> Hd (sub m1)
  | Tl m1 -> Tl (sub m1)
  | IfZero (c, a, b) -> IfZero (sub c, sub a, sub b)
  | IfEmpty (c, a, b) -> IfEmpty (sub c, sub a, sub b)
  | Fix m1 -> Fix (sub m1)
  | Let (y, e1, e2) -> if y = x then Let (y, sub e1, e2)     (* x masqué dans e2 *)
                       else Let (y, sub e1, sub e2)

  (* remplace x par v dans corps, sans capture :
   on renomme d'abord les variables liées de corps en évitant
   les variables libres de v et celles de corps *)
let substitue_sans_capture (x : string) (v : pterm) (corps : pterm) : pterm =
  substitution x v (alphaconv_evite corps [] ((variables_libres v) @ (variables_libres corps)))



  (* est_valeur : un terme est une valeur s'il a fini de calculer *)
let rec est_valeur (t : pterm) : bool =
  match t with
  | Abs (_, _) -> true
  | N _ -> true
  | Var _ -> true
  | Nil -> true
  | Cons (v1, v2) -> est_valeur v1 && est_valeur v2   (* liste de valeurs *)
  | _ -> false

(* une étape de réduction Left-to-Right Call-by-Value
   renvoie Some t' si t se réduit en t', None si aucune réduction possible *)
let rec ltr_cbv_step (t : pterm) : pterm option =
  match t with
  (* ---------- partie 2 ---------- *)
  | App (m, n) ->
      if not (est_valeur m) then
        (match ltr_cbv_step m with Some m' -> Some (App (m', n)) | None -> None)
      else if not (est_valeur n) then
        (match ltr_cbv_step n with Some n' -> Some (App (m, n')) | None -> None)
      else
        (match m with
         | Abs (x, corps) -> Some (substitue_sans_capture x n corps)   (* règle β *)
         | _ -> None)
  | Add (m, n) ->
      if not (est_valeur m) then
        (match ltr_cbv_step m with Some m' -> Some (Add (m', n)) | None -> None)
      else if not (est_valeur n) then
        (match ltr_cbv_step n with Some n' -> Some (Add (m, n')) | None -> None)
      else
        (match (m, n) with (N a, N b) -> Some (N (a + b)) | _ -> None)
  (* ---------- partie 3 : soustraction ---------- *)
  | Sub (m, n) ->
      if not (est_valeur m) then
        (match ltr_cbv_step m with Some m' -> Some (Sub (m', n)) | None -> None)
      else if not (est_valeur n) then
        (match ltr_cbv_step n with Some n' -> Some (Sub (m, n')) | None -> None)
      else
                   (* entiers naturels : la soustraction est bornée à 0 *)
           (match (m, n) with (N a, N b) -> Some (N (max 0 (a - b))) | _ -> None)
  (* ---------- partie 3 : listes ---------- *)
  | Cons (m, n) ->
      (* on évalue la tête, puis la queue *)
      if not (est_valeur m) then
        (match ltr_cbv_step m with Some m' -> Some (Cons (m', n)) | None -> None)
      else if not (est_valeur n) then
        (match ltr_cbv_step n with Some n' -> Some (Cons (m, n')) | None -> None)
      else None   (* Cons de deux valeurs : c'est une valeur *)
  | Hd m ->
      if not (est_valeur m) then
        (match ltr_cbv_step m with Some m' -> Some (Hd m') | None -> None)
      else
        (match m with
         | Cons (v, _) -> Some v
         | _ -> None)          (* hd [] : bloqué *)
  | Tl m ->
      if not (est_valeur m) then
        (match ltr_cbv_step m with Some m' -> Some (Tl m') | None -> None)
      else
        (match m with
         | Cons (_, l) -> Some l
         | _ -> None)          (* tl [] : bloqué *)
  (* ---------- partie 3 : branchements ---------- *)
  | IfZero (c, a, b) ->
      (* on évalue SEULEMENT la condition, puis on choisit UNE branche *)
      if not (est_valeur c) then
        (match ltr_cbv_step c with Some c' -> Some (IfZero (c', a, b)) | None -> None)
      else
        (match c with
         | N 0 -> Some a
         | N _ -> Some b
         | _ -> None)
  | IfEmpty (c, a, b) ->
      if not (est_valeur c) then
        (match ltr_cbv_step c with Some c' -> Some (IfEmpty (c', a, b)) | None -> None)
      else
        (match c with
         | Nil -> Some a
         | Cons (_, _) -> Some b
         | _ -> None)
  (* ---------- partie 3 : point fixe ---------- *)
  | Fix m ->
      if not (est_valeur m) then
        (match ltr_cbv_step m with Some m' -> Some (Fix m') | None -> None)
      else
        (match m with
         (* fix (phi -> M)  -->  M [ fix (phi -> M) / phi ] *)
         | Abs (phi, corps) -> Some (substitue_sans_capture phi (Fix m) corps)
         | _ -> None)
  (* ---------- partie 3 : let ---------- *)
  | Let (x, e1, e2) ->
      (* on évalue e1 en une valeur v, puis on remplace x par v dans e2 *)
      if not (est_valeur e1) then
        (match ltr_cbv_step e1 with Some e1' -> Some (Let (x, e1', e2)) | None -> None)
      else Some (substitue_sans_capture x e1 e2)
  (* ---------- valeurs : rien à réduire ---------- *)
  | Var _ | Abs (_, _) | N _ | Nil -> None
 


  (* exception levée quand on dépasse le nombre maximum d'étapes *)
exception Timeout

(* réduit t jusqu'au bout en affichant chaque réduit
   fuel : nombre d'étapes encore autorisées (le "timeout") *)

let rec ltr_cbv_norm_aux (t : pterm) (fuel : int) (bavard : bool) : pterm =
  if fuel <= 0 then raise Timeout
  else
    match ltr_cbv_step t with
    | Some t' ->
        if bavard then
          print_endline ("  --> " ^ print_term t');
        ltr_cbv_norm_aux t' (fuel - 1) bavard
    | None -> t


(* évalue t avec au plus max_etapes étapes ; affiche les étapes si bavard *)
let ltr_cbv_eval (t : pterm) (max_etapes : int) (bavard : bool) : unit =
  print_endline ("Evaluation de " ^ (print_term t));
  try
    let res = ltr_cbv_norm_aux t max_etapes bavard in
    if est_valeur res then print_endline ("  Resultat : " ^ (print_term res))
    else print_endline ("  Bloque sur : " ^ (print_term res))
  with Timeout ->
    print_endline ("  TIMEOUT : plus de " ^ (string_of_int max_etapes) ^ " etapes (divergence ?)")
 
(* évaluation avec affichage de toutes les étapes (utilisée en partie 2) *)
let ltr_cbv_norm (t : pterm) (max_etapes : int) : unit = ltr_cbv_eval t max_etapes true



(* évalue t et renvoie le résultat sous forme de chaîne, sans rien afficher
   (utilisée par les tests automatiques) *)
let evalue (t : pterm) (max_etapes : int) : string =
  try
    let res = ltr_cbv_norm_aux t max_etapes false in
    if est_valeur res then print_term res else "BLOQUE"
  with Timeout -> "TIMEOUT"