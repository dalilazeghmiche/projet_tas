open Syntaxe

(* =========== PARTIES 2.2, 3.2 et 4.2 : SEMANTIQUE =========== *)

(* ---------- noms frais et alpha-conversion ---------- *)

(* générateur de noms frais pour les variables de termes *)
let compteur_var_t : int ref = ref 0
let nouvelle_var_t () : string =
  compteur_var_t := !compteur_var_t + 1;
  "_x" ^ (string_of_int !compteur_var_t)

(* renvoie la liste des variables libres d'un terme *)
let rec variables_libres (t : pterm) : string list =
  match t with
  | Var x -> [x]
  | Abs (x, m) -> List.filter (fun y -> y <> x) (variables_libres m)
  | App (m, n) | Add (m, n) | Sub (m, n) | Cons (m, n) | Assign (m, n) ->
      (variables_libres m) @ (variables_libres n)
  | N _ | Nil | Unit | Region _ -> []
  | Hd m | Tl m | Fix m | Ref m | Deref m -> variables_libres m
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
  | Unit -> Unit
  | Region n -> Region n
  | Ref m -> Ref (ac m)
  | Deref m -> Deref (ac m)
  | Assign (m, n) -> Assign (ac m, ac n)

(* alpha-conversion (convention de Barendregt) : les variables liées
   deviennent fraîches, distinctes entre elles ET des variables libres de t *)
let alphaconv (t : pterm) (rn : (string * string) list) : pterm =
  alphaconv_evite t rn (variables_libres t)

(* ---------- substitution ---------- *)

(* substitution : remplace la variable x par le terme n dans le terme m
   (calcule m[n/x]) *)
let rec substitution (x : string) (n : pterm) (m : pterm) : pterm =
  let sub (u : pterm) : pterm = substitution x n u in
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
  | Unit -> Unit
  | Region k -> Region k
  | Ref m1 -> Ref (sub m1)
  | Deref m1 -> Deref (sub m1)
  | Assign (m1, m2) -> Assign (sub m1, sub m2)

(* remplace x par v dans corps, sans capture :
   on renomme d'abord les variables liées de corps en évitant
   les variables libres de v et celles de corps *)
let substitue_sans_capture (x : string) (v : pterm) (corps : pterm) : pterm =
  substitution x v (alphaconv_evite corps [] ((variables_libres v) @ (variables_libres corps)))

(* ---------- valeurs ---------- *)

(* est_valeur : un terme est une valeur s'il a fini de calculer *)
let rec est_valeur (t : pterm) : bool =
  match t with
  | Abs (_, _) | N _ | Var _ | Nil | Unit | Region _ -> true
  | Cons (v1, v2) -> est_valeur v1 && est_valeur v2   (* liste de valeurs *)
  | _ -> false

(* ---------- état mémoire (partie 4) ---------- *)

(* un état associe des régions (numéros) à des termes (des valeurs) *)
type etat = (int * pterm) list

(* nouvelle région : son numéro est le nombre de régions déjà créées *)
let nouvelle_region (s : etat) : int = List.length s

(* affiche un état : { rho0 -> v0 ; rho1 -> v1 } *)
let print_etat (s : etat) : string =
  let cases = List.map (fun (n, v) -> "rho" ^ (string_of_int n) ^ " -> " ^ (print_term v))
                       (List.rev s) in
  "{ " ^ (String.concat " ; " cases) ^ " }"

(* ---------- une étape de réduction ---------- *)

(* une étape de réduction Left-to-Right Call-by-Value sur un couple (terme, état)
   renvoie Some (t', s') si (t, s) se réduit en (t', s'), None sinon *)
let rec ltr_cbv_step (t : pterm) (s : etat) : (pterm * etat) option =
  (* réduit le sous-terme u, puis reconstruit le terme avec la fonction k *)
  let dans (u : pterm) (k : pterm -> pterm) : (pterm * etat) option =
    match ltr_cbv_step u s with
    | Some (u', s') -> Some (k u', s')
    | None -> None
  in
  match t with
  (* ---------- partie 2 ---------- *)
  | App (m, n) ->
      if not (est_valeur m) then dans m (fun m' -> App (m', n))          (* règle µl *)
      else if not (est_valeur n) then dans n (fun n' -> App (m, n'))     (* règle µr *)
      else
        (match m with
         | Abs (x, corps) -> Some (substitue_sans_capture x n corps, s)  (* règle β *)
         | _ -> None)
  | Add (m, n) ->
      if not (est_valeur m) then dans m (fun m' -> Add (m', n))
      else if not (est_valeur n) then dans n (fun n' -> Add (m, n'))
      else (match (m, n) with (N a, N b) -> Some (N (a + b), s) | _ -> None)
  (* ---------- partie 3 : soustraction (bornée à 0 : entiers naturels) ---------- *)
  | Sub (m, n) ->
      if not (est_valeur m) then dans m (fun m' -> Sub (m', n))
      else if not (est_valeur n) then dans n (fun n' -> Sub (m, n'))
      else (match (m, n) with (N a, N b) -> Some (N (max 0 (a - b)), s) | _ -> None)
  (* ---------- partie 3 : listes ---------- *)
  | Cons (m, n) ->
      if not (est_valeur m) then dans m (fun m' -> Cons (m', n))
      else if not (est_valeur n) then dans n (fun n' -> Cons (m, n'))
      else None                                      (* Cons de deux valeurs : valeur *)
  | Hd m ->
      if not (est_valeur m) then dans m (fun m' -> Hd m')
      else (match m with Cons (v, _) -> Some (v, s) | _ -> None)      (* hd [] : bloqué *)
  | Tl m ->
      if not (est_valeur m) then dans m (fun m' -> Tl m')
      else (match m with Cons (_, l) -> Some (l, s) | _ -> None)      (* tl [] : bloqué *)
  (* ---------- partie 3 : branchements (on n'évalue que la condition) ---------- *)
  | IfZero (c, a, b) ->
      if not (est_valeur c) then dans c (fun c' -> IfZero (c', a, b))
      else (match c with N 0 -> Some (a, s) | N _ -> Some (b, s) | _ -> None)
  | IfEmpty (c, a, b) ->
      if not (est_valeur c) then dans c (fun c' -> IfEmpty (c', a, b))
      else (match c with Nil -> Some (a, s) | Cons (_, _) -> Some (b, s) | _ -> None)
  (* ---------- partie 3 : point fixe ---------- *)
  | Fix m ->
      if not (est_valeur m) then dans m (fun m' -> Fix m')
      else
        (match m with
         (* fix (phi -> M)  -->  M [ fix (phi -> M) / phi ] *)
         | Abs (phi, corps) -> Some (substitue_sans_capture phi (Fix m) corps, s)
         | _ -> None)
  (* ---------- partie 3 : let ---------- *)
  | Let (x, e1, e2) ->
      if not (est_valeur e1) then dans e1 (fun e1' -> Let (x, e1', e2))
      else Some (substitue_sans_capture x e1 e2, s)
  (* ---------- partie 4 : traits impératifs ---------- *)
  | Ref e ->
      (* on réduit e ; si c'est une valeur v, on crée une nouvelle région rho -> v *)
      if not (est_valeur e) then dans e (fun e' -> Ref e')
      else let rho = nouvelle_region s in
           Some (Region rho, (rho, e) :: s)
  | Deref e ->
      (* on réduit e ; si c'est une région rho, !rho donne le terme associé à rho *)
      if not (est_valeur e) then dans e (fun e' -> Deref e')
      else
        (match e with
         | Region rho -> (match List.assoc_opt rho s with
                          | Some v -> Some (v, s)
                          | None -> None)                    (* région inconnue : bloqué *)
         | _ -> None)
  | Assign (e1, e2) ->
      (* on réduit e1, puis e2 ; si e1 est une région rho, on y range la valeur de e2 *)
      if not (est_valeur e1) then dans e1 (fun e1' -> Assign (e1', e2))
      else if not (est_valeur e2) then dans e2 (fun e2' -> Assign (e1, e2'))
      else
        (match e1 with
         | Region rho when List.mem_assoc rho s ->
             Some (Unit, (rho, e2) :: (List.remove_assoc rho s))
         | _ -> None)
  (* ---------- valeurs : rien à réduire (pas de réduction sous les lambdas) ---------- *)
  | Var _ | Abs (_, _) | N _ | Nil | Unit | Region _ -> None

(* ---------- évaluation complète ---------- *)

(* exception levée quand on dépasse le nombre maximum d'étapes *)
exception Timeout

(* réduit (t, s) jusqu'au bout ; affiche chaque réduit si bavard = true
   fuel : nombre d'étapes encore autorisées (le "timeout") *)
let rec ltr_cbv_norm_aux (t : pterm) (s : etat) (fuel : int) (bavard : bool) : pterm * etat =
  if fuel <= 0 then raise Timeout
  else
    match ltr_cbv_step t s with
    | Some (t', s') ->
        if bavard then print_endline ("  --> " ^ (print_term t'));
        ltr_cbv_norm_aux t' s' (fuel - 1) bavard
    | None -> (t, s)

(* évalue t (en partant d'un état vide) avec au plus max_etapes étapes *)
let ltr_cbv_eval (t : pterm) (max_etapes : int) (bavard : bool) : unit =
  print_endline ("Evaluation de " ^ (print_term t));
  try
    let (res, s) = ltr_cbv_norm_aux t [] max_etapes bavard in
    (if est_valeur res then print_endline ("  Resultat : " ^ (print_term res))
     else print_endline ("  Bloque sur : " ^ (print_term res)));
    if s <> [] then print_endline ("  Etat     : " ^ (print_etat s))
  with Timeout ->
    print_endline ("  TIMEOUT : plus de " ^ (string_of_int max_etapes) ^ " etapes (divergence ?)")

(* évaluation avec affichage de toutes les étapes *)
let ltr_cbv_norm (t : pterm) (max_etapes : int) : unit = ltr_cbv_eval t max_etapes true

(* évalue t et renvoie le résultat sous forme de chaîne, sans rien afficher
   (utilisée par les tests automatiques) *)
let evalue (t : pterm) (max_etapes : int) : string =
  try
    let (res, _) = ltr_cbv_norm_aux t [] max_etapes false in
    if est_valeur res then print_term res else "BLOQUE"
  with Timeout -> "TIMEOUT"