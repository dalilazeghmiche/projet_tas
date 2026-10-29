open Syntaxe


(*=========== PARTIE 2.2 : SEMANTIQUE ===================*)

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
  | App (m, n) -> (variables_libres m) @ (variables_libres n)
  | N _ -> []
  | Add (m, n) -> (variables_libres m) @ (variables_libres n)

(* tire un nom frais, et recommence tant que le nom fait partie de la liste interdite *)
let rec nom_frais (interdits : string list) : string =
  let v = nouvelle_var_t () in
  if List.mem v interdits then nom_frais interdits else v

  (* alpha-conversion qui évite les noms de la liste interdits
   rn : liste (ancien nom, nouveau nom) des variables liées au-dessus *)
let rec alphaconv_evite (t : pterm) (rn : (string * string) list) (interdits : string list) : pterm =
  match t with
  | Var x -> (match List.assoc_opt x rn with
              | Some x' -> Var x'
              | None -> Var x)
  | Abs (x, m) -> let x' = nom_frais interdits in
                  Abs (x', alphaconv_evite m ((x, x') :: rn) interdits)
  | App (m, n) -> App (alphaconv_evite m rn interdits, alphaconv_evite n rn interdits)
  | N k -> N k
  | Add (m, n) -> Add (alphaconv_evite m rn interdits, alphaconv_evite n rn interdits)
 
(* alpha-conversion (convention de Barendregt) : les variables liées
   deviennent fraîches, distinctes entre elles ET des variables libres de t *)
let alphaconv (t : pterm) (rn : (string * string) list) : pterm =
  alphaconv_evite t rn (variables_libres t)
                  


(* substitution : remplace la variable x par le terme n dans le terme m
   (calcule m[n/x]) *)
let rec substitution (x : string) (n : pterm) (m : pterm) : pterm =
  match m with
  | Var y -> if y = x then n else Var y
  | Abs (y, corps) -> if y = x then Abs (y, corps)
                      else Abs (y, substitution x n corps)
  | App (m1, m2) -> App (substitution x n m1, substitution x n m2)
  | N k -> N k
  | Add (m1, m2) -> Add (substitution x n m1, substitution x n m2)





  (* est_valeur : un terme est une valeur s'il est "fini" :
   une abstraction, un entier, ou une variable *)
let est_valeur (t : pterm) : bool =
  match t with
  | Abs (_, _) -> true
  | N _ -> true
  | Var _ -> true
  | _ -> false

(* une étape de réduction Left-to-Right Call-by-Value
   renvoie Some t' si t se réduit en t', None si aucune réduction possible *)
let rec ltr_cbv_step (t : pterm) : pterm option =
  match t with
  | App (m, n) ->
      if not (est_valeur m) then
        (* règle µl : on réduit d'abord la fonction *)
        (match ltr_cbv_step m with
         | Some m' -> Some (App (m', n))
         | None -> None)
      else if not (est_valeur n) then
        (* règle µr : la fonction est une valeur, on réduit l'argument *)
        (match ltr_cbv_step n with
         | Some n' -> Some (App (m, n'))
         | None -> None)
      else
        (* règle β : on renomme les variables liées du corps en évitant
           les variables libres de l'argument n, puis on substitue *)
        (match m with
         | Abs (x, corps) -> Some (substitution x n (alphaconv_evite corps [] ((variables_libres n) @ (variables_libres corps))))
         | _ -> None)
  | Add (m, n) ->
      if not (est_valeur m) then
        (match ltr_cbv_step m with
         | Some m' -> Some (Add (m', n))
         | None -> None)
      else if not (est_valeur n) then
        (match ltr_cbv_step n with
         | Some n' -> Some (Add (m, n'))
         | None -> None)
      else
        (match (m, n) with
         | (N a, N b) -> Some (N (a + b))
         | _ -> None)
  | _ -> None   (* Var, Abs, N : déjà des valeurs, on ne réduit pas sous les λ *)




  (* exception levée quand on dépasse le nombre maximum d'étapes *)
exception Timeout

(* réduit t jusqu'au bout en affichant chaque réduit
   fuel : nombre d'étapes encore autorisées (le "timeout") *)
let rec ltr_cbv_norm_aux (t : pterm) (fuel : int) : pterm =
  if fuel <= 0 then raise Timeout
  else
    match ltr_cbv_step t with
    | Some t' -> print_endline ("  --> " ^ (print_term t'));
                 ltr_cbv_norm_aux t' (fuel - 1)
    | None -> t

(* évalue t avec au plus max_etapes étapes, et affiche le résultat *)
let ltr_cbv_norm (t : pterm) (max_etapes : int) : unit =
  print_endline ("Evaluation de " ^ (print_term t));
  try
    let res = ltr_cbv_norm_aux t max_etapes in
    if est_valeur res then print_endline ("  Resultat : " ^ (print_term res))
    else print_endline ("  Bloque sur : " ^ (print_term res))
  with Timeout ->
    print_endline ("  TIMEOUT : plus de " ^ (string_of_int max_etapes) ^ " etapes (divergence ?)")
