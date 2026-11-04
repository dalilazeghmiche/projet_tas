open Syntaxe
open Typeur
open Eval

(* =========== TESTS AUTOMATIQUES =========== *)
(* chaque test compare le résultat obtenu au résultat attendu ;
   seuls les échecs sont affichés, puis un bilan *)

let nb_ok : int ref = ref 0
let nb_echec : int ref = ref 0

let verifie (nom : string) (obtenu : string) (attendu : string) : unit =
  if obtenu = attendu then incr nb_ok
  else begin
    incr nb_echec;
    print_endline ("ECHEC : " ^ nom);
    print_endline ("   attendu : " ^ attendu);
    print_endline ("   obtenu  : " ^ obtenu)
  end

(* teste le résultat de l'évaluation *)
let teste_eval (nom : string) (t : pterm) (attendu : string) : unit =
  verifie ("eval " ^ nom) (evalue t 1000) attendu

(* teste le type inféré *)
let teste_type (nom : string) (t : pterm) (attendu : string) : unit =
  verifie ("type " ^ nom) (type_de t) attendu

(* ---------- termes utilisés dans les tests ---------- *)
let id : pterm = Abs ("x", Var "x")
let k : pterm = Abs ("x", Abs ("y", Var "x"))
let s : pterm = Abs ("x", Abs ("y", Abs ("z", App (App (Var "x", Var "z"), App (Var "y", Var "z")))))
let delta : pterm = Abs ("x", App (Var "x", Var "x"))
let omega : pterm = App (delta, delta)
let l123 : pterm = Cons (N 1, Cons (N 2, Cons (N 3, Nil)))
let somme : pterm =
  Fix (Abs ("f", Abs ("n", IfZero (Var "n", N 0, Add (Var "n", App (Var "f", Sub (Var "n", N 1)))))))
let longueur : pterm =
  Fix (Abs ("f", Abs ("l", IfEmpty (Var "l", N 0, Add (N 1, App (Var "f", Tl (Var "l")))))))
let map : pterm =
  Fix (Abs ("m", Abs ("g", Abs ("l",
    IfEmpty (Var "l", Nil, Cons (App (Var "g", Hd (Var "l")), App (App (Var "m", Var "g"), Tl (Var "l"))))))))

(* ---------- partie 2 : évaluation ---------- *)
let tests_eval_partie2 () : unit =
  teste_eval "I 3" (App (id, N 3)) "3";
  teste_eval "(fun x -> x+1) 3" (App (Abs ("x", Add (Var "x", N 1)), N 3)) "4";
  teste_eval "K 1 2" (App (App (k, N 1), N 2)) "1";
  teste_eval "S K K 7" (App (App (App (s, k), k), N 7)) "7";
  teste_eval "I 2 + I 3" (Add (App (id, N 2), App (id, N 3))) "5";
  teste_eval "pas de reduction sous lambda" k "(fun x -> (fun y -> x))";
  teste_eval "omega diverge" omega "TIMEOUT";
  teste_eval "variable libre bloquee" (App (Var "y", N 3)) "BLOQUE";
  teste_eval "3 + (fun x -> x) bloque" (Add (N 3, id)) "BLOQUE"

(* ---------- partie 2 : capture de variables ---------- *)
let tests_capture () : unit =
  teste_eval "capture y" (App (App (k, Var "y"), N 5)) "y";
  teste_eval "capture x1" (App (App (k, Var "x1"), N 5)) "x1";
  teste_eval "capture _x1" (App (App (k, Var "_x1"), N 5)) "_x1";
  teste_eval "capture duplication"
    (App (App (Abs ("f", Abs ("y", App (Var "f", App (Var "f", Var "y")))),
               Abs ("z", Add (Var "z", Var "y"))), N 1)) "BLOQUE";
  teste_eval "capture let" (App (App (Abs ("z", Let ("x", Var "z", Abs ("y", Var "x"))), Var "y"), N 0)) "y";
  teste_eval "masquage lambda" (App (App (Abs ("x", Abs ("x", Var "x")), N 3), N 4)) "4"

(* ---------- partie 2 : typage ---------- *)
let tests_type_partie2 () : unit =
  teste_type "I" id "(a -> a)";
  teste_type "K" k "(a -> (b -> a))";
  teste_type "S" s "((a -> (b -> c)) -> ((a -> b) -> (a -> c)))";
  teste_type "S K K" (App (App (s, k), k)) "(a -> a)";
  teste_type "omega" omega "PAS TYPABLE";
  teste_type "fun x -> x + x" (Abs ("x", Add (Var "x", Var "x"))) "(Nat -> Nat)";
  teste_type "(fun x -> x+x) I" (App (Abs ("x", Add (Var "x", Var "x")), id)) "PAS TYPABLE";
  teste_type "variable libre" (App (Var "y", N 3)) "PAS TYPABLE"

(* ---------- partie 3 : évaluation ---------- *)
let tests_eval_partie3 () : unit =
  teste_eval "5 - 2" (Sub (N 5, N 2)) "3";
  teste_eval "2 - 5 borne a 0" (Sub (N 2, N 5)) "0";
  teste_eval "3 - 3" (Sub (N 3, N 3)) "0";
  teste_eval "hd" (Hd l123) "1";
  teste_eval "tl" (Tl l123) "(2 :: (3 :: []))";
  teste_eval "cons evalue la tete" (Cons (Add (N 1, N 1), Nil)) "(2 :: [])";
  teste_eval "hd [] bloque" (Hd Nil) "BLOQUE";
  teste_eval "tl [] bloque" (Tl Nil) "BLOQUE";
  teste_eval "ifzero 0" (IfZero (Sub (N 1, N 1), N 10, N 20)) "10";
  teste_eval "ifzero 7" (IfZero (N 7, N 10, N 20)) "20";
  teste_eval "ifempty []" (IfEmpty (Tl (Cons (N 1, Nil)), N 1, N 2)) "1";
  teste_eval "ifempty non vide" (IfEmpty (l123, N 1, N 2)) "2";
  teste_eval "ifzero n'evalue pas else" (IfZero (N 0, N 1, omega)) "1";
  teste_eval "ifempty n'evalue pas else" (IfEmpty (Nil, N 0, omega)) "0";
  teste_eval "ifzero sur liste bloque" (IfZero (Nil, N 1, N 2)) "BLOQUE";
  teste_eval "let" (Let ("x", Add (N 2, N 3), Add (Var "x", Var "x"))) "10";
  teste_eval "let masquage" (Let ("x", N 1, Let ("x", N 2, Var "x"))) "2";
  teste_eval "let e1 voit x exterieur" (Let ("x", N 1, Let ("x", Add (Var "x", N 10), Var "x"))) "11";
  teste_eval "somme 10" (App (somme, N 10)) "55";
  teste_eval "longueur" (App (longueur, l123)) "3";
  teste_eval "map" (App (App (map, Abs ("x", Add (Var "x", N 10))), l123)) "(11 :: (12 :: (13 :: [])))";
  teste_eval "fix diverge" (Fix (Abs ("f", App (Var "f", N 0)))) "TIMEOUT"

(* ---------- partie 3 : typage ---------- *)
let tests_type_partie3 () : unit =
  teste_type "x - 1" (Abs ("x", Sub (Var "x", N 1))) "(Nat -> Nat)";
  teste_type "[1;2;3]" l123 "[Nat]";
  teste_type "[]" Nil "[a]";
  teste_type "hd" (Abs ("l", Hd (Var "l"))) "([a] -> a)";
  teste_type "tl" (Abs ("l", Tl (Var "l"))) "([a] -> [a])";
  teste_type "ifzero" (Abs ("x", IfZero (Var "x", N 1, N 2))) "(Nat -> Nat)";
  teste_type "somme" somme "(Nat -> Nat)";
  teste_type "longueur" longueur "([a] -> Nat)";
  teste_type "map" map "((a -> b) -> ([a] -> [b]))";
  teste_type "1 :: [] :: []" (Cons (N 1, Cons (Nil, Nil))) "PAS TYPABLE";
  teste_type "branches differentes" (Abs ("x", IfZero (Var "x", N 1, Nil))) "PAS TYPABLE";
  teste_type "hd 3" (Hd (N 3)) "PAS TYPABLE";
  teste_type "ifempty 0" (IfEmpty (N 0, N 1, N 2)) "PAS TYPABLE";
  teste_type "[] + 1" (Add (Nil, N 1)) "PAS TYPABLE";
  (* let-polymorphisme *)
  teste_type "let id id" (Let ("id", id, App (Var "id", Var "id"))) "(a -> a)";
  teste_type "let id poly"
    (Let ("id", id, IfEmpty (App (Var "id", Nil), App (Var "id", N 1), N 2))) "Nat";
  teste_type "fun id pas poly"
    (App (Abs ("id", IfEmpty (App (Var "id", Nil), App (Var "id", N 1), N 2)), id)) "PAS TYPABLE";
  teste_type "let len poly"
    (Let ("len", longueur, Add (App (Var "len", l123), App (Var "len", Cons (Nil, Nil))))) "Nat";
  (* pièges du let *)
  teste_type "contrainte de e1 gardee" (Abs ("y", Let ("z", Add (Var "y", N 1), Var "y"))) "(Nat -> Nat)";
  teste_type "contrainte de e1 gardee (echec)"
    (App (Abs ("y", Let ("z", Add (Var "y", N 1), Var "y")), Nil)) "PAS TYPABLE";
  teste_type "pas de generalisation a tort"
    (Abs ("y", Let ("z", Var "y", IfZero (Var "z", N 0, Hd (Var "z"))))) "PAS TYPABLE";
  teste_type "generalisation partielle"
    (Abs ("x", Let ("g", Abs ("y", Var "x"), Add (App (Var "g", N 1), App (Var "g", Nil))))) "(Nat -> Nat)";
  teste_type "recursion monomorphe"
           (Fix (Abs ("f", Abs ("x", IfZero (N 0, App (Var "f", N 1), App (Var "f", Nil)))))) "PAS TYPABLE";
     (* règle (Fix) du cours : fix seulement à un type fonctionnel *)
     teste_type "fix type non fonctionnel" (Fix (Abs ("n", Add (Var "n", N 1)))) "PAS TYPABLE";
     teste_type "fix (fun f -> f)" (Fix (Abs ("f", Var "f"))) "(a -> b)"


(* ---------- partie 4 : termes utilisés ---------- *)
(* let x = e1 in e2 où x n'est pas utilisé : séquence e1 ; e2 *)
let seq (e1 : pterm) (e2 : pterm) : pterm = Let ("_", e1, e2)
let ex_sujet : pterm =
  Let ("l", Ref Nil, seq (Assign (Var "l", Cons (Abs ("x", Var "x"), Nil))) (Add (Hd (Deref (Var "l")), N 2)))
let ex_compteur : pterm =
  Let ("c", Ref (N 0),
       Let ("incr", Abs ("u", Assign (Var "c", Add (Deref (Var "c"), N 1))),
            seq (App (Var "incr", Unit)) (seq (App (Var "incr", Unit)) (Deref (Var "c")))))
 
(* ---------- partie 4 : évaluation ---------- *)
let tests_eval_partie4 () : unit =
  teste_eval "!(ref 5)" (Deref (Ref (N 5))) "5";
  teste_eval "ref evalue son argument" (Deref (Ref (Add (N 1, N 1)))) "2";
  teste_eval "ref 5 donne une region" (Ref (N 5)) "rho0";
  teste_eval "assign renvoie ()" (Assign (Ref (N 1), N 2)) "()";
  teste_eval "r := !r + 1" (Let ("r", Ref (N 1), seq (Assign (Var "r", Add (Deref (Var "r"), N 1))) (Deref (Var "r")))) "2";
  teste_eval "compteur" ex_compteur "2";
  teste_eval "deux regions independantes"
    (Let ("a", Ref (N 1), Let ("b", Ref (N 2), seq (Assign (Var "a", N 10)) (Deref (Var "b"))))) "2";
  teste_eval "partage (alias)"
    (Let ("a", Ref (N 1), Let ("b", Var "a", seq (Assign (Var "b", N 5)) (Deref (Var "a"))))) "5";
  teste_eval "!3 bloque" (Deref (N 3)) "BLOQUE";
  teste_eval "1 := 2 bloque" (Assign (N 1, N 2)) "BLOQUE";
  teste_eval "exemple du sujet bloque" ex_sujet "BLOQUE"
 
(* ---------- partie 4 : typage ---------- *)
let tests_type_partie4 () : unit =
  teste_type "()" Unit "Unit";
  teste_type "ref 5" (Ref (N 5)) "(Ref Nat)";
  teste_type "fun r -> !r" (Abs ("r", Deref (Var "r"))) "((Ref a) -> a)";
  teste_type "fun r v -> r := v" (Abs ("r", Abs ("v", Assign (Var "r", Var "v")))) "((Ref a) -> (a -> Unit))";
  teste_type "compteur" ex_compteur "Nat";
  teste_type "!3" (Deref (N 3)) "PAS TYPABLE";
  teste_type "1 := 2" (Assign (N 1, N 2)) "PAS TYPABLE";
  teste_type "r := [] avec r : Ref Nat" (Let ("r", Ref (N 1), Assign (Var "r", Nil))) "PAS TYPABLE";
  (* polymorphisme faible *)
  polymorphisme_faible := false;
  teste_type "exemple du sujet SANS polymorphisme faible" ex_sujet "Nat";
  polymorphisme_faible := true;
  teste_type "exemple du sujet AVEC polymorphisme faible" ex_sujet "PAS TYPABLE";
  teste_type "weak : la premiere utilisation fixe le type"
    (Let ("l", Ref Nil, seq (Assign (Var "l", Cons (N 1, Nil))) (Hd (Deref (Var "l"))))) "Nat";
  teste_type "weak : deuxieme utilisation incompatible"
    (Let ("l", Ref Nil, seq (Assign (Var "l", Cons (N 1, Nil))) (Assign (Var "l", Cons (Nil, Nil))))) "PAS TYPABLE";
  teste_type "weak : pas generalise par un let interne"
    (Let ("l", Ref Nil, Let ("f", Abs ("x", Assign (Var "l", Cons (Var "x", Nil))),
                             seq (App (Var "f", N 1)) (App (Var "f", Nil))))) "PAS TYPABLE";
  teste_type "application expansive : (fun x -> ref x) []"
    (Let ("r", App (Abs ("x", Ref (Var "x")), Nil),
          seq (Assign (Var "r", Cons (Abs ("y", Var "y"), Nil))) (Add (Hd (Deref (Var "r")), N 2)))) "PAS TYPABLE";
  teste_type "non-expansif reste polymorphe"
    (Let ("id", Abs ("x", Var "x"), seq (App (Var "id", N 1)) (App (Var "id", Nil)))) "[a]";
  teste_type "ref dans une fonction" (Abs ("y", Let ("r", Ref (Var "y"), Deref (Var "r")))) "(a -> a)";
  teste_type "limite : application partielle non generalisee"
    (Let ("f", App (Abs ("x", Abs ("y", Var "y")), N 1), seq (App (Var "f", N 1)) (App (Var "f", Nil)))) "PAS TYPABLE"

(* lance tous les tests et affiche le bilan *)
let lance () : unit =
  print_endline "====== TESTS AUTOMATIQUES ======";
  tests_eval_partie2 ();
  tests_capture ();
  tests_type_partie2 ();
  tests_eval_partie3 ();
  tests_type_partie3 ();
  tests_eval_partie4 ();
  tests_type_partie4 ();
  print_endline ("Bilan : " ^ (string_of_int !nb_ok) ^ " tests reussis, "
                 ^ (string_of_int !nb_echec) ^ " echec(s)")
