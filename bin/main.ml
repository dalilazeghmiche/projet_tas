open Syntaxe
open Typeur
open Eval




(* ***EXEMPLES*** *)  
let ex_id : pterm = Abs ("x", Var "x") 
let inf_ex_id : string = inference ex_id 
let ex_k : pterm = Abs ("x", Abs ("y", Var "x")) 
let inf_ex_k : string = inference ex_k
let ex_s : pterm = Abs ("x", Abs ("y", Abs ("z", App (App (Var "x", Var "z"), App (Var "y", Var "z")))))
let inf_ex_s : string = inference ex_s 
let ex_nat1 : pterm = App (Abs ("x", Add(Var "x", N 1)), N 3)
let inf_ex_nat1 : string = inference ex_nat1
let ex_nat2 : pterm = Abs ("x", Add( Var "x", Var "x"))
let inf_ex_nat2 : string = inference ex_nat2
let ex_omega : pterm = App (Abs ("x", App (Var "x", Var "x")), Abs ("y", App (Var "y", Var "y")))
let inf_ex_omega : string = inference ex_omega
let ex_nat3 : pterm = App (ex_nat2, ex_id)
let inf_ex_nat3 : string = inference ex_nat3

(* ***EXEMPLES PARTIE 3*** *)
(* la liste [1; 2; 3] *)
let l123 : pterm = Cons (N 1, Cons (N 2, Cons (N 3, Nil)))

(* somme n = n + (n-1) + ... + 0, définie avec fix *)
let somme : pterm =
  Fix (Abs ("f", Abs ("n", IfZero (Var "n", N 0, Add (Var "n", App (Var "f", Sub (Var "n", N 1)))))))

(* longueur d'une liste *)
let longueur : pterm =
  Fix (Abs ("f", Abs ("l", IfEmpty (Var "l", N 0, Add (N 1, App (Var "f", Tl (Var "l")))))))

(* map g l : applique g à chaque élément de l *)
let map : pterm =
  Fix (Abs ("m", Abs ("g", Abs ("l",
    IfEmpty (Var "l", Nil, Cons (App (Var "g", Hd (Var "l")), App (App (Var "m", Var "g"), Tl (Var "l"))))))))


(* type d'abord le programme, puis l'évalue seulement s'il est typable *)
let executer (t : pterm) : unit =
  print_endline ("Programme : " ^ (print_term t));
  match type_de t with
  | "PAS TYPABLE" -> print_endline "  Rejete par le typeur : il n'est pas evalue"
  | ty -> print_endline ("  Type     : " ^ ty);
          print_endline ("  Resultat : " ^ (evalue t 10000))

(* affiche une étape de réduction *)
let print_step (t : pterm) : string =
  match ltr_cbv_step t with
  | Some t' -> (print_term t) ^ "   -->   " ^ (print_term t')
  | None -> (print_term t) ^ "   : aucune reduction possible"

let main () =
 print_endline "======================";
 print_endline inf_ex_id;
 print_endline "======================";
 print_endline inf_ex_k;
 print_endline "======================";
 print_endline inf_ex_s;
 print_endline "======================";
 print_endline inf_ex_omega;
 print_endline "======================";
 print_endline inf_ex_nat1;
 print_endline "======================";
 print_endline inf_ex_nat2;
 print_endline "======================";
 print_endline inf_ex_nat3;
 print_endline "========ALPHA-CONVERSION=====";
 print_endline (print_term (alphaconv ex_k []));
 print_endline (print_term (alphaconv (Abs ("x", App (Var "x", Var "y"))) []));
 print_endline (print_term (alphaconv (Abs ("x", Abs ("x", Var "x"))) [])) ; 

 print_endline "====== SUBSTITUTION ======";
 print_endline (print_term (substitution "x" (N 3) (Add (Var "x", N 1))));
 print_endline (print_term (substitution "x" ex_id (App (Var "x", Var "y"))));
 print_endline (print_term (substitution "x" (N 3) (Abs ("x", Var "x"))));
 print_endline (print_term (substitution "x" (N 3) (Abs ("y", Add (Var "x", Var "y")))));


 print_endline "====== UNE ETAPE LTR-CBV ======";
 print_endline (print_step ex_nat1);
 print_endline (print_step (Add (N 3, N 1)));
 print_endline (print_step (App (ex_id, ex_id)));
 print_endline (print_step (App (App (ex_k, ex_id), N 5)));
 print_endline (print_step (Add (App (ex_id, N 2), App (ex_id, N 3))));
 print_endline (print_step ex_omega);
 print_endline (print_step ex_k);
 print_endline (print_step (N 7));

 print_endline "====== EVALUATION COMPLETE ======";
 ltr_cbv_norm ex_nat1 100;
 ltr_cbv_norm (Add (App (ex_id, N 2), App (ex_id, N 3))) 100;
 ltr_cbv_norm (App (App (App (ex_s, ex_k), ex_k), N 7)) 100;
 ltr_cbv_norm (App (Var "y", N 3)) 100;
 ltr_cbv_norm ex_omega 5;

 print_endline "====== CORRECTIONS DU TYPEUR ======";
 print_endline (inference (App (Var "y", N 3)));
 print_endline (inference_fuel ex_s 3);

 print_endline "====== TEST CAPTURE ======";
 ltr_cbv_norm (App (Abs ("x", Abs ("y", Var "x")), Var "y")) 10;
 ltr_cbv_norm (App (App (Abs ("x", Abs ("y", Var "x")), Var "y"), N 5)) 10;
 ltr_cbv_norm (App (Abs ("x", Abs ("y", Var "x")), Var "x1")) 10;
 ltr_cbv_norm (App (Abs ("x", Abs ("y", Var "x")), Var "_x21")) 10;
 ltr_cbv_norm (App (Abs ("x", Abs ("y", Var "_x23")), N 3)) 10;
  print_endline "====== PARTIE 3 : SYNTAXE ======";
 print_endline (print_term (Sub (N 5, N 2)));
 print_endline (print_term (Cons (N 1, Cons (N 2, Nil))));
 print_endline (print_term (Hd (Cons (N 1, Nil))));
 print_endline (print_term (IfZero (N 0, N 1, N 2)));
 print_endline (print_term (IfEmpty (Nil, N 1, N 2)));
 print_endline (print_term (Let ("id", Abs ("x", Var "x"), App (Var "id", N 3))));
 print_endline (print_term (Fix (Abs ("f", Abs ("n", IfZero (Var "n", N 0, App (Var "f", Sub (Var "n", N 1))))))));
 print_endline (print_type (Liste Nat));
 print_endline (print_type (Forall (["X"], Arr (Liste (Var "X"), Var "X"))));
 print_endline "====== PARTIE 3 : EVALUATION ======";
 ltr_cbv_norm (Sub (N 5, N 2)) 10;
 ltr_cbv_norm (Hd l123) 10;
 ltr_cbv_norm (Tl l123) 10;
 ltr_cbv_norm (Cons (Add (N 1, N 1), Nil)) 10;
 ltr_cbv_norm (Hd Nil) 10;
 ltr_cbv_norm (IfZero (Sub (N 1, N 1), N 10, N 20)) 10;
 ltr_cbv_norm (IfZero (N 7, N 10, N 20)) 10;
 ltr_cbv_norm (IfEmpty (Tl (Cons (N 1, Nil)), N 1, N 2)) 10;
 ltr_cbv_norm (Let ("x", Add (N 2, N 3), Add (Var "x", Var "x"))) 10;
 ltr_cbv_norm (Let ("id", Abs ("x", Var "x"), App (Var "id", N 5))) 10;
 ltr_cbv_norm (IfZero (N 0, N 1, ex_omega)) 10;
 ltr_cbv_norm (App (somme, N 3)) 100;
 print_endline "====== PARTIE 3 : FONCTIONS RECURSIVES (resultat seul) ======";
 ltr_cbv_eval (App (somme, N 10)) 1000 false;
 ltr_cbv_eval (App (longueur, l123)) 1000 false;
 ltr_cbv_eval (App (App (map, Abs ("x", Add (Var "x", N 10))), l123)) 1000 false;
 ltr_cbv_eval (Fix (Abs ("f", App (Var "f", N 0)))) 50 false;

 print_endline "====== PARTIE 3 : TYPAGE ======";
 print_endline (inference (Abs ("x", Sub (Var "x", N 1))));
 print_endline (inference l123);
 print_endline (inference Nil);
 print_endline (inference (Abs ("l", Hd (Var "l"))));
 print_endline (inference (Abs ("l", Tl (Var "l"))));
 print_endline (inference (Abs ("x", IfZero (Var "x", N 1, N 2))));
 print_endline (inference (Abs ("l", IfEmpty (Var "l", N 0, Hd (Var "l")))));
 print_endline (inference somme);
 print_endline (inference longueur);
 print_endline (inference map);
 print_endline (inference (App (App (map, Abs ("x", Add (Var "x", N 1))), l123)));
 print_endline (inference (Fix (Abs ("f", Var "f"))));
 print_endline "--- termes non typables ---";
 print_endline (inference (Cons (N 1, Cons (Nil, Nil))));
 print_endline (inference (Abs ("x", IfZero (Var "x", N 1, Nil))));
 print_endline (inference (Hd (N 3)));
 print_endline (inference (IfEmpty (N 0, N 1, N 2)));
 print_endline (inference (Add (Nil, N 1)));
 print_endline "--- let-polymorphisme ---";
 print_endline (inference (Let ("x", N 3, Add (Var "x", Var "x"))));
 print_endline (inference (Let ("id", Abs ("x", Var "x"), App (Var "id", Var "id"))));
 print_endline (inference (Let ("id", Abs ("x", Var "x"), IfEmpty (App (Var "id", Nil), App (Var "id", N 1), N 2))));
 print_endline (inference (App (Abs ("id", IfEmpty (App (Var "id", Nil), App (Var "id", N 1), N 2)), Abs ("x", Var "x"))));
 print_endline (inference (Let ("f", map, App (App (Var "f", Abs ("x", Add (Var "x", N 1))), App (App (Var "f", Abs ("l", Hd (Var "l"))), Cons (l123, Nil))))));
 print_endline "--- pieges du let ---";
 print_endline (inference (Abs ("y", Let ("z", Add (Var "y", N 1), Var "y"))));
 print_endline (inference (App (Abs ("y", Let ("z", Add (Var "y", N 1), Var "y")), Nil)));
 print_endline (inference (Abs ("y", Let ("z", Var "y", Add (Var "z", N 1)))));
 print_endline (inference (Abs ("y", Let ("z", Var "y", IfZero (Var "z", N 0, Hd (Var "z"))))));
 print_endline (inference (Let ("x", Hd Nil, Add (Var "x", N 1))));
 print_endline "====== TYPER PUIS EVALUER ======";
 executer (App (somme, N 10));
 executer (App (App (map, Abs ("x", Add (Var "x", N 1))), l123));
 executer (Let ("id", Abs ("x", Var "x"), IfEmpty (App (Var "id", Nil), App (Var "id", N 1), N 2)));
 executer (Sub (N 2, N 5));
 executer (Add (N 3, Abs ("x", Var "x")));
 executer (App (Hd Nil, N 1));
 executer ex_omega;
 executer (Let ("x", Hd Nil, Add (Var "x", N 1)))

let _ =
  main ();
  Tests.lance ()