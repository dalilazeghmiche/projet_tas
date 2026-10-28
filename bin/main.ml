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
 print_endline (inference_fuel ex_s 3)
let _ = main ()
