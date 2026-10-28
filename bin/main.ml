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
 print_endline (print_term (alphaconv (Abs ("x", Abs ("x", Var "x"))) []))  

let _ = main ()