open Syntaxe


(*=========== PARTIE 2.2 : SEMANTIQUE ===================*)

(* générateur de noms frais pour les variables de termes *)

let compteur_var_t : int ref = ref 0
let nouvelle_var_t () : string = 
  compteur_var_t := !compteur_var_t +1;
  "x" ^ (string_of_int !compteur_var_t)


(* alpha-conversion : renomme toutes les variables liées par des noms frais 
    rn : liste (ancien nom, nouveau nom) des variables liées au-dessus *)
let rec alphaconv(t : pterm) (rn : (string * string ) list) : pterm = 
  match t with
  | Var x -> (match List.assoc_opt x rn with
              | Some x' -> Var x'
              | None -> Var x)    
  | Abs (x, m) -> let x' = nouvelle_var_t() in 
                  Abs (x', alphaconv m ((x,x') :: rn))
  | App(m,n) -> App (alphaconv m rn , alphaconv n rn)
  | N k -> N k  
  | Add (m,n ) -> Add (alphaconv m rn , alphaconv n rn)                         




