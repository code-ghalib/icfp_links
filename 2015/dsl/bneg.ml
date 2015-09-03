(* Composing the transformations *)

(* 
#load "higher.cmo";;
#load "dsl.cmo";;
#load "rr.cmo";;
#load "bconst_prop.cmo";;
#load "bneg_double.cmo";;
#load "bneg_down.cmo";;
*)
open Higher;;
open Dsl;;
open Rr;;

let _ = view exc1

let exc1_cp d = Bconst_prop.obscp exc1 d

let _ = view exc1_cp

let _ = view @@ Bneg_down.obsNDown @@ Bneg_double.obsN2N @@ exc1_cp

let _ = view @@ Bneg_double.obsN2N @@ Bneg_down.obsNDown @@ exc1_cp
(* 
  Order matters
 *)


let chain1 e = 
  Bconst_prop.obscp @@ Bneg_down.obsNDown @@ Bneg_double.obsN2N @@ e

let chain2 e = 
  Bneg_down.obsNDown @@ Bneg_double.obsN2N @@ Bconst_prop.obscp @@ e


let rec ntimes : int -> ('a -> 'a) -> ('a -> 'a) = fun n tr ->
  fun e -> if n = 0 then e else ntimes (n-1) tr (tr e)

let _  = view exc1

let _ = view (ntimes 3 chain1 @@ exc1)
let _ = view (ntimes 3 chain2 @@ exc1)

(* See the types! 
 * Difference from Haskell
   How to overcome closedness? Use ConstraintKind
*)


