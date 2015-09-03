(* Pushing the negation down *)

(*    Neg (And x y) -> Or  (Neg x) (Neg y)
 *    Neg (Or x y)  -> And (Neg x) (Neg y)
 *)

(* 
#load "higher.cmo";;
#load "dsl.cmo";;
#load "rr.cmo";;
*)
open Higher;;
open Dsl;;
open Rr;;

(* Annotate! With available static knowledge *)

(* The static knowledge here is binary connective *)

(*
 *)

type connector = CAnd | COr
let flip_conn = function
  | CAnd -> COr
  | COr  -> CAnd

module DNDown(F:SYM) = struct
  module X = struct
    type 'a from = 'a F.repr
          (* Each optimization has its own term type suitable for it.
           *)
    type 'a term = 
      | Unk : 'a from -> 'a term         (* no annotation *)
      | Con : connector * bool from * bool from -> bool term
    let fwd x = Unk x                    (* generic reflect*)
    let bwd : type a. a term -> a from = function
      | Unk e -> e
      | Con (CAnd,e1,e2) -> F.an_ e1 e2
      | Con (COr, e1,e2) -> F.or_ e1 e2
  end
  include X
  include Trans_def(X)
  module IDelta = struct
    (* a bit contrived: could have eliminated the negation right here *)
    let neg = function
      | Unk e -> Unk (F.neg e)
      | Con (c,e1,e2) -> Con (flip_conn c, F.neg e1, F.neg e2)
    let an_ e1 e2 = Con (CAnd,bwd e1,bwd e2)
    let or_ e1 e2 = Con (COr,bwd e1,bwd e2)
  end
end

(* Why this is not a deep encoding?
 *)

(* Combine the optimization with the base interpreter 
*)
module PNDownW(F:SYMW) = struct
  module OptM  = DNDown(F)
  include SYMTW(OptM)(F)
  include OptM.IDelta       (* overriding int and add in SYMT *)
end

let obsNDown = fun (type obs) e ((module F):obs symw) -> 
  e ((module PNDownW(F)): obs symw)

let exnn = fun (type obs) ((module I):obs symw) -> let open I in observe @@
  neg @@ an_ (neg (neg wire_x)) wire_y

let _ = view exnn

let _ = view (obsNDown exnn)

let _ = view exc1
let _ = view (obsNDown exc1)
(* Why not down all the way? *)


let _ = view (obsNDown (obsNDown exc1))
(* They compose! *)

let _ = view (obsNDown (obsNDown (obsNDown exc1)))
(* There is a double negation, in a form where it can be eliminated *)

