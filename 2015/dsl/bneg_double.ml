(* Double-negation elimination 
 *  _systematically_
 *)

(* 
#load "higher.cmo";;
#load "dsl.cmo";;
#load "rr.cmo";;
*)
open Higher;;
open Dsl;;
open Rr;;

(* Our Constant Propagator was a partial _evaluator_, a fold.
 * Can we use the approach for something that clearly is not
 * a fold?
 *)


(* Here we implement double-negation elimination
 * (in electrical sense):
 *    neg (neg e) ---> e
 * It is a context-sensitive re-writing, and so is not a fold,
 * on the surface of it
 *)

(* // *)
(*
 * Annotate! with available static knowledge
 * Here, annotate terms with the context in which they occur
 *)

module DN2N(F:SYM) = struct
  module X = struct
    type 'a from = 'a F.repr
          (* Each optimization has its own term type suitable for it.
           *)
    type 'a term = 
      | Unk : 'a from -> 'a term         (* no annotation *)
      | Neg : bool from -> bool term     (* it is a negation *)
    let fwd x = Unk x                    (* generic reflect*)
    let bwd : type a. a term -> a from = function
      | Unk e -> e
      | Neg e -> F.neg e
  end
  include X
  include Trans_def(X)
  module IDelta = struct
      (* Now, the optimization is programmed as overriding neg
         to perform non-standard evaluation.
       *)
    let neg = function
      | Unk e -> Neg e    (* we statically know we negated *)
      | Neg e -> Unk e
  end
end

(* Combine the optimization with the base interpreter 
*)
module PN2NW(F:SYMW) = struct
  module OptM  = DN2N(F)
  include SYMTW(OptM)(F)
  include OptM.IDelta       (* overriding int and add in SYMT *)
end

let obsN2N = fun (type obs) e ((module F):obs symw) -> 
  e ((module PN2NW(F)): obs symw)

let exnn = fun (type obs) ((module I):obs symw) -> let open I in observe @@
  neg @@ neg @@ an_ (neg (neg wire_x)) wire_y

let _ = view exnn

let _ = view (obsN2N exnn)

let _ = view exc1
let _ = view (obsN2N exc1)
(* QUIZ: There is double negation, but it is not eliminated. Why? *)


