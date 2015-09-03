(* Conversion to the disjunctive normal form *)


(*
   (L1 OR L2 ...) AND ...
*)

(* 
#load "higher.cmo";;
#load "dsl.cmo";;
#load "rr.cmo";;
#load "bconst_prop.cmo";;
#load "bneg_double.cmo";;
#load "hgates.cmo";;
*)
open Higher;;
open Dsl;;
open Rr;;
open Hgates;;


(* Assume that negation has alfready been pushed down *)

module DCNF(F:SYM) = struct
  module X = struct
    type 'a from = 'a F.repr
    type 'a term = 
      | Unk : 'a from -> 'a term         (* no annotation *)
      | OR  :  bool from * bool from -> bool term
      | AND :  bool from * bool from -> bool term
    let fwd x = Unk x                    (* generic reflect*)
    let bwd : type a. a term -> a from = function
      | Unk e -> e
      | AND (e1,e2) -> F.an_ e1 e2
      | OR  (e1,e2) -> F.or_ e1 e2
  end
  include X
  include Trans_def(X)
  module IDelta = struct
    let rec or_ e1 e2 = match (e1,e2) with
    | (AND (e1,e2),e) -> AND (bwd (or_ (fwd e1) e), bwd (or_ (fwd e2) e))
    | (e,AND (e1,e2)) -> AND (bwd (or_ e (fwd e1)), bwd (or_ e (fwd e2)))
    | (e1,e2)         -> OR (bwd e1, bwd e2)
    let an_ e1 e2 = AND (bwd e1,bwd e2)
  end
end

module PCNF(F:SYMHO) = struct
  module OptM  = DCNF(F)
  include SYMTHO(OptM)(F)
  include OptM.IDelta       (* overriding int and add in SYMT *)
end

let cnfHO = fun (type obs) e ((module F):obs symho) -> 
  e ((module PCNF(F)): obs symho)


let ecnf1 = fun (type obs) ((module I):obs symho) -> 
   let module X = XOR(I) in let open X in let open I in observe @@
   lam @@ fun x -> lam @@ fun y -> lam @@ fun z -> lam @@ fun u ->
    or_ x (an_ y (or_ z u))

let _ = viewHO ecnf1

let _ = viewHO (cnfHO ecnf1)

let _ = viewHO (ntimes 5 chainHO @@ ehadd3)

let _ = viewHO @@ cnfHO @@ (ntimes 5 chainHO @@ ehadd3)

let _ = viewHO @@ ntimes 5 cnfHO @@ (ntimes 5 chainHO @@ ehadd3)

;;

