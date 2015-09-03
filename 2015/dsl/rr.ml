(* Reflection-Reification pair *)

module type Trans_base = sig
  type 'a from
  type 'a term
  val fwd  : 'a from -> 'a term  (* reflection  *)
  val bwd  : 'a term -> 'a from  (* reification *)
end

(* fwd is generally not surjective and bwd is not injective
 *    bwd . fwd == id,  fwd . bwd /= id
 *)

module type Trans = sig
  include Trans_base
  val map1 : ('a from -> 'b from) -> ('a term -> 'b term)
  val map2 : ('a from -> 'b from -> 'c from) ->
          ('a term -> 'b term -> 'c term)
end



(* Adding mapping functions. Do we need fmap3 etc? (NO)
 * Can we do with less?
*)

module Trans_def(X:Trans_base) = struct
  open X
  let map1 f term        = fwd (f (bwd term))
  let map2 f term1 term2 = fwd (f (bwd term1) (bwd term2))
end

(* QUIZ *)
(* map1 looks like fmap of a Functor. Can it be defined or related
   to Functor?
 *)

(* The default, generic optimizer
   Concrete optimizers are built by overriding the interpretations
   of some DSL forms.
*)
(* Naming conventions:
 *  I  - symantics (interpreter)
 *  F  - source
 *  X  - transformer
 *  P  - optimization pass
 *  O  - data for the optimization pass
 *  e  - expression
 *)

open Basic_gates

module SYMT(X:Trans)(F:SYM with type 'a repr = 'a X.from) = struct
  open X
  type 'a repr = 'a term
  type obs = F.obs
  let lit x = fwd (F.lit x)
  let neg e = map1 F.neg e
  let an_   = map2 F.an_
  let or_   = map2 F.or_
  let observe e = F.observe (bwd e)
end

module SYMTW(X:Trans)(F:SYMW with type 'a repr = 'a X.from) = struct
  include SYMT(X)(F)
  let wire_x = X.fwd F.wire_x
  let wire_y = X.fwd F.wire_y
  let wire_z = X.fwd F.wire_z
end

