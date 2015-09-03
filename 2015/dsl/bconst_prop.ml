(* Boolean constant propagation *)

(* 
#load "higher.cmo";;
#load "dsl.cmo";;
*)
open Higher;;
open Dsl;;

(* Previously we have dealt with evaluators 
   Can we write transformers?
*)

(* Task: propagating boolean constants
     Neg True -> False, Neg False -> True
     And True x -> x, And False x ->False
     Or  True x ->True, Or False x -> x
*)

(* A dummy transformer:
 * an interpreter
 *)

(* Interpret an expression by redirecting to another interpreter
*)

module T0(I:SYM) = struct
  type 'a repr = 'a I.repr
  type obs = I.obs

  let lit = I.lit
  let neg = I.neg
  let an_ = I.an_
  let or_ = I.or_

  let observe = I.observe
end

module T0W(I:SYMW) = struct
  include T0(I)
  let wire_x = I.wire_x
  let wire_y = I.wire_y
  let wire_z = I.wire_z
end

(* // *)
(* Partial evaluation *)
(* Constant propogation -> propogate the known information during comiplation*)
(* Annotated expressions
 * Now we annotate expressions with what is known about them statically
 * Unk: nothing is known statically;
 * Lit: statically known value
 *)

(* Like T0, but using the static knowledge where available *)
module TCP(I:SYM) = struct
    (*Rules of boolean specification - if you know something, how to propogate
     * or simiplify for 1 single level (note this is not recursive)*)
  type 'a repr =
    | Unk : 'a I.repr -> 'a repr
    | Lit : bool -> bool repr
  type obs = I.obs

  (* Erasing annotations *)
  (* When deconstructing GADT, type annotations are required *)
  let dyn : type a. a repr -> a I.repr = function
    | Unk e -> e
    | Lit x -> I.lit x

  let lit x = Lit x             (* full static knowledge *)

  let neg = function
    | Unk e -> Unk (I.neg e)
    | Lit x -> Lit (not x)

  let an_ x y = match (x,y) with
  | (Lit true,e)   | (e, Lit true)  -> e
  | (Lit false, _) | (_, Lit false) -> Lit false
  | (Unk e1, Unk e2) -> Unk (I.an_ e1 e2) 

  let or_ x y = match (x,y) with
  | (Lit true,_)   | (_, Lit true)  -> Lit true
  | (Lit false, e) | (e, Lit false) -> e
  | (Unk e1, Unk e2) -> Unk (I.or_ e1 e2) 

  let observe x = I.observe (dyn x)
end

(* When do Unk things occur? *)
module TCPW(I:SYMW) = struct
  include TCP(I)
  let wire_x = Unk I.wire_x
  let wire_y = Unk I.wire_y
  let wire_z = Unk I.wire_z
end

(*
 * The Unk lines look like those in the dummy transformer T0
 * (deal with un-annotated values)
 *)


let exc1_eval = N_id.prj @@ exc1 @@ (module RW)

let exc1_view = view exc1

let obscp = fun (type obs) e ((module I):obs symw) -> 
  e ((module TCPW(I)) : obs symw)

let exc1_cp_eval = N_id.prj @@ (obscp exc1) @@ (module RW)

let exc1_cp_view = N_string.prj @@ (obscp exc1) @@ (module SW)

let exc1_cp d = obscp exc1 d  (* For future reference *)

(* Transformer of tagless-final expressions as transformer of
   interpreters!
 *)

(* Lots of boilerplate (dealing with Unk) *)
(* Always can add no annotation (Unk), always can erase annotations
 * We now capture the pattern
 *)
