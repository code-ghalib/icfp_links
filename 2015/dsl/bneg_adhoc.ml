(* Demonstrating `non-compositional', context-sensitive processing
   One step of normalization: pushing negation towards literals
 *)

(*
 * When I first mentioned the initial and final styles in passing
 * in July 2009 in Oxford, one Oxford professor said:
 * ``Isn't it bloody obvious that you can't pattern-match in the final
 * style?''
 * The answer: it isn't bloody and it isn't obvious and it is not
 * impossible to pattern-match in the final style.
 *)

(* 
#load "higher.cmo";;
#load "dsl.cmo";;
*)
open Higher;;
open Dsl;; 

(* Pushing negation down 
 *)

(*RK: this may be wrong, just look at the TNegDown below
  The nested pattern-matching establishes a context:
   push_neg (Neg Lit) -> Neg Lit
   push_neg Lit       -> Neg Lit
   push_neg Neg (And x y) -> Or  (Neg x) (Neg y)
   push_neg Neg (Or x y)  -> And (Neg x) (Neg y)
*)

(* // *)
(* 
 *)

(* Tagless transformer 
 *)

module TNegDown(I:SYM) = struct
  type ctx = Pos | Neg
  type 'a repr = ctx -> 'a I.repr
  type obs = I.obs

  let lit x = function
    | Pos -> I.lit x
    | Neg -> I.lit (not x)

  let neg e = function 
    | Pos -> e Neg
    | Neg -> e Pos

  let an_ e1 e2 = function 
    | Pos -> I.an_ (e1 Pos) (e2 Pos) (* homomorhism *)
    | Neg -> I.or_ (e1 Neg) (e2 Neg)

  let or_  e1 e2 = function
    | Pos -> I.or_ (e1 Pos) (e2 Pos) (* homomorhism *)
    | Neg -> I.an_ (e1 Neg) (e2 Neg)

  let observe x = I.observe (x Pos)  (* Initial context *)
end

(* QUIZ
 * How to prove correctness? 
 *)

module TNegDownW(I:SYMW) = struct
  include TNegDown(I)
  let wire_x = function
    | Pos -> I.wire_x
    | Neg -> I.neg I.wire_x
  let wire_y = function
    | Pos -> I.wire_y
    | Neg -> I.neg I.wire_y
  let wire_z = function
    | Pos -> I.wire_z
    | Neg -> I.neg I.wire_z
end

let push_neg = fun (type obs) e ((module I):obs symw) -> 
  e ((module TNegDownW(I)) : obs symw)

(* // *)
(*
 * To remind, here is our sample term
 *)

let ex2N = fun (type obs) ((module I):obs symw)-> 
  let open I in observe @@
     (neg @@ an_ (lit true) (neg wire_x))

let ex2N_eval = N_id.prj @@ ex2N @@ (module RW)
let ex2N_view = view ex2N

(* eta-expansion *)
let ex2N_nneg d = push_neg ex2N d

(*
 * The new expression can be evaluated with any interpreter
 * The result of the standard evaluation (the `meaning') is preserved
 *)
let ex2N_nneg_eval = N_id.prj @@ ex2N_nneg @@ (module RW)
let ex2N_nneg_view = view ex2N_nneg

let exadd2_nneg d = push_neg exadd2 d
let exadd2_nneg_view = view exadd2_nneg
let exadd2_nneg_eval = N_id.prj @@ ex2N_nneg @@ (module RW)

