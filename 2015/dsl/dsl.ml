(* Basic gates and circuits *)

(* Higher-kinded programming in OCaml, as described in
   Lightweight Higher-Kinded Polymorphism
   Jeremy Yallop and Leo White
   Functional and Logic Programming 2014
*)

(* 
#load "higher.cmo";;
*)
open Higher;;


(* Define the syntax of circuits (in the form close to BNF)
 * Read  ``bool repr'' as a wire
*)

module type SYM = sig
  type 'a repr
  type obs

  val lit : bool -> bool repr
  val neg : bool repr -> bool repr
  val an_ : bool repr -> bool repr -> bool repr
  val or_ : bool repr -> bool repr -> bool repr

  val observe : 'a repr -> ('a,obs) app
end

(* 
*)
type 'obs sym = (module SYM with type obs = 'obs)

(*
 
 *)

(* See inferred type, cf Haskell and complain about syntax and boilerplate *)
let ex1 = fun (type obs) ((module I):obs sym) -> let open I in observe @@
  an_ (lit true) (neg (lit false))

(* An alternative
   `Object algebras' (although it was presented at SSGIP in 2010,
   two years before object algebras)

class virtual ['repr,'obs] sym = object 
  method virtual lit : bool -> (bool,'repr) app
  method virtual neg : (bool,'repr) app -> (bool,'repr) app
  method virtual an_ : (bool,'repr) app -> 
                       (bool,'repr) app -> (bool,'repr) app
  method virtual or_ : ((bool,'repr) app as 'x) -> 'x -> 'x

  method virtual observe : 'a. ('a,'repr) app -> ('a,'obs) app
end

*)


(* Boring: all constants. 
*)

module type SYMW = sig
  include SYM
  val wire_x : bool repr
  val wire_y : bool repr
  val wire_z : bool repr
end

type 'obs symw = (module SYMW with type obs = 'obs)


(* check the inferred type! *)

let ex2 = fun (type obs) ((module I):obs symw) -> let open I in observe @@
  an_ (lit true) (neg wire_x)

(* How to get xor? Extend the language again?
*)
module XOR(I:SYM) = struct
  open I
  let xor x y = an_ (or_ x y) (neg (an_ x y))
end

(*
 * simple adder
*)

let exadd2 = fun (type obs) ((module I):obs symw) -> 
   let module X = XOR(I) in let open X in let open I in observe @@
     xor wire_x wire_y

let exadd3 = fun (type obs) ((module I):obs symw) -> 
   let module X = XOR(I) in let open X in let open I in observe @@
     xor (xor wire_x wire_y) wire_z

let exc1 = fun (type obs) ((module I):obs symw) -> 
   let module X = XOR(I) in let open X in let open I in observe @@
    xor wire_x (xor wire_y (lit true))

(* How can we check this is correct?

 *)

(* The structure also defines denotational semantics! Compositional
*)


(* // *)
(* Meta-circular interpreter (usually called R)
   It interprets |'a repr| as just |a|, that is, |bool repr|
   as just OCaml boolean
*)

(* consider an iso-morphism between |'a r| and |('a,rname) app|
 * where
 *  type 'a r = 'a
 *
 *  val inj_r : 'a r -> ('a,rname) app
 *  val prj_r : ('a,rname) app -> 'a r
 *
 * Why we need the iso-morphism? Emulation of higher-kinded polymorphism
 * (see the beginning of this file). 
 *  So, rname is the name of the type constructor r.

 In Yallop and White's `higher', we do 
*)

module N_id = Newtype1(struct type 'a t = 'a end)
(* 
  so that inj_r is spelled N_id.inj and prj_r is spelled N_id.prj
  and rname is spelled N_id.t
*)

(* It is really the metacircular interpreter *)
module R = struct
  type 'a repr = 'a
  type obs = N_id.t
  let lit x = x
  let neg = not
  let an_ = (&&)
  let or_ = (||)

  let observe = N_id.inj 
end

  
let ex1_eval = N_id.prj @@ ex1 @@ (module R)


(* To run ex2, we need an instance of SYMW *)

module RW = struct
  include R
  let wire_x = true
  let wire_y = false
  let wire_z = true
end

(* What if we use a wrong interpreter

let exadd2_eval = N_id.prj @@ exadd2 @@ (module R)
*)

let exadd2_eval = N_id.prj @@ exadd2 @@ (module RW)



(* QUIZ *)
(* The SymW instance had constant values. What if we want different
   values?
 Compare with Haskell and discuss trade-offs
Ans: before we had
'a repr = 'a
we can make it instead
'a repr = env -> 'a (* reader monad: env*)

or use first class modules as below - use first class module to say take a new
module with wire_x = some value
*)



let exadd2_eval = N_id.prj @@ exadd2 @@ (module struct include RW
  let wire_x = false end)
(* get values at runtime*)
let exadd2_eval_rt x y z = N_id.prj @@ exadd2 @@ (module struct include RW
  let wire_x = x let wire_y = y let wire_z = z end)

(* // *)
(* Another interpreter, to show the circuit *)

(* 
 Interpret |a repr| as a string, regardless of the type |a|
*)

module N_string = Newtype1(struct type 'a t = string end)

module S0 = struct
  type 'a repr = string
  type obs = N_string.t

  let paren : string -> string = fun x -> "(" ^ x ^ ")"
 
  let lit x = if x then "tt" else "ff"
  let neg x   = "~" ^ x (* doesn't negate, just shows it as the negation *)
  let an_ x y = paren @@ x ^ " && " ^ y
  let or_ x y = paren @@ x ^ " || " ^ y

  let observe = N_string.inj
end

let ex1S = N_string.prj @@ ex1 @@ (module S0)

module SW0 = struct
  include S0
  let wire_x = "X"
  let wire_y = "Y"
  let wire_z = "Z"
end

let exadd2_view = N_string.prj @@ exadd2 @@ (module SW0)
let exadd3_view = N_string.prj @@ exadd3 @@ (module SW0)

(* View the type of these values to see it interpreted as string *)

(* Is it clear that xor was a macro? *)

(* QUIZ: How to avoid too many parenthesis?
 *
 * add precedence levels -> or has lowest, and has slightly more, negation has
 * the most
*)


module S = struct
  type prec = int
  type 'a repr = prec -> string
  type obs = N_string.t

  let paren = function
    | true -> fun x -> "(" ^ x ^ ")"
    | _    -> fun x -> x
 
  let lit x   = fun p -> if x then "tt" else "ff"
  let neg x   = fun p -> paren (p>10) @@ "~" ^ (x 11)
  let an_ x y = fun p -> paren (p>4) @@ x 4 ^ " && " ^ y 4
  let or_ x y = fun p -> paren (p>3) @@ x 3 ^ " || " ^ y 3

  let observe x = N_string.inj (x 0)
end

module SW = struct
  include S
  let wire_x = fun _ -> "X"
  let wire_y = fun _ -> "Y"
  let wire_z = fun _ -> "Z"
end

let view e = N_string.prj @@ e @@ ((module SW) : SW.obs symw)

let exadd3_view = view exadd3

(* Simplification is in order! *)

(* QUIZ *)
(* write an interpreter to draw the circuit as a diagram *)

(* How to implement the circuit if we only have NAND gates? 
 * (show two ways, one using normalization)
*)

module type NAND = sig
  type 'a repr
  type obs

  val lit  : bool -> bool repr
  val nand : bool repr -> bool repr -> bool repr

  val observe : 'a repr -> ('a,obs) app
end

type 'obs nand = (module NAND with type obs = 'obs)

(* Interpret one language as another language in terms of just NAND gates ->
    * it's a transpiler now  - instead of transforming the language, transform
    * the interpreters *)

module TNAND(I:NAND) = struct
  type 'a repr = 'a I.repr
  type obs = I.obs

  let lit = I.lit
  let neg x   = I.nand x x
  let an_ x y = neg (I.nand x y)
  (* neg (neg (or x y)) = neg (and (neg x) (neg y)) *)
  let or_ x y = I.nand (neg x) (neg y)

  let observe = I.observe
end

let ex1S = N_string.prj @@ ex1 @@ (module S)

let ex1_nand = fun (type obs) ((module I):obs nand) -> 
  ex1 (module TNAND(I))


module SN = struct
  include S
  let nand x y = fun p -> paren (p>3) @@ x 3 ^ " // " ^ y 3
end

let ex1S = N_string.prj @@ ex1_nand @@ (module SN)

(* What about the wires? 
 * Monkey-patching
*)

module type NANDW = sig
  include NAND
  val wire_x : bool repr
  val wire_y : bool repr
  val wire_z : bool repr
end

type 'obs nandw = (module NANDW with type obs = 'obs)

let exadd3_nand = fun (type obs) ((module I):obs nandw) -> 
  exadd3(module (struct include TNAND(I) 
                    let wire_x = I.wire_x 
                    let wire_y = I.wire_y 
                    let wire_z = I.wire_z end))

(*
 * more monkey-patching: cf. local instances
 *)

let exadd3_nand_view = N_string.prj @@ exadd3_nand @@ 
   (module (struct include SW let nand = SN.nand end))


;;
