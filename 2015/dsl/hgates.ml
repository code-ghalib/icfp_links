(* Extending the language: making it higher-order *)


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

(* Now the types of repr really come into play
 * If ``bool repr'' was a wire, think of
 * ``(bool -> bool) repr'' as a circuit with one input and one output
 * Then app is an operation to connect circuits
*)

module type SYMHO = sig
  include SYM
  val lam : ('a repr -> 'b repr) -> ('a -> 'b) repr
  val app : ('a -> 'b) repr -> ('a repr -> 'b repr)
end


(* The signatures of lam and app look like the typing rules of STLC
 * We embed not only syntax, but also the typing rules!
 *)

type 'obs symho = (module SYMHO with type obs = 'obs)

let ehadd3 = fun (type obs) ((module I):obs symho) -> 
   let module X = XOR(I) in let open X in let open I in observe @@
   lam @@ fun x -> lam @@ fun y -> lam @@ fun z ->
    xor (xor x y) z

(* Inferred type? *)


let ehadd3t = fun (type obs) ((module I):obs symho) -> 
   let module X = XOR(I) in let open X in let open I in observe @@
   lam @@ fun x -> lam @@ fun y -> 
   let ehadd3 = 
     (lam @@ fun x -> lam @@ fun y -> lam @@ fun z -> xor (xor x y) z) in
   let (%@) f x = app f x in
   ehadd3 %@ x %@ y %@ (lit true)

(* Check the inferred type
 *)


(* // *)
(* Extending the earlier interpreters (merely extending!) *)

module RHO = struct
  include R
  let lam f   = f
  let app f x = f x
end

(* Old expressions can be interpreted with the new interpreter *)
let evalHO e = N_id.prj @@ e @@ ((module RHO) : RHO.obs symho)

let true = N_id.prj @@ ex1 @@ (module RHO)  (* XXX *)

let _ = evalHO ehadd3

let false = (evalHO ehadd3) true false true

let false = (evalHO ehadd3t) true false


(* // *)
module SHO = struct
  include S
  
  let app f x = fun p -> paren (p>10) @@ f 10 ^ " " ^ x 11

  let varnames = "xyzuvw"
  let varname = function
    | i when i < String.length varnames -> 
        String.make 1 @@ varnames.[i]
    | i -> "x" ^ string_of_int i

  let counter = ref 0
  let gensym () = let v = !counter in incr counter; v

  let lam f    = fun p -> 
                   let v  = varname @@ gensym () in
                   let body = f (fun prec -> v) 0 in
                   paren (p > 0) ("L" ^ v ^ ". " ^ body)

  let observe e = counter := 0; S.observe e
end

let viewHO e = N_string.prj @@ e @@ ((module SHO) : SHO.obs symho)

(* // *)

let _ = viewHO ehadd3


let _ = viewHO ehadd3
(* 
  check that is idempotent 
 *)

let _ = viewHO ehadd3t


(* And now we can do transformations *)

(* Extend the non-systematic transformation *)
module TCPHO(I:SYMHO) = struct
  include Bconst_prop.TCP(I)
  let app : type a b. (a -> b) repr -> a repr -> b repr = fun f x ->
    match f with
    | Unk f -> Unk (I.app f (dyn x))
    (* No other cases. Why? *)
  let lam f = Unk (I.lam (fun x -> dyn (f (Unk x)))) 
end

let obscpHO = fun (type obs) e ((module F):obs symho) -> 
  e ((module TCPHO(F)): obs symho)

module SYMTHO(X:Trans)(F:SYMHO with type 'a repr = 'a X.from) = struct
  open X
  include SYMT(X)(F)
  let app x y = map2 F.app x y
  let lam f   = fwd (F.lam (fun x -> bwd (f (fwd x))))
end

(* Re-using Bneg_double.DN2N pass as it was *)
module PN2NHO(F:SYMHO) = struct
  module OptM  = Bneg_double.DN2N(F)
  include SYMTHO(OptM)(F)
  include OptM.IDelta       (* overriding int and add in SYMT *)
end

let obsN2NHO = fun (type obs) e ((module F):obs symho) -> 
  e ((module PN2NHO(F)): obs symho)

module PNDownHO(F:SYMHO) = struct
  module OptM  = Bneg_down.DNDown(F)
  include SYMTHO(OptM)(F)
  include OptM.IDelta       (* overriding int and add in SYMT *)
end

let obsNDownHO = fun (type obs) e ((module F):obs symho) -> 
  e ((module PNDownHO(F)): obs symho)

let _ = viewHO (obsNDownHO ehadd3)

let chainHO e = 
  obscpHO @@ obsNDownHO @@ obsN2NHO @@ e

let rec ntimes : int -> ('a -> 'a) -> ('a -> 'a) = fun n tr ->
  fun e -> if n = 0 then e else ntimes (n-1) tr (tr e)

let _ = viewHO (ntimes 3 obsNDownHO @@ ehadd3)

let _ = viewHO (ntimes 5 chainHO @@ ehadd3)

let false = evalHO (ntimes 5 chainHO @@ ehadd3) true false true



let _ = viewHO (ntimes 5 chainHO ehadd3t)

(* But here we are not too successful: there is an application
 * to True. We should enhance our PE to do known applications as well.
 *)

(* HO optimizations: applying a statically-known function *)

module DStaticApp(F:SYMHO) = struct
  module X = struct
    type 'a from = 'a F.repr
          (* This is not a recursive type ! *)
    type 'a term = 
      | Unk : 'a from -> 'a term
            (* statically-known function *)
      | Fun : ('a term -> 'b term) -> ('a -> 'b) term
    let fwd x = Unk x
    let rec bwd : type a. a term -> a from = function
      | Unk x -> x
      | Fun f -> F.lam (fun x -> bwd (f (fwd x)))
  end
  include X
  include Trans_def(X)
  module IDelta = struct
   let lam f = Fun f
   let app: ('a->'b) term -> 'a term -> 'b term = fun f x ->
   match f with
   | Fun ff -> ff x
   | _      -> Unk (F.app (bwd f) (bwd x))
 end
end

module PStaticApp(F:SYMHO) = struct
  module OptM  = DStaticApp(F)
  include SYMTHO(OptM)(F)
  include OptM.IDelta
end

let appHO = fun (type obs) e ((module F):obs symho) -> 
  e ((module PStaticApp(F)): obs symho)

let _ = viewHO @@ appHO @@ (ntimes 5 chainHO ehadd3t)

let _ = viewHO @@ ntimes 5 chainHO @@ appHO @@ (ntimes 5 chainHO ehadd3t)

