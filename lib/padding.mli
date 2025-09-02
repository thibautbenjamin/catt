open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)(Tm)

module Filtration : sig
  (* Data defining a filtration *)
  module type DataS = sig
    val min : int
    val max : int
    val ctx : int -> ctx
    val v : int -> Var.t
  end

  (* Functions relative to a filtration *)
  module type S = sig
    include DataS

    val sub : int -> sub
    val v_constr : int -> constr
    val src_v : int -> constr
    val tgt_v : int -> constr
    val v_plus : int -> Var.t
    val v_bridge : int -> Var.t
    val in_plus : int -> sub
    val in_minus : int -> sub
  end

  module Make (_ : DataS) : S
end

module type PaddingDataS = sig
  val p : int -> Tm.t
  val q : int -> Tm.t
end

module type PaddedS = sig
  val padded : int -> Tm.t
end

module Padded (F : Filtration.S) (D : PaddingDataS) : PaddedS

module type CanonicalPaddingDataArgsS = sig
  val ps : int -> ps
  val p_src : int -> constr
  val q_tgt : int -> constr
  val p_inc : int -> constr list
  val q_inc : int -> constr list
  val pad_in_ps : int -> sub
end

module CanonicalPaddingData
    (F : Filtration.S)
    (Args : CanonicalPaddingDataArgsS)
    (P : PaddedS) : PaddingDataS

module Padding : sig
  module type DataS = sig
    module F : Filtration.S
    module D : PaddingDataS
    module P : PaddedS
  end

  module type S = sig
    include DataS

    val ctx : ctx
    val v : Var.t
    val v_constr : constr
    val v_plus : Var.t
    val v_bridge : Var.t
    val p : Tm.t
    val q : Tm.t
    val padded : Tm.t
    val padded_func : int -> int -> Tm.t
  end

  module Make (_ : DataS) : S

  module type CanonicalDataS = sig
    module F : Filtration.S
    module D : CanonicalPaddingDataArgsS
  end

  module MakeCanonical (A : CanonicalDataS) : S
end

(* module Padding (F : Filtration.S) (D : PaddingDataS) (P : PaddedS) : PaddingS *)

module type FiltrationMorphismS = sig
  val sub : int -> sub
end

module PaddingApp
    (Tgt : Filtration.S)
    (M : FiltrationMorphismS)
    (P : Padding.S) : Padding.S

module type RepaddingDataS = sig
  val f : int -> Tm.t
  val g : int -> Tm.t
end

module type RepaddedS = sig
  val repad : int -> Tm.t
end

module Repadded (P1 : Padding.S) (P2 : Padding.S) (D : RepaddingDataS) :
  RepaddedS

module type CanonicalRepaddingDataArgsS = sig
  val ps : int -> ps
  val incl : int -> constr list
end

module CanonicalRepaddingData
    (Args : CanonicalRepaddingDataArgsS)
    (P1 : Padding.S)
    (P2 : Padding.S)
    (R : RepaddedS) : RepaddingDataS

module Repadding : sig
  module type DataS = sig
    module P1 : Padding.S
    module P2 : Padding.S
    module D : RepaddingDataS
    module R : RepaddedS
  end

  module type S = sig
    include DataS

    val repadded : Tm.t
    val f : Tm.t
    val g : Tm.t
  end

  module Make (_ : DataS) : S
end

(* OLD API -- Should be removed ultimately *)
val pad : constr -> constr -> Tm.t -> Var.t -> sub -> constr

val repad :
  constr ->
  constr ->
  constr ->
  constr ->
  constr ->
  constr ->
  Tm.t ->
  sub ->
  sub ->
  Var.t ->
  sub ->
  constr

val repad_old :
  constr ->
  constr ->
  constr ->
  constr ->
  constr ->
  constr ->
  constr ->
  sub ->
  sub ->
  Var.t ->
  sub ->
  constr
