open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)(Tm)

module type StringS = sig
  val value : string
end

module Filtration : sig
  (* Data needed to define a filtration *)
  module type MakerS = sig
    val min : int
    val max : int
    val ctx : int -> ctx
    val v : int -> Var.t
  end

  (* Data of the filtration *)
  module type S = sig
    include MakerS

    val sub : int -> sub
    val v_constr : int -> constr
    val src_v : int -> constr
    val tgt_v : int -> constr
    val v_plus : int -> Var.t
    val v_bridge : int -> Var.t
    val in_plus : int -> sub
    val in_minus : int -> sub
  end

  module Make (_ : MakerS) : S
end

module Padding : sig
  module type PaddingDataS = sig
    val p : int -> Tm.t
    val q : int -> Tm.t
  end

  module type PaddedS = sig
    val padded : int -> Tm.t
  end

  module type CanonicalPaddingDataArgsS = sig
    val ps : int -> ps
    val p_src : int -> constr
    val q_tgt : int -> constr
    val p_inc : int -> constr list
    val q_inc : int -> constr list
    val pad_in_ps : int -> sub
  end

  module type MakerS = sig
    module F : Filtration.S
    module D : PaddingDataS
    module P : PaddedS

    val name : string
  end

  module type S = sig
    include MakerS

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

  module Make (_ : MakerS) : S

  module type MakerCanonicalS = sig
    module F : Filtration.S
    module D : CanonicalPaddingDataArgsS

    val name : string
  end

  module MakeCanonical (_ : MakerCanonicalS) : S
end

module type FiltrationMorphismS = sig
  val sub : int -> sub
  val name : string
end

module PaddingApp (_ : Filtration.S) (_ : FiltrationMorphismS) (_ : Padding.S) :
  Padding.S

module Suspend (_ : Padding.S) : Padding.S

module Repadding : sig
  module type RepaddingDataS = sig
    val f : int -> Tm.t
    val g : int -> Tm.t
  end

  module type RepaddedS = sig
    val repad : int -> Tm.t
  end

  module type CanonicalRepaddingDataArgsS = sig
    val ps : int -> ps
    val incl : int -> constr list
  end

  module type MakerS = sig
    module P1 : Padding.S
    module P2 : Padding.S
    module D : RepaddingDataS
    module R : RepaddedS

    val name : string
  end

  module type S = sig
    include MakerS

    val repadded : Tm.t
    val f : Tm.t
    val g : Tm.t
  end

  module Make (_ : MakerS) : S

  module type MakerCanonicalS = sig
    module P1 : Padding.S
    module P2 : Padding.S
    module D : CanonicalRepaddingDataArgsS

    val name : string
  end

  module MakeCanonical (_ : MakerCanonicalS) : S
end
