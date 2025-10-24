open Common

module Make
    (Theory : Theory.S)
    (Sub : sig
      type t
    end)
    (PS : sig
      type t

      val source : t -> Sub.t
      val target : t -> Sub.t
    end)
    (Tm : sig
      type t

      val preimage : t -> Sub.t -> t
      val contains_all_vars : t -> bool
    end)
    (Ty : sig
      type t

      val dim : t -> int
      val retrieve_arrow : t -> Tm.t * Tm.t
      val contains_all_vars : t -> bool
    end) =
struct
  type res = Inv | NonInv of Tm.t * Tm.t | No

  let check ps t =
    let needs_check =
      match Theory.theory.invertibility with
      | None -> true
      | Some d when d >= Ty.dim t -> true
      | _ -> false
    in
    if (not needs_check) || Ty.contains_all_vars t then Inv
    else
      try
        let src, tgt = Ty.retrieve_arrow t in
        let src_inclusion = PS.source ps in
        let src = Tm.preimage src src_inclusion in
        if not (Tm.contains_all_vars src) then No
        else
          let tgt_inclusion = PS.target ps in
          let tgt = Tm.preimage tgt tgt_inclusion in
          if not (Tm.contains_all_vars tgt) then No else NonInv (src, tgt)
      with NotInImage -> No
end
