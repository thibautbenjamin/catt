open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)

let point_context = [ (Var.Name "x", (Obj, true)) ]
let x = (Var (Var.Name "x"), Obj)
let arr (tm1, ty1) (tm2, _) = Arr (ty1, tm1, tm2)
let constr_to_sub_ps (tm, ty) = (tm, true) :: Unchecked.ty_to_sub_ps ty

let rec id_n = function
  | 0 -> x
  | n ->
      ( Coh
          ( Suspension.coh (Some (n - 1)) (Builtin.id ()),
            constr_to_sub_ps @@ id_n (n - 1) ),
        id_type n )

and id_type = function 0 -> Obj | n -> arr (id_n (n - 1)) (id_n (n - 1))

let test_constr =
  Construct.wcomp (id_n 2) 1 (Construct.wcomp (id_n 2) 1 (id_n 3))
(* Construct.wcomp (id_n 2) 1 (id_n 3) *)

let test =
  let tm, _ = test_constr in
  let checked_ctx = Ctx.check point_context in
  Tm.develop @@ check_term checked_ctx ("test", 0, []) tm
