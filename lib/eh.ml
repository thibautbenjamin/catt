open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)
open Std
open Builtin

let char_sub tm ty = 
  let char_sub_type = function
  | Obj -> []
  | Arr(common_ty,tm1,tm2) -> (tm2,false) :: (tm1,false) :: char_sub_type common_ty
in (tm,true) :: char_sub_type ty

let id_n_x = function
  | 0 -> Var (Name "x")
  | n -> Coh (id(),char_sub (id_n_x (n-1)) (id_n_x_type (n-1)))
and id_n_x_type = function
  | 0 -> Obj
  | n -> Arr(id_n_x_type (n-1),id_n_x (n-1),id_n_x (n-1))

let idcomp n k = 

let gamma i l = [(Name "x",(Obj,false)) ; (Name "v_" ^ string_of_int i ^ "_" ^ string_of_int l,(Arr(,,),))]