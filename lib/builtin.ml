open Kernel
open Kernel.Unchecked_types

module Memo = struct
  let tbl = Hashtbl.create 97

  let find i f =
    try Hashtbl.find tbl i with
    | Not_found ->
      let res = f i in
      Hashtbl.add tbl i res;
      res

  let id = check_coh (Cohdecl (Br[], Arr(Obj,Var(Db 0),Var(Db 0)),"builtin_id")) []
end

let comp_arity s =
  let n = List.length s in
  if !Settings.explicit_substitutions then
    (n-1)/2
  else n

let rec comp_ps i =
  match i with
  | i when i <= 0 -> Error.fatal "builtin composition with less than 0 argument"
  | i when i = 1 -> Br [Br[]]
  | i ->
    match comp_ps (i-1) with
    | Br l -> Br (Br[] :: l)

let comp_ty i =
  Arr(Obj, Var(Db 0), Var (Db (2*i-1)))

let comp s =
  let arity = comp_arity s in
  let build_comp i =
    let ps = comp_ps i in
    let ty = comp_ty i in
    check_coh (Cohdecl (ps,ty, "builtin_comp")) []
  in
  Memo.find arity build_comp

let id = Memo.id
