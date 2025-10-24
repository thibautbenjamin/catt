open Common

module Make (Theory : Theory.S) = struct
  open Kernel.Make (Theory)

  module Memo = struct
    let tbl = Hashtbl.create 97

    let find i f =
      try Hashtbl.find tbl i
      with Not_found ->
        let res = f i in
        Hashtbl.add tbl i res;
        res
  end

  let tdb i = Var (Var.Db i)
  let tree i = Br (List.init i (fun _ -> Br []))
  let x i = if i = 0 then (tdb 0, Obj) else (tdb ((2 * i) - 1), Obj)
  let f i = (tdb (2 * i), Arr (Obj, fst @@ x (i - 1), fst @@ x i))

  let comp_n arity =
    let build_comp i =
      let ps = tree i in
      let pp_data = (Printf.sprintf "builtin_comp%i" arity, 0, []) in
      Coh.check_noninv ps (fst (x 0)) (fst (x 0)) pp_data
    in
    Memo.find arity build_comp

  let arity_comp s expl =
    let n = List.length s in
    if expl || !Settings.explicit_substitutions then (n - 1) / 2 else n

  let comp s expl =
    let arity = arity_comp s expl in
    comp_n arity

  let bcomp x y f z g =
    let comp = comp_n 2 in
    let sub = [ (g, true); (z, false); (f, true); (y, false); (x, false) ] in
    Coh (comp, sub)
end
