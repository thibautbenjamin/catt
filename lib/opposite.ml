open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)

let rec op_data_to_string = function
  | [] -> ""
  | [ i ] -> Printf.sprintf "%i" i
  | i :: l -> Printf.sprintf "%i,%s" i (op_data_to_string l)

let ps ps op_data =
  let rec level i ps =
    match ps with
    | Br [] -> Br []
    | Br l when List.mem (i + 1) op_data ->
        let l = List.map (level (i + 1)) l in
        Br (List.rev l)
    | Br l -> Br (List.map (level (i + 1)) l)
  in
  level 0 ps

let equiv_op_ps ps op_data =
  let rec level i ps =
    match ps with
    | Br [] -> [ (Var (Var.Db 0), true) ]
    | Br l ->
        let components = List.map (fun p -> level (i + 1) p) l in
        if List.mem (i + 1) op_data then
          Unchecked.opsuspwedge_subs_ps components l
        else Unchecked.suspwedge_subs_ps components l
  in
  level 0 ps

let op_pp_data pp_data op_data =
  let name = Unchecked.full_name pp_data in
  let name = Printf.sprintf "%s_op{%s}" name (op_data_to_string op_data) in
  (name, 0, [])

let rec ty typ op_data =
  let d = Unchecked.dim_ty typ in
  match typ with
  | Obj -> Obj
  | Arr (a, t, u) ->
      let a = ty a op_data in
      let t = tm t op_data in
      let u = tm u op_data in
      if List.mem d op_data then Arr (a, u, t) else Arr (a, t, u)
  | Meta_ty m -> Meta_ty m

and tm t op_data =
  match t with
  | Var x -> Var x
  | Coh (c, s) ->
      let p, _, _ = Coh.forget c in
      let equiv = equiv_op_ps p op_data in
      let c = coh c op_data equiv in
      let op_s = sub (Unchecked.sub_ps_to_sub s) op_data in
      let s' = Unchecked.sub_ps_apply_sub equiv op_s in
      Coh (c, s')
  | App (t, s) ->
      let op_t, _ =
        Tm.apply
          (fun c -> ctx c op_data)
          (fun t -> tm t op_data)
          (fun pp_data -> op_pp_data pp_data op_data)
          t
      in
      let op_s = sub s op_data in
      let op_s = Unchecked.(sub_ps_to_sub (sub_to_sub_ps op_s)) in
      App (op_t, op_s)
  | Meta_tm m -> Meta_tm m

and sub s op_data =
  match s with
  | [] -> []
  | (x, (t, e)) :: s -> (x, (tm t op_data, e)) :: sub s op_data

and coh c op_data equiv =
  Coh.apply_ps
    (fun p -> ps p op_data)
    (fun t ->
      Unchecked.ty_sub_preimage (ty t op_data) (Unchecked.sub_ps_to_sub equiv))
    (fun pp -> op_pp_data pp op_data)
    c

and ctx c op_data =
  match c with
  | [] -> []
  | (x, (t, e)) :: c ->
      let t = ty t op_data in
      let c = ctx c op_data in
      (x, (t, e)) :: c

let coh c op_data =
  let ps, _, _ = Coh.forget c in
  let equiv = equiv_op_ps ps op_data in
  coh c op_data equiv

let tm t op_data =
  Io.info ~v:3 (lazy ("computing opposite of term " ^ Unchecked.tm_to_string t));
  let t = tm t op_data in
  Io.info ~v:4 (lazy ("opposite computed: " ^ Unchecked.tm_to_string t));
  t

let checked_tm t op_data =
  let name = Option.map (fun a -> op_pp_data a op_data) (Tm.pp_data t) in
  let c = Tm.ctx t in
  let t = Tm.develop t in
  let c = ctx c op_data in
  let t = tm t op_data in
  check_term (Ctx.check c) ?name t
