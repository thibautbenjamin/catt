

let show_instances = true
let abbrev_mode = false

(** Printing of an expression *)                     
let string_of_var = function
  |Name s -> s
  |New (s,k) ->
    if show_instances then s^(Printf.sprintf ".%d" k) else s

let rec to_string e =
  match e.desc with
  |Var x -> string_of_var x
  |Obj -> "*"
  |Arr (t,u,v) ->
    if abbrev_mode && (not e.show)
    then Printf.sprintf "%s -> %s" (to_string u) (to_string v)
    else Printf.sprintf "%s | %s -> %s" (to_string t) (to_string u) (to_string v)
  |Coh (c,e) ->
    Printf.sprintf "coh %s => %s" (string_of_ps c) (to_string e)
  |Sub (e,s) ->
    Printf.sprintf "%s [%s] " (to_string e) (string_of_sub s)
  |Badsub _ -> assert false
and string_of_ps ps =
  match ps with
  |PNil (x,t) -> Printf.sprintf "(%s,%s)" (string_of_var x) (to_string t)
  |PCons(ps,(x1,t1),(x2,t2)) ->
    Printf.sprintf "%s (%s,%s) (%s,%s)" (string_of_ps ps) (string_of_var x1) (to_string t1) (string_of_var x2) (to_string t2)
  |PDrop ps -> Printf.sprintf "%s!" (string_of_ps ps)
and string_of_sub s =
  match s with
  |[] -> ""
  |(x,t)::c -> Printf.sprintf "%s (%s/%s)" (string_of_sub c) (string_of_var x) (to_string t)
