module List = struct
  include List

  let remove x l =
    filter (fun y -> y <> x) l

  let union l1 l2 =
    fold_left (fun l x -> if not (mem x l) then x::l else l) l1 l2

  let unions l =
    fold_left union [] l

  let included l1 l2 =
    for_all (fun x -> mem x l2) l1

  let set_equal l1 l2 =
    included l1 l2 && included l2 l1

  let diff l1 l2 =
    filter (fun x  -> not (mem x l2)) l1

  let rec get i l =
    match l,i with
    |[],_ -> raise (Not_found)
    |t::_,0 -> t
    |_::l,i -> get (i-1) l

  let map_both fn =
    List.map (fun (a,b) -> (fn a, fn b))

  let map_right fn =
    List.map (fun (a,b) -> (a, fn b))
end
