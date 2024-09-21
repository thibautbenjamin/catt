module List = struct
  include List

  let remove x l = filter (fun y -> y <> x) l

  let rec last = function
    | [] -> raise (Invalid_argument "last")
    | [ t ] -> t
    | _ :: l -> last l

  let union l1 l2 =
    fold_left (fun l x -> if not (mem x l) then x :: l else l) l1 l2

  let unions l = fold_left union [] l
  let included l1 l2 = for_all (fun x -> mem x l2) l1
  let set_equal l1 l2 = included l1 l2 && included l2 l1
  let diff l1 l2 = filter (fun x -> not (mem x l2)) l1

  let rec get i l =
    match (l, i) with
    | [], _ -> raise Not_found
    | t :: _, 0 -> t
    | _ :: l, i -> get (i - 1) l

  let map_both fn = List.map (fun (a, b) -> (fn a, fn b))
  let map_right fn = List.map (fun (a, b) -> (a, fn b))

  let rec map3 fn l1 l2 l3 =
    match (l1, l2, l3) with
    | [], [], [] -> []
    | a1 :: l1, a2 :: l2, a3 :: l3 -> fn a1 a2 a3 :: map3 fn l1 l2 l3
    | _ -> raise (Invalid_argument "List.map3")

  let rec map4 fn l1 l2 l3 l4 =
    match (l1, l2, l3, l4) with
    | [], [], [], [] -> []
    | a1 :: l1, a2 :: l2, a3 :: l3, a4 :: l4 ->
        fn a1 a2 a3 a4 :: map4 fn l1 l2 l3 l4
    | _ -> raise (Invalid_argument "List.map3")
end
