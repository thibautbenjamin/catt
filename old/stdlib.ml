module List = struct
  include List

  let remove x l =
    filter (fun y -> y <> x) l
            
  let union l1 l2 =
    fold_left (fun l x -> if not (mem x l) then x::l else l) l1 l2

  let included l1 l2 =
    for_all (fun x -> mem x l2) l1

  let diff l1 l2 =
    filter (fun x  -> not (mem x l2)) l1
end
                
         
