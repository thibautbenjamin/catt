open Common
open Syntax

module PS = struct
  type t = ps

  exception Invalid
 
  let to_string  = string_of_ps   

  let rec marker = function
    | PStart (x,tx) -> (x,tx)
    | PExt (ps,_,y) -> y
    | PDrop ps ->
       let f,tf = marker ps in
       match tf.desc with
       | Arr (_,_,x,{desc = Var y}) ->
          let t =
            let rec aux = function
              | PStart (a,t) -> assert (a = y); t
              | PExt (ps,(a,ta),(b,tb)) ->
                 if a = y then ta
                 else if b = y then tb
                 else aux ps
              | PDrop ps -> aux ps
            in aux ps
          in y,t
       | _ -> raise Invalid
                     
  let rec free_vars = function
    | PStart (x,_) -> [x]
    | PExt (ps,(x,_),(y,_)) -> y::x::(free_vars ps)
    | PDrop ps -> free_vars ps

  let make l : t =
    let (a,ta,l) = match l with
      |(a, ta)::l -> begin match ta.desc with
                     | Obj _ -> a,ta,l
                     | _ -> error "pasting scheme must start with an object"
                     end
      |[] -> error "pasting scheme cannot be empty"
    in
    let rec aux ps = function
      | ((x,tx)::(y,ty)::l) as l'  -> begin
          match ty.desc with
          | Arr (_,_, {desc = Var source}, {desc = Var targ}) ->
             if (x <> targ) then
               error ~pos:ty.pos "not a pasting scheme (types do not match: target of the arrow is %s, but %s was expected)"
                     (string_of_var targ) (string_of_var x);
             let (a,ta) = marker ps in
             if a = source then
               let fv = free_vars ps in
               assert (not (List.mem y fv));
               assert (not (List.mem x fv));
               let ps = PExt (ps,(x,tx),(y,ty)) in
               aux ps l
             else
               aux (PDrop ps) l'
          | _ -> error ~pos:ty.pos "not a pasting scheme (types do not match : got %s, but an arrow was expected)" (string_of_expr ty)
        end          
      | [] -> ps
      | [x,tx] ->  error ~pos:tx.pos "This is not a pasting scheme (invalid parity)"
    in
    aux (PStart (a,ta)) l

  let rec height = function
    | PStart _ -> 0
    | PExt (ps,_,_) -> (height ps) + 1
    | PDrop ps -> (height ps) - 1

  let rec dim = function
    | PStart _ -> 0
    | PExt (ps,_,_) -> max (dim ps) (height ps + 1)
    | PDrop ps -> dim ps

  let source i ps =
    assert (i >= 0);
    let rec aux = function
      | PStart _ as ps -> ps 
      | PExt (ps,_,_) when height ps >= i -> aux ps
      | PExt (ps,y,f) -> PExt(aux ps,y,f)
      | PDrop ps when height ps > i -> aux ps
      | PDrop ps -> PDrop (aux ps)
    in aux ps

  let target i ps =
    assert (i >= 0);
    let replace g = function
      | PStart x -> PStart g
      | PExt (ps,y,f) -> PExt (ps,y,g)
      | _ -> assert false
    in
    let rec aux = function
      | PStart _ as ps -> ps
      | PExt (ps,_,_) when height ps > i -> aux ps
      | PExt (ps,y,f) when height ps = i -> replace y (aux ps)
      | PExt (ps,y,f) -> PExt (aux ps,y,f)
      | PDrop ps when height ps > i -> aux ps
      | PDrop ps -> PDrop (aux ps)
    in
    aux ps
                      
  let rec map f = function
    | PStart x -> PStart (f x)
    | PExt (ps,x,y) ->
       let ps = map f ps in
       let x = f x in
       let y = f y in
       PExt (ps,x,y)
    | PDrop ps -> PDrop (map f ps)

  let rec fold_left f s = function
    | PStart x -> f s x
    | PExt (ps,x,y) ->
       let s = fold_left f s ps in
       let s = f s x in
       f s y
    | PDrop ps -> fold_left f s ps

  let rec fold_left2 f s ps1 ps2 =
    match ps1, ps2 with
    | PStart x1, PStart x2 -> f s x1 x2
    | PExt (ps1,y1,f1), PExt(ps2,y2,f2) ->
       let s = fold_left2 f s ps1 ps2 in
       let s = f s y1 y2 in
       f s f1 f2
    | PDrop ps1, PDrop ps2 -> fold_left2 f s ps1 ps2
    | (PStart _  | PExt _ | PDrop _), _ -> assert false

  let rec fold_right f ps s =
    match ps with
    | PStart x -> f x s
    | PExt (ps,x,y) ->
       let s = f y s in
       let s = f x s in
       fold_right f ps s
    | PDrop ps -> fold_right f ps s
end
