open Common
open Syntax

module PS = struct
  type t = (var * expr) list

  let rename_vars (ps:t) : t*sub = 
    let rec aux (ps:t) (s:sub ) =
    match ps with
    |[] -> [],[]
    |(x,e)::q ->
      let new_var = refresh (Name ("_"^(name x))) in
      let renamed,sub = aux q ((x,mk(Var new_var))::s) in
      (new_var,substitute e s e.pos e.show)::renamed, (x,mk(Var new_var))::sub
    in aux ps []

  let extract (e : expr) =
    match e.desc with
    |Coh (ps,_) -> ps
    |(Var _ |Obj |Arr _ |Sub _ |Badsub _) -> error "got %s, but a coherence was expected" (to_string e)
           
  let rec create_sub (ps : t) (l : var list) : sub =
    match ps,l with
    |[],[] -> []
    |(x,t)::ps, y::l -> (x, (mk (Var y)))::(create_sub ps l)
    |_,_ -> error "application of a coherence must instantiate all the variables"
    
end
                           
