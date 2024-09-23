let printf e = Printf.printf e
let eprintf e = Printf.eprintf e
let debug e = Printf.ksprintf (fun s -> Printf.printf "[=D.D=] %s\n\n%!" s) e

let info ?(v = 0) e =
  if !Settings.verbosity >= v then
    print_string (Printf.sprintf "[=I.I=] %s.\n%!" (Lazy.force e))

let command e = Printf.ksprintf (fun s -> Printf.printf "[=^.^=] %s\n%!" s) e

let error e =
  Printf.ksprintf (fun s -> eprintf "\027[1;91m[=X.X=] %s\n\027[0m%!" s) e
