let print_string_fun = ref print_string
let print_string s = !print_string_fun s
let print_newline () = print_string "\n"
let print_endline s = print_string s; print_newline ()
let read_line_fun = ref read_line
let read_lin () = !read_line_fun ()

let printf e = Printf.printf e
let eprintf e = Printf.eprintf e
let debug e = Printf.ksprintf (fun s -> printf "[=D.D=] %s\n\n%!" s) e
let info ?(v = 0) e =
  if !Settings.verbosity >= v then
    printf "[=I.I=] %s.\n%!" (Lazy.force e)
let command e = Printf.ksprintf (fun s -> printf "[=^.^=] %s\n%!" s) e
let error e = Printf.ksprintf (fun s -> eprintf "\027[1;91m[=X.X=] %s\n\027[0m%!" s) e
