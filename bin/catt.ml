open Catt

let usage = "catt [options] [file]"
let interactive = ref false
let no_builtins = ref false
let debug = ref false
let keep_going = ref false

let () =
  Printexc.record_backtrace true;
  let file_in = ref [] in
  Stdlib.Arg.parse
    [
      ("-i", Stdlib.Arg.Set interactive, "Interactive mode.");
      ( "--no-builtins",
        Stdlib.Arg.Set no_builtins,
        "Prevent using built-in compositions and identities" );
      ( "--debug",
        Stdlib.Arg.Set debug,
        "Debug mode: stop on error and drops a menu" );
      ( "--keep-going",
        Stdlib.Arg.Set keep_going,
        "Do not exit on terms that don't typecheck." );
    ]
    (fun s -> file_in := s :: !file_in)
    usage;
  let _ =
    match !file_in with
    | [ f ] -> (
        Settings.use_builtins := not !no_builtins;
        Settings.keep_going := !keep_going;
        Settings.debug := !debug;
        match Prover.parse_file f with
        | Ok cmds -> Catt.Command.exec ~loop_fn:Prover.loop cmds
        | Error () -> exit 1)
    | _ -> ()
  in
  if !interactive then Prover.loop ()
