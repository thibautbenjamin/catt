open Catt

let usage = "catt [options] [file]"
let interactive = ref false
let no_builtins = ref false
let debug = ref false

let () =
  Printexc.record_backtrace true;
  let file_in = ref [] in
  Stdlib.Arg.parse
    [
      "-i", Stdlib.Arg.Set interactive, "Interactive mode.";
      "--no-builtins", Stdlib.Arg.Set no_builtins, "Prevent using built-in compositions and identities";
      "--debug", Stdlib.Arg.Set debug, "Debug mode: stop on error and drops a menu"
    ]
    (fun s -> file_in := s::!file_in)
    usage;
  let _ = match !file_in with
    | [f] ->
      Settings.use_builtins := not !no_builtins;
      Settings.debug := !debug;
      Command.exec ~loop_fn:Prover.loop (Prover.parse_file f)
    | _ -> ()
  in if !interactive then Prover.loop ()
