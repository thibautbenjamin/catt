(** Main for CATT. *)
let parse_file f =
  let sin =
    let fi = open_in f in
    let flen = in_channel_length fi in
    let buf = Bytes.create flen in
    really_input fi buf 0 flen;
    close_in fi;
    buf
  in
  Catt.Prover.parse (Bytes.to_string sin)

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
      Catt.Settings.use_builtins := not !no_builtins;
      Catt.Settings.debug := !debug;
      Catt.Command.exec ~loop_fn:Catt.Prover.loop (parse_file f)
    | _ -> ()
  in if !interactive then Catt.Prover.loop ()
