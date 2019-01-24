(** Main for CATT. *)
open Common

let parse_file f =
  let sin =
    let fi = open_in f in
    let flen = in_channel_length fi in
    let buf = Bytes.create flen in
    really_input fi buf 0 flen;
    close_in fi;
    buf
  in
  Prover.parse (Bytes.to_string sin)

let usage = "catt [options] [file]"
let interactive = ref false

let () =
  Printexc.record_backtrace true;
  let file_in = ref [] in
  Arg.parse
    [
      "-i", Arg.Set interactive, " Interactive mode."
    ]
    (fun s -> file_in := s::!file_in)
    usage;
  Kernel.init_env ();
  let _ = match !file_in with
    | [f] -> Command.exec (parse_file f)
    | _ -> ()
  in if !interactive then Prover.loop ()
