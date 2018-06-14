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

let usage = "catt [file]"

let () =
  Printexc.record_backtrace true;
  let file_in = ref [] in
  Arg.parse
    []
    (fun s -> file_in := s::!file_in)
    usage;
  let _ = match !file_in with
    | [f] -> Command.exec (parse_file f)
| _ -> ()
  in ()
