(** Interaction with a webpage. *)
open Lwt.Infix
module Dom = Js_of_ocaml.Dom
module Sys_js = Js_of_ocaml.Sys_js
module Html = Js_of_ocaml.Dom_html
module Js = Js_of_ocaml.Js
module Events = Js_of_ocaml_lwt.Lwt_js_events
module Firebug = Js_of_ocaml.Firebug

let doc = Html.document
let button txt action =
  let button_type = Js.string "button" in
  let b = Html.createInput ~_type:button_type doc in
  b##.value := Js.string txt;
  b##.onclick := Html.handler (fun _ -> action (); Js._true);
  b

let _debug s =
  Firebug.console##debug (Js.string s)

let loop s =
  Printf.printf "\n";
  Catt.Prover.exec s (fun () -> ());
  flush stdout;
  Catt.Prover.init ();
  flush stdout

let run _ =
  let top =
    Js.Opt.get
      (doc##getElementById (Js.string "toplevel"))
      (fun () -> assert false)
  in
  let textbox = Html.createTextarea doc in
  textbox##.id := Js.string "cattInput";
  textbox##.cols := 80;
  textbox##.rows := 25;
  Dom.appendChild top textbox;
  Dom.appendChild top (Html.createBr doc);
  textbox##focus;
  textbox##select;

  (* Current offset in textbox. *)
  let tb_off = ref 0 in
  let print s =
    let s = Js.to_string textbox##.value ^ s in
    tb_off := String.length s;
    textbox##.value := Js.string s;
    Js.Unsafe.set textbox (Js.string "scrollTop")
      (Js.Unsafe.get textbox (Js.string "scrollHeight"))
  in
  let read () =
    let s = Js.to_string textbox##.value in
    let cmd = String.sub s !tb_off (String.length s - !tb_off) in
    tb_off := String.length s;
    cmd
  in

  Sys_js.set_channel_flusher stdout print;
  Sys_js.set_channel_flusher stderr print;
  Catt.Prover.init ();
  flush stdout;

  let b =
    button
      "Send"
      (fun () ->
         let s = read () in
         let s =
           let s = ref s in
           let remove_last () =
             if !s = "" then false else
               let c = !s.[String.length !s - 1] in
               c = '\n' || c = '\r'
           in
           while remove_last () do
             (* remove trailing \n *)
             s := String.sub !s 0 (String.length !s - 1)
           done;
           !s
         in
         loop s;
         textbox##focus;
         doc##.documentElement##.scrollTop := doc##.body##.scrollHeight)
  in
  b##.id := Js.string "send";
  Dom.appendChild top b;

  let rec key_listener key =
    Events.keydown key >>= fun event ->
    if event##.key = Js.Optdef.return (Js.string "Enter") then
      b##click;
    key_listener key
  in
  Lwt.async (fun () -> key_listener textbox);
  Js._false

let () =
  Html.window##.onload := Html.handler run
