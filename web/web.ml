(** Interaction with a webpage. *)

module Dom = Js_of_ocaml.Dom
module Html = Js_of_ocaml.Dom_html
module Js = Js_of_ocaml.Js
module Firebug = Js_of_ocaml.Firebug

(* let envs = ref Lang.Envs.empty  *)

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
  Catt.Prover.exec s;
  (* envs := Prover.exec !envs s; *)
  Catt.Prover.init ()

let run _ =
  let top =
    Js.Opt.get
      (doc##getElementById (Js.string "toplevel"))
      (fun () -> assert false)
  in

  let output = Html.createDiv doc in
  output##.id := Js.string "output";
  output##.style##.whiteSpace := Js.string "pre";
  Dom.appendChild top output;

  let textbox = Html.createTextarea doc in
  textbox##.id := Js.string "input";
  textbox##.cols := 80;
  textbox##.rows := 25;
  (* textbox##value <- Js.string "# "; *)
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
    (* Scroll down. *)
    Js.Unsafe.set textbox (Js.string "scrollTop") (Js.Unsafe.get textbox (Js.string "scrollHeight"))
  in
  let read () =
    let s = Js.to_string textbox##.value in
    let cmd = String.sub s !tb_off (String.length s - !tb_off) in
    tb_off := String.length s;
    cmd
  in

  Catt.Io.print_string_fun := print;
  Catt.Prover.init ();

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

  ignore (Js.Unsafe.eval_string "init();");

  Js._false

let () =
  Html.window##.onload := Html.handler run
