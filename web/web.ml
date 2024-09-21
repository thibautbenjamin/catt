(** Interaction with a webpage. *)
module Dom = Js_of_ocaml.Dom
module Sys_js = Js_of_ocaml.Sys_js
module Html = Js_of_ocaml.Dom_html
module Js = Js_of_ocaml.Js
module Firebug = Js_of_ocaml.Firebug

let doc = Html.document

let button ~id txt action =
  let button_type = Js.string "button" in
  let b = Html.createInput ~_type:button_type doc in
  b##.value := Js.string txt;
  b##.onclick := Html.handler (fun _ -> action (); Js._true);
  b##.id := Js.string id;
  b

let _debug s =
  Firebug.console##debug (Js.string s)

let run_action s =
  try
    match (Catt.Prover.parse s) with
    | Ok cmds -> Catt.Command.exec ~loop_fn:Catt.Prover.loop cmds
    | Error () -> ()
  with | _ -> Catt.Io.error "Uncaught exception"

let run _ =
  let top =
    Js.Opt.get
      (doc##getElementById (Js.string "toplevel"))
      (fun () -> assert false)
  in

  let button_bar = Html.createDiv doc in
  button_bar##.id := Js.string "buttonBar";
  let left_bar = Html.createDiv doc in
  left_bar##.id := Js.string "leftBar";
  let right_bar = Html.createDiv doc in
  right_bar##.id := Js.string "rightBar";


  let editor_area = Html.createDiv doc in
  editor_area##.id := Js.string "editorArea";

  let input_area = Html.createTextarea doc in
  input_area##.id := Js.string "inputArea";
  input_area##.placeholder := Js.string "Input CaTT code here";

  let output_area = Html.createTextarea doc in
  output_area##.id := Js.string "outputArea";
  output_area##.placeholder := Js.string "Output...";
  output_area##.readOnly := Js.bool true;

  let print s =
    let text = Js.to_string output_area##.value in
    output_area##.value := Js.string (text ^ s);
  in
  let clear_output () =
    output_area##.value := Js.string ""
  in

  let run_action () =
    clear_output();
    let s = Js.to_string input_area##.value in
    run_action s
  in
  let run_button = button ~id:"runButton" "Run" run_action in

  Dom.appendChild top button_bar;
  Dom.appendChild button_bar left_bar;
  Dom.appendChild left_bar run_button;
  Dom.appendChild button_bar right_bar;

  Dom.appendChild top editor_area;
  Dom.appendChild editor_area input_area;
  Dom.appendChild editor_area output_area;
  input_area##focus;
  input_area##select;

  Sys_js.set_channel_flusher stdout print;
  Sys_js.set_channel_flusher stderr print;
  Js._false

let () =
  Html.window##.onload := Html.handler run
