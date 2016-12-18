(**
 * Xuankang Lin [XL]:
 *   I am injecting some code into Herd7 to save the generated executions
 *   to file. They are preserved for future learning.
 *)

(* It's too tricky to comply exactly with their functor style, I'll need to
 * specify type of Test_herd and such such to write an abstract module. So I
 * simply follow the style in test_herd and top_herd. 
 *)
module Make (SemArg : SemExtra.S) = struct

  module SemMod = SemArg

  (* for defining Test_herd *)
  module Arch = SemMod.A
  module Test = Test_herd.Make(Arch)

  (* Dump all the events to file, including each one's
   *  ID / Thread-ID / Action / Variable / Value.
   *)
  (* FIXME: rf_map, test is temporary *)
  let dump_events log_oc events rf_map test =
    (* TODO *)

    (* FIXME: Below is for debugging *)
    let module PP = Pretty.Make(SemArg) in
    PP.dump_es_rfm log_oc test events rf_map ;
    ()

  (* Dump all the po relations to file. *)
  let dump_po log_oc =
    (* TODO *)
    ()

  (* Dump all the rf relations to file. *)
  let dump_rf log_oc rf_map =
    (* TODO *)
    ()

end
