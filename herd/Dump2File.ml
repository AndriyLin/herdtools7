(**
 * Xuankang Lin [XL]:
 *   I am injecting some code into Herd7 to save the generated executions
 *   to file. They are preserved for future learning.
 *)

open Printf

(* It's too tricky to comply exactly with their functor style, I'll need to
 * specify type of Test_herd and such such to write an abstract module. So I
 * simply follow the style in test_herd and top_herd.
 *)
module Make (SemArg : SemExtra.S) = struct

  module Sem = SemArg
  module Evt = Sem.E
  module Arch = Sem.A


  (* Filter out only specific events to display.
   *   In Pretty.ml, PC.showevents and PC.showinitwrites are used for
   *   filtering. While here, I choose NonRegEvents and all InitWrites. *)
  let filter_event e = not (Evt.is_reg_any e)
  let select_events = Evt.EventSet.filter filter_event
  let filter_rel =
    Evt.EventRel.filter (fun (e1,e2) -> filter_event e1 && filter_event e2)

  (* Copied from Pretty.ml. Simplify the Event Structure,
   * only retaining the events/relations to display. *)
  let select_es es =
    { es with
      Evt.events = select_events es.Evt.events ;
      intra_causality_data = filter_rel es.Evt.intra_causality_data;
      intra_causality_control = filter_rel es.Evt.intra_causality_control; }

  let id_str_of e = sprintf "eiid:%i" e.Evt.eiid

  (* Print out ID / Thread-ID / Action / Address (variable) / Value.
   *   is_init_f: a filter function that returns true when e is init. *)
  let dump_event log_oc is_init_f e =
    let pl chan = fprintf chan "%s\n" in
    begin
      pl log_oc (id_str_of e) ;

      let tid_str_of e =
        let pid = match Evt.proc_of e with
          | Some p -> p
          | None -> (-1) (* e.g. init events do not belong to a thread *)
        in sprintf "Pid:%i" pid in
      pl log_oc ("  " ^ (tid_str_of e)) ;

      (* TODO Action / Address / Value should all be parsed from pp_action... *)
      let action_str_of e = "Action:" ^ Evt.pp_action e in
      let action_str = "  " ^ (action_str_of e) in
      let action_str =
        if is_init_f e
        then action_str ^ "(Init)"
        else action_str in
      pl log_oc action_str ;

      (* TODO *)
      let address_str_of e = "Address:" ^ Evt.pp_action e in
      pl log_oc ("  " ^ (address_str_of e)) ;

      (* TODO *)
      let value_str_of e = "Value:" ^ Evt.pp_action e in
      pl log_oc ("  " ^ (value_str_of e))
    end

  (* Dump all the events to file, including each one's
   *  ID / Thread-ID / Action / Variable / Value.
   *)
  let dump_events log_oc es =
    let es = select_es es in (* retain only NonRegEvents *)
    let evts = es.Evt.events in
    let n_evts = Evt.EventSet.cardinal evts in
    let init_evts = Evt.mem_stores_init_of evts in

    (* Dump all events, with init writes highlighted. *)
    let iter_event =
      dump_event log_oc (fun e -> Evt.EventSet.mem e init_evts) in

    fprintf log_oc "=====events=====%n\n" n_evts ;  (* print set size *)
    Evt.EventSet.iter iter_event evts



  (* Copied from Pretty.ml:
   *   Filter out only those rfs concerning the events to show. *)
  let select_rfmap rfm =
    Sem.RFMap.fold
      (fun wt rf k ->
        match wt,rf with
        | (Sem.Load e1, Sem.Store e2) ->
           begin
             match filter_event e1, filter_event e2 with
             | true, true -> Sem.RFMap.add wt rf k
             | true, false ->
                if Evt.is_mem_store_init e2
                then Sem.RFMap.add wt Sem.Init k
                else k
             | _, _ -> k
           end
        | (Sem.Final _, Sem.Store e)
        | (Sem.Load e,Sem.Init) ->
           if filter_event e
           then Sem.RFMap.add wt rf k
           else k
        | (Sem.Final _, Sem.Init) -> k)
      rfm Sem.RFMap.empty


  (* Dump all the rf relations to file.
   * I don't need to do things like make_rf_from_rfmap() as in Pretty.ml *)
  let dump_rf log_oc rf_map =
    let rf_map = select_rfmap rf_map in
    let n_rfs = Sem.RFMap.cardinal rf_map in
    fprintf log_oc "=====rf relations=====%n\n" n_rfs ; (* print map size *);

    Sem.pp_rfmap log_oc "\n"
                 (fun chan wt rf ->
                   match wt, rf with
                   | Sem.Load er, Sem.Store ew ->
                      fprintf log_oc "%s -> %s"
                              (id_str_of ew) (id_str_of er)
                   | Sem.Final loc, Sem.Store ew ->
                      fprintf log_oc "%s -> _ (final), loc: %s"
                              (id_str_of ew) (Arch.pp_location loc)
                   | Sem.Load er, Sem.Init ->
                      fprintf log_oc "_ -> %s (init)"
                              (id_str_of er) (* TODO: also dump er's variable? *)
                   | Sem.Final loc, Sem.Init ->
                      fprintf log_oc "_ -> _ (init->final), loc: %s"
                              (Arch.pp_location loc)
                 )
                 rf_map ;
    fprintf log_oc "\n"



  (* Copied from Pretty.ml *)
  let make_rf_from_rfmap rfmap =
    Sem.RFMap.fold
      (fun wt rf k -> match wt,rf with
                      | Sem.Load er, Sem.Store ew when Evt.is_mem er ->
                         Evt.EventRel.add (ew,er) k
                      | _ -> k)
      rfmap
      Evt.EventRel.empty

  (* Copied from Pretty.ml *)
  let rec min_max_to_succ = function
    | []|[_] -> Evt.EventRel.empty
    | (_xmin,xmax)::((ymin,_ymax)::_ as rem) ->
        Evt.EventRel.union
          (Evt.EventRel.cartesian xmax ymin)
          (min_max_to_succ rem)

  (* Copied from Pretty.ml *)
  let make_visible_po es by_proc_and_poi =
    let intra =
      Evt.EventRel.transitive_closure
        (Evt.EventRel.union
           es.Evt.intra_causality_data
           es.Evt.intra_causality_control) in
    let min_max_list =
      List.map
        (List.map
           (fun es ->
             let mins =
               Evt.EventSet.filter
                 (fun e -> not (Evt.EventRel.exists_pred intra e))
                 es
             and maxs =
               Evt.EventSet.filter
                 (fun e -> not (Evt.EventRel.exists_succ intra e))
                 es in
             mins,maxs))
        by_proc_and_poi in
    Evt.EventRel.unions
      (List.map min_max_to_succ min_max_list)


  (* Dump all the po relations to file. Although there is "pos" in concrete,
   * somehow it is empty at this moment. *)
  let dump_po log_oc es rf_map =
    let module PU = PrettyUtils.Make(Sem) in
    let events_by_proc_and_poi = PU.make_by_proc_and_poi es in

    (* Copied from Pretty.ml, I don't know why this is necessary.. *)
    let replaces_po =
      let vbss = [] in
      let all_vbss = Evt.EventRel.unions (List.map snd vbss) in
      let rf = make_rf_from_rfmap rf_map in
      let r = Evt.EventRel.union rf all_vbss in
      Evt.EventRel.union r (Evt.EventRel.inverse r)
    in

    let po_edges = make_visible_po es events_by_proc_and_poi in
    let po_edges = Evt.EventRel.diff po_edges replaces_po in
    (* let po_edges = reduces_more  po_edges replaces_po in *)
    (* commented out in Pretty.ml *)
    let n_pos = Evt.EventRel.cardinal po_edges in

    let iter_po =
      Evt.EventRel.pp log_oc "\n"
                      (fun chan (e1, e2) ->
                        fprintf chan "%s -> %s"
                                (id_str_of e1) (id_str_of e2)
                      )
    in
    fprintf log_oc "=====po relations=====%n\n" n_pos ; (* print set size *)
    iter_po po_edges ;
    fprintf log_oc "\n"

end
