(** An analyzer that takes the CFG from [MyCFG], a solver from [Selector], constraints from [Constraints] (using the specification from [MCP]) *)

open Prelude
open Cil
open MyCFG
open Pretty
open Analyses
open GobConfig
open Constraints
open Goblintutil

(** Given a [Cfg], computes the solution to [MCP.Path] *)
module AnalyzeCFG (Cfg:CfgBidir) =
struct

  (** The main function to preform the selected analyses. *)
  let analyze (file: file) (startfuns: fundec list)  (module Spec : GoodSpec with type V'.t = Base.BaseArgs.t) =
    (** The Equation system *)
    let module EQSys = FlatFromGoodSpec (Spec) (ListCallString) (Cfg) in

    (** Hashtbl for locals *)
    let module LHT   = BatHashtbl.Make (EQSys.LVar) in
    (** Hashtbl for globals *)
    let module GHT   = BatHashtbl.Make (EQSys.GVar) in

    (** The solver *)
    let module Slvr  = Selector.Make (EQSys) (LHT) (GHT) in
    (* (** The verifyer *)
    let module Vrfyr = Verify2 (EQSys) (LHT) (GHT) in
    (** The comparator *)
    let module Comp = Compare (Spec) (EQSys) (LHT) (GHT) in *)
    (* (** Another iterator. Set "exp.use_gen_solver" to false. *)
       let module I = IterateLikeAstree (Spec) (Cfg) (GHT) in *)

    (** Triple of the function, context, and the local value. *)
    let module RT = Analyses.GoodResultType2 (Spec) (ListCallString) (Spec.V') in
    (** Set of triples [RT] *)
    let module LT = SetDomain.HeadlessSet (RT) in
    (** Analysis result structure---a hashtable from program points to [LT] *)
    let module Result = Analyses.Result (LT) (struct let result_name = "analysis" end) in


    (** exctract global xml from result *)
    let make_global_fast_xml f g =
      let open Printf in
      let print_globals k v =
        fprintf f "\n<glob><key>%s</key>%a</glob>" (Goblintutil.escape (Basetype.Variables.short 800 k)) Spec.G'.printXml v;
      in
      GHT.iter print_globals g
    in

    let print_dead_code (xs:Result.t) =
      let dead_locations : unit Deadcode.Locmap.t = Deadcode.Locmap.create 10 in
      let module NH = Hashtbl.Make (MyCFG.Node) in
      let live_nodes : unit NH.t = NH.create 10 in
      let count = ref 0 in
      let open BatMap in let open BatPrintf in
      let module StringMap = Make (String) in
      let live_lines = ref StringMap.empty in
      let dead_lines = ref StringMap.empty in
      let add_one (l,n,f) v =
        let add_fun  = BatISet.add l.line in
        let add_file = StringMap.modify_def BatISet.empty f.svar.vname add_fun in
        if LT.for_all (fun (_,x,f) -> Spec.D'.is_bot x) v then begin
          dead_lines := StringMap.modify_def StringMap.empty l.file add_file !dead_lines;
          Deadcode.Locmap.add dead_locations l ()
        end else begin
          live_lines := StringMap.modify_def StringMap.empty l.file add_file !live_lines;
          NH.add live_nodes n ()
        end;
      in
      Result.iter add_one xs;
      let live file fn =
        try StringMap.find fn (StringMap.find file !live_lines)
        with Not_found -> BatISet.empty
      in
      dead_lines := StringMap.mapi (fun fi -> StringMap.mapi (fun fu ded -> BatISet.diff ded (live fi fu))) !dead_lines;
      dead_lines := StringMap.map (StringMap.filter (fun _ x -> not (BatISet.is_empty x))) !dead_lines;
      dead_lines := StringMap.filter (fun _ x -> not (StringMap.is_empty x)) !dead_lines;
      let print_func f xs =
        let one_range b e first =
          count := !count + (e - b + 1);
          if not first then printf ", ";
          begin if b=e then
              printf "%d" b
            else
              printf "%d..%d" b e
          end; false
        in
        printf "  function '%s' has dead code on lines: " f;
        ignore (BatISet.fold_range one_range xs true);
        printf "\n"
      in
      let print_file f =
        printf "File '%s':\n" f;
        StringMap.iter print_func
      in
      if StringMap.is_empty !dead_lines
      then printf "No dead code found!\n"
      else begin
        StringMap.iter print_file !dead_lines;
        printf "Found dead code on %d line%s!\n" !count (if !count>1 then "s" else "")
      end;
      let str = function true -> "then" | false -> "else" in
      let report tv loc dead =
        if Deadcode.Locmap.mem dead_locations loc then
          match dead, Deadcode.Locmap.find_option Deadcode.dead_branches_cond loc with
          | true, Some exp -> ignore (Pretty.printf "Dead code: the %s branch over expression '%a' is dead! (%a)\n" (str tv) d_exp exp d_loc loc)
          | true, None     -> ignore (Pretty.printf "Dead code: an %s branch is dead! (%a)\n" (str tv) d_loc loc)
          | _ -> ()
      in
      if get_bool "dbg.print_dead_code" then begin
        Deadcode.Locmap.iter (report true)  Deadcode.dead_branches_then;
        Deadcode.Locmap.iter (report false) Deadcode.dead_branches_else;
        Deadcode.Locmap.clear Deadcode.dead_branches_then;
        Deadcode.Locmap.clear Deadcode.dead_branches_else
      end;
      NH.mem live_nodes
    in

    (** convert result that can be out-put *)
    let solver2source_result h : Result.t =
      (* processed result *)
      let res = Result.create 113 in

      (* Adding the state at each system variable to the final result *)
      let add_local_var (n,es,v) state =
        let loc = MyCFG.getLoc n in
        if loc <> locUnknown then try
            let (_,_, fundec) as p = loc, n, MyCFG.getFun n in
            if Result.mem res p then
              (* If this source location has been added before, we look it up
               * and add another node to it information to it. *)
              let prev = Result.find res p in
              Result.replace res p (LT.add ((es,v),state,fundec) prev)
            else
              Result.add res p (LT.singleton ((es,v),state,fundec))
          (* If the function is not defined, and yet has been included to the
           * analysis result, we generate a warning. *)
          with Not_found -> Messages.warn ("Undefined function has escaped.")
      in
      LHT.iter add_local_var h;
      res
    in


    let _ = GU.global_initialization := true in
    let _ = GU.earlyglobs := false in
    Spec.init ();
    Access.init file;

    MyCFG.write_cfgs := MyCFG.dead_code_cfg file (module Cfg:CfgBidir);

    let startvars   = List.map (fun x -> (MyCFG.Function x.svar ,ListCallString.empty,`V (return_varinfo ()))) startfuns in

    let local_xml = ref (Result.create 0) in
    let global_xml = ref (GHT.create 0) in
    let lh, gh = Stats.time "solving" (Slvr.solve [] []) startvars in
    local_xml := solver2source_result lh;
    global_xml := gh;

    let liveness = ref (fun _ -> true) in
    if (get_bool "dbg.print_dead_code") then
          liveness := print_dead_code !local_xml;

    if (get_bool "exp.cfgdot") then
      MyCFG.dead_code_cfg file (module Cfg:CfgBidir) !liveness;

    Spec.finalize ();
    if (get_bool "dbg.verbose") then print_endline "Generating output.";
      Result.output (lazy !local_xml) !global_xml make_global_fast_xml file


  let analyze file fs =
    analyze file fs (module Base.Main)
end

(** The main function to perform the selected analyses. *)
let analyze (file: file) fs =
  if (get_bool "dbg.verbose") then print_endline "Generating the control flow graph.";
  let cfgF, cfgB = MyCFG.getCFG file in
  let module CFG = struct let prev = cfgB let next = cfgF end in
  let module A = AnalyzeCFG (CFG) in
  A.analyze file fs
