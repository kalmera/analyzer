(** Signatures for analyzers, analysis specifications, and result output.  *)

open Cil
open Pretty
open GobConfig

module GU = Goblintutil
module M  = Messages

(** Analysis starts from lists of functions: start functions, exit functions, and
  * other functions. *)
type fundecs = fundec list * fundec list * fundec list

module type VarType =
sig
  include Hashtbl.HashedType
  val pretty_trace: unit -> t -> doc
  val compare : t -> t -> int
  val category : t -> int

  val printXml : 'a BatInnerIO.output -> t -> unit
  val var_id   : t -> string
  val file_name : t -> string
  val line_nr   : t -> int
  val node      : t -> MyCFG.node
end

module Var =
struct
  type t = MyCFG.node

  let category = function
    | MyCFG.Statement     s -> 1
    | MyCFG.Function      f -> 2
    | MyCFG.FunctionEntry f -> 3

  let hash x =
    match x with
    | MyCFG.Statement     s -> Hashtbl.hash (s.sid, 0)
    | MyCFG.Function      f -> Hashtbl.hash (f.vid, 1)
    | MyCFG.FunctionEntry f -> Hashtbl.hash (f.vid, 2)

  let equal = MyCFG.Node.equal

  let getLocation n = MyCFG.getLoc n

  let pretty () x =
    match x with
    | MyCFG.Statement     s -> dprintf "node \"%a\"" Basetype.CilStmt.pretty s
    | MyCFG.Function      f -> dprintf "call of %s" f.vname
    | MyCFG.FunctionEntry f -> dprintf "entry state of %s" f.vname

  let pretty_trace () x =  dprintf "%a on %a \n" pretty x Basetype.ProgLines.pretty (getLocation x)

  let compare n1 n2 =
    match n1, n2 with
    | MyCFG.FunctionEntry f, MyCFG.FunctionEntry g -> compare f.vid g.vid
    | _                    , MyCFG.FunctionEntry g -> -1
    | MyCFG.FunctionEntry g, _                     -> 1
    | MyCFG.Statement _, MyCFG.Function _  -> -1
    | MyCFG.Function  _, MyCFG.Statement _ -> 1
    | MyCFG.Statement s, MyCFG.Statement l -> compare s.sid l.sid
    | MyCFG.Function  f, MyCFG.Function g  -> compare f.vid g.vid

  let kind = function
    | MyCFG.Function f                         -> `ExitOfProc f
    | MyCFG.Statement {skind = Instr [Call _]} -> `ProcCall
    | _ -> `Other

  let printXml f n =
    let id ch n =
      match n with
      | MyCFG.Statement s     -> BatPrintf.fprintf ch "%d" s.sid
      | MyCFG.Function f      -> BatPrintf.fprintf ch "ret%d" f.vid
      | MyCFG.FunctionEntry f -> BatPrintf.fprintf ch "fun%d" f.vid
    in
    let l = MyCFG.getLoc n in
    BatPrintf.fprintf f "<call id=\"%a\" file=\"%s\" fun=\"%s\" line=\"%d\" order=\"%d\">\n" id n l.file (MyCFG.getFun n).svar.vname l.line l.byte

  let var_id n =
    match n with
    | MyCFG.Statement s     -> string_of_int s.sid
    | MyCFG.Function f      -> "ret" ^ string_of_int f.vid
    | MyCFG.FunctionEntry f -> "fun" ^ string_of_int f.vid

  let line_nr n = (MyCFG.getLoc n).line
  let file_name n = (MyCFG.getLoc n).file
  let description n = sprint 80 (pretty () n)
  let context () _ = Pretty.nil
  let node n = n
end


module VarF (LD: Printable.S) =
struct
  type t = MyCFG.node * LD.t

  let category = function
    | (MyCFG.Statement     s,_) -> 1
    | (MyCFG.Function      f,_) -> 2
    | (MyCFG.FunctionEntry f,_) -> 3

  let hashmul x y = if x=0 then y else if y=0 then x else x*y
  let hash x =
    match x with
    | (MyCFG.Statement     s,d) -> hashmul (LD.hash d) (s.sid*17)
    | (MyCFG.Function      f,d) -> hashmul (LD.hash d) (f.vid*19)
    | (MyCFG.FunctionEntry f,d) -> hashmul (LD.hash d) (f.vid*23)

  let equal (n1,d1) (n2,d2) = MyCFG.Node.equal n1 n2 && LD.equal d1 d2

  let getLocation (n,d) = MyCFG.getLoc n

  let pretty () x =
    match x with
    | (MyCFG.Statement     s,d) -> dprintf "node \"%a\"" Basetype.CilStmt.pretty s
    | (MyCFG.Function      f,d) -> dprintf "call of %s" f.vname
    | (MyCFG.FunctionEntry f,d) -> dprintf "entry state of %s" f.vname

  let pretty_trace () x =
    match x with
    | ((*MyCFG.FunctionEntry f*)_,d) -> dprintf "%a" pretty x
  (*       | _ -> dprintf "%a on %a" pretty x Basetype.ProgLines.pretty (getLocation x) *)


  let compare (n1,d1) (n2,d2) =
    let comp =
      match n1, n2 with
      | MyCFG.FunctionEntry f, MyCFG.FunctionEntry g -> compare f.vid g.vid
      | _                    , MyCFG.FunctionEntry g -> -1
      | MyCFG.FunctionEntry g, _                     -> 1
      | MyCFG.Statement _, MyCFG.Function _  -> -1
      | MyCFG.Function  _, MyCFG.Statement _ -> 1
      | MyCFG.Statement s, MyCFG.Statement l -> compare s.sid l.sid
      | MyCFG.Function  f, MyCFG.Function g  -> compare f.vid g.vid
    in
    if comp == 0 then LD.compare d1 d2 else comp

  let printXml f (n,c) =
    Var.printXml f n;
    BatPrintf.fprintf f "<context>\n";
    LD.printXml f c;
    BatPrintf.fprintf f "</context>\n"

  let var_id (n,_) = Var.var_id n

  let line_nr (n,_) = (MyCFG.getLoc n).line
  let file_name (n,_) = (MyCFG.getLoc n).file
  let description (n,_) = sprint 80 (Var.pretty () n)
  let context () (_,c) = LD.pretty () c
  let node (n,_) = n
end

module type CallString =
sig
  include Printable.S
  val compare: t -> t -> int
  val empty   : t
  val cons : (MyCFG.node * (lval option * varinfo * exp list) * MyCFG.node) -> t -> t
  val dest: t -> [ `empty
                 | `call of ((MyCFG.node * (lval option * varinfo * exp list) * MyCFG.node) * t)] list
end

module Edge
  : sig
    include Hashtbl.HashedType
    val compare: t -> t -> int
  end with type t = MyCFG.node * MyCFG.edge * MyCFG.node =
struct
  type t = MyCFG.node * MyCFG.edge * MyCFG.node
  let rec list_eq eq xs ys =
    match xs, ys with
    | [], [] -> true
    | x::xs, y::ys when eq x y -> list_eq eq xs ys
    | _ -> false

  let eq_lval l1 l2 = Util.equals (Lval l1) (Lval l2)

  open MyCFG
  let eq_edge e1 e2 =
    match e1, e2 with
    | Assign (l1,e1), Assign (l2,e2) -> Util.equals e1 e2 && eq_lval l1 l2
    | Proc (Some l1, e1, es1), Proc (Some l2, e2, es2) -> eq_lval l1 l2 && Util.equals e1 e2 && list_eq Util.equals es1 es2
    | Proc (None, e1, es1), Proc (None, e2, es2) -> Util.equals e1 e2 && list_eq Util.equals es1 es2
    | Entry f1, Entry f2 -> f1.svar.vid = f2.svar.vid
    | Ret (Some e1,f1), Ret (Some e2,f2)-> Util.equals e1 e2 && f1.svar.vid = f2.svar.vid
    | Ret (None,f1), Ret (None,f2) -> f1.svar.vid = f2.svar.vid
    | Test (e1,b1), Test (e2,b2) -> b1 = b2 && Util.equals e1 e2
    | ASM (s1,o1,i1), ASM (s2,o2,i2) -> s1 = s2
    | Skip, Skip -> true
    | SelfLoop, SelfLoop -> true
    | _ -> false
  let equal (f1,e1,t1) (f2,e2,t2) = MyCFG.Node.equal f1 f2 && MyCFG.Node.equal t1 t2 && eq_edge e1 e2
  let hash (f,e,t) = MyCFG.Node.hash f lxor MyCFG.Node.hash t

  let compareE x y = Pervasives.compare x y

  let compare (f1,e1,t1) (f2,e2,t2) =
    let c = MyCFG.Node.compare f1 f2 in
    if c<>0 then c else
      let c = compareE e1 e2 in
      if c<>0 then c else
        MyCFG.Node.compare t1 t2
end

module ListCallString
  : CallString =
struct
  include Printable.Blank
  type t = (MyCFG.node * (lval option * varinfo * exp list) * MyCFG.node) list

  let rec printArgs f = function
    | [] -> ()
    | [x] -> BatPrintf.fprintf f "%s" (Goblintutil.escape(Exp.Exp.short 80 x))
    | x::xs -> BatPrintf.fprintf f "%s, %a" (Goblintutil.escape(Exp.Exp.short 80 x)) printArgs xs

  let rec printXml f : t -> unit = function
    | [] -> BatPrintf.fprintf f "ε"
    | ((l,(_,g,args),s)::xs) -> BatPrintf.fprintf f "(%s,%s)::%a" (Var.var_id l) (Var.var_id s) printXml xs

  let printXml f xs =
    BatPrintf.fprintf f "<value><text>\n%a</text></value>\n" printXml xs

  let rec prettyArgs () : exp list -> Pretty.doc = function
    | [] -> nil
    | [x] -> Pretty.dprintf "%s" (Goblintutil.escape(Exp.Exp.short 80 x))
    | x::xs -> Pretty.dprintf "%s, %a" (Goblintutil.escape(Exp.Exp.short 80 x)) prettyArgs xs

  let rec pretty _: t -> Pretty.doc = function
    | [] -> Pretty.dprintf "main"
    | ((_,(_,g,args),_)::xs) -> Pretty.dprintf "%s(%a)::%a" g.vname prettyArgs args pretty xs

  let empty = []
  let cons x xs = x :: xs
  let dest = function
    | []      -> [`empty]
    | (x::xs) -> [`call (x,xs)]
  let rec equal (xs:t) (ys:t): bool =
    let eq (l1,f1,as1) (l2,f2,as2) = true
      (* let eq1 = match l1,l2 with
        | None, None -> true
        | Some l1, Some l2 -> Exp.Exp.equal (Lval l1) (Lval l2)
        | _ -> false
      in
      let rec eqExpList l1 l2  = match l1,l2 with
        | [], [] -> true
        | e1::l1, e2::l2 -> Exp.Exp.equal e1 e2 && eqExpList l1 l2
        | _ -> false
      in
      eq1 && f1.vid = f2.vid && eqExpList as1 as2 *)
    in
    let eq (f1,e1,t1) (f2,e2,t2) =
      MyCFG.Node.equal f1 f2 && eq e1 e2 && MyCFG.Node.equal t1 t2
    in
    match xs, ys with
    | [], [] -> true
    | (x::xs), (y::ys) -> eq x y && equal xs ys
    | _ -> false

  let rec hash = function
  | [] -> 0
  | (x::xs) ->
    let h (l,f,ass) = 10
      (* let eq1 = match l with
        | None -> 100
        | Some l1 -> Exp.Exp.hash (Lval l1)
      in
      let rec eqExpList l1 = match l1 with
        | [] -> 1
        | e1::l1 -> Hashtbl.hash (Exp.Exp.hash e1, eqExpList l1)
      in
      Hashtbl.hash (eq1, f.vid, eqExpList ass) *)
    in
    let h (f,e,t)  =
      Hashtbl.hash (MyCFG.Node.hash f, h e, MyCFG.Node.hash t)
    in
    Hashtbl.hash (h x, hash xs)

  let rec compare xs ys =
    match xs, ys with
    | [], [] -> 0
    | _, []  -> 1
    | [], _  -> -1
    | (x::xs), (y::ys) ->
      let eq (l1,f1,as1) (l2,f2,as2) = 0
        (* let c = match l1,l2 with
          | None, None -> 0
          | None, _ -> -1
          | _, None -> 1
          | Some l1, Some l2 -> Exp.Exp.compare (Lval l1) (Lval l2)
        in
        if c <> 0 then c else
          let c = Pervasives.compare f1.vid f2.vid in
          if c <> 0 then c else
            let rec eqExpList l1 l2  = match l1,l2 with
              | [], [] -> 0
              | [], _ -> -1
              | _, [] -> 1
              | e1::l1, e2::l2 ->
                let c = Exp.Exp.compare e1 e2 in
                if c <> 0 then c else eqExpList l1 l2
            in
            eqExpList as1 as2 *)
      in
      let eq (f1,e1,t1) (f2,e2,t2) =
        let c = MyCFG.Node.compare f1 f2 in
        if c <> 0 then c else
          let c = eq e1 e2 in
          if c <> 0 then c else MyCFG.Node.compare t1 t2
      in

      let c = eq x y in
      if c = 0 then compare xs ys else c
end


module VarCS (CS: CallString) (V:Printable.S) : VarType with type t = MyCFG.node * CS.t * V.t =
struct
  type t = MyCFG.node * CS.t * V.t

  let hash (n,l,v) =
    match n with
    | MyCFG.Statement s -> Hashtbl.hash (CS.hash l ,s.sid, V.hash v)
    | MyCFG.Function f -> Hashtbl.hash (CS.hash l, f.vid, V.hash v)
    | MyCFG.FunctionEntry f -> Hashtbl.hash (CS.hash l, f.vid, V.hash v)

  let equal (n1,d1,v1) (n2,d2,v2) =
    MyCFG.Node.equal n1 n2 && CS.equal d1 d2 && V.equal v1 v2

  let getLocation (n,_,_) = MyCFG.getLoc n

  let pretty () (n,d,v) =
    match n with
    | MyCFG.Statement s -> dprintf "node:\"%a\", var: %a" Basetype.CilStmt.pretty s V.pretty v
    | MyCFG.Function f -> dprintf "call: %s, var: %a" f.vname V.pretty v
    | MyCFG.FunctionEntry f -> dprintf "entry: %s, var: %a" f.vname V.pretty v

  let pretty_trace () x =
    dprintf "%a on %a" pretty x Basetype.ProgLines.pretty (getLocation x)

  let var_id (n,_,_) = Var.var_id n

  let line_nr (n,_,_) = (MyCFG.getLoc n).line
  let file_name (n,_,_) = (MyCFG.getLoc n).file
  let description (n,_,_) = sprint 80 (Var.pretty () n)
  let context () (_,c,_) = Pretty.nil
  let node (n,_,_) = n

  let category = function
    | (MyCFG.Statement     s,_,_) -> 1
    | (MyCFG.Function      f,_,_) -> 2
    | (MyCFG.FunctionEntry f,_,_) -> 3

  let compare (n1,d1,v1) (n2,d2,v2) =
    let comp =
      match n1, n2 with
      | MyCFG.FunctionEntry f, MyCFG.FunctionEntry g -> compare f.vid g.vid
      | _                    , MyCFG.FunctionEntry g -> -1
      | MyCFG.FunctionEntry g, _                     -> 1
      | MyCFG.Statement _, MyCFG.Function _  -> -1
      | MyCFG.Function  _, MyCFG.Statement _ -> 1
      | MyCFG.Statement s, MyCFG.Statement l -> compare s.sid l.sid
      | MyCFG.Function  f, MyCFG.Function g  -> compare f.vid g.vid
    in
    if comp<>0 then comp else
      let comp = CS.compare d1 d2 in
        if comp<>0 then comp else V.compare v1 v2

  let printXml f (n,c,v) =
    Var.printXml f n
end

module VarCSC (CS: CallString) : VarType with type t = MyCFG.node * CS.t =
struct
  type t = MyCFG.node * CS.t

  let hash (n,l) =
    match n with
    | MyCFG.Statement s -> Hashtbl.hash (CS.hash l ,s.sid, 0)
    | MyCFG.Function f -> Hashtbl.hash (CS.hash l, f.vid, 1)
    | MyCFG.FunctionEntry f -> Hashtbl.hash (CS.hash l, f.vid, 2)

  let equal (n1,d1) (n2,d2) =
    MyCFG.Node.equal n1 n2 && CS.equal d1 d2

  let getLocation (n,_) = MyCFG.getLoc n

  let pretty () (n,d) =
    match n with
    | MyCFG.Statement s -> dprintf "node:\"%a\"" Basetype.CilStmt.pretty s
    | MyCFG.Function f -> dprintf "call: %s" f.vname
    | MyCFG.FunctionEntry f -> dprintf "entry: %s" f.vname

  let pretty_trace () x =
    dprintf "%a on %a" pretty x Basetype.ProgLines.pretty (getLocation x)

  let var_id (n,_) = Var.var_id n

  let line_nr (n,_) = (MyCFG.getLoc n).line
  let file_name (n,_) = (MyCFG.getLoc n).file
  let description (n,_) = sprint 80 (Var.pretty () n)
  let context () (_,c) = Pretty.nil
  let node (n,_) = n

  let category = function
    | (MyCFG.Statement     s,_) -> 1
    | (MyCFG.Function      f,_) -> 2
    | (MyCFG.FunctionEntry f,_) -> 3

  let compare (n1,d1) (n2,d2) =
    let comp =
      match n1, n2 with
      | MyCFG.FunctionEntry f, MyCFG.FunctionEntry g -> compare f.vid g.vid
      | _                    , MyCFG.FunctionEntry g -> -1
      | MyCFG.FunctionEntry g, _                     -> 1
      | MyCFG.Statement _, MyCFG.Function _  -> -1
      | MyCFG.Function  _, MyCFG.Statement _ -> 1
      | MyCFG.Statement s, MyCFG.Statement l -> compare s.sid l.sid
      | MyCFG.Function  f, MyCFG.Function g  -> compare f.vid g.vid
    in
    if comp<>0 then comp else
      CS.compare d1 d2

  let printXml f (n,c) =
    Var.printXml f n
end

exception Deadcode


(** [Dom (D)] produces D lifted where bottom means dead-code *)
module Dom (LD: Lattice.S) =
struct
  include Lattice.Lift (LD) (struct
      let bot_name = "Dead code"
      let top_name = "Totally unknown and messed up"
    end)

  let lift (x:LD.t) : t = `Lifted x

  let unlift x =
    match x with
    | `Lifted x -> x
    | _ -> raise Deadcode

  let lifted f x =
    match x with
    | `Lifted x -> `Lifted (f x)
    | tb -> tb

  let printXml f = function
    | `Top -> BatPrintf.fprintf f "<value>%s</value>" (Goblintutil.escape top_name)
    | `Bot -> ()
    | `Lifted x -> LD.printXml f x
end


open Xml

module type ResultConf =
sig
  val result_name: string
end

module type RS =
sig
  include Printable.S
  include ResultConf
  type key = Basetype.ProgLinesFun.t
  type value
  val create: int -> t
  val clear: t -> unit
  val copy: t -> t
  val add: t -> key -> value -> unit
  val remove: t -> key -> unit
  val find: t -> key -> value
  val find_all: t -> key -> value list
  val replace : t -> key -> value -> unit
  val mem : t -> key -> bool
  val iter: (key -> value -> unit) -> t -> unit
  val fold: (key -> value -> 'b -> 'b) -> t -> 'b -> 'b
  val length: t -> int

  val resultXML: t -> Xml.xml
  val output: t -> unit
end

module Result (Range: SetDomain.PrintableS) (C: ResultConf) =
struct
  include Hash.Printable (Basetype.ProgLinesFun) (Range)
  include C

  let toXML x =
    let full_result = toXML x in
    let fatten_maps  (o:xml list) (x:xml) :xml list =
      match x with
      | Xml.Element (_,_,child) -> child @ o
      | z -> z::o in

    let group_loc_ch x =
      match x with
      | Xml.Element ("Loc",b,c) -> Xml.Element ("Loc",b,List.fold_left fatten_maps [] c)
      | z -> z in

    match full_result with
    | Xml.Element (_,_,child) ->
      Xml.Element (result_name, [("name", "Who cares?")],
                   List.map group_loc_ch child)
    | _ -> failwith "Empty analysis?"

  let resultXML x = toXML x

  let printXml f xs =
    let print_id f = function
      | MyCFG.Statement stmt  -> BatPrintf.fprintf f "%d" stmt.sid
      | MyCFG.Function g      -> BatPrintf.fprintf f "ret%d" g.vid
      | MyCFG.FunctionEntry g -> BatPrintf.fprintf f "fun%d" g.vid
    in
    let print_one (loc,n,fd) v =
      BatPrintf.fprintf f "<call id=\"%a\" file=\"%s\" line=\"%d\" order=\"%d\">\n" print_id n loc.file loc.line loc.byte;
      BatPrintf.fprintf f "%a</call>\n" Range.printXml v
    in
    iter print_one xs

  let printXmlWarning f () =
    let one_text f (m,l) =
      BatPrintf.fprintf f "\n<text file=\"%s\" line=\"%d\">%s</text>" l.file l.line (GU.escape m)
    in
    let one_w f = function
      | `text (m,l)  -> one_text f (m,l)
      | `group (n,e) ->
        BatPrintf.fprintf f "<group name=\"%s\">%a</group>\n" n (BatList.print ~first:"" ~last:"" ~sep:"" one_text) e
    in
    let one_w f x = BatPrintf.fprintf f "\n<warning>%a</warning>" one_w x in
    List.iter (one_w f) !Messages.warning_table

  let printXmlGlobals f () =
    let one_text f (m,l) =
      BatPrintf.fprintf f "\n<text file=\"%s\" line=\"%d\">%s</text>" l.file l.line m
    in
    let one_w f = function
      | `text (m,l)  -> one_text f (m,l)
      | `group (n,e) ->
        BatPrintf.fprintf f "<group name=\"%s\">%a</group>\n" n (BatList.print ~first:"" ~last:"" ~sep:"" one_text) e
    in
    List.iter (one_w f) !Messages.warning_table

  let output table gtable gtfxml (file: file) =
    if get_string "result"="none" then () else begin
      let out = Messages.get_out result_name !GU.out in
      let module SH = BatHashtbl.Make (Basetype.RawStrings) in
      let file2funs = SH.create 100 in
      let funs2node = SH.create 100 in
      iter (fun (_,n,_) _ -> SH.add funs2node (MyCFG.getFun n).svar.vname n) (Lazy.force table);
      iterGlobals file (function
          | GFun (fd,loc) -> SH.add file2funs loc.file fd.svar.vname
          | _ -> ()
        );
      let p_node f = function
        | MyCFG.Statement stmt  -> BatPrintf.fprintf f "%d" stmt.sid
        | MyCFG.Function g      -> BatPrintf.fprintf f "ret%d" g.vid
        | MyCFG.FunctionEntry g -> BatPrintf.fprintf f "fun%d" g.vid
      in
      let p_nodes f xs =
        List.iter (BatPrintf.fprintf f "<node name=\"%a\"/>\n" p_node) xs
      in
      let p_funs f xs =
        let one_fun n =
          BatPrintf.fprintf f "<function name=\"%s\">\n%a</function>\n" n p_nodes (SH.find_all funs2node n)
        in
        List.iter one_fun xs
      in
      let write_file f fn =
        Messages.xml_file_name := fn;
        BatPrintf.printf "Writing xml to temp. file: %s\n%!" fn;
        BatPrintf.fprintf f "<run><parameters>%a</parameters><result>\n" (BatArray.print ~first:"" ~last:"" ~sep:" " BatString.print) BatSys.argv;
        BatEnum.iter (fun b -> BatPrintf.fprintf f "<file name=\"%s\" path=\"%s\">\n%a</file>\n" (Filename.basename b) b p_funs (SH.find_all file2funs b)) (SH.keys file2funs);
        BatPrintf.fprintf f "%a" printXml (Lazy.force table);
        gtfxml f gtable;
        printXmlWarning f ();
        BatPrintf.fprintf f "</result></run>\n";
        BatPrintf.fprintf f "%!"
      in
      if get_bool "g2html" then
        BatFile.with_temporary_out ~mode:[`create;`text;`delete_on_exit] write_file
      else
        let f = BatIO.output_channel out in
        write_file f (get_string "outfile")
    end
end



(* Experiment to reduce the number of arguments on transfer functions and allow
   sub-analyses. The list sub contains the current local states of analyses in
   the same order as writen in the dependencies list (in MCP).

   The foreign states when calling special_fn or enter are joined if the foreign
   analysis tries to be path-sensitive in these functions. First try to only
   depend on simple analyses.

   It is not clear if we need pre-states, post-states or both on foreign analyses.
*)
type ('d,'g) ctx =
  { ask      : Queries.t -> Queries.Result.t
  ; local    : 'd
  ; global   : varinfo -> 'g
  ; presub   : (string * Obj.t) list
  ; postsub  : (string * Obj.t) list
  ; spawn    : varinfo -> 'd -> unit
  ; split    : 'd -> exp -> bool -> unit
  ; sideg    : varinfo -> 'g -> unit
  ; assign   : ?name:string -> lval -> exp -> unit
  }

let swap_st ctx st =
  {ctx with local=st}

let set_st_gl ctx st gl spawn_tr eff_tr split_tr =
  {ctx with local=st;
            global=gl;
            spawn=spawn_tr ctx.spawn;
            sideg=eff_tr ctx.sideg;
            split=split_tr ctx.split}


type ('v, 'd, 'g) ctx' =
  { ask'      : Queries.t -> Queries.Result.t
  ; local'    : 'v -> 'd
  ; global'   : varinfo -> 'g
  ; spawn'    : varinfo -> 'd -> unit
  (* ; split'    : 'd -> exp -> bool -> unit *)
  ; sideg'    : varinfo -> 'g -> unit
  }

module type GoodSpec =
sig

  module V' : sig
    include Printable.S
    val flag: t
  end 
  module D' : Lattice.S
  module G' : Lattice.S

  val init     : unit -> unit
  val finalize : unit -> unit

  val startstate' : V'.t -> D'.t
  val otherstate' : V'.t -> D'.t


  val sync'  : (V'.t, D'.t, G'.t) ctx' -> V'.t -> D'.t * (varinfo * G'.t) list
  val query' : (V'.t, D'.t, G'.t) ctx' -> Queries.t -> Queries.Result.t

  val assign': (V'.t, D'.t, G'.t) ctx' -> lval -> exp -> V'.t -> D'.t
  val branch': (V'.t, D'.t, G'.t) ctx' -> exp -> bool -> V'.t -> D'.t
  val body'  : (V'.t, D'.t, G'.t) ctx' -> fundec -> V'.t -> D'.t
  val return': (V'.t, D'.t, G'.t) ctx' -> exp option  -> fundec -> V'.t -> D'.t


  val special' : (V'.t, D'.t, G'.t) ctx' ->
      lval option -> varinfo -> exp list -> V'.t -> D'.t
  val enter'   : (V'.t, D'.t, G'.t) ctx' ->
      lval option -> varinfo -> exp list -> V'.t -> D'.t
  val combine' : (V'.t, D'.t, G'.t) ctx' ->
      lval option -> exp -> varinfo -> exp list -> (V'.t -> D'.t) -> V'.t -> D'.t
end

module type Spec =
sig
  module D : Lattice.S
  module G : Lattice.S
  module C : Printable.S

  val var_count : D.t -> int

  val name : string

  val init : unit -> unit
  val finalize : unit -> unit

  val startstate : varinfo -> D.t
  val morphstate : varinfo -> D.t -> D.t
  val exitstate  : varinfo -> D.t
  val otherstate : varinfo -> D.t

  val should_join : D.t -> D.t -> bool
  val val_of  : C.t -> D.t
  val context : D.t -> C.t
  val call_descr : fundec -> C.t -> string
  val part_access: (D.t, G.t) ctx -> exp -> varinfo option -> bool -> (Access.LSSSet.t * Access.LSSet.t)

  val sync  : (D.t, G.t) ctx -> D.t * (varinfo * G.t) list
  val query : (D.t, G.t) ctx -> Queries.t -> Queries.Result.t
  val assign: (D.t, G.t) ctx -> lval -> exp -> D.t
  val branch: (D.t, G.t) ctx -> exp -> bool -> D.t
  val body  : (D.t, G.t) ctx -> fundec -> D.t
  val return: (D.t, G.t) ctx -> exp option  -> fundec -> D.t
  val intrpt: (D.t, G.t) ctx -> D.t


  val special : (D.t, G.t) ctx -> lval option -> varinfo -> exp list -> D.t
  val enter   : (D.t, G.t) ctx -> lval option -> varinfo -> exp list -> (D.t * D.t) list
  val combine : (D.t, G.t) ctx -> lval option -> exp -> varinfo -> exp list -> D.t -> D.t
end


module type BackwardSpec =
sig
  module D : Lattice.S
  module G : Lattice.S

  val name: string

  val startstate: varinfo -> D.t

  val body: fundec -> D.t -> D.t
  val assign : lval -> exp -> D.t -> D.t
  val enter : lval option -> exp -> exp list -> D.t -> D.t
end

module UnitBackwardSpec : BackwardSpec =
struct
  module D = Lattice.Unit
  module G = Lattice.Unit

  let name = "unit"

  let startstate _ = ()

  let body f st = st
  let assign lv rv st = st
  let enter lvo fn args st = st
end

(** A side-effecting system. *)
module type MonSystem =
sig
  type v    (** variables *)
  type d    (** values    *)
  type 'a m (** basically a monad carrier *)

  (** Variables must be hashable, comparable, etc.  *)
  module Var : VarType with type t = v
  (** Values must form a lattice. *)
  module Dom : Lattice.S with type t = d
  (** box --- needed here for transformations *)
  val box : v -> d -> d -> d

  (** The system in functional form. *)
  val system : v -> ((v -> d) -> (v -> d -> unit) -> d) m
end

(** Any system of side-effecting inequations over lattices. *)
module type IneqConstrSys = MonSystem with type 'a m := 'a list

(** Any system of side-effecting equations over lattices. *)
module type EqConstrSys = MonSystem with type 'a m := 'a option

(** A side-effecting system with globals. *)
module type GlobConstrSys =
sig
  module LVar : VarType
  module GVar : VarType

  module D : Lattice.S
  module G : Lattice.S

  val system : LVar.t -> ((LVar.t -> D.t) -> (LVar.t -> D.t -> unit) -> (GVar.t -> G.t) -> (GVar.t -> G.t -> unit) -> D.t) list
end

(** A solver is something that can translate a system into a solution (hash-table) *)
module type GenericEqBoxSolver =
  functor (S:EqConstrSys) ->
  functor (H:Hash.H with type key=S.v) ->
  sig
    (** The hash-map [solve box xs vs] is a local solution for interesting variables [vs],
        reached from starting values [xs].  *)
    val solve : (S.v -> S.d -> S.d -> S.d) -> (S.v*S.d) list -> S.v list -> S.d H.t
  end

(** A solver is something that can translate a system into a solution (hash-table) *)
module type GenericIneqBoxSolver =
  functor (S: IneqConstrSys) ->
  functor (H:Hash.H with type key=S.v) ->
  sig
    (** The hash-map [solve box xs vs] is a local solution for interesting variables [vs],
        reached from starting values [xs].  *)
    val solve : (S.v -> S.d -> S.d -> S.d) -> (S.v*S.d) list -> S.v list -> S.d H.t
  end

(** A solver is something that can translate a system into a solution (hash-table) *)
module type GenericGlobSolver =
  functor (S:GlobConstrSys) ->
  functor (LH:Hash.H with type key=S.LVar.t) ->
  functor (GH:Hash.H with type key=S.GVar.t) ->
  sig
    (** The hash-map [solve box xs vs] is a local solution for interesting variables [vs],
        reached from starting values [xs].  *)
    val solve : (S.LVar.t*S.D.t) list -> (S.GVar.t*S.G.t) list -> S.LVar.t list -> S.D.t LH.t * S.G.t GH.t
  end

module BackwardsResultType (S:BackwardSpec) =
struct
  open S
  include Printable.Prod (D) (Basetype.CilFundec)
  let isSimple _ = false
  let short w _ = ""
  let toXML (x,_ as st:t) =
    let open Xml in
    let flatten_single = function
      | Element (_,_,[x]) | x ->  x in
    let try_replace_text s = function
      | Element (tag, attr, children) -> Element (tag, ["text", s], children)
      | x -> x
    in
    let esc = Goblintutil.escape in
    let res = try_replace_text "Value" (flatten_single (D.toXML x)) in
    Element ("Node",["text",esc (short 80 st)],[res])
  let pretty () (x,_) = D.pretty () x
  let printXml f (d,fd) =
    D.printXml f d
end


module ResultType2 (S:Spec) =
struct
  open S
  include Printable.Prod3 (C) (D) (Basetype.CilFundec)
  let isSimple _ = false
  let short w (es,x,f:t) = call_descr f es
  let toXML (es,x,_ as st:t) =
    let open Xml in
    let flatten_single = function
      | Element (_,_,[x]) | x ->  x in
    let try_replace_text s = function
      | Element (tag, attr, children) -> Element (tag, ["text", s], children)
      | x -> x
    in
    let esc = Goblintutil.escape in
    let ctx = try_replace_text "Context" (flatten_single (C.toXML es)) in
    let res = try_replace_text "Value" (flatten_single (D.toXML x)) in
    Element ("Node",["text",esc (short 80 st)],[ctx;res])
  let pretty () (_,x,_) = D.pretty () x
  let printXml f (c,d,fd) =
    BatPrintf.fprintf f "<context>\n%a</context>\n%a" C.printXml c D.printXml d
end

module GoodResultType2 (S:GoodSpec) (CS:CallString) (V:Printable.S) =
struct
  open S
  include Printable.Prod3 (Printable.Prod (CS) (V)) (D') (Basetype.CilFundec)
  let isSimple _ = false
  let short w ((es,v),x,f:t) = Basetype.CilFundec.short 80 f
  let toXML ((es,v),x,_ as st:t) =
    let open Xml in
    let flatten_single = function
      | Element (_,_,[x]) | x ->  x in
    let try_replace_text s = function
      | Element (tag, attr, children) -> Element (tag, ["text", s], children)
      | x -> x
    in
    let esc = Goblintutil.escape in
    let ctx = try_replace_text "Context" (flatten_single (CS.toXML es)) in
    let res = try_replace_text "Value" (flatten_single (D'.toXML x)) in
    Element ("Node",["text",esc (short 80 st)],[ctx;res])
  let pretty () (_,x,_) = D'.pretty () x
  let printXml f ((c,v),d,fd) =
    BatPrintf.fprintf f "<path>\n<analysis name=\"base\">\n<value>\n<map>\n<key>callstring:</key>\n%a<key>variable:</key>\n%a<key>value</key>%a</map>\n</value>\n</analysis>\n</path>\n" CS.printXml c V.printXml v D'.printXml d
end

module GoodResultType2C (S:Spec) (CS:CallString) =
struct
  open S
  include Printable.Prod3 (CS) (D) (Basetype.CilFundec)
  let isSimple _ = false
  let short w (es,x,f:t) = Basetype.CilFundec.short 80 f
  let toXML (es,x,_ as st:t) =
    let open Xml in
    let flatten_single = function
      | Element (_,_,[x]) | x ->  x in
    let try_replace_text s = function
      | Element (tag, attr, children) -> Element (tag, ["text", s], children)
      | x -> x
    in
    let esc = Goblintutil.escape in
    let ctx = try_replace_text "Context" (flatten_single (CS.toXML es)) in
    let res = try_replace_text "Value" (flatten_single (D.toXML x)) in
    Element ("Node",["text",esc (short 80 st)],[ctx;res])
  let pretty () (_,x,_) = D.pretty () x
  let printXml f (c,d,fd) =
    BatPrintf.fprintf f "<path>\n<analysis name=\"base\">\n<value>\n<map>\n<key>callstring:</key>\n%a<key>value</key>%a</map>\n</value>\n</analysis>\n</path>\n" CS.printXml c D.printXml d
end

(** Relatively safe default implementations of some boring Spec functions. *)
module DefaultSpec =
struct
  let var_count _ = 0

  let init     () = ()
  let finalize () = ()
  (* no inits nor finalize -- only analyses like Mutex, Base, ... need
     these to do postprocessing or other imperative hacks. *)

  let should_join _ _ = true
  (* hint for path sensitivity --- MCP overrides this so don't we don't bother. *)

  let call_descr f _ = f.svar.vname
  (* prettier name for equation variables --- currently base can do this and
     MCP just forwards it to Base.*)

  let intrpt x = x.local
  (* Just ignore. *)

  let query _ (q:Queries.t) = Queries.Result.top ()
  (* Don't know anything --- most will want to redefine this. *)

  let morphstate v d = d
  (* Only for those who track thread IDs. *)

  let sync ctx     = (ctx.local,[])
  (* Most domains do not have a global part. *)

  let context x = x
  (* Everything is context sensitive --- override in MCP and maybe elsewhere*)

  let val_of x = x
  (* Assume that context is same as local domain. *)

  let part_access _ _ _ _ =
    (Access.LSSSet.singleton (Access.LSSet.empty ()), Access.LSSet.empty ())
    (* No partitioning on accesses and not locks *)
end
