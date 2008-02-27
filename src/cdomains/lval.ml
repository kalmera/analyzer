(* 
 * Copyright (c) 2005-2007,
 *     * University of Tartu
 *     * Vesal Vojdani <vesal.vojdani@gmail.com>
 *     * Kalmer Apinis <kalmera@ut.ee>
 *     * Jaak Randmets <jaak.ra@gmail.com>
 *     * Toomas Römer <toomasr@gmail.com>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 * 
 *     * Redistributions of source code must retain the above copyright notice,
 *       this list of conditions and the following disclaimer.
 * 
 *     * Redistributions in binary form must reproduce the above copyright notice,
 *       this list of conditions and the following disclaimer in the documentation
 *       and/or other materials provided with the distribution.
 * 
 *     * Neither the name of the University of Tartu nor the names of its
 *       contributors may be used to endorse or promote products derived from
 *       this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *)

open Cil
open Pretty

type ('a, 'b) offs = [
  | `NoOffset 
  | `Field of 'a * ('a,'b) offs
  | `Index of 'b * ('a,'b) offs
  ] 
  
module Offset (Idx: Printable.S) =
struct
  type t = Offs of ((fieldinfo, Idx.t) offs) | Bot
  
  include Printable.Std
  include Lattice.StdCousot
  
  let name () = "Offset"
  
  let from_offset x : t = Offs x  
 
  let top () = Offs `NoOffset 
  let bot () = Bot
 
  let is_bot x = 
    match x with 
      | Bot -> true 
      | _ -> false

  let is_top x =
    match x with
      | Offs `NoOffset -> true
      | _ -> false
  
  let equal x y = 
    match x, y with
      | Offs x, Offs y -> x == y
      | Bot, Bot -> true
      | _ -> false
  
  let leq x y = 
    match x, y with
      | Bot, _ -> true
      | Offs _, Offs _ -> true
      | _, Bot -> false
  
  let isSimple x = true
  
  let meet x y =
    let rec offs_meet x y  =
      match x, y with
        | `NoOffset, x -> x
        | x, `NoOffset -> x
        | `Field (x1,y1), `Field (x2,y2) when x1 == x2 
            -> `Field (x1, offs_meet y1 y2)
        | `Index (x1,y1), `Index (x2,y2) when Idx.equal x1 x2
            -> `Index (x1, offs_meet y1 y2)
        | _ -> `NoOffset
    in
    match x, y with
      | Bot, _ -> Bot 
      | _, Bot -> Bot 
      | Offs (`Field x), Offs (`Index y) -> Bot 
      | Offs (`Index x), Offs (`Field y) -> Bot
      | Offs x, Offs y -> Offs (offs_meet x y)

  let join x y =
    let rec offs_join x y =
      match x, y with
        | `NoOffset, x -> `NoOffset
        | x, `NoOffset -> `NoOffset
        | `Field (x1,y1), `Field (x2,y2) when x1 == x2 
            -> `Field (x1, offs_join y1 y2)
        | `Index (x1,y1), `Index (x2,y2) when Idx.equal x1 x2
            -> `Index (x1, offs_join y1 y2)
        | _ -> `NoOffset
    in
    match x, y with
      | Bot, x -> x 
      | x, Bot -> x 
      | Offs (`Field x), Offs (`Index y) -> Offs `NoOffset 
      | Offs (`Index x), Offs (`Field y) -> Offs `NoOffset
      | Offs x, Offs y -> Offs (offs_join x y)
  
  let short _ x =
    let rec offs_short x = 
      match x with 
        | `NoOffset -> ""
        | `Index (x,o) -> (Idx.short 80 x) ^ (offs_short o) 
        | `Field (x,o) -> (x.fname) ^ (offs_short o) 
    in
    match x with 
      | Offs x -> offs_short x
      | Bot -> "Erronous offset"
      
  let pretty_f sf () x = text (sf 80 x)
  let toXML_f sf x = Xml.Element ("Leaf", [("text", sf 80 x)],[]) 
  
  let pretty = pretty_f short
  let toXML = toXML_f short
end

module type S =
sig
  type heap
  type field
  type idx
  include Printable.S

  val null_ptr: unit -> t
  val str_ptr: unit -> t
  val is_null: t -> bool
  val get_location: t -> location 
  val classify: t -> int
  val class_name: int -> string

  val from_var: varinfo -> t
  (** Creates an address from variable. *)  
  val from_var_offset: (varinfo * (field,idx) offs) -> t
  (** Creates an address from a variable and offset. *) 
  val to_var_offset: t -> (varinfo * (field,idx) offs) list
  (** Get the offset *)
  val to_var: t -> varinfo list
  (** Strips the varinfo out of the address representation. *)
  val to_var_may: t -> varinfo list
  val to_var_must: t -> varinfo list
  (** Strips the varinfo out of the address representation. *)
  val get_type: t -> typ
  (** Finds the type of the address location. *)
end

module Lval (Idx: Printable.S) = 
struct
  type heap = unit
  type field = fieldinfo
  type idx = Idx.t
  type t = Addr of (varinfo * (field, idx) offs) | NullPtr | StrPtr
  include Printable.Std
  
  let null_ptr () = NullPtr
  let str_ptr () = StrPtr
  let is_null a =
    match a with 
      | NullPtr -> true
      | _ -> false

  let get_location x =
    match x with 
      | Addr (x,_) -> x.vdecl 
      | _ -> Cil.builtinLoc 
  
  let classify x = 
    match x with
      | Addr (x,_) when x.vglob -> 2
      | Addr (x,_) when x.vdecl.line = -1 -> -1
      | Addr (x,_) when x.vdecl.line = -3 -> 5
      | Addr (x,_) when x.vdecl.line = -4 -> 4
      | _ -> 1
  
  let class_name n = 
    match n with
      |  1 -> "Local"
      |  2 -> "Global"
      |  4 -> "Context"
      |  5 -> "Parameter"
      | -1 -> "Temp"
      |  _ -> "None"        
  let from_var x = Addr (x, `NoOffset)
  
  let from_var_offset x = Addr x
  
  let to_var a =
    match a with
      | Addr (x,_) -> [x]
      | StrPtr
      | NullPtr    -> []
  let to_var_may a =
    match a with
      | Addr (x,_) -> [x]
      | StrPtr
      | NullPtr    -> []
  let to_var_must a = 
    match a with
      | Addr (x,`NoOffset) -> [x]
      | _ -> []
      
  let to_var_offset a =
    match a with
      | Addr x -> [x]
      | _      -> []

  let get_type_addr (x, ofs) = 
    let unarray t = match t with
      | TArray (t,_,_) -> t
      | _ -> failwith "C'est Unpossible!"
    in let rec find_type t ofs = match ofs with
      | `NoOffset -> t
      | `Field (fld, ofs) -> find_type fld.ftype ofs
      | `Index (idx, ofs) -> find_type (unarray t) ofs
    in
      find_type x.vtype ofs
  
  let get_type x =
    match x with
      | Addr x  -> get_type_addr x
      | StrPtr  -> charPtrType
      | NullPtr -> voidType

  let copy x = x
  let isSimple _  = true

  let short_addr (x, offs) = 
    let rec off_str ofs = 
      match ofs with
        | `NoOffset -> ""
        | `Field (fld, ofs) -> "." ^ fld.fname ^ off_str ofs
        | `Index (v, ofs) -> "[" ^ Idx.short Goblintutil.summary_length v ^ "]" ^ off_str ofs
    in
      x.Cil.vname ^ off_str offs

  let short _ x = 
    match x with 
      | Addr x  -> short_addr x
      | StrPtr  -> "STRING"
      | NullPtr -> "NULL"

  let toXML_f_addr sf (x,y) = 
    let esc = Goblintutil.escape in
    let typeinf = esc (Pretty.sprint Goblintutil.summary_length (Cil.d_type () x.Cil.vtype)) in
    let info = "id=" ^ esc (string_of_int x.Cil.vid) ^ "; type=" ^ typeinf in
      Xml.Element ("Leaf", [("text", esc (sf max_int (Addr (x,y)))); ("info", info)],[])

  let toXML_f sf x =
    match x with 
      | Addr x  -> toXML_f_addr sf x
      | StrPtr | NullPtr -> Xml.Element ("Leaf", [("text", short max_int x)],[])

  let pretty_f sf () x = Pretty.text (sf max_int x)

  let toXML = toXML_f short 
  let pretty = pretty_f short 
end