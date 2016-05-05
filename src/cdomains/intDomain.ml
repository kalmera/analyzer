open GobConfig
open Pretty

module GU = Goblintutil
module JB = Json
module M = Messages

module type S =
sig
  include Lattice.S
  val to_int: t -> int64 option
  val of_int: int64 -> t
  val is_int: t -> bool

  val to_bool: t -> bool option
  val of_bool: bool -> t
  val is_bool: t -> bool
  val to_excl_list: t -> int64 list option
  val of_excl_list: int64 list -> t
  val is_excl_list: t -> bool
  val of_interval: int64 * int64 -> t
  val starting   : int64 -> t
  val ending     : int64 -> t
  val maximal    : t -> int64 option
  val minimal    : t -> int64 option

  val neg: t -> t
  val add: t -> t -> t
  val sub: t -> t -> t
  val mul: t -> t -> t
  val div: t -> t -> t
  val rem: t -> t -> t

  val lt: t -> t -> t
  val gt: t -> t -> t
  val le: t -> t -> t
  val ge: t -> t -> t
  val eq: t -> t -> t
  val ne: t -> t -> t

  val bitnot: t -> t
  val bitand: t -> t -> t
  val bitor : t -> t -> t
  val bitxor: t -> t -> t
  val shift_left : t -> t -> t
  val shift_right: t -> t -> t

  val lognot: t -> t
  val logand: t -> t -> t
  val logor : t -> t -> t

  val cast_to_width : int -> t -> t
end

(* TODO functor for different sizes *)

module Interval32 : S with type t = (int64 * int64) option =
struct
  open Int64

  type t = (int64 * int64) option

  let max_int_f b = Int64.sub (Int64.shift_left Int64.one (b-1)) Int64.one
  let min_int_f b = Int64.neg (Int64.shift_left Int64.one (b-1))

  let max_int = max_int_f 32
  let min_int = min_int_f 32

  let top () = Some (min_int, max_int)
  let bot () = None
  let is_top x = x=top ()
  let is_bot = function None -> true | _ -> false

  let hash (x:t) = Hashtbl.hash x
  let equal (x:t) y = x=y
  let compare (x:t) y = Pervasives.compare x y
  let short _ = function None -> "bottom" | Some (x,y) -> "["^to_string x^","^to_string y^"]"
  let isSimple _ = true
  let name () = "32bit intervals"
  let pretty_f sh () x = text (sh 80 x)
  let pretty = pretty_f short
  let toXML_f sh x = Xml.Element ("Leaf", [("text", sh 80 x)],[])
  let toXML = toXML_f short
  let printXml f x = BatPrintf.fprintf f "<value>\n<data>\n%s\n</data>\n</value>\n" (short 800 x)
  let pretty_diff () (x,y) = Pretty.dprintf "%a instead of %a" pretty x pretty y


  let norm = function None -> None | Some (x,y) ->
    if Int64.compare x y > 0 then None
    else if Int64.compare min_int x > 0 || Int64.compare max_int y < 0 then top ()
    else Some (x,y)

  let (@@) f x = f x

  let equal x y =
    match x, y with
    | None, None -> true
    | Some (x1,x2), Some (y1,y2) -> Int64.compare x1 y1 = 0 && Int64.compare x2 y2 = 0
    | _ -> false

  let leq (x:t) (y:t) =
    match x, y with
    | None, _ -> true
    | Some _, None -> false
    | Some (x1,x2), Some (y1,y2) -> Int64.compare x1 y1 >= 0 && Int64.compare x2 y2 <= 0

  let join (x:t) y =
    match x, y with
    | None, z | z, None -> z
    | Some (x1,x2), Some (y1,y2) -> norm @@ Some (min x1 y1, max x2 y2)

  let meet (x:t) y =
    match x, y with
    | None, z | z, None -> None
    | Some (x1,x2), Some (y1,y2) -> norm @@ Some (max x1 y1, min x2 y2)

  let is_int = function Some (x,y) when Int64.compare x y = 0 -> true | _ -> false
  let of_int x = norm @@ Some (x,x)
  let to_int = function Some (x,y) when Int64.compare x y = 0 -> Some x | _ -> None

  let of_interval (x,y) = norm @@ Some (x,y)

  let of_bool = function true -> Some (Int64.one,Int64.one) | false -> Some (Int64.zero,Int64.zero)
  let is_bool = function None -> false | Some (x,y) ->
    if Int64.compare x Int64.zero = 0 && Int64.compare y Int64.zero = 0 then true
    else not (leq (of_int Int64.zero) (Some (x,y)))
  let to_bool = function None -> None | Some (x,y) ->
    if Int64.compare x Int64.zero = 0 && Int64.compare y Int64.zero = 0 then Some false
    else if leq (of_int Int64.zero) (Some (x,y)) then None else Some true

  let starting n = norm @@ Some (n,max_int)
  let ending   n = norm @@ Some (min_int,n)
  let maximal = function None -> None | Some (x,y) -> Some y
  let minimal = function None -> None | Some (x,y) -> Some x

  let to_excl_list _ = None
  let of_excl_list _ = top ()
  let is_excl_list _ = false

  let cast_to_width b = function
    | None -> None
    | Some (x,y) -> norm @@ Some (max x (min_int_f b),min y (max_int_f b))

  let widen x y =
    match x, y with
    | None, z | z, None -> z
    | Some (l0,u0), Some (l1,u1) ->
      let l2 = if Int64.compare l0 l1 = 0 then l0 else min l1 min_int in
      let u2 = if Int64.compare u0 u1 = 0 then u0 else max u1 max_int in
      norm @@ Some (l2,u2)

  let narrow x y =
    match x, y with
    | _,None | None, _ -> None
    | Some (x1,x2), Some (y1,y2) ->
      let lr = if Int64.compare min_int x1 = 0 then y1 else x1 in
      let ur = if Int64.compare max_int x2 = 0 then y2 else x2 in
      norm @@ Some (lr,ur)

  let log f i1 i2 =
    match is_bot i1, is_bot i2 with
    | true, _
    | _   , true -> bot ()
    | _ ->
      match to_bool i1, to_bool i2 with
      | Some x, Some y -> of_bool (f x y)
      | _              -> top ()

  let logor  = log (||)
  let logand = log (&&)

  let log1 f i1 =
    if is_bot i1 then
      bot ()
    else
      match to_bool i1 with
      | Some x -> of_bool (f x)
      | _      -> top ()

  let lognot = log1 not

  let bit f i1 i2 =
    match is_bot i1, is_bot i2 with
    | true, _
    | _   , true -> bot ()
    | _ ->
      match to_int i1, to_int i2 with
      | Some x, Some y -> (try of_int (f x y) with Division_by_zero -> top ())
      | _              -> top ()

  let bitxor = bit Int64.logxor
  let bitand = bit Int64.logand
  let bitor  = bit Int64.logor

  let bit1 f i1 =
    if is_bot i1 then
      bot ()
    else
      match to_int i1 with
      | Some x -> of_int (f x)
      | _      -> top ()

  let bitnot = bit1 Int64.lognot
  let shift_right = bit (fun x y -> Int64.shift_right x (Int64.to_int y))
  let shift_left  = bit (fun x y -> Int64.shift_left  x (Int64.to_int y))
  let rem  = bit Int64.rem

  let neg = function None -> None | Some (x,y) -> norm @@ Some (Int64.neg y, Int64.neg x)
  let add x y =
    match x, y with
    | None, _ | _, None -> None
    | Some (x1,x2), Some (y1,y2) -> norm @@ Some (Int64.add x1 y1, Int64.add x2 y2)

  let sub i1 i2 = add i1 (neg i2)

  let mul x y =
    match x, y with
    | None, _ | _, None -> bot ()
    | Some (x1,x2), Some (y1,y2) ->
      let x1y1 = (Int64.mul x1 y1) in let x1y2 = (Int64.mul x1 y2) in
      let x2y1 = (Int64.mul x2 y1) in let x2y2 = (Int64.mul x2 y2) in
      norm @@ Some ((min (min x1y1 x1y2) (min x2y1 x2y2)),
                    (max (max x1y1 x1y2) (max x2y1 x2y2)))

  let rec div x y =
    match x, y with
    | None, _ | _, None -> bot ()
    | Some (x1,x2), Some (y1,y2) ->
      begin match y1, y2 with
        | 0L, 0L       -> bot ()
        | 0L, _        -> div (Some (x1,x2)) (Some (1L,y2))
        | _      , 0L  -> div (Some (x1,x2)) (Some (y1,(-1L)))
        | _ when leq (of_int 0L) (Some (y1,y2)) -> top ()
        | _ ->
          let x1y1n = (Int64.div x1 y1) in let x1y2n = (Int64.div x1 y2) in
          let x2y1n = (Int64.div x2 y1) in let x2y2n = (Int64.div x2 y2) in
          let x1y1p = (Int64.div x1 y1) in let x1y2p = (Int64.div x1 y2) in
          let x2y1p = (Int64.div x2 y1) in let x2y2p = (Int64.div x2 y2) in
          norm @@ Some ((min (min x1y1n x1y2n) (min x2y1n x2y2n)),
                        (max (max x1y1p x1y2p) (max x2y1p x2y2p)))
      end
  let ne i1 i2 = sub i1 i2

  let eq i1 i2 =
    match to_bool (sub i1 i2) with
    | Some x -> of_bool (not x)
    | None -> None

  let ge x y =
    match x, y with
    | None, _ | _, None -> None
    | Some (x1,x2), Some (y1,y2) ->
      if Int64.compare y2 x1 <= 0 then of_bool true
      else if Int64.compare x2 y1 < 0 then of_bool false
      else top ()

  let le x y =
    match x, y with
    | None, _ | _, None -> None
    | Some (x1,x2), Some (y1,y2) ->
      if Int64.compare x2 y1 <= 0 then of_bool true
      else if Int64.compare  y2 x1 < 0 then of_bool false
      else top ()

  let gt x y =
    match x, y with
    | None, _ | _, None -> None
    | Some (x1,x2), Some (y1,y2) ->
      if Int64.compare  y2 x1 < 0 then of_bool true
      else if Int64.compare x2 y1 <= 0 then of_bool false
      else top ()

  let lt x y =
    match x, y with
    | None, _ | _, None -> None
    | Some (x1,x2), Some (y1,y2) ->
      if Int64.compare x2 y1 < 0 then of_bool true
      else if Int64.compare y2 x1 <= 0 then of_bool false
      else top ()
end


exception Unknown
exception Error

module Integers : S with type t = int64  = (* no top/bot, order is <= *)
struct
  include Printable.Std
  include Lattice.StdCousot
  let name () = "integers"
  type t = int64
  let hash (x:t) = ((Int64.to_int x) - 787) * 17
  let equal (x:t) (y:t) = x=y
  let copy x = x
  let top () = raise Unknown
  let is_top _ = false
  let bot () = raise Error
  let is_bot _ = false
  let isSimple _  = true
  let short _ x = if x = GU.inthack then "*" else Int64.to_string x
  let pretty_f _ _ x = text (Int64.to_string x)
  let toXML_f _ x = Xml.Element ("Leaf", [("text", Int64.to_string x)],[])
  let toXML m = toXML_f short m
  let pretty () x = pretty_f short () x
  let leq x y = x <= y
  let pretty_diff () (x,y) = Pretty.dprintf "%a instead of %a" pretty x pretty y
  let join x y = if Int64.compare x y > 0 then x else y
  let meet x y = if Int64.compare x y > 0 then y else x

  let of_bool x = if x then Int64.one else Int64.zero
  let to_bool' x = x <> Int64.zero
  let to_bool x = Some (to_bool' x)
  let is_bool _ = true
  let of_int  x = x
  let to_int  x = Some x
  let is_int  _ = true

  let to_excl_list x = None
  let of_excl_list x = top ()
  let is_excl_list x = false
  let of_interval  x = top ()
  let starting     x = top ()
  let ending       x = top ()
  let maximal      x = None
  let minimal      x = None

  let neg  = Int64.neg
  let add  = Int64.add (* TODO: signed overflow is undefined behavior! *)
  let sub  = Int64.sub
  let mul  = Int64.mul
  let div x y = (* TODO: exception is not very helpful here?! *)
    match y with
    | 0L -> raise Division_by_zero  (* -- this is for a bug (#253) where div throws *)
    | _  -> Int64.div x y           (*    sigfpe and ocaml has somehow forgotten how to deal with it*)
  let rem x y =
    match y with
    | 0L -> raise Division_by_zero  (* ditto *)
    | _  -> Int64.rem x y
  let lt n1 n2 = of_bool (n1 <  n2)
  let gt n1 n2 = of_bool (n1 >  n2)
  let le n1 n2 = of_bool (n1 <= n2)
  let ge n1 n2 = of_bool (n1 >= n2)
  let eq n1 n2 = of_bool (n1 =  n2)
  let ne n1 n2 = of_bool (n1 <> n2)
  let bitnot = Int64.lognot
  let bitand = Int64.logand
  let bitor  = Int64.logor
  let bitxor = Int64.logxor
  let shift_left  n1 n2 = Int64.shift_left n1 (Int64.to_int n2)
  let shift_right n1 n2 = Int64.shift_right n1 (Int64.to_int n2)
  let lognot n1    = of_bool (not (to_bool' n1))
  let logand n1 n2 = of_bool ((to_bool' n1) && (to_bool' n2))
  let logor  n1 n2 = of_bool ((to_bool' n1) || (to_bool' n2))
  let pretty_diff () (x,y) = dprintf "%s: %a instead of %a" (name ()) pretty x pretty y
  let cast_to_width w x =
    let y = BatInt64.pow 2L (Int64.of_int w) in
    if y=0L then
      x
    else
      Int64.rem x (BatInt64.pow 2L (Int64.of_int w)) (* TODO: this is implementation-dependent! *)

  let printXml f x = BatPrintf.fprintf f "<value>\n<data>\n%s\n</data>\n</value>\n" (short 800 x)
end

module FlatPureIntegers = (* Integers, but raises Unknown/Error on join/meet *)
struct
  include Integers

  let top () = raise Unknown
  let bot () = raise Error
  let leq = equal
  let pretty_diff () (x,y) = Pretty.dprintf "Integer %a instead of %a" pretty x pretty y
  let join x y = if equal x y then x else top ()
  let meet x y = if equal x y then x else bot ()
end

module Flat (Base: S) = (* identical to Lift, but goes to `Top/`Bot if Base raises Unknown/Error *)
struct
  include Lattice.Flat (Base) (struct
      let top_name = "Unknown int"
      let bot_name = "Error int"
    end)

  let name () = "flat integers"
  let cast_to_width _ x = x

  let of_int  x = `Lifted (Base.of_int x)
  let to_int  x = match x with
    | `Lifted x -> Base.to_int x
    | _ -> None
  let is_int  x = match x with
    | `Lifted x -> true
    | _ -> false

  let of_bool x = `Lifted (Base.of_bool x)
  let to_bool x = match x with
    | `Lifted x -> Base.to_bool x
    | _ -> None
  let is_bool = is_int

  let to_excl_list x = None
  let of_excl_list x = top ()
  let is_excl_list x = false
  let of_interval  x = top ()
  let starting     x = top ()
  let ending       x = top ()
  let maximal      x = None
  let minimal      x = None

  let lift1 f x = match x with
    | `Lifted x ->
      (try `Lifted (f x) with Unknown -> `Top | Error -> `Bot)
    | x -> x
  let lift2 f x y = match x,y with
    | `Lifted x, `Lifted y ->
      (try `Lifted (f x y) with Unknown -> `Top | Error -> `Bot)
    | `Bot, `Bot -> `Bot
    | _ -> `Top

  let neg  = lift1 Base.neg
  let add  = lift2 Base.add
  let sub  = lift2 Base.sub
  let mul  = lift2 Base.mul
  let div  = lift2 Base.div
  let rem  = lift2 Base.rem
  let lt = lift2 Base.lt
  let gt = lift2 Base.gt
  let le = lift2 Base.le
  let ge = lift2 Base.ge
  let eq = lift2 Base.eq
  let ne = lift2 Base.ne
  let bitnot = lift1 Base.bitnot
  let bitand = lift2 Base.bitand
  let bitor  = lift2 Base.bitor
  let bitxor = lift2 Base.bitxor
  let shift_left  = lift2 Base.shift_left
  let shift_right = lift2 Base.shift_right
  let lognot = lift1 Base.lognot
  let logand = lift2 Base.logand
  let logor  = lift2 Base.logor
  let printXml f x = BatPrintf.fprintf f "<value>\n<data>\n%s\n</data>\n</value>\n" (short 800 x)
end

module Lift (Base: S) = (* identical to Flat, but does not go to `Top/`Bot if Base raises Unknown/Error *)
struct
  include Lattice.Lift (Base) (struct
      let top_name = "MaxInt"
      let bot_name = "MinInt"
    end)

  let name () = "lifted integers"
  let cast_to_width _ x = x

  let of_int  x = `Lifted (Base.of_int x)
  let to_int  x = match x with
    | `Lifted x -> Base.to_int x
    | _ -> None
  let is_int  x = match x with
    | `Lifted x -> true
    | _ -> false

  let of_bool x = `Lifted (Base.of_bool x)
  let to_bool x = match x with
    | `Lifted x -> Base.to_bool x
    | _ -> None
  let is_bool = is_int

  let to_excl_list x = None
  let of_excl_list x = top ()
  let is_excl_list x = false
  let of_interval  x = top ()
  let starting     x = top ()
  let ending       x = top ()
  let maximal      x = None
  let minimal      x = None

  let lift1 f x = match x with
    | `Lifted x -> `Lifted (f x)
    | x -> x
  let lift2 f x y = match x,y with
    | `Lifted x, `Lifted y -> `Lifted (f x y)
    | `Bot, `Bot -> `Bot
    | _ -> `Top

  let neg  = lift1 Base.neg
  let add  = lift2 Base.add
  let sub  = lift2 Base.sub
  let mul  = lift2 Base.mul
  let div  = lift2 Base.div
  let rem  = lift2 Base.rem
  let lt = lift2 Base.lt
  let gt = lift2 Base.gt
  let le = lift2 Base.le
  let ge = lift2 Base.ge
  let eq = lift2 Base.eq
  let ne = lift2 Base.ne
  let bitnot = lift1 Base.bitnot
  let bitand = lift2 Base.bitand
  let bitor  = lift2 Base.bitor
  let bitxor = lift2 Base.bitxor
  let shift_left  = lift2 Base.shift_left
  let shift_right = lift2 Base.shift_right
  let lognot = lift1 Base.lognot
  let logand = lift2 Base.logand
  let logor  = lift2 Base.logor
  let printXml f x = BatPrintf.fprintf f "<value>\n<data>\n%s\n</data>\n</value>\n" (short 800 x)
end

module Flattened = Flat (Integers)
module Lifted    = Lift (Integers)

module Reverse (Base: S) = (* TODO: (almost) copy of Lattice.Reverse... *)
struct
  include Base
  let bot = Base.top
  let is_bot = Base.is_top
  let top = Base.bot
  let is_top = Base.is_bot
  let leq x y = Base.leq y x
  let join x y = Base.meet x y
  let meet x y = Base.join x y
  let name () = "Reversed (" ^ name () ^ ")"
  let pretty_diff () (x,y) =
    Pretty.dprintf "%s: %a not leq %a" (name ()) pretty x pretty y
end

module Trier =
struct
  module S = SetDomain.Make (Integers)
  include Printable.Std
  include Lattice.StdCousot
  type t = [
    | `Excluded of S.t
    | `Definite of Integers.t
    | `Bot
  ]

  let cast_to_width w = function
    | `Excluded s -> `Excluded (S.empty ()) (* TODO can we do better here? *)
    | `Definite x -> `Definite (Integers.cast_to_width w x)
    | `Bot -> `Bot
  let hash (x:t) =
    match x with
    | `Excluded s -> S.hash s
    | `Definite i -> 83*Integers.hash i
    | `Bot -> 61426164

  let equal x y =
    match x, y with
    | `Bot, `Bot -> true
    | `Definite x, `Definite y -> Integers.equal x y
    | `Excluded xs, `Excluded ys -> S.equal xs ys
    | _ -> false

  let name () = "trier"
  let top () = `Excluded (S.empty ())
  let is_top x =
    match x with
    | `Excluded s -> S.is_empty s
    | _ -> false
  let bot () = `Bot
  let is_bot x = x = `Bot

  let bot_name = "Error int"
  let top_name = "Unknown int"

  let isSimple _ = true

  let short w x =
    match x with
    | `Bot -> bot_name
    | `Definite x -> Integers.short w x
    (* Print the empty exclusion as if it where a distinct top element: *)
    | `Excluded s when S.is_empty s -> top_name
    (* Prepend the exclusion sets with something: *)
    | `Excluded s -> "Not " ^ S.short w s

  let pretty_f sf () x = text (sf max_int x)
  let toXML_f sf x = Xml.Element ("Leaf", [("text", sf Goblintutil.summary_length x)],[])
  let toXML m = toXML_f short m
  let pretty () x = pretty_f short () x

  let leq x y = match (x,y) with
    (* `Bot <= x is always true *)
    | `Bot, _ -> true
    (* Anything except bot <= bot is always false *)
    | _, `Bot -> false
    (* Two known values are leq whenver equal *)
    | `Definite x, `Definite y -> x = y
    (* A definite value is leq all exclusion sets that don't contain it *)
    | `Definite x, `Excluded s -> not (S.mem x s)
    (* No finite exclusion set can be leq than a definite value *)
    | `Excluded _, `Definite _ -> false
    (* Excluding X <= Excluding Y whenever Y <= X *)
    | `Excluded x, `Excluded y -> S.subset y x

  let pretty_diff () (x,y) = Pretty.dprintf "Integer %a instead of %a" pretty x pretty y

  let join x y =
    match (x,y) with
    (* The least upper bound with the bottom element: *)
    | `Bot, x -> x
    | x, `Bot -> x
    (* The case for two known values: *)
    | `Definite x, `Definite y ->
      (* If they're equal, it's just THAT value *)
      if x = y then `Definite x
      (* Unless one of them is zero, we can exclude it: *)
      else if x = Int64.zero || y = Int64.zero then top ()
      else `Excluded (S.singleton Int64.zero)
    (* A known value and an exclusion set... the definite value should no
     * longer be excluded: *)
    | `Excluded s, `Definite x -> `Excluded (S.remove x s)
    | `Definite x, `Excluded s -> `Excluded (S.remove x s)
    (* For two exclusion sets, only their intersection can be excluded: *)
    | `Excluded x, `Excluded y -> `Excluded (S.inter x y)

  let meet x y =
    match (x,y) with
    (* Gretest LOWER bound with the least element is trivial: *)
    | `Bot, _ -> `Bot
    | _, `Bot -> `Bot
    (* Definite elements are either equal or the glb is bottom *)
    | `Definite x, `Definite y -> if x = y then `Definite x else `Bot
    (* The glb of a definite element and an exclusion set is either bottom or
     * just the element itself, if it isn't in the exclusion set *)
    | `Excluded s, `Definite x -> if S.mem x s then `Bot else `Definite x
    | `Definite x, `Excluded s -> if S.mem x s then `Bot else `Definite x
    (* The greatest lower bound of two exclusion sets is their union, this is
     * just DeMorgans Law *)
    | `Excluded x, `Excluded y -> `Excluded (S.union x y)

  let of_bool x = `Definite (Integers.of_bool x)
  let to_bool x =
    match x with
    | `Definite x -> Integers.to_bool x
    | `Excluded s when S.mem Int64.zero s -> Some true
    | _ -> None
  let is_bool x =
    match x with
    | `Definite x -> true
    | `Excluded s -> S.mem Int64.zero s
    | _ -> false

  let of_int  x = `Definite (Integers.of_int x)
  let to_int  x = match x with
    | `Definite x -> Integers.to_int x
    | _ -> None
  let is_int  x = match x with
    | `Definite x -> true
    | _ -> false

  let of_interval (x,y) = if Int64.compare x y == 0 then of_int x else top ()
  let ending   x = top ()
  let starting x = top ()
  let maximal _ = None
  let minimal _ = None

  let of_excl_list l = `Excluded (List.fold_right S.add l (S.empty ()))
  let is_excl_list l = match l with `Excluded _ -> true | _ -> false
  let to_excl_list x = match x with
    | `Definite _ -> None
    | `Excluded s -> Some (S.elements s)
    | `Bot -> None

  (* Default behaviour for unary operators, simply maps the function to the
   * Trier data structure. *)
  let lift1 f x = match x with
    | `Excluded s -> `Excluded (S.map f s)
    | `Definite x -> `Definite (f x)
    | `Bot -> `Bot

  let lift2 f x y = match x,y with
    (* We don't bother with exclusion sets: *)
    | `Excluded _, _ -> top ()
    | _, `Excluded _ -> top ()
    (* The good case: *)
    | `Definite x, `Definite y -> (try `Definite (f x y) with | Division_by_zero -> top ())
    (* If any one of them is bottom, we return top *)
    | _ -> top ()

  (* Default behaviour for binary operators that are injective in either
   * argument, so that Exclusion Sets can be used: *)
  let lift2_inj f x y = match x,y with
    (* If both are exclusion sets, there isn't anything we can do: *)
    | `Excluded _, `Excluded _ -> top ()
    (* A definite value should be applied to all members of the exclusion set *)
    | `Definite x, `Excluded s -> `Excluded (S.map (f x)  s)
    (* Same thing here, but we should flip the operator to map it properly *)
    | `Excluded s, `Definite x -> let f x y = f y x in `Excluded (S.map (f x) s)
    (* The good case: *)
    | `Definite x, `Definite y -> `Definite (f x y)
    (* If any one of them is bottom, we return bottom *)
    | _ -> `Bot

  (* The equality check: *)
  let eq x y = match x,y with
    (* Not much to do with two exclusion sets: *)
    | `Excluded _, `Excluded _ -> top ()
    (* Is x equal to an exclusion set, if it is a member then NO otherwise we
     * don't know: *)
    | `Definite x, `Excluded s -> if S.mem x s then of_bool false else top ()
    | `Excluded s, `Definite x -> if S.mem x s then of_bool false else top ()
    (* The good case: *)
    | `Definite x, `Definite y -> of_bool (x=y)
    (* If either one of them is bottom, we return bottom *)
    | _ -> `Bot

  (* The inequality check: *)
  let ne x y = match x,y with
    (* Not much to do with two exclusion sets: *)
    | `Excluded _, `Excluded _ -> top ()
    (* Is x inequal to an exclusion set, if it is a member then Yes otherwise we
     * don't know: *)
    | `Definite x, `Excluded s -> if S.mem x s then of_bool true else top ()
    | `Excluded s, `Definite x -> if S.mem x s then of_bool true else top ()
    (* The good case: *)
    | `Definite x, `Definite y -> of_bool (x<>y)
    (* If either one of them is bottom, we return bottom *)
    | _ -> `Bot

  let neg  = lift1 Integers.neg
  let add  = lift2_inj Integers.add
  let sub  = lift2_inj Integers.sub
  let mul  = lift2_inj Integers.mul
  let div  = lift2 Integers.div
  let rem  = lift2 Integers.rem
  let lt = lift2 Integers.lt
  let gt = lift2 Integers.gt
  let le = lift2 Integers.le
  let ge = lift2 Integers.ge
  let bitnot = lift1 Integers.bitnot
  let bitand = lift2 Integers.bitand
  let bitor  = lift2 Integers.bitor
  let bitxor = lift2 Integers.bitxor
  let shift_left  = lift2 Integers.shift_left
  let shift_right = lift2 Integers.shift_right
  (* TODO: lift does not treat Not {0} as true. *)
  let logand = lift2 Integers.logand
  let logor  = lift2 Integers.logor
  let lognot = eq (of_int 0L)
  let printXml f x = BatPrintf.fprintf f "<value>\n<data>\n%s\n</data>\n</value>\n" (short 800 x)
end

module InfInt =
struct
  (*module Int64 = OverflowInt64*)

  type t = NInf | Fin of int64 | PInf

  let equal x y =
    match x, y with
    | NInf, NInf -> true
    | PInf, PInf -> true
    | Fin x, Fin y when Int64.compare x y == 0 -> true
    | _ -> false

  let compare x y =
    match x, y with
    | NInf , NInf   ->  0
    | NInf , _      -> -1
    | Fin x, NInf   ->  1
    | Fin x, Fin y  -> Int64.compare x y
    | Fin x, _      -> -1
    | PInf , PInf   ->  0
    | PInf , _      ->  1

  let max x y =
    match x, y with
    | NInf, _      -> y
    | _   ,NInf    -> x
    | PInf, _      -> PInf
    | _   ,PInf    -> PInf
    | Fin x, Fin y -> if x < y then Fin y else Fin x

  let min x y =
    match x, y with
    | NInf, _      -> NInf
    | _   ,NInf    -> NInf
    | PInf, _      -> y
    | _   ,PInf    -> x
    | Fin x, Fin y -> if x < y then Fin x else Fin y

  let leq x y = compare x y <= 0
  let lt  x y = compare x y <  0

  let neg x =
    match x with
    | NInf -> PInf
    | PInf -> NInf
    | Fin x-> Fin (Int64.neg x)

  let addp d x y =
    match x, y with
    | NInf , NInf  -> NInf
    | NInf , Fin _ -> NInf
    | NInf , PInf  -> d
    | Fin _, NInf  -> NInf
    | Fin x, Fin y -> Fin (Int64.add x y)
    | Fin x, PInf  -> PInf
    | PInf , NInf  -> d
    | PInf , Fin x -> PInf
    | PInf , PInf  -> PInf

  let mul x y =
    let nf x = match Int64.compare x 0L with
      | 0          -> Fin 0L
      | x when x<0 -> PInf
      | _          -> NInf
    in
    let pf x = match Int64.compare x 0L with
      | 0          -> Fin 0L
      | x when x<0 -> NInf
      | _          -> PInf
    in
    match x, y with
    | NInf , NInf  -> PInf
    | NInf , Fin x -> nf x
    | NInf , PInf  -> NInf
    | Fin x, NInf  -> nf x
    | Fin x, Fin y -> Fin (Int64.mul x y)
    | Fin x, PInf  -> pf x
    | PInf , NInf  -> NInf
    | PInf , Fin x -> pf x
    | PInf , PInf  -> PInf

  let divp d x y =
    let nf x = match Int64.compare x 0L with
      | 0          -> d
      | x when x<0 -> PInf
      | _          -> NInf
    in
    let pf x = match Int64.compare x 0L with
      | 0          -> d
      | x when x<0 -> NInf
      | _          -> PInf
    in
    match x, y with
    | NInf , NInf  -> d
    | NInf , Fin x -> nf x
    | NInf , PInf  -> d
    | Fin x, NInf  -> nf x
    | Fin x, Fin y -> Fin (Int64.div x y)
    | Fin x, PInf  -> pf x
    | PInf , NInf  -> d
    | PInf , Fin x -> pf x
    | PInf , PInf  -> d

end


module Interval : S with type t = InfInt.t * InfInt.t =
struct
  include Printable.Std
  module I = InfInt
  type t = I.t * I.t
  let name () = "int intervals"

  let of_interval (x,y) = (I.Fin x, I.Fin y)
  let ending   x = (I.NInf , I.Fin x)
  let starting x = (I.Fin x, I.PInf)
  let maximal (_,y:t) =
    match y with
    | I.Fin x -> Some x
    | _ -> None
  let minimal (x,_:t) =
    match x with
    | I.Fin x -> Some x
    | _ -> None

  let equal (x1,x2:t) (y1,y2:t) =
    I.equal x1 y1 && I.equal x2 y2

  let hash (x:t) = Hashtbl.hash x
  let compare (x1,x2:t) (y1,y2:t) =
    let c = I.compare x1 y1 in
    if c == 0 then c else I.compare x2 y2

  let top () = (I.NInf,I.PInf)
  let is_top (x,y) =
    match x, y with
    | I.NInf, I.PInf -> true
    | _              -> false

  let bot () = (I.PInf,I.NInf)
  let is_bot (x,y) =
    I.compare x y > 0

  let isSimple _ = true
  let short _ (x,y) =
    let f p =
      match p with
      | I.NInf -> "-∞"
      | I.PInf -> "∞"
      | I.Fin x-> Int64.to_string x
    in
    if is_bot (x,y) then
      "⊥"
    else if (I.compare x y == 0) then
      "["^f x^"]"
    else
      "["^f x^".."^f y^"]"

  let pretty_f sh () x = text (sh 10 x)
  let pretty = pretty_f short
  let toXML_f sf x = Xml.Element ("Leaf", [("text", sf Goblintutil.summary_length x)],[])
  let toXML = toXML_f short
  let pretty_diff () (x,y) = dprintf "%s: %a instead of %a" (name ()) pretty x pretty y

  let leq  (x1,x2) (y1,y2) = I.leq y1 x1 && I.leq x2 y2
  let join (x1,x2) (y1,y2) = (I.min x1 y1, I.max x2 y2)
  let meet (x1,x2) (y1,y2) = (I.max x1 y1, I.min x2 y2)

  let widen (l0,u0 as i1) (l1,u1 as i2) =
    let res = (if I.lt l1 l0 then I.NInf else l0), (if I.lt u0 u1 then I.PInf else u0) in
    if M.tracing then M.tracel "widen" "Widening %a and %a yields %a\n" pretty i1 pretty i2 pretty res;
    res

  let narrow (l0,u0) (l1,u1) =
    let lr = match l0 with
      | I.NInf -> l1
      | _      -> l0 in
    let ur = match u0 with
      | I.PInf -> u1
      | _      -> u0 in
    (lr,ur)

  let of_int i = (I.Fin i, I.Fin i)
  let to_int (x,y:t) =
    match x, y with
    | I.Fin x, I.Fin y when Int64.compare x y == 0 -> Some x
    | _ -> None
  let is_int (x,y:t) =
    match x, y with
    | I.Fin x, I.Fin y when Int64.compare x y == 0 -> true
    | _ -> false

  let of_bool b = if b then (I.Fin 1L, I.PInf) else (I.Fin 0L, I.Fin 0L)
  let to_bool i =
    match i with
    | I.Fin 0L, I.Fin 0L -> Some false
    | _ when not (leq (of_int 0L) i) -> Some true
    | _ -> None
  let is_bool i =
    match to_bool i with
    | Some _ -> true
    | _      -> false

  let neg (x,y) = (I.neg y, I.neg x)
  let add (x1,x2) (y1,y2) = (I.addp I.NInf x1 y1, I.addp I.PInf x2 y2)
  let sub i1 i2 = add i1 (neg i2)
  let mul (x1,x2) (y1,y2) =
    if is_bot (x1, x2) || is_bot (y1, y2) then
      bot ()
    else begin
      let x1y1 = (I.mul x1 y1) in let x1y2 = (I.mul x1 y2) in
      let x2y1 = (I.mul x2 y1) in let x2y2 = (I.mul x2 y2) in
      (I.min (I.min x1y1 x1y2) (I.min x2y1 x2y2)),
      (I.max (I.max x1y1 x1y2) (I.max x2y1 x2y2))
    end

  let rec div (x1,x2:t) (y1,y2:t) =
    if is_bot (x1, x2) || is_bot (y1, y2) then
      bot ()
    else begin
      match y1, y2 with
      | I.Fin 0L, I.Fin 0L -> bot ()
      | I.Fin 0L, _        -> div (x1,x2) (I.Fin 1L,y2)
      | _      , I.Fin 0L  -> div (x1,x2) (y1, I.Fin (-1L))
      | _ when leq (of_int 0L) (y1,y2) -> top ()
      | _ ->
        let x1y1n = (I.divp I.NInf x1 y1) in let x1y2n = (I.divp I.NInf x1 y2) in
        let x2y1n = (I.divp I.NInf x2 y1) in let x2y2n = (I.divp I.NInf x2 y2) in
        let x1y1p = (I.divp I.PInf x1 y1) in let x1y2p = (I.divp I.PInf x1 y2) in
        let x2y1p = (I.divp I.PInf x2 y1) in let x2y2p = (I.divp I.PInf x2 y2) in
        (I.min (I.min x1y1n x1y2n) (I.min x2y1n x2y2n)),
        (I.max (I.max x1y1p x1y2p) (I.max x2y1p x2y2p))
    end

  let log f i1 i2 =
    match is_bot i1, is_bot i2 with
    | true, _
    | _   , true -> bot ()
    | _ ->
      match to_bool i1, to_bool i2 with
      | Some x, Some y -> of_bool (f x y)
      | _              -> top ()

  let logor  = log (||)
  let logand = log (&&)

  let log1 f i1 =
    if is_bot i1 then
      bot ()
    else
      match to_bool i1 with
      | Some x -> of_bool (f x)
      | _      -> top ()

  let lognot = log1 not

  let bit f i1 i2 =
    match is_bot i1, is_bot i2 with
    | true, _
    | _   , true -> bot ()
    | _ ->
      match to_int i1, to_int i2 with
      | Some x, Some y -> (try of_int (f x y) with Division_by_zero -> top ())
      | _              -> top ()

  let bitxor = bit Int64.logxor
  let bitand = bit Int64.logand
  let bitor  = bit Int64.logor

  let bit1 f i1 =
    if is_bot i1 then
      bot ()
    else
      match to_int i1 with
      | Some x -> of_int (f x)
      | _      -> top ()

  let bitnot = bit1 Int64.lognot
  let shift_right = bit (fun x y -> Int64.shift_right x (Int64.to_int y))
  let shift_left  = bit (fun x y -> Int64.shift_left  x (Int64.to_int y))
  let rem  = bit Int64.rem

  let ne i1 i2 =
    match is_bot i1, is_bot i2 with
    | true, _
    | _   , true -> bot ()
    | _ ->
      match sub i1 i2 with
      | (I.Fin 0L, I.Fin 0L) -> of_bool false
      | x when not (leq (I.Fin 0L, I.Fin 0L) x) -> of_bool true
      | _ -> top ()

  let eq i1 i2 =
    match is_bot i1, is_bot i2 with
    | true, _
    | _   , true -> bot ()
    | _ ->
      match sub i1 i2 with
      | (I.Fin 0L, I.Fin 0L) -> of_bool true
      | x when not (leq (I.Fin 0L, I.Fin 0L) x) -> of_bool false
      | _ -> top ()

  let ge (x1,x2) (y1,y2) =
    if is_bot (x1, x2) || is_bot (y1, y2) then
      bot ()
    else begin
      if I.leq y2 x1 then of_bool true  else
      if I.lt  x2 y1 then of_bool false else
        top ()
    end

  let le (x1,x2) (y1,y2) =
    if is_bot (x1, x2) || is_bot (y1, y2) then
      bot ()
    else begin
      if I.leq x2 y1 then of_bool true  else
      if I.lt  y2 x1 then of_bool false else
        top ()
    end

  let gt (x1,x2) (y1,y2) =
    if is_bot (x1, x2) || is_bot (y1, y2) then
      bot ()
    else begin
      if I.lt  y2 x1 then of_bool true  else
      if I.leq x2 y1 then of_bool false else
        top ()
    end

  let lt (x1,x2) (y1,y2) =
    if is_bot (x1, x2) || is_bot (y1, y2) then
      bot ()
    else begin
      if I.lt  x2 y1 then of_bool true  else
      if I.leq y2 x1 then of_bool false else
        top ()
    end

  let printXml f x = BatPrintf.fprintf f "<value>\n<data>\n%s\n</data>\n</value>\n" (short 800 x)

  let of_excl_list l = top ()
  let is_excl_list l = false
  let to_excl_list x = None
(*
  let add x y = try add x y with OverflowInt64.Overflow _ -> top ()
  let sub x y = try sub x y with OverflowInt64.Overflow _ -> top ()
  let mul x y = try mul x y with OverflowInt64.Overflow _ -> top ()
  *)
  let cast_to_width _ x = x
end


(* BOOLEAN DOMAINS *)

module type BooleansNames =
sig
  val truename: string
  val falsename: string
end

module MakeBooleans (N: BooleansNames) =
struct
  include Printable.Std
  include Lattice.StdCousot
  type t = bool
  let hash = function true -> 51534333 | _ -> 561123444
  let equal (x:t) (y:t) = x=y
  let name () = "booleans"
  let cast_to_width _ x = x
  let copy x = x
  let isSimple _ = true
  let short _ x = if x then N.truename else N.falsename
  let pretty_f sf _ x = Pretty.text (sf Goblintutil.summary_length x)
  let toXML_f sf x = Xml.Element ("Leaf", [("text", sf Goblintutil.summary_length x)],[])
  let toXML m = toXML_f short m
  let pretty () x = pretty_f short () x

  let top () = true
  let is_top x = x
  let bot () = false
  let is_bot x = not x
  let leq x y = not x || y
  let join = (||)
  let meet = (&&)

  let of_bool x = x
  let to_bool x = Some x
  let is_bool x = not x
  let of_int x  = x = Int64.zero
  let to_int x  = if x then None else Some Int64.zero
  let is_int x  = not x

  let to_excl_list x = None
  let of_excl_list x = top ()
  let is_excl_list x = false
  let of_interval  x = top ()
  let starting     x = top ()
  let ending       x = top ()
  let maximal      x = None
  let minimal      x = None

  let neg x = x
  let add x y = x || y
  let sub x y = x || y
  let mul x y = x && y
  let div x y = true
  let rem x y = true
  let lt n1 n2 = true
  let gt n1 n2 = true
  let le n1 n2 = true
  let ge n1 n2 = true
  let eq n1 n2 = true
  let ne n1 n2 = true
  let bitnot x = true
  let bitand x y = x && y
  let bitor  x y = x || y
  let bitxor x y = x && not y || not x && y
  let shift_left  n1 n2 = n1
  let shift_right n1 n2 = n1
  let lognot = (not)
  let logand = (&&)
  let logor  = (||)
  let pretty_diff () (x,y) = dprintf "%s: %a instead of %a" (name ()) pretty x pretty y
  let printXml f x = BatPrintf.fprintf f "<value>\n<data>\n%s\n</data>\n</value>\n" (short 800 x)
end

module Booleans = MakeBooleans (
  struct
    let truename = "True"
    let falsename = "False"
  end)

module None : S with type t = unit  =
struct
  include Printable.Std
  include Lattice.StdCousot
  let cast_to_width _ x = x
  let name () = "none"
  type t = unit
  let hash () = 101010
  let equal _ _ = true
  let copy x = ()
  let top () = ()
  let is_top _ = true
  let bot () = ()
  let is_bot _ = true
  let isSimple _  = true
  let short _ x = "?"
  let pretty_f _ _ x = text "?"
  let toXML_f _ x = Xml.Element ("Leaf", [("text", "?")],[])
  let toXML m = toXML_f short m
  let pretty () x = pretty_f short () x
  let leq x y = true
  let join () () = ()
  let meet x y = ()

  let of_bool _ = ()
  let to_bool _ = None
  let is_bool _ = false
  let of_int  _ = ()
  let to_int  _ = None
  let is_int  _ = false

  let is_excl_list _ = false
  let of_excl_list _ = top ()
  let to_excl_list _ = None
  let of_interval  x = top ()
  let starting     x = top ()
  let ending       x = top ()
  let maximal      x = None
  let minimal      x = None

  let neg x = ()
  let add _ _ = ()
  let sub _ _ = ()
  let mul _ _ = ()
  let div _ _ = ()
  let rem _ _ = ()
  let lt n1 n2 = ()
  let gt n1 n2 = ()
  let le n1 n2 = ()
  let ge n1 n2 = ()
  let eq n1 n2 = ()
  let ne n1 n2 = ()
  let bitnot n1 = ()
  let bitand n1 n2 = ()
  let bitor  n1 n2 = ()
  let bitxor n1 n2 = ()
  let shift_left  n1 n2 = ()
  let shift_right n1 n2 = ()
  let lognot n1    = ()
  let logand n1 n2 = ()
  let logor  n1 n2 = ()
  let pretty_diff () (x,y) = dprintf "%s: %a instead of %a" (name ()) pretty x pretty y
  let printXml f x = BatPrintf.fprintf f "<value>\n<data>\n%s\n</data>\n</value>\n" (short 800 x)
end


module Enums : S = struct
  open Batteries
  module I = Integers
  type e = I.t
  type t = Neg of e list | Pos of e list

  let name () = "enums"

  let bot () = Pos []
  let top () = Neg []
  let short _ = function
    | Pos[] -> "bot" | Neg[] -> "top"
    | Pos xs -> "{" ^ (String.concat ", " (List.map (I.short 30) xs)) ^ "}"
    | Neg xs -> "not {" ^ (String.concat ", " (List.map (I.short 30) xs)) ^ "}"

  let of_int x = Pos [x]
  let cast_to_width w = function Pos xs -> Pos (List.map (I.cast_to_width w) xs |> List.sort_unique compare) | Neg _ -> top ()

  let of_interval (x,y) =
    let rec build_set set start_num end_num =
      if start_num > end_num then set
      else (build_set (set @ [start_num]) (Int64.add start_num (Int64.of_int 1)) end_num) in
    Pos (build_set [] x y)

  let rec merge_cup a b = match a,b with
    | [],x | x,[] -> x
    | x::xs, y::ys -> (match compare x y with
        | 0 -> x :: merge_cup xs ys
        | 1 -> y :: merge_cup a ys
        | _ -> x :: merge_cup xs b
      )
  let rec merge_cap a b = match a,b with
    | [],_ | _,[] -> []
    | x::xs, y::ys -> (match compare x y with
        | 0 -> x :: merge_cap xs ys
        | 1 -> merge_cap a ys
        | _ -> merge_cap xs b
      )
  let rec merge_sub a b = match a,b with
    | [],_ -> []
    | _,[] -> a
    | x::xs, y::ys -> (match compare x y with
        | 0 -> merge_sub xs ys
        | 1 -> merge_sub a ys
        | _ -> x :: merge_sub xs b
      )
  (* let merge_sub x y = Set.(diff (of_list x) (of_list y) |> to_list) *)
  let join = curry @@ function
    | Pos x, Pos y -> Pos (merge_cup x y)
    | Neg x, Neg y -> Neg (merge_cap x y)
    | Neg x, Pos y
    | Pos y, Neg x -> Neg (merge_sub x y)
  let meet = curry @@ function
    | Pos x, Pos y -> Pos (merge_cap x y)
    | Neg x, Neg y -> Neg (merge_cup x y)
    | Pos x, Neg y
    | Neg y, Pos x -> Pos (merge_sub x y)
  (* let join x y = let r = join x y in print_endline @@ "join " ^ short 10 x ^ " " ^ short 10 y ^ " = " ^ short 10 r; r *)
  (* let meet x y = let r = meet x y in print_endline @@ "meet " ^ short 10 x ^ " " ^ short 10 y ^ " = " ^ short 10 r; r *)

  let widen x y = join x y
  let narrow x y = meet x y

  let leq x y = join x y = y

  let abstr_compare = curry @@ function
    | Neg _, Neg _ -> Pos[-1L; 0L ;1L]
    | Pos[],_ | _,Pos[] -> Pos[]
    | Pos x, Pos y ->
      let x_max = List.last x in
      let x_min = List.hd x in
      let y_max = List.last y in
      let y_min = List.hd y in
      if  x_max < y_min then Pos[-1L]
      else if y_max < x_min then Pos[1L]
      else if x_min = y_max then
        if  y_min = x_max then Pos[0L]
        else Pos[0L;1L]
      else if y_min = x_max then Pos[-1L;0L]
      else Pos[-1L;0L;1L]
    | Pos l, Neg l' ->
      (match merge_sub l l' with
       | [] -> Pos[-1L;1L]
       | _ -> Pos[-1L;0L;1L]
      )
    | Neg l, Pos l' ->
      (match merge_sub l' l with
       | [] -> Pos[-1L;1L]
       | _ -> Pos[-1L;0L;1L]
      )

  let max_elems () = get_int "ana.int.enums_max" (* maximum number of resulting elements before going to top *)
  let lift1 f = function
    | Pos[x] -> Pos[f x]
    | Pos xs when List.length xs <= max_elems () -> Pos (List.sort_unique compare @@ List.map f xs)
    | _ -> Neg[]
  let lift2 f = curry @@ function
    | Pos[],_| _,Pos[] -> Pos[]
    | Pos[x],Pos[y] -> Pos[f x y]
    | Pos xs,Pos ys ->
      let r = List.cartesian_product xs ys |> List.map (uncurry f) |> List.sort_unique compare in
      if List.length r <= max_elems () then Pos r else Neg[]
    | _,_ -> Neg[]
  let lift2 f a b =
    try lift2 f a b with Division_by_zero -> top ()

  let neg  = lift1 I.neg
  let add  = curry @@ function
    | Pos[0L],x | x,Pos[0L] -> x
    | x,y -> lift2 I.add x y
  let sub  = lift2 I.sub
  let mul  = curry @@ function
    | Pos[1L],x | x,Pos[1L] -> x
    | Pos[0L],_ | _,Pos[0L] -> Pos[0L]
    | x,y -> lift2 I.mul x y
  let div  = curry @@ function
    | Pos[1L],x | x,Pos[1L] -> x
    | Pos[0L],_ -> Pos[0L]
    | _,Pos[0L] -> top ()
    | x,y -> lift2 I.div x y
  let rem  = lift2 I.rem
  let lt = lift2 I.lt
  let gt = lift2 I.gt
  let le = lift2 I.le
  let ge = lift2 I.ge
  let eq = lift2 I.eq
  let ne = lift2 I.ne
  let bitnot = lift1 I.bitnot
  let bitand = lift2 I.bitand
  let bitor  = lift2 I.bitor
  let bitxor = lift2 I.bitxor
  let shift_left  = lift2 I.shift_left
  let shift_right = lift2 I.shift_right
  let lognot = lift1 I.lognot
  let logand = lift2 I.logand
  let logor  = lift2 I.logor

  let is_top x = x = top ()
  let is_bot x = x = bot ()
  let hash = Hashtbl.hash
  let equal = (=)
  let compare = compare
  let isSimple _  = true
  let pretty_list xs = text "(" ++ (try List.reduce (fun a b -> a ++ text "," ++ b) xs with _ -> nil) ++ text ")"
  let pretty_f _ _ = function
    | Pos [] -> text "bot"
    | Neg [] -> text "top"
    | Pos xs -> text "Pos" ++ pretty_list (List.map (I.pretty ()) xs)
    | Neg xs -> text "Neg" ++ pretty_list (List.map (I.pretty ()) xs)
  let toXML_f sh x = Xml.Element ("Leaf", [("text", sh 80 x)],[])
  let toXML m = toXML_f short m
  let pretty () x = pretty_f short () x
  let pretty_diff () (x,y) = Pretty.dprintf "%a instead of %a" pretty x pretty y
  let printXml f x = BatPrintf.fprintf f "<value>\n<data>\n%s\n</data>\n</value>\n" (short 800 x)

  let of_bool x = Pos [if x then Int64.one else Int64.zero]
  let to_bool = function
    | Pos [] | Neg [] -> None
    | Pos [0L] -> Some false
    | Pos xs when List.for_all ((<>) 0L) xs -> Some true
    | Neg xs when List.exists ((=) 0L) xs -> Some true
    | _ -> None
  let is_bool = Option.is_some % to_bool
  let of_int  x = Pos [x]
  let to_int = function Pos [x] -> Some x | _ -> None
  let is_int = Option.is_some % to_int

  let to_excl_list = function Neg x when x<>[] -> Some x | _ -> None
  let of_excl_list x = Neg x
  let is_excl_list = Option.is_some % to_excl_list
  let starting     x = top ()
  let ending       x = top ()
  let maximal = function Pos xs when xs<>[] -> Some (List.last xs) | _ -> None
  let minimal = function Pos (x::xs) -> Some x | _ -> None
  (* let of_incl_list xs = failwith "TODO" *)
end

