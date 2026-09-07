(** Wrapped Intervals model a range of values on a circle, allowing both
    unsigned and signed interpretation whilst maintaining precision in
    intermediate steps.

    Based on the APLAS12 paper "Signedness-Agnostic Program Analysis: Precise
    Integer Bounds for Low-Level Code" by Navas, Schachte, Søndergaard, and
    Stuckey (doi: 10.1007/978-3-642-35182-2_9).

    Implementation in the Crab Static Analyser used as a general reference and
    for the unsigned and signed division functions.
    https://github.com/seahorn/crab/blob/418b63c66b91f04bf36ae59d5eecb936c48836ee/include/crab/domains/wrapped_interval_impl.hpp

    Algorithms for bitwise operations on unsigned intervals used for building
    signedness agnostic versions were adapted from Chapter 4.3 of Hacker's
    Delight (Second Edition) by Henry S. Warren.

    Further details about implementation can be found in
    docs/dev/wrapped_intervals.pdf *)

open Bincaml_util.Common
open Bitvec

module WrappedIntervalsLattice = struct
  let name = "wrappedIntervals"

  type t = Top | Interval of { lower : Bitvec.t; upper : Bitvec.t } | Bot
  [@@deriving ord, eq]

  let show l =
    match l with
    | Bot -> Bincaml_util.Unicode.bot_char
    | Top -> Bincaml_util.Unicode.top_char
    | Interval { lower; upper } -> "⟦" ^ show lower ^ ", " ^ show upper ^ "⟧"

  let interval lower upper =
    size_is_equal lower upper;
    if Bitvec.(equal lower (add upper (of_int ~size:(size upper) 1))) then Top
    else Interval { lower; upper }

  let umin ~width = zero ~size:width
  let umax ~width = ones ~size:width
  let smin ~width = concat (ones ~size:1) (zero ~size:(width - 1))
  let smax ~width = zero_extend ~extension:1 (ones ~size:(width - 1))
  let sp ~width = interval (umax ~width) (umin ~width)
  let np ~width = interval (smax ~width) (smin ~width)
  let top = Top
  let bottom = Bot
  let pretty t = Containers_pp.text (show t)

  let cardinality ~width v =
    match v with
    | Bot -> Z.of_int 0
    | Top -> Z.pow (Z.of_int 2) width
    | Interval { lower; upper } ->
        sub upper lower |> to_unsigned_bigint |> Z.add (Z.of_int 1)

  let is_singleton v =
    match v with
    | Bot | Top -> None
    | Interval { lower; upper } ->
        if Bitvec.equal lower upper then Some lower else None

  let complement v =
    match v with
    | Bot -> Top
    | Top -> Bot
    | Interval { lower; upper } ->
        let new_lower = add upper (of_int ~size:(size upper) 1) in
        let new_upper = sub lower (of_int ~size:(size lower) 1) in
        interval new_lower new_upper

  let member t e =
    match t with
    | Bot -> false
    | Top -> true
    | Interval { lower; upper } ->
        size_is_equal lower e;
        size_is_equal upper e;
        ule (sub e lower) (sub upper lower)

  let leq a b =
    match (a, b) with
    | a, b when equal a b -> true
    | Bot, _ | _, Top -> true
    | Top, _ | _, Bot -> false
    | Interval { lower = al; upper = au }, Interval { lower = bl; upper = bu }
      ->
        member b al && member b au && ((not (member a bl)) || not (member a bu))

  let join a b =
    if leq a b then b
    else if leq b a then a
    else
      match (a, b) with
      | Interval { lower = al; upper = au }, Interval { lower = bl; upper = bu }
        ->
          let al_mem = member b al in
          let au_mem = member b au in
          let bl_mem = member a bl in
          let bu_mem = member a bu in
          if al_mem && au_mem && bl_mem && bu_mem then top
          else if au_mem && bl_mem then interval al bu
          else if al_mem && bu_mem then interval bl au
          else
            let width = size al in
            let inner_span = cardinality ~width (interval au bl) in
            let outer_span = cardinality ~width (interval bu al) in
            if
              Z.lt inner_span outer_span
              || (Z.equal inner_span outer_span && ule al bl)
            then interval al bu
            else interval bl au
      | _, _ -> failwith "unreachable"

  (* Join for multiple intervals to increase precision (join is not monotone) *)
  let lub (ints : t list) =
    let bigger a b =
      match (a, b) with
      | x, y when equal x y -> a
      | Bot, _ | _, Top -> b
      | _, Bot | Top, _ -> a
      | Interval { lower }, _ ->
          let width = size lower in
          if Z.compare (cardinality ~width a) (cardinality ~width b) < 0 then b
          else a
    in
    let gap a b =
      match (a, b) with
      | Interval { upper = au; _ }, Interval { lower = bl; _ }
        when (not (member b au)) && not (member a bl) ->
          complement (interval bl au)
      | _, _ -> bottom
    in
    (*
      Paper mentions last cases of join are omitted for extend, but does not specify which cases.
      In practice, just using join as is works.
    *)
    let extend = join in
    let sorted =
      List.sort
        (fun s t ->
          match (s, t) with
          | Interval { lower = al; _ }, Interval { lower = bl; _ } ->
              Bitvec.compare al bl
          | _, _ -> if equal s t then 0 else if leq s t then -1 else 1)
        ints
    in
    let f1 =
      List.fold_left
        (fun acc t ->
          match t with
          | Interval { lower; upper } when ule upper lower -> extend acc t
          | Top -> extend acc t
          | _ -> acc)
        bottom sorted
    in
    let g, f =
      List.fold_left
        (fun (g, f) t -> (bigger g @@ gap f t, extend f t))
        (bottom, f1) sorted
    in
    complement (bigger g (complement f))

  let widening a b =
    match (a, b) with
    | Bot, s | s, Bot -> s
    | Top, _ | _, Top -> Top
    | Interval { lower = al; upper = au }, Interval { lower = bl; upper = bu }
      ->
        size_is_equal al bl;
        size_is_equal au bu;
        let width = size al in
        if compare b a <= 0 then a
        else if Z.geq (cardinality ~width a) (Z.pow (Z.of_int 2) (width - 1))
        then top
        else
          let joined = join a b in
          if equal joined (interval al bu) then
            join joined
              (interval al
                 (sub (mul au (of_int ~size:width 2)) al
                 |> add (of_int ~size:width 1)))
          else if equal joined (interval bl au) then
            join joined
              (interval
                 (sub
                    (sub (mul al (of_int ~size:width 2)) au)
                    (of_int ~size:width 1))
                 au)
          else if member b al && member b au then
            join b
              (interval bl
                 (sub
                    (bl
                    |> add (mul au (of_int ~size:width 2))
                    |> add (of_int ~size:width 1))
                    (mul al (of_int ~size:width 2))))
          else top

  (* possibly incorrect?! this isn't implemented in crab or described in the paper *)
  let narrowing a b = match (a, b) with Top, i -> i | _ -> a

  let intersect a b =
    match (a, b) with
    | Bot, _ | _, Bot -> []
    | Top, x | x, Top -> [ x ]
    | a, b when equal a b -> [ b ]
    | Interval { lower = al; upper = au }, Interval { lower = bl; upper = bu }
      ->
        let al_mem = member b al in
        let au_mem = member b au in
        let bl_mem = member a bl in
        let bu_mem = member a bu in
        let a_in_b = al_mem && au_mem in
        let b_in_a = bl_mem && bu_mem in
        if a_in_b && b_in_a then [ interval al bu; interval bl au ]
        else if a_in_b then [ a ]
        else if b_in_a then [ b ]
        else if al_mem && (not au_mem) && (not bl_mem) && bu_mem then
          [ interval al bu ]
        else if (not al_mem) && au_mem && bl_mem && not bu_mem then
          [ interval bl au ]
        else []

  let meet a b = lub (intersect a b)

  let nsplit ~width t =
    match t with
    | Bot -> []
    | Top ->
        [
          interval (umin ~width) (smax ~width);
          interval (smin ~width) (umax ~width);
        ]
    | Interval { lower; upper } ->
        let width = size lower in
        let np = np ~width in
        if leq np t then
          [ interval lower (smax ~width); interval (smin ~width) upper ]
        else [ t ]

  let ssplit ~width t =
    match t with
    | Bot -> []
    | Top ->
        [
          interval (umin ~width) (smax ~width);
          interval (smin ~width) (umax ~width);
        ]
    | Interval { lower; upper } ->
        let width = size lower in
        let sp = sp ~width in
        if leq sp t then
          [ interval lower (umax ~width); interval (umin ~width) upper ]
        else [ t ]

  let cut ~width t = List.concat_map (ssplit ~width) (nsplit ~width t)
end

module WrappedIntervalsLatticeOps = struct
  include WrappedIntervalsLattice

  let bind1 f t =
    match t with
    | Bot -> Bot
    | Top -> Top
    | Interval { lower; upper } -> f lower upper

  let neg = bind1 (fun l u -> interval (neg u) (neg l))
  let bitnot = bind1 (fun l u -> interval (bitnot u) (bitnot l))

  let sign_extend ~width t k =
    if width = 0 then Top
    else
      lub
      @@ List.filter_map
           (fun t ->
             match t with
             | Interval { lower; upper } ->
                 Some
                   (interval
                      (sign_extend ~extension:k lower)
                      (sign_extend ~extension:k upper))
             | _ -> None)
           (nsplit ~width t)

  let zero_extend ~width t k =
    if width = 0 then
      let zeros = zero ~size:k in
      interval zeros zeros
    else
      lub
      @@ List.filter_map
           (fun t ->
             match t with
             | Interval { lower; upper } ->
                 Some
                   (interval
                      (zero_extend ~extension:k lower)
                      (zero_extend ~extension:k upper))
             | _ -> None)
           (ssplit ~width t)

  let add ~width s t =
    match (s, t) with
    | Bot, _ | _, Bot -> bottom
    | Interval { lower = al; upper = au }, Interval { lower = bl; upper = bu }
      ->
        if
          Z.(
            leq
              (add (cardinality ~width s) (cardinality ~width t))
              (cardinality ~width top))
        then interval (add al bl) (add au bu)
        else top
    | _, _ -> top

  let sub ~width s t =
    match (s, t) with
    | Bot, _ | _, Bot -> bottom
    | Interval { lower = al; upper = au }, Interval { lower = bl; upper = bu }
      ->
        if
          Z.(
            leq
              (add (cardinality ~width s) (cardinality ~width t))
              (cardinality ~width top))
        then interval (sub al bu) (sub au bl)
        else top
    | _, _ -> top

  let mul ~width s t =
    let rusmul s t =
      let umul =
        match (s, t) with
        | ( Interval { lower = al; upper = au },
            Interval { lower = bl; upper = bu } ) ->
            let w = size al in
            let cond =
              let al = to_unsigned_bigint al in
              let au = to_unsigned_bigint au in
              let bl = to_unsigned_bigint bl in
              let bu = to_unsigned_bigint bu in
              Z.(lt (sub (mul au bu) (mul al bl)) (pow (of_int 2) w))
            in
            if cond then interval (mul al bl) (mul au bu) else top
        | _, _ -> top
      in
      let smul =
        match (s, t) with
        | ( Interval { lower = al; upper = au },
            Interval { lower = bl; upper = bu } ) ->
            let w = size al in
            let msb_hi b =
              Bitvec.(equal (extract ~hi:w ~lo:(w - 1) b) (ones ~size:1))
            in
            let cond (a, b) (c, d) =
              let a = to_unsigned_bigint a in
              let b = to_unsigned_bigint b in
              let c = to_unsigned_bigint c in
              let d = to_unsigned_bigint d in
              let res = Z.(sub (mul a b) (mul c d)) in
              Z.(lt res (pow (of_int 2) w))
              && Z.(lt (neg (pow (of_int 2) w)) res)
            in
            let all_hi = msb_hi al && msb_hi au && msb_hi bl && msb_hi bu in
            let all_lo =
              (not @@ msb_hi al)
              && (not @@ msb_hi au)
              && (not @@ msb_hi bl)
              && (not @@ msb_hi bu)
            in
            if (all_hi || all_lo) && cond (au, bu) (al, bl) then
              interval (mul al bl) (mul au bu)
            else if
              msb_hi al && msb_hi au
              && (not (msb_hi bl))
              && (not (msb_hi bu))
              && cond (au, bl) (al, bu)
            then interval (mul al bu) (mul au bl)
            else if
              (not (msb_hi al))
              && (not (msb_hi au))
              && msb_hi bl && msb_hi bu
              && cond (al, bu) (au, bl)
            then interval (mul au bl) (mul al bu)
            else top
        | _, _ -> top
      in
      intersect umul smul
    in
    lub
    @@ List.concat_map
         (fun a -> List.concat_map (fun b -> rusmul a b) (cut ~width t))
         (cut ~width s)

  (*
    Division implementation derived from Crab
    https://github.com/seahorn/crab/blob/418b63c66b91f04bf36ae59d5eecb936c48836ee/include/crab/domains/wrapped_interval_impl.hpp#L1034-L1091
    https://github.com/seahorn/crab/blob/418b63c66b91f04bf36ae59d5eecb936c48836ee/include/crab/domains/wrapped_interval_impl.hpp#L210-L297
  *)
  let trim_zeroes ~width t =
    let zero = zero ~size:width in
    match t with
    | Bot -> []
    | Top -> [ interval (of_int ~size:width 1) (umax ~width) ]
    | Interval { lower; upper } ->
        let equal = Bitvec.equal in
        if equal lower zero && equal upper zero then []
        else if equal lower zero then [ interval (of_int ~size:width 1) upper ]
        else if equal upper zero then [ interval lower (umax ~width) ]
        else if member t zero then
          [
            interval lower (umax ~width); interval (of_int ~size:width 1) upper;
          ]
        else [ t ]

  let udiv ~width s t =
    let divide s t =
      match (s, t) with
      | Interval { lower = al; upper = au }, Interval { lower = bl; upper = bu }
        ->
          interval (udiv al bu) (udiv au bl)
      | _, _ -> top
    in
    lub
    @@ List.concat_map
         (fun a ->
           List.concat_map
             (fun bs -> List.map (fun b -> divide a b) (trim_zeroes ~width bs))
             (ssplit ~width t))
         (ssplit ~width s)

  let sdiv ~width s t =
    let divide s t =
      match (s, t) with
      | Interval { lower = al; upper = au }, Interval { lower = bl; upper = bu }
        -> (
          let w = size al in
          let msb_hi b =
            Bitvec.(equal (extract ~hi:w ~lo:(w - 1) b) (ones ~size:1))
          in
          let ( = ) = Bitvec.equal in
          let smin, neg1 = (smin ~width:w, umax ~width:w) in
          match (msb_hi al, msb_hi bl) with
          | true, true
            when not ((au = smin && bl = neg1) || (al = smin && bu = neg1)) ->
              interval (sdiv au bl) (sdiv al bu)
          | false, false
            when not ((al = smin && bu = neg1) || (au = smin && bl = neg1)) ->
              interval (sdiv al bu) (sdiv au bl)
          | true, false
            when not ((al = smin && bl = neg1) || (au = smin && bu = neg1)) ->
              interval (sdiv al bl) (sdiv au bu)
          | false, true
            when not ((au = smin && bu = neg1) && al = smin && bl = neg1) ->
              interval (sdiv au bu) (sdiv al bl)
          | _, _ -> top)
      | _, _ -> top
    in
    lub
    @@ List.concat_map
         (fun a ->
           List.concat_map
             (fun bs -> List.map (fun b -> divide a b) (trim_zeroes ~width bs))
             (cut ~width t))
         (cut ~width s)

  let bitlogop ~width min max s t =
    let pre s t =
      match (s, t) with
      | Interval { lower = al; upper = au }, Interval { lower = bl; upper = bu }
        ->
          interval (min (al, au) (bl, bu)) (max (al, au) (bl, bu))
      | _, _ -> top
    in
    lub
    @@ List.concat_map
         (fun a -> List.map (fun b -> pre a b) (ssplit ~width t))
         (ssplit ~width s)

  let bitor =
    let min_or (al, au) (bl, bu) =
      let rec min_or_aux m =
        (* Lazy evaluation trick *)
        let recurse _ = min_or_aux (lshr m (of_int ~size:(size m) 1)) in
        let open Bitvec in
        if is_zero m then bitor al bl
        else if is_nonzero (bitand (bitnot al) bl |> bitand m) then
          let temp = bitor al m |> bitand (neg m) in
          if ule temp au then bitor temp bl else recurse ()
        else if is_nonzero (bitand al (bitnot bl) |> bitand m) then
          let temp = bitor bl m |> bitand (neg m) in
          if ule temp bu then bitor al temp else recurse ()
        else recurse ()
      in
      let init = smin ~width:(size al) in
      min_or_aux init
    in

    let max_or (al, au) (bl, bu) =
      let rec max_or_aux m =
        let open Bitvec in
        let one = of_int ~size:(size m) 1 in
        let recurse _ = max_or_aux (lshr m one) in
        if is_zero m then bitor au bu
        else if is_nonzero (bitand au bu |> bitand m) then
          let tempau = bitor (sub au m) (sub m one) in
          let tempbu = bitor (sub bu m) (sub m one) in
          if uge tempau al then bitor tempau bu
          else if uge tempbu bl then bitor au tempbu
          else recurse ()
        else recurse ()
      in
      let init = smin ~width:(size al) in
      max_or_aux init
    in
    bitlogop min_or max_or

  let bitand =
    let min_and (al, au) (bl, bu) =
      let rec min_and_aux m =
        let recurse _ = min_and_aux (lshr m (of_int ~size:(size m) 1)) in
        let open Bitvec in
        if is_zero m then bitand al bl
        else if is_nonzero (bitand (bitnot al) (bitnot bl) |> bitand m) then
          let tempal = bitand (bitor al m) (neg m) in
          let tempbl = bitand (bitor bl m) (neg m) in
          if ule tempal au then bitand tempal bl
          else if ule tempbl bu then bitand al tempbl
          else recurse ()
        else recurse ()
      in
      let init = smin ~width:(size al) in
      min_and_aux init
    in

    let max_and (al, au) (bl, bu) =
      let rec max_and_aux m =
        let recurse _ = max_and_aux (lshr m (of_int ~size:(size m) 1)) in
        let open Bitvec in
        let one = of_int ~size:(size m) 1 in
        if is_zero m then bitand au bu
        else if is_nonzero (bitand au (bitnot bu) |> bitand m) then
          let temp = bitor (bitand au (bitnot m)) (sub m one) in
          if uge temp al then bitand temp bu else recurse ()
        else if is_nonzero (bitand (bitnot au) bu |> bitand m) then
          let temp = bitor (bitand bu (bitnot m)) (sub m one) in
          if uge temp bl then bitand au temp else recurse ()
        else recurse ()
      in
      let init = smin ~width:(size al) in
      max_and_aux init
    in
    bitlogop min_and max_and

  let bitxor =
    let min_xor (al, au) (bl, bu) =
      let rec min_xor_aux m (al, au) (bl, bu) =
        let recurse = min_xor_aux (lshr m (of_int ~size:(size m) 1)) in
        let open Bitvec in
        if is_zero m then bitxor al bl
        else if is_nonzero (bitand (bitnot al) bl |> bitand m) then
          let temp = bitor al m |> bitand (neg m) in
          let al = if ule temp au then bitor temp bl else al in
          recurse (al, au) (bl, bu)
        else if is_nonzero (bitand al (bitnot bl) |> bitand m) then
          let temp = bitor bl m |> bitand (neg m) in
          let bl = if ule temp bu then bitor al temp else bl in
          recurse (al, au) (bl, bu)
        else recurse (al, au) (bl, bu)
      in
      let init = smin ~width:(size al) in
      min_xor_aux init (al, au) (bl, bu)
    in

    let max_xor (al, au) (bl, bu) =
      let rec max_xor_aux m (al, au) (bl, bu) =
        let open Bitvec in
        let one = of_int ~size:(size m) 1 in
        let recurse = max_xor_aux (lshr m one) in
        if is_zero m then bitxor au bu
        else if is_nonzero (bitand au bu |> bitand m) then
          let tempau = bitor (sub au m) (sub m one) in
          let tempbu = bitor (sub bu m) (sub m one) in
          let au, bu =
            if uge tempau al then (tempau, bu)
            else if uge tempbu bl then (au, tempbu)
            else (au, bu)
          in
          recurse (al, au) (bl, bu)
        else recurse (al, au) (bl, bu)
      in
      let init = smin ~width:(size al) in
      max_xor_aux init (al, au) (bl, bu)
    in
    bitlogop min_xor max_xor

  let truncate t k =
    match t with
    | Bot -> bottom
    | Top -> top
    | Interval { lower; upper } ->
        let w = size lower in
        if w < k then interval (zero ~size:0) (zero ~size:0)
        else
          let truncl = extract ~hi:k ~lo:0 lower in
          let truncu = extract ~hi:k ~lo:0 upper in
          let shiftl = ashr lower (of_int ~size:w k) in
          let shiftu = ashr upper (of_int ~size:w k) in
          if
            Bitvec.(
              (equal shiftl shiftu && ule truncl truncu)
              || equal (add shiftl (of_int ~size:w 1)) shiftu
                 && ugt truncl truncu)
          then interval truncl truncu
          else top

  let bitshop ~width f t k =
    if equal t Bot then t
    else
      Option.map_or ~default:top (fun k ->
          let k =
            to_unsigned_bigint k |> fun k ->
            if Z.fits_int k then Z.to_int k else width + 1
          in
          f ~width t k)
      @@ is_singleton k

  let shl =
    bitshop (fun ~width t k ->
        let k = if width < k then width else k in
        match truncate t (width - k) with
        | Interval { lower; upper } ->
            let lower = Bitvec.zero_extend ~extension:k lower in
            let upper = Bitvec.zero_extend ~extension:k upper in
            interval
              (shl lower (of_int ~size:width k))
              (shl upper (of_int ~size:width k))
        | _ ->
            interval (zero ~size:width)
              (concat (ones ~size:(width - k)) (zero ~size:k)))

  let lshr =
    bitshop (fun ~width t k ->
        let fallback =
          interval (zero ~size:width)
            (concat (zero ~size:k) (ones ~size:(width - k)))
        in
        if leq (sp ~width) t then fallback
        else
          match t with
          | Interval { lower; upper } ->
              interval
                (lshr lower (of_int ~size:width k))
                (lshr upper (of_int ~size:width k))
          | _ -> fallback)

  let ashr =
    bitshop (fun ~width t k ->
        let fallback =
          let k = min k width in
          interval
            (concat (ones ~size:k) (zero ~size:(width - k)))
            (concat (zero ~size:k) (ones ~size:(width - k)))
        in
        if leq (np ~width) t then fallback
        else
          match t with
          | Interval { lower; upper } ->
              interval
                (ashr lower (of_int ~size:width k))
                (ashr upper (of_int ~size:width k))
          | _ -> fallback)

  let extract ~width ~hi ~lo t =
    assert (0 <= lo);
    assert (lo <= hi);
    assert (hi <= width);
    if hi <= lo then bottom
    else
      let k = of_int ~size:width lo in
      truncate (lshr ~width t (interval k k)) (hi - lo)

  let concat (s, sw) (t, tw) =
    let t = if leq (sp ~width:tw) t then top else t in
    match (s, t) with
    | Bot, _ | _, Bot -> bottom
    | Top, Top -> top
    | Interval { lower = al; upper = au }, Interval { lower = bl; upper = bu }
      ->
        interval (concat al bl) (concat au bu)
    | Interval { lower = al; upper = au }, Top ->
        interval (concat al (zero ~size:tw)) (concat au (ones ~size:tw))
    | Top, Interval { lower = bl; upper = bu } ->
        interval (concat (zero ~size:sw) bl) (concat (ones ~size:sw) bu)
end

module WrappedIntervalsValueAbstraction = struct
  include WrappedIntervalsLatticeOps

  let eval_const (op : Lang.Ops.AllOps.const) rt =
    match op with
    | `Bool _ -> top
    | `Integer _ -> top
    | `Bitvector bv | `Pointer (bv, _) ->
        if size bv = 0 then top else interval bv bv
    (* NOTE: This kind of thing happens frequently, should I go through all of the fields and make a intervals out of those bvs?*)
    | `Record fields -> top
    | `Sort _ -> top

  let eval_unop (op : Lang.Ops.AllOps.unary) (a, t) rt =
    match t with
    | Types.Bitvector width -> (
        match op with
        | `BVNEG -> neg a
        | `BVNOT -> bitnot a
        | `ZeroExtend k -> zero_extend ~width a k
        | `SignExtend k -> sign_extend ~width a k
        | `Extract (hi, lo) -> extract ~width ~hi ~lo a
        | _ -> top)
    | _ -> top

  let eval_binary op (a, ta) (b, tb) rt =
    match (ta, tb) with
    | Types.Bitvector width, Types.Bitvector w2 when width = w2 -> (
        match op with
        | #Lang.Ops.Spec.binary -> Top
        | #Lang.Ops.RecordOps.binary -> Top
        | #Lang.Ops.IntOps.binary -> Top
        | #Lang.Ops.LogicalOps.binary -> Top
        | `BVADD | `PTRADD -> add ~width a b
        | `BVSUB -> sub ~width a b
        | `BVMUL -> mul ~width a b
        | `BVUDIV -> udiv ~width a b
        | `BVSDIV -> sdiv ~width a b
        | `BVOR -> bitor ~width a b
        | `BVAND -> bitand ~width a b
        | `BVNAND -> bitand ~width a b |> bitnot
        | `BVXOR -> bitxor ~width a b
        | `BVASHR -> ashr ~width a b
        | `BVLSHR -> lshr ~width a b
        | `BVSHL -> shl ~width a b
        | `BVSLE | `BVSLT | `BVSMOD | `BVSREM | `BVULE | `BVULT | `BVUREM -> top
        )
    | _ -> top

  let eval_binop (op : Lang.Ops.AllOps.binary) a b rt =
    match op with #Lang.Ops.AllOps.binary as op -> eval_binary op a b rt

  let eval_intrin (op : Lang.Ops.AllOps.intrin) (args : (t * Types.t) list) rt =
    let op a b =
      match op with
      | `BVADD -> (eval_binary `BVADD a b rt, rt)
      | `BVOR -> (eval_binary `BVOR a b rt, rt)
      | `BVXOR -> (eval_binary `BVXOR a b rt, rt)
      | `BVAND -> (eval_binary `BVAND a b rt, rt)
      | `BVConcat ->
          ( (match (snd a, snd b) with
            | Types.Bitvector wa, Types.Bitvector wb ->
                concat (fst a, wa) (fst b, wb)
            | _ -> top),
            rt )
      | _ -> (top, rt)
    in
    match args with
    | h :: b :: tl -> fst @@ List.fold_left op (op h b) tl
    | _ -> failwith "operators must have two operands"
end

module WrappedIntervalsValueAbstractionBasil = struct
  include WrappedIntervalsValueAbstraction
  module E = Lang.Expr.BasilExpr
end

module StateAbstraction =
  Intra_analysis.MapState (WrappedIntervalsValueAbstractionBasil)

module Eval = Intra_analysis.EvalStmt (WrappedIntervalsValueAbstractionBasil)

module Domain = struct
  include StateAbstraction

  let top_val = WrappedIntervalsLattice.top

  let init ?(vertex = None) p =
    let vs = Lang.Procedure.formal_in_params p |> StringMap.values in
    vs
    |> Iter.map (fun v -> (v, top_val))
    |> Iter.fold (fun m (v, d) -> update v d m) top

  open struct
    type bin_pred =
      [ `EQ | `NEQ | `ULE | `ULT | `UGT | `UGE | `SLE | `SLT | `SGT | `SGE ]

    let from_op (op : Lang.Expr.BasilExpr.binary) : bin_pred option =
      match op with
      | `EQ -> Some `EQ
      | `NEQ -> Some `NEQ
      | `BVULE -> Some `ULE
      | `BVULT -> Some `ULT
      | `BVSLE -> Some `SLE
      | `BVSLT -> Some `SLT
      | _ -> None

    let invert p =
      match p with
      | `EQ -> `NEQ
      | `NEQ -> `EQ
      | `ULE -> `UGT
      | `ULT -> `UGE
      | `UGT -> `ULE
      | `UGE -> `ULT
      | `SLE -> `SGT
      | `SLT -> `SGE
      | `SGT -> `SLE
      | `SGE -> `SLT

    let swap p =
      match p with
      | `EQ -> `EQ
      | `NEQ -> `NEQ
      | `ULE -> `UGE
      | `ULT -> `UGT
      | `UGT -> `ULT
      | `UGE -> `ULE
      | `SLE -> `SGE
      | `SLT -> `SGT
      | `SGT -> `SLT
      | `SGE -> `SLE

    let reduce_bin_left op s t =
      let open WrappedIntervalsLattice in
      let meet s t = lub @@ intersect s t in
      let bind f =
        match t with
        | Bot -> Bot
        | Top -> s
        | Interval { lower; upper } -> f lower upper
      in
      let ineq min max op =
        match op with
        | `LE ->
            bind (fun _ b ->
                let width = size b in
                if member t (max ~width) then s
                else meet s @@ interval (min ~width) b)
        | `LT ->
            bind (fun _ b ->
                let width = size b in
                if member t (max ~width) then
                  meet s
                  @@ interval (min ~width)
                       Bitvec.(sub (max ~width) @@ of_int ~size:width 1)
                else if Bitvec.equal b (min ~width) then Bot
                else
                  meet s
                  @@ interval (min ~width)
                       Bitvec.(sub b @@ of_int ~size:width 1))
        | `GE ->
            bind (fun a _ ->
                let width = size a in
                if member t (min ~width) then s
                else meet s @@ interval a (max ~width))
        | `GT ->
            bind (fun a _ ->
                let width = size a in
                if member t (min ~width) then
                  meet s
                  @@ interval
                       Bitvec.(add (min ~width) (of_int ~size:width 1))
                       (max ~width)
                else if Bitvec.equal a (max ~width) then Bot
                else
                  meet s
                  @@ interval (add a @@ of_int ~size:width 1) (max ~width))
      in
      let uineq = ineq umin umax in
      let sineq = ineq smin smax in
      match op with
      | `EQ -> meet s t
      | `NEQ -> meet s @@ complement t
      | `ULE -> uineq `LE
      | `ULT -> uineq `LT
      | `UGE -> uineq `GE
      | `UGT -> uineq `GT
      | `SLE -> sineq `LE
      | `SLT -> sineq `LT
      | `SGE -> sineq `GE
      | `SGT -> sineq `GT

    let reduce_bin ~read op l r =
      let abstract_eval expr =
        Eval.EV.eval read (Lang.Expr.BasilExpr.fix expr)
      in
      let open WrappedIntervalsLattice in
      let open Lang.Expr.AbstractExpr in
      match (l, r) with
      | RVar { id = lv }, RVar { id = rv } ->
          let l = read lv in
          let r = read rv in
          Iter.of_list
            [
              (lv, reduce_bin_left op l r); (rv, reduce_bin_left (swap op) r l);
            ]
      | RVar { id }, re ->
          let l = read id in
          let r = abstract_eval re in
          Iter.singleton (id, reduce_bin_left op l r)
      | le, RVar { id } ->
          let l = abstract_eval le in
          let r = read id in
          Iter.singleton (id, reduce_bin_left (swap op) r l)
      | _ -> Iter.empty

    let rec reduce_expr ~read expr =
      let open Lang.Expr in
      let open WrappedIntervalsLattice in
      let into_varmap =
        Iter.fold
          (fun acc (v, e) ->
            VarMap.update v
              (function Some l -> Some (e :: l) | None -> Some [ e ])
              acc)
          VarMap.empty
      in
      let meet s t = lub @@ intersect s t in
      let glb ints = List.map complement ints |> lub |> complement in
      match AbstractExpr.map BasilExpr.unfix (BasilExpr.unfix expr) with
      | BinaryExpr { op; arg1; arg2 } ->
          from_op op
          |> Option.map_or ~default:Iter.empty (fun op ->
              reduce_bin ~read op arg1 arg2)
      | UnaryExpr { op = `BoolNOT; arg = BinaryExpr { op; arg1 = l; arg2 = r } }
        ->
          from_op op
          |> Option.map_or ~default:Iter.empty (fun op ->
              reduce_bin ~read (invert op) (BasilExpr.unfix l)
                (BasilExpr.unfix r))
      | ApplyIntrin { op = `AND; args } ->
          List.map BasilExpr.fix args
          |> Iter.of_list
          |> Iter.flat_map (reduce_expr ~read)
          |> into_varmap |> VarMap.map glb |> VarMap.to_iter
      | ApplyIntrin { op = `OR; args } ->
          List.map BasilExpr.fix args
          |> Iter.of_list
          |> Iter.flat_map (reduce_expr ~read)
          |> into_varmap
          |> VarMap.mapi (fun v rs ->
              let s = read v in
              if List.length rs = List.length args then meet s (lub rs) else s)
          |> VarMap.to_iter
      | _ -> Iter.empty
  end

  let transfer_state read stmt =
    let evald_stmt = Eval.stmt_eval_fwd read stmt in
    let open Lang.Expr in
    let pred_updates =
      match stmt with
      | Lang.Stmt.Instr_Assert { body } | Lang.Stmt.Instr_Assume { body } ->
          reduce_expr ~read body
      | _ -> Iter.empty
    in
    let updates =
      match evald_stmt with
      | Lang.Stmt.Instr_Assign { al } -> List.to_iter al
      | Lang.Stmt.Instr_Assert _ | Lang.Stmt.Instr_Assume _ -> Iter.empty
      | Lang.Stmt.Instr_Load { lhs; rhs; addr = Scalar } ->
          Iter.singleton (lhs, rhs)
      | Lang.Stmt.Instr_Store { lhs; value; addr = Scalar } ->
          Iter.singleton (lhs, value)
      | Lang.Stmt.Instr_Load { lhs } -> Iter.singleton (lhs, top_val)
      | Lang.Stmt.Instr_Store { lhs } -> Iter.singleton (lhs, top_val)
      | Lang.Stmt.Instr_IntrinCall { lhs } ->
          List.to_iter lhs |> Iter.map (fun v -> (v, top_val))
      | Lang.Stmt.Instr_Call { lhs } ->
          StringMap.values lhs |> Iter.map (fun v -> (v, top_val))
      | Lang.Stmt.Instr_IndirectCall _ -> Iter.empty
    in
    Iter.append pred_updates updates

  let transfer dom stmt =
    Iter.fold (fun a (k, v) -> update k v a) dom
    @@ transfer_state (flip read dom) stmt

  let transfer_phi m (p : Var.t Lang.Block.phi) =
    match p with
    | { lhs; rhs } ->
        rhs
        |> List.map (fun (_, k) -> read k m)
        |> List.fold_left WrappedIntervalsLattice.join
             WrappedIntervalsLattice.bottom
        |> fun v -> update lhs v m
end

module DFGAnalysis = Dataflow_graph.AnalysisFwdNarrowing (Domain)
module Analysis = Intra_analysis.Forwards (Domain)

let analyse (p : Lang.Program.proc) =
  Analysis.analyse ~widening_set:Graph.ChaoticIteration.FromWto
    ~widening_delay:50 p

let%expect_test "narrow_loop" =
  let prog =
    (Loader.Loadir.ast_of_string
       {|
proc @main()  -> () {  }

[
   block %entry [ var l_1:bv64 := 0x0:bv64; goto (%ret,%loop); ];
   block %loop ( var l_2:bv64 := phi(%loop -> l_4:bv64, %entry -> l_1:bv64) ) [
     var l_3:bv64 := l_2:bv64;
     assert bvsle(l_3:bv64, 0x100:bv64);
     var l_4:bv64 := bvadd(l_3:bv64, 0x1:bv64);
     goto (%ret,%loop);
   ];
   block %ret (
     var l_5:bv64 := phi(%loop -> l_4:bv64, %loop -> l_4:bv64, %entry -> l_1:bv64)
   ) [
     var l_6:bv64 := l_5:bv64;
     assert boolnot(bvsle(l_6:bv64, 0x100:bv64));
     return;
   ]
];
prog entry @main;
    |})
      .prog
  in
  let proc = Lang.Program.entry_proc_exn prog in
  let r = DFGAnalysis.flow_insensitive proc in
  print_endline @@ StateAbstraction.show r;
  (* l_6->[0x101, 0x101] we infer an exact value! *)
  [%expect
    {| (l_1->⟦0x0:bv64, 0x0:bv64⟧, l_4->⟦0x8000000000000032:bv64, 0x101:bv64⟧, l_2->⟦0x8000000000000031:bv64, 0x101:bv64⟧, l_3->⟦0x8000000000000031:bv64, 0x100:bv64⟧, l_5->⟦0x8000000000000032:bv64, 0x101:bv64⟧, l_6->⟦0x101:bv64, 0x101:bv64⟧, _->⊤) |}]
