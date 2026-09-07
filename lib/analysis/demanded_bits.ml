(** {0 IDE Demanded Width}

    An interprocedural implementation of demanded bits, encoded as the smallest
    bitvector width to capture all bits that may influence behaviour. It fully
    subsumes standard interprocedural liveness.

    We model a variety of bitvector operations precisely, including shifts,
    slices, extends and trivial masking operations (where the mask is contiguous
    in its selected range). Our composition operation is also precise, with the
    only imprecision derived from our join. Results could be improved with a
    lower bound on the demanded bits, rather than a fixed 0, but we defer this
    to future work (if ever).

    While I find the implementation quite neat, it is not really practical for
    subsequent transforms. Reducing all bitvector variables to their demanded
    width will likely result in a messier program, introducing just as many
    slices and extends as we intend to remove. It may help SMT solving though,
    as the benefits of reducing a 64-bit multiplication are substantial.

    Moreover, bincaml doesn't support procedures that are polymorphic in
    bitvector width, so context-sensitivity demanded width is of little use.
    This last one is a pretty strong case to {i not} make this analysis
    context-sensitive, but seeing as its still interprocedural and we can do
    liveness at the same time. Though maybe profiles say otherwise.

    Subsequent uses of this domain probably need to coarsen a little to get
    practical widths. We make an attempt at this in [Coarse].

    TODO: The IDE framework currently treats return as the only backwards walk
    root. Abrupt exits and divergent loops need a framework-level notion of
    termination before this analysis can soundly account for them. I suspect
    this includes indirect calls.

    TODO: The IDE framework seeds every formal output as initially demanded in
    [init_p2], and phase-two results are joined per procedure. This weakens
    output precision and limits how much call-site context sensitivity survives
    into the final per-procedure map consumed by transforms. *)

open Lang
open Containers
open Common
open Idessi

(** {1 Demand Lattice}

    The demanded width of a variable, encoded as an [int], such that:
    - [0]: Bottom, i.e., dead.
    - [n]: Bits [n:0] are demanded.
    - [max_int]: Top, i.e., live.

    Any arbitrary value can represent Top, as long as it encompasses all
    possible widths. [max_int] is pretty overkill here, but I can't find a
    better choice.

    Assumes bitvectors have been typed in the IR and all widths reside within
    the range of valid demands. *)
module Demand = struct
  type t = int

  let equal = Int.equal
  let compare = Int.compare
  let bottom = 0
  let top = max_int
  let join = Int.max

  let show n =
    if n = bottom then "⊥" else if n = top then "⊤" else Printf.sprintf "bv%d" n

  let of_type ty = Option.value (Types.bit_width ty) ~default:top
  let of_var v = of_type (Var.typ v)
  let of_expr e = of_type (Expr.BasilExpr.get_typ e)
end

(** {1 Edge Lattice}

    The edge lattice, encoding how the demand requirements of one variable
    influence another. Edges encode a function over [Demand.t], intended to zero
    out an initial dead range and shift a live range, capped by some upper bound
    informed by the type. Edges are parameterised by:
    - [xs]: The first live width.
    - [ys]: The shift applied to the first live width.
    - [cap]: The upper bound.

    Formally, these correspond to: [\u. if u < xs then 0 else min cap (u + ys)].
    As a crude visualisation:

    {v
         cap |              /--------
             |             /
             |            /
          ys |           /
             |          |
             |          |
           0 |----------'
             +----------+------------
                       xs
    v}

    We enforce a rather crude constraint over these functions to get our desired
    properties. We observe that, for the demand constraints we model, if [xs] is
    0 then we don't really expect a meaningful function other than immediately
    producing [cap]. So we use [xs = 0] and [cap = ys = C] to encode some
    constant function [\_. C].

    Given our encoding of demand, the lattice operations manipulate [int]. These
    have been carefully worked through to ensure we cannot trigger overflow
    conditions.

    To detect fixed-points, the operations are also very carefully structured to
    maintain a canonical form, such that structural equality implies equality
    over the represented functions.
    - [0 <= cap < top + ys]: [cap] is not negative and reachable for some input.
      Former is necessary as we want to remain in the interval, latter is
      necessary such that the [cap] has an effect.
    - [0 <= xs]: [xs] is not negative, as all would be equivalent to [0].
    - [xs + ys <= cap]: The first positive output mustn't exceed the bound,
      otherwise its redundant.
    - [cap = 0 -> xs = 0]: If the bound is zero, then everything is zero,
      otherwise it would be redundant.
    - [0 < cap -> 0 < xs + ys]: The point nominated by [xs] must be non-zero,
      unless the whole thing is zero.
    - [xs = 0 -> cap = ys]: Force a constant form for unconditional cases. Our
      crude hack.

    I think its pretty clear that this domain is over-engineered. There is room
    for simplification, but I leave this to future work. Its also pretty clear
    that the above list is too much for any one person's head. Consequently,
    there is an Isabelle formalisation.

    TODO: Where do I put this? *)
module Edge = struct
  type t = { xs : int; ys : int; cap : int } [@@deriving eq, ord, show]

  let pp fmt e = Format.pp_print_string fmt (show e)

  (** [sat_add a b c] compute [min a (b + c)] accounting for possible overflow.
      Invariants ensure underflow isn't possible. *)
  let sat_add a b c =
    let s = b + c in
    if b >= 0 && c >= 0 && s < 0 then a else if a < s then a else s

  (** {2 Constructors} *)

  (** [constant c] returns the constant edge [\_. c]. *)
  let constant c = { xs = 0; ys = c; cap = c }

  (** [bottom] returns the constant edge [\_. bottom]. *)
  let bottom = constant Demand.bottom

  (** [top] returns the constant edge [\_. top]. *)
  let top = constant Demand.top

  (** [identity] returns the edge [\u. u]. *)
  let identity = { xs = 1; ys = 0; cap = Demand.top }

  (** [saturate c] returns a conditional live edge, i.e, one that is only live
      if its input is and the input has no influence on which bits. Formally,
      the edge [\u. if u < 1 || c < 0 then 0 else c]. *)
  let saturate c = if c <= 0 then bottom else { xs = 1; ys = c - 1; cap = c }

  (** [mask lo hi] returns an edge to model extraction from [lo] to [hi],
      exclusive of the upper bound. Formally, the edge
      [\u. if u <= lo || hi <= lo || lo < 0 then 0 else min hi U]. *)
  let mask lo hi =
    if hi <= lo || lo < 0 then bottom else { xs = lo + 1; ys = 0; cap = hi }

  (** [rshift d w] returns an edge to model a right shift of [d] over bitvectors
      of width [w]. Formally, the edge
      [\u. if u <= 0 || w <= 0 then 0 else min w (u + d)]. *)
  let rshift d w =
    if w <= 0 || d < 0 then bottom else { xs = 1; ys = min (w - 1) d; cap = w }

  (** [lshift d w] returns an edge to model a left shift of [d] over bitvectors
      of width [w]. Formally, the edge
      [\u. if u <= d || w <= d || d < 0 then 0 else (min w u) - d]. *)
  let lshift d w =
    if w = 0 || w <= d then bottom else { xs = 1 + d; ys = -d; cap = w - d }

  (** {2 Operations} *)

  (** [eval v f] applies [v] to the edge [f]. *)
  let eval v f = if v < f.xs then 0 else sat_add f.cap v f.ys

  (** [compose a b] returns the composition of edge a and b. It is precise, such
      that its result must be [\w. a (b w)]. *)
  let compose a b =
    if a.xs <= 0 then a
    else if b.cap < a.xs then bottom
    else
      let xs = max b.xs (a.xs - b.ys) in
      let ys = sat_add (a.cap - xs) b.ys a.ys in
      let cap = sat_add a.cap b.cap a.ys in
      { xs; ys; cap }

  (** [join a b] returns a new edge guaranteed to be greater than its inputs
      across the range, i.e., [max (a w) (b w) <= join a b w].

      The resulting edge must be an over-approximation, but we ensure it is as
      precise a function as we can represent. *)
  let join a b =
    if a.cap <= 0 then b
    else if b.cap <= 0 then a
    else if a.xs <= 0 || b.xs <= 0 then constant (max a.cap b.cap)
    else { xs = min a.xs b.xs; ys = max a.ys b.ys; cap = max a.cap b.cap }
end

(** {1 Uses}

    Edge construction for an expression, targeting a given variable. Plenty of
    room for optimisation here, if profiling suggests it. *)
module Uses = struct
  open Expr.AbstractExpr

  (** {2 Constant Utilities} *)

  let opt_uint e =
    match Expr.BasilExpr.unfix e with
    | Constant { const = `Bitvector bv } -> Some (Bitvec.to_unsigned_bigint bv)
    | _ -> None

  let is_uint e = Option.is_some (opt_uint e)
  let uint e = Option.get (opt_uint e)

  (** [shift_amount w e] translates the shift argument [e] into an [int]. Takes
      the expression's width [w] to saturate. *)
  let shift_amount w e =
    let z = uint e in
    if Z.fits_int z then Int.min (Z.to_int z) w else w

  (** [mask_edge a] computes the mask given arguments [a] to a [BVAND]. Edges
      can only represent a contiguous interval, so we consider everything
      between the highest and lowest set bits. *)
  let mask_edge a : Edge.t =
    match List.filter_map opt_uint a with
    | [] -> Edge.identity
    | m :: ms -> (
        match List.fold_left Z.logand m ms with
        | m when Z.equal m Z.zero -> Edge.bottom
        | m -> Edge.mask (Z.trailing_zeros m) (Z.numbits m))

  (** {2 Expression Walk} *)

  let rec needed (e : Expr.BasilExpr.t) (v : Var.t) : Edge.t =
    match Expr.BasilExpr.unfix e with
    (* Loading a var is essentially id, capped by width. *)
    | RVar { id } when Var.equal id v -> Edge.rshift 0 (Demand.of_var v)
    | RVar _ | Constant _ -> Edge.bottom
    (* Bit [i] to [i + off], up to [w]. Logical shifts by the width
       produce zero; arithmetic shifts by the width produce the sign bit. *)
    | BinaryExpr { op = `BVLSHR; arg1; arg2 } when is_uint arg2 ->
        let w = Demand.of_expr arg1 in
        let off = shift_amount w arg2 in
        if off >= w then Edge.bottom
        else Edge.compose (needed arg1 v) (Edge.rshift off w)
    | BinaryExpr { op = `BVASHR; arg1; arg2 } when is_uint arg2 ->
        let w = Demand.of_expr arg1 in
        let off = shift_amount w arg2 in
        let shift = if off >= w then Edge.saturate w else Edge.rshift off w in
        Edge.compose (needed arg1 v) shift
    (* Bit [i] to [i - off], up to [w - off]: the top [off] bits of the
       argument are shifted out of the result altogether. *)
    | BinaryExpr { op = `BVSHL; arg1; arg2 } when is_uint arg2 ->
        let w = Demand.of_expr arg1 in
        let off = shift_amount w arg2 in
        Edge.compose (needed arg1 v) (Edge.lshift off w)
    (* Bit [i] to [i + lo], up to [hi]. *)
    | UnaryExpr { op = `Extract (hi, lo); arg } ->
        Edge.compose (needed arg v) (Edge.rshift lo hi)
    (* Bit [i] isn't needed if it will be masked out, model as extract. *)
    | ApplyIntrin { op = `BVAND; args } ->
        let mask = mask_edge args in
        List.fold_left
          (fun a e -> Edge.join a (Edge.compose (needed e v) mask))
          Edge.bottom args
    (* Model as join of a series of left shifts. *)
    | ApplyIntrin { op = `BVConcat; args } ->
        let walk a (acc, lo) =
          let w = lo + Demand.of_expr a in
          (Edge.join acc (Edge.compose (needed a v) (Edge.lshift lo w)), w)
        in
        fst (List.fold_right walk args (Edge.bottom, 0))
    (* Trivial pass-through cases. *)
    | UnaryExpr { op = `ZeroExtend _ | `SignExtend _; arg }
    | UnaryExpr { op = `BVNOT | `BVNEG; arg } ->
        needed arg v
    | BinaryExpr { op = `BVSUB | `BVNAND; arg1; arg2 } ->
        Edge.join (needed arg1 v) (needed arg2 v)
    | ApplyIntrin { op = `BVADD | `BVMUL | `BVOR | `BVXOR; args } ->
        List.fold_left (fun a e -> Edge.join a (needed e v)) Edge.bottom args
    (* TODO: What is necessary here? Do I have to reason about binders? *)
    | Lambda _ -> failwith "demanded_bits: quantifier/lambda in expression"
    | Let _ -> failwith "demanded_bits: let-binding in expression"
    (* Sound over-approximation case *)
    | e ->
        fold (fun acc a -> Demand.join acc (need_all a v)) 0 e |> Edge.saturate

  and need_all e v = Edge.eval (Demand.of_expr e) (needed e v)
end

(** {1 The IDE domain}

    We use a pretty standard setup here. [Label v] corresponds to a variable,
    with edges between them denoting demands. [Lambda] denotes unconditional
    demands due to assertions, assumptions, etc. I have tried to document my
    understanding of what is happening here. *)
module Domain = struct
  (** {2 Domain boilerplate}

      Edge functions form the IDE edge lattice. Their underlying value lattice
      is demanded width, and the analysis walks backwards through the SSI
      use-to-definition graph. *)
  let direction = `Backwards

  module Value = Demand
  include Edge

  (** Dataflow labels tracked by the solver. *)
  module DL = struct
    type t = Lambda | Label of Var.t [@@deriving eq, ord, show]

    let show = function Lambda -> "Λ" | Label v -> Var.name v
  end

  type state_update = (DL.t * t) Iter.t

  open DL

  (** Procedure summaries are indexed by formal outputs. *)
  let init_data (proc : Program.proc) =
    Procedure.formal_out_params proc |> StringMap.values

  (** Phase two computes a per-procedure demand map by evaluating summaries.

      The current solver produces whole-procedure results, so each formal output
      is seeded as fully demanded. This matches liveness-style behaviour, but it
      also means output precision from individual call sites is joined away in
      the final map. *)
  let init_p2 (proc : Program.proc) =
    Procedure.formal_out_params proc
    |> StringMap.values
    |> Iter.map (fun v -> (v, Demand.of_var v))

  (** Demand introduced by a statement regardless of successor demand. *)
  let unconditional_uses (stmt : Program.stmt) : state_update =
    Stmt.iter_rexpr stmt
    |> Iter.flat_map (function
      | `Expr e ->
          Expr.BasilExpr.free_vars_iter e
          |> Iter.map (fun u -> (Label u, constant (Uses.need_all e u)))
      | `Var m -> Iter.singleton (Label m, constant (Demand.of_var m)))

  (** Transfer a statement over one demanded label.

      For [Label lhs] at an assignment [lhs := rhs], demand on [lhs] is pushed
      to each free variable in [rhs] using the expression-specific edge. For
      [Lambda], assignments produce no facts. Other instructions push
      unconditional edges to all free variables. Labelled non-assignment
      transfers are always empty. *)
  let transfer (stmt : Program.stmt) (d : DL.t) : state_update =
    let open Stmt in
    match (d, stmt) with
    | Lambda, Instr_Assign _ -> Iter.empty
    | Lambda, _ -> unconditional_uses stmt
    | Label v, Instr_Assign { al } ->
        Iter.of_list al
        |> Iter.flat_map (fun (lhs, rhs) ->
            if Var.equal v lhs then
              Expr.BasilExpr.free_vars_iter rhs
              |> Iter.map (fun u -> (Label u, Uses.needed rhs u))
            else Iter.empty)
    | _ -> Iter.empty

  (** Transfer a phi node, simply as an identity edge. *)
  let transfer_phi lhs rhs d =
    match d with
    | Lambda -> Iter.empty
    | Label v when Var.equal v lhs ->
        Iter.of_list rhs |> Iter.map (fun u -> (Label u, identity))
    | Label _ -> failwith "demanded_bits: phi with unrelated variable"

  (** Transfer demand on a callee formal input through a call site.

      In a backwards transfer, [d] is the callee formal input currently demanded
      by the callee summary. [call_info] maps callee formal names to the actual
      argument expressions used at this call site. So we link the callee's
      demand to the free variables of the argument.

      I believe this function will never be called with a [Lambda]. *)
  let transfer_call (call_info : call_info) (_arg_info : param_info) (d : DL.t)
      : state_update =
    match d with
    | Lambda ->
        failwith "demanded_bits: transfer_call reached with Lambda (backwards)"
    | Label formal -> (
        let name = Var.name formal in
        match StringMap.find_opt name call_info with
        | None -> failwith "demanded_bits: call site missing argument"
        | Some arg ->
            Expr.BasilExpr.free_vars_iter arg
            |> Iter.map (fun u -> (Label u, Uses.needed arg u)))
end

module Analysis = IDESSI (Domain)

(** {1 Coarse post-pass}

    The IDE result records how many bits are demanded from each variable. This
    pass turns that demand into candidate replacement widths, accounting for
    producers whose result width cannot be chosen independently.

    TODO: This is just a partial implementation of what I am thinking, need the
    transform now.

    TODO: Clarify API on formal ins and outs *)
module Coarse : sig
  type t
  (** Analysis state *)

  val find_var : t -> IDSet.elt -> Var.t -> Demand.t
  (** Get the demand result for a given variable, in a given procedure *)

  val find_return : t -> IDSet.elt -> string -> Var.t -> Demand.t
  (** Get the demand result for a given formal out, in a given procedure *)

  val analyse : int VarMap.t IDMap.t -> Program.t -> t
  (** Entry point to run coarsening *)
end = struct
  type t = {
    vars : Demand.t VarMap.t IDMap.t;
    returns : Demand.t StringMap.t IDMap.t;
  }

  let empty = { vars = IDMap.empty; returns = IDMap.empty }

  let demand_of p2 pid v =
    let w = Demand.of_var v in
    let d =
      IDMap.get_or pid p2 ~default:VarMap.empty
      |> VarMap.get_or v ~default:Demand.bottom
    in
    if d <= Demand.bottom then Demand.bottom else min w d

  let add_var pid v width t =
    let vars =
      IDMap.update pid
        (fun proc_widths ->
          let proc_widths = Option.get_or ~default:VarMap.empty proc_widths in
          let width =
            max width (VarMap.get_or v proc_widths ~default:Demand.bottom)
          in
          Some (VarMap.add v width proc_widths))
        t.vars
    in
    { t with vars }

  let find_var t pid v =
    IDMap.find_opt pid t.vars
    |> Option.flat_map (VarMap.find_opt v)
    |> Option.get_lazy (fun () -> Demand.of_var v)

  let add_return pid name width t =
    let returns =
      IDMap.update pid
        (fun proc_returns ->
          let proc_returns =
            Option.get_or ~default:StringMap.empty proc_returns
          in
          let width =
            max width
              (StringMap.get_or name proc_returns ~default:Demand.bottom)
          in
          Some (StringMap.add name width proc_returns))
        t.returns
    in
    { t with returns }

  let find_return t pid name v =
    IDMap.find_opt pid t.returns
    |> Option.flat_map (StringMap.find_opt name)
    |> Option.get_lazy (fun () -> Demand.of_var v)

  let fold_blocks proc f a =
    Procedure.iter_blocks proc
    |> Iter.fold (fun a (_, (b : Program.bloc)) -> f b a) a

  (** Phase one walks every call-site and takes the join of the demand among the
      returned variables.

      This is what I would expect the IDE result to actually be, but the current
      structure doesn't allow it. *)
  let phase1 p2 t (pid, proc) =
    let call t = function
      | Stmt.Instr_Call c ->
          StringMap.fold
            (fun name var -> add_return c.procid name (demand_of p2 pid var))
            c.lhs t
      | _ -> t
    in
    fold_blocks proc (fun b a -> Block.stmts_iter b |> Iter.fold call a) t

  (** Phase two walks every producer and determines the new width for the
      variables it defines. *)
  let phase2 p2 t (pid, proc) =
    (* Helpers to add a given width *)
    let demand t var = add_var pid var (demand_of p2 pid var) t in
    let return procid name var =
      add_var pid var (find_return t procid name var)
    in

    (* For a statement, process the variables it produces *)
    let stmt t s =
      match s with
      | Stmt.Instr_Assign _ | Stmt.Instr_Store _ ->
          Stmt.iter_lvar s |> Iter.fold demand t
      | Stmt.Instr_Call c -> StringMap.fold (return c.procid) c.lhs t
      | _ -> t
    in

    (* For a block, process phis before statements *)
    let block (b : Program.bloc) t =
      List.fold_left
        (fun t (phi : Var.t Block.phi) -> demand t phi.lhs)
        t b.phis
      |> fun t -> Block.stmts_iter b |> Iter.fold stmt t
    in
    (* Record formals and body producers for this procedure *)
    let t =
      StringMap.values (Procedure.formal_in_params proc) |> Iter.fold demand t
    in
    let t = StringMap.fold (return pid) (Procedure.formal_out_params proc) t in
    fold_blocks proc block t

  let analyse p2 prog =
    let t = Iter.fold (phase1 p2) empty (Program.procs prog) in
    Iter.fold (phase2 p2) t (Program.procs prog)
end
