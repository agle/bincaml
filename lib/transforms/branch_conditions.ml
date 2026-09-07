open Bincaml_util.Common
open Lang

(* TODO:
    - Handle ccmp instructions (where branch conditions depend on branch conditions, needing a depth 1 path sensitive analysis)
    - Handle registers being overwritten before branching (SSA):
        there was an instance of
        cmn w0, #1
        mov w0, #0
        b.ne #0xfffffffffffffff0
        in cntlm. Here w0 gets overwritten before we can identify a branch condition in terms of w0's current value...
  every failing branch condition in cntlm is of one of these two forms!
*)

open struct
  let equiv_exp e1 e2 = Expr.BasilExpr.(equal (drop_attrib e1) (drop_attrib e2))
end

module FlagSemantics = struct
  type computation =
    | Sum of Expr.BasilExpr.t * Expr.BasilExpr.t  (** Computed e1 + e2 *)
    | Diff of Expr.BasilExpr.t * Expr.BasilExpr.t  (** Computed e1 - e2 *)
    | Expr of Expr.BasilExpr.t  (** The result of evaluating an expr *)
    | Always
    | Never
  [@@deriving eq, ord, show { with_path = false }]

  type t =
    | Const of computation
    | O of computation  (** Overflow from computation *)
    | C of computation  (** Carry from computation *)
    | Z of computation  (** When computation is zero *)
    | N of computation  (** When computation is negative *)
  [@@deriving eq, ord, show { with_path = false }]

  let equiv_computations c c' =
    let open Expr.BasilExpr in
    match (c, c') with
    | Sum (e1, e2), Sum (e1', e2') -> equiv_exp e1 e1' && equiv_exp e2 e2'
    | Diff (e1, e2), Diff (e1', e2') -> equiv_exp e1 e1' && equiv_exp e2 e2'
    | Expr e, Expr e' -> equiv_exp e e'
    | _ -> false

  (** Determine whether [v] exists in an expression in [f] *)
  let contains_var v f =
    match f with
    | O c | C c | Z c | N c | Const c -> (
        match c with
        | Sum (e1, e2) | Diff (e1, e2) ->
            VarSet.mem v (Expr.BasilExpr.free_vars e1)
            || VarSet.mem v (Expr.BasilExpr.free_vars e2)
        | Expr e -> VarSet.mem v (Expr.BasilExpr.free_vars e)
        | Never | Always -> false)

  let extract_overflow_cary arg1 arg2 =
    let open Types in
    let open Expr.AbstractExpr in
    let open Expr.BasilExpr in
    let sext_eq extension bv1 bv2 =
      Bitvec.(equal (sign_extend ~extension bv1) bv2)
    in
    let zext_eq extension bv1 bv2 =
      Bitvec.(equal (zero_extend ~extension bv1) bv2)
    in
    let is_one bv = Bitvec.(equal bv (one ~size:(size bv))) in
    match (unfix3 arg1, unfix3 arg2) with
    | ( UnaryExpr
          {
            op = `SignExtend s1;
            arg =
              ApplyIntrin
                {
                  op = `BVADD;
                  args = [ a; Constant { const = `Bitvector bv1 } ];
                };
          },
        ApplyIntrin
          {
            op = `BVADD;
            args =
              [
                UnaryExpr { op = `SignExtend s2; arg = c };
                Constant { const = `Bitvector bv2 };
              ];
          } )
      when s1 = s2 && s1 > 0 && equiv_exp (fix a) (fix c) && sext_eq s1 bv1 bv2
      ->
        if Bitvec.is_negative bv1 then
          Some (O (Diff (fix a, bvconst (Bitvec.neg bv1))))
        else Some (O (Sum (fix a, bvconst bv1)))
    | ( UnaryExpr
          {
            op = `SignExtend s1;
            arg = ApplyIntrin { op = `BVADD; args = [ a; b ] };
          },
        ApplyIntrin
          {
            op = `BVADD;
            args =
              [
                UnaryExpr { op = `SignExtend s2; arg = c };
                UnaryExpr { op = `SignExtend s3; arg = d };
              ];
          } )
      when s1 = s2 && s2 = s3 && s1 > 0
           && equiv_exp (fix a) (fix c)
           && equiv_exp (fix b) (fix d) ->
        Some (O (Sum (fix a, fix b)))
    | ( UnaryExpr
          {
            op = `SignExtend s1;
            arg = BinaryExpr { op = `BVSUB; arg1 = a; arg2 = b };
          },
        BinaryExpr
          {
            op = `BVSUB;
            arg1 = UnaryExpr { op = `SignExtend s2; arg = c };
            arg2 = UnaryExpr { op = `SignExtend s3; arg = d };
          } )
      when s1 = s2 && s2 = s3 && s1 > 0
           && equiv_exp (fix a) (fix c)
           && equiv_exp (fix b) (fix d) ->
        Some (O (Diff (fix a, fix b)))
    | ( UnaryExpr
          {
            op = `ZeroExtend z1;
            arg =
              ApplyIntrin
                {
                  op = `BVADD;
                  args = [ a; Constant { const = `Bitvector bv1 } ];
                };
          },
        ApplyIntrin
          {
            op = `BVADD;
            args =
              [
                UnaryExpr { op = `ZeroExtend z2; arg = c };
                Constant { const = `Bitvector bv2 };
              ];
          } )
      when z1 = z2 && z1 > 0 && equiv_exp (fix a) (fix c) && zext_eq z1 bv1 bv2
      ->
        if Bitvec.is_negative bv1 then
          Some (C (Diff (fix a, bvconst (Bitvec.neg bv1))))
        else Some (C (Sum (fix a, bvconst bv1)))
    | ( UnaryExpr
          {
            op = `ZeroExtend z1;
            arg = ApplyIntrin { op = `BVADD; args = [ a; b ] };
          },
        ApplyIntrin
          {
            op = `BVADD;
            args =
              [
                UnaryExpr { op = `ZeroExtend z2; arg = c };
                UnaryExpr { op = `ZeroExtend z3; arg = d };
              ];
          } )
      when z1 = z2 && z2 = z3 && z1 > 0
           && equiv_exp (fix a) (fix c)
           && equiv_exp (fix b) (fix d) ->
        Some (C (Sum (fix a, fix b)))
    | ( UnaryExpr
          {
            op = `ZeroExtend z1;
            arg = BinaryExpr { op = `BVSUB; arg1 = a; arg2 = b };
          },
        ApplyIntrin
          {
            op = `BVADD;
            args =
              [
                UnaryExpr { op = `ZeroExtend z2; arg = c };
                UnaryExpr
                  {
                    op = `ZeroExtend z3;
                    arg = UnaryExpr { op = `BVNOT; arg = d };
                  };
                Constant { const = `Bitvector bv };
              ];
          } )
      when z1 = z2 && z2 = z3 && z1 > 0
           && equiv_exp (fix a) (fix c)
           && equiv_exp (fix b) d
           && is_one bv ->
        Some (C (Diff (fix a, fix b)))
    | _ -> None

  let extract_expr arg =
    let open Expr.AbstractExpr in
    let open Expr.BasilExpr in
    match unfix2 arg with
    | ApplyIntrin
        { op = `BVADD; args = [ a; Constant { const = `Bitvector bv } ] } ->
        if Bitvec.is_negative bv then Diff (fix a, bvconst (Bitvec.neg bv))
        else Sum (fix a, bvconst bv)
    | ApplyIntrin { op = `BVADD; args = [ a; b ] } -> Sum (fix a, fix b)
    | BinaryExpr { op = `BVSUB; arg1 = a; arg2 = b } -> Diff (fix a, fix b)
    | a -> Expr (fix2 a)

  let extract_semantics e =
    let e = Algsimp.normalise e in
    let open Expr.AbstractExpr in
    let open Expr.BasilExpr in
    match unfix3 e with
    | Constant { const = `Bitvector k }
      when Bitvec.equal k (Bitvec.zero ~size:1) ->
        Some (Const Never)
    | Constant { const = `Bitvector k } when Bitvec.equal k (Bitvec.one ~size:1)
      ->
        Some (Const Always)
    | UnaryExpr
        {
          op = `BVNOT;
          arg =
            UnaryExpr
              { op = `BOOLTOBV1; arg = BinaryExpr { op = `EQ; arg1; arg2 } };
        } ->
        extract_overflow_cary arg1 arg2
    | UnaryExpr
        {
          op = `BOOLTOBV1;
          arg =
            BinaryExpr
              { op = `EQ; arg1; arg2 = Constant { const = `Bitvector bv } };
        }
      when Bitvec.is_zero bv ->
        Some (Z (extract_expr (fix arg1)))
    | UnaryExpr { op = `Extract (e1, e2); arg }
      when e1 = e2 + 1
           && Option.equal ( = )
                (Types.bit_width @@ type_of (fix2 arg))
                (Some e1) ->
        Some (N (extract_expr (fix2 arg)))
    | _ -> None
end

(** Add flag semantic annotations as attributes for debugging *)
let annotate_flag_assigns stmt =
  let open Stmt in
  match stmt with
  | Instr_Assign { attrib; al } ->
      let annotations =
        al
        |> List.filter (fun (v, _) ->
            Types.equal (Var.typ v) (Types.Bitvector 1))
        |> List.filter_map (fun (v, e) ->
            let o = FlagSemantics.extract_semantics e in
            if
              Option.is_none o
              && String.starts_with ~prefix:"$PSTATE_" (Var.name v)
            then
              Logs.debug (fun m ->
                  m "%s had no assigned semantic meaning for expr %s"
                    (Var.name v)
                    (Expr.BasilExpr.to_string (Algsimp.normalise e)));
            o |> Option.map (fun s -> (v, s)))
      in
      let attrib =
        List.fold_left
          (fun attrib (v, s) ->
            StringMap.add
              (".flag_semantics_" ^ Var.name v)
              (`String (FlagSemantics.show s))
              attrib)
          attrib annotations
      in
      Instr_Assign { attrib; al }
  | _ -> stmt

let annotate_flag_assign_stmts (p : Program.proc) =
  Procedure.map_blocks_nondet
    (fun (bid, block) -> Block.map ~phi:id annotate_flag_assigns block)
    p

module FlagLattice = struct
  include Analysis.Lattice_types.FlatLattice (struct
    include FlagSemantics

    let name = "flag"
  end)

  module E = Lang.Expr.BasilExpr

  let eval_const op =
    match op with
    | `Bitvector k when Bitvec.equal k (Bitvec.zero ~size:1) -> V (Const Never)
    | `Bitvector k when Bitvec.equal k (Bitvec.one ~size:1) -> V (Const Always)
    | _ -> Top

  let eval_unop _ _ = Top
  let eval_binop _ _ _ = Top
  let eval_intrin _ _ = Top

  let contains_var v x =
    match x with
    | Top -> false
    | Bot -> false
    | V f -> FlagSemantics.contains_var v f
end

(** Assigns flag meaning values to flag variables at each code point. If a flag
    assumes a value of a variable that gets updated, that flags value will get
    dropped and set to top. This should be precise enough still as branches
    probably only occur direct after flags are set (probably). Note that none of
    this is a problem if ssa is run prior to this transform. *)
module FlagDomain = struct
  include Analysis.Intra_analysis.MapState (FlagLattice)

  let name = "pstate-flag-analysis"

  (* Assume nothing about the initial state *)
  let init ?vertex _ =
    match vertex with Some (Some Procedure.Vert.Entry) -> top | _ -> bottom

  (** Remove flags from state that referred to [v] (e.g. if [v] was updated) *)
  let drop_modified v =
    mapi (fun v' x ->
        if FlagLattice.contains_var v x then FlagLattice.top else x)

  let transfer m stmt =
    match stmt with
    | Stmt.Instr_Assign { al } ->
        List.fold_left
          (fun m (v, e) ->
            let m = drop_modified v m in
            let f =
              FlagSemantics.extract_semantics e
              |> Option.map (fun f -> FlagLattice.V f)
              |> Option.get_or ~default:FlagLattice.top
            in
            update v f m)
          m al
    | _ -> m

  let transfer_phi m (p : Var.t Block.phi) =
    match p with
    | { lhs; rhs } ->
        (* assume phis never assign to in use variables (yikes) *)
        rhs
        |> List.map (fun (_, k) -> read k m)
        |> List.fold_left FlagLattice.join FlagLattice.bottom
        |> fun v -> drop_modified lhs m |> update lhs v
end

module FlagAnalysis = struct
  include Analysis.Intra_analysis.Forwards (FlagDomain)

  let analyse p = analyse p
end

module Eval = Analysis.Intra_analysis.EvalExpr (FlagLattice)

(** Rewrites boolean exprs in terms of flags to be in terms of numerical
    conditions. *)
module Rewriter = struct
  (** A type of condition as described in
      https://support.arm.com/documentation/dui0231/b/arm-instruction-reference/conditional-execution

      We track one computation for each flag read, noting that sometimes not all
      flags will be computed in the same way. *)
  type t =
    | EQ of { z : FlagSemantics.computation }
    | CS of { c : FlagSemantics.computation }
    | MI of { n : FlagSemantics.computation }
    | VS of { v : FlagSemantics.computation }
    | HI of { c : FlagSemantics.computation; z : FlagSemantics.computation }
    | GE of { n : FlagSemantics.computation; v : FlagSemantics.computation }
    | GT of {
        n : FlagSemantics.computation;
        v : FlagSemantics.computation;
        z : FlagSemantics.computation;
      }
    | Not of t
    | Top  (** Unknown condition type *)
  [@@deriving show { with_path = false }]

  (** Extracts a condition from a boolean expression *)
  let rec extract_condition m e : t =
    let open FlagSemantics in
    let open Expr.AbstractExpr in
    match e with
    | BinaryExpr { op = `EQ; arg1; arg2 } -> (
        (* evaluate arg1 and arg2, if they are of the right form keep *)
        let arg1 = Eval.eval (flip FlagDomain.read m) arg1 in
        let arg2 = Eval.eval (flip FlagDomain.read m) arg2 in
        match (arg1, arg2) with
        | V (Z z), V (Const Always) -> EQ { z }
        | V (C c), V (Const Always) -> CS { c }
        | V (N n), V (Const Always) -> MI { n }
        | V (O v), V (Const Always) -> VS { v }
        | V (N n), V (O v | Const v) -> GE { n; v }
        | _ -> Top)
    | ApplyIntrin
        {
          op = `AND;
          args =
            [
              Expr.BasilExpr.E (BinaryExpr { op = `EQ; arg1 = a; arg2 = b });
              E (BinaryExpr { op = `EQ; arg1 = c; arg2 = d });
            ];
        } -> (
        (* there has to be a better way .......... *)
        let a = Eval.eval (flip FlagDomain.read m) a in
        let b = Eval.eval (flip FlagDomain.read m) b in
        let c = Eval.eval (flip FlagDomain.read m) c in
        let d = Eval.eval (flip FlagDomain.read m) d in
        match (a, b, c, d) with
        | V (C c), V (Const Always), V (Z z), V (Const Never) -> HI { c; z }
        | V (N n), V (O v | Const v), V (Z z), V (Const Never) -> GT { n; v; z }
        | _ -> Top)
    | UnaryExpr { op = `BoolNOT; arg } -> (
        match extract_condition m (Expr.BasilExpr.unfix arg) with
        | Not c -> c
        | c -> Not c)
    | _ -> Top

  (** Replace a condition with its interpretation as an expression *)
  let rec condition_expr cond =
    let open FlagSemantics in
    let open Expr.BasilExpr in
    let value = function
      | Diff (e, e') -> binexp ~op:`BVSUB e e'
      | Sum (e, e') -> applyintrin ~op:`BVADD [ e; e' ]
      | Expr e -> e
      | Always -> bvconst (Bitvec.one ~size:1)
      | Never -> bvconst (Bitvec.zero ~size:1)
    in
    let zero_of e =
      match type_of e with
      | Bitvector size -> Some (bvconst (Bitvec.zero ~size))
      | _ -> None
    in
    match cond with
    | EQ { z = Diff (e, e') } -> Some (binexp ~op:`EQ e e')
    | EQ { z = Sum (e, e') } -> Some (binexp ~op:`EQ e (unexp ~op:`BVNEG e'))
    | EQ { z = Expr e } -> zero_of e |> Option.map (binexp ~op:`EQ e)
    | CS { c = Diff (e, e') } -> Some (binexp ~op:`BVULE e' e)
    | CS { c = Sum (e, e') } -> Some (binexp ~op:`BVULE (unexp ~op:`BVNEG e') e)
    | MI { n } ->
        let e = value n in
        zero_of e |> Option.map (binexp ~op:`BVSLT e)
    (* | VS c -> failwith "overflow rewrite is complicated" *)
    | HI { c = Diff (e, e') as c; z } when equiv_computations c z ->
        Some (binexp ~op:`BVULT e' e)
    | HI { c = Sum (e, e') as c; z } when equiv_computations c z ->
        Some (binexp ~op:`BVULT (unexp ~op:`BVNEG e') e)
    | GE { n = Diff (e, e') as c; v } when equiv_computations c v ->
        Some (binexp ~op:`BVSLE e' e)
    | GE { n = Sum (e, e') as c; v } when equiv_computations c v ->
        Some (binexp ~op:`BVSLE (unexp ~op:`BVNEG e') e)
    | GE { n; v = Never } ->
        let e = value n in
        zero_of e |> Option.map (fun zero -> binexp ~op:`BVSLE zero e)
    | GT { n = Diff (e, e') as n; v; z }
      when equiv_computations n v && equiv_computations n z ->
        Some (binexp ~op:`BVSLT e' e)
    | GT { n = Sum (e, e') as n; v; z }
      when equiv_computations n v && equiv_computations n z ->
        Some (binexp ~op:`BVSLT (unexp ~op:`BVNEG e') e)
    | GT { n; v = Never; z } when equiv_computations n z ->
        let e = value n in
        zero_of e |> Option.map (fun zero -> binexp ~op:`BVSLT zero e)
    | Not cond -> (
        let open Expr.AbstractExpr in
        match condition_expr cond with
        | Some (E (BinaryExpr { op = `BVULE; arg1; arg2 })) ->
            Some (binexp ~op:`BVULT arg2 arg1)
        | Some (E (BinaryExpr { op = `BVULT; arg1; arg2 })) ->
            Some (binexp ~op:`BVULE arg2 arg1)
        | Some (E (BinaryExpr { op = `BVSLE; arg1; arg2 })) ->
            Some (binexp ~op:`BVSLT arg2 arg1)
        | Some (E (BinaryExpr { op = `BVSLT; arg1; arg2 })) ->
            Some (binexp ~op:`BVSLE arg2 arg1)
        | Some e -> Some (Expr.BasilExpr.boolnot e)
        | None -> None)
    | _ -> None

  let rw m e =
    let open Expr.BasilExpr in
    e |> extract_condition m |> condition_expr |> Expr.BasilExpr.replace_opt

  (** Rewrite an expression's branch conditions in terms of flag analysis
      results *)
  let rewrite_expr (m : FlagDomain.t) e =
    Expr.BasilExpr.rewrite_down ~rw_fun:(rw m) e
end

let annotate_stmt_flags m stmt =
  let open Stmt in
  match stmt with
  | Instr_Assume { attrib; body; branch } ->
      let annotations =
        FlagDomain.to_list m |> snd
        |> List.filter_map (fun (v, s) ->
            match s with FlagLattice.V s -> Some (v, s) | _ -> None)
      in
      let attrib =
        List.fold_left
          (fun attrib (v, s) ->
            StringMap.add
              (".flag_semantics_" ^ Var.name v)
              (`String (FlagSemantics.show s))
              attrib)
          attrib annotations
      in
      Instr_Assume { attrib; body; branch }
  | _ -> stmt

let rewrite_stmt_conditions m =
  Stmt.map ~f_lvar:id ~f_rvar:id ~f_expr:(Rewriter.rewrite_expr m)

(** Map statements of a procedure given FlagAnalysis results *)
let stmt_transform (trans : FlagDomain.t -> Program.stmt -> Program.stmt)
    (p : Program.proc) =
  let a = FlagAnalysis.analyse p in
  Procedure.map_blocks_nondet
    (fun (bid, b) ->
      let r =
        FlagAnalysis.A.M.find_opt (Procedure.Vert.Begin bid) a
        |> Option.get_or ~default:FlagDomain.top
      in
      Block.map_fold_forwards
        ~phi:(fun m phi -> (List.fold_left FlagDomain.transfer_phi m phi, phi))
        ~f:(fun m stmt -> (FlagDomain.transfer m stmt, trans m stmt))
        r b
      |> snd)
    p

(** Add flag annotations to assume statements based on flag variables prior
    (debugging) *)
let annotate_assume_flags = stmt_transform annotate_stmt_flags

(** Rewrite boolean expressions of flags into numerical conditions *)
let rewrite_conditions = stmt_transform rewrite_stmt_conditions

let transform = rewrite_conditions

let%expect_test "flag_types" =
  let lst =
    Loader.Loadir.ast_of_string
      {|
var $R0:bv64;
var $R1:bv64;
var $H2:bv64;
var $H3:bv64;
var $PSTATE_N:bv1;
var $PSTATE_Z:bv1;
var $PSTATE_C:bv1;
var $PSTATE_V:bv1;

proc @main() -> ()
[
  block %main [
     $PSTATE_V:bv1 := bvnot(booltobv1(eq(sign_extend(32, bvadd(extract(32,0, $R0), 0x1:bv32)), bvadd(sign_extend(32, extract(32,0, $R0)), 0x1:bv64))));
     $PSTATE_V:bv1 := bvnot(booltobv1(eq(sign_extend(32, bvadd(bvadd(extract(32,0, $R0), 0xfffffffd:bv32), 0x1:bv32)), bvadd(bvadd(sign_extend(32, extract(32,0, $R0)), 0xfffffffffffffffd:bv64), 0x1:bv64))));
     $PSTATE_V:bv1 := bvnot(booltobv1(eq(sign_extend(32, bvadd(bvadd(extract(32,0, $R0), bvnot(bvshl(extract(32,0, $R1), zero_extend(20, 0x0:bv12)))), 0x1:bv32)), bvadd(bvadd(sign_extend(32, extract(32,0, $R0)), sign_extend(32, bvnot(bvshl(extract(32,0, $R1), zero_extend(20, 0x0:bv12))))), 0x1:bv64))));
     $PSTATE_V:bv1 := bvnot(booltobv1(eq(sign_extend(32, bvadd(local_31:bv32, bvshl(local_32:bv32, zero_extend(20, 0x0:bv12)))), bvadd(sign_extend(32, local_31:bv32), sign_extend(32, bvshl(local_32:bv32, zero_extend(20, 0x0:bv12)))))));

     $PSTATE_C:bv1 := bvnot(booltobv1(eq(zero_extend(32, bvadd(extract(32,0, $R0), 0x1:bv32)), bvadd(zero_extend(32, extract(32,0, $R0)), 0x1:bv64))));
     $PSTATE_C:bv1 := bvnot(booltobv1(eq(zero_extend(32, bvadd(bvadd(extract(32,0, $R0), 0xfffffffd:bv32), 0x1:bv32)), bvadd(bvadd(zero_extend(32, extract(32,0, $R0)), 0xfffffffd:bv64), 0x1:bv64))));
     $PSTATE_C:bv1 := bvnot(booltobv1(eq(zero_extend(32, bvadd(bvadd(extract(32,0, $R0), bvnot(bvshl(extract(32,0, $R1), zero_extend(20, 0x0:bv12)))), 0x1:bv32)), bvadd(bvadd(zero_extend(32, extract(32,0, $R0)), zero_extend(32, bvnot(bvshl(extract(32,0, $R1), zero_extend(20, 0x0:bv12))))), 0x1:bv64))));
     $PSTATE_C:bv1 := bvnot(booltobv1(eq(zero_extend(32, bvadd($H2:bv32, bvshl($H3:bv32, zero_extend(20, 0x0:bv12)))), bvadd(zero_extend(32, $H2:bv32), zero_extend(32, bvshl($H3:bv32, zero_extend(20, 0x0:bv12)))))));

     $PSTATE_Z:bv1 := booltobv1(eq(bvadd($H2:bv32, bvshl($H3:bv32, zero_extend(20, 0x0:bv12))), 0x0:bv32));
     $PSTATE_Z:bv1 := booltobv1(eq(bvadd(extract(32,0, $R0), 0x1:bv32), 0x0:bv32));
     $PSTATE_Z:bv1 := booltobv1(eq(bvadd(bvadd(extract(32,0, $R0), bvnot(bvshl(extract(32,0, $R1), zero_extend(20, 0x0:bv12)))), 0x1:bv32), 0x0:bv32));

     $PSTATE_N:bv1 := extract(32,31, bvadd(extract(32,0, $R0), 0x1:bv32));
     $PSTATE_N:bv1 := extract(32,31, bvadd(bvadd(extract(32,0, $R0), bvnot(bvshl(extract(32,0, $R1), zero_extend(20, 0x0:bv12)))), 0x1:bv32));
     $PSTATE_N:bv1 := extract(32,31, bvadd(bvadd(extract(32,0, $R0), 0xffffffff:bv32), 0x1:bv32));

     $PSTATE_V:bv1 := 0x0:bv1;
     $PSTATE_C:bv1 := 0x0:bv1;
     $PSTATE_Z:bv1 := 0x1:bv1;
     $PSTATE_N:bv1 := 0x0:bv1;

    goto (%ret);
  ];
  block %ret [ return; ]
];

prog entry @main;
    |}
  in
  let prog =
    lst.prog |> Program.map_procedures (fun _ -> annotate_flag_assign_stmts)
  in
  print_endline
  @@ Containers_pp.Pretty.to_string ~width:800 (Lang.Program.prog_pretty prog);
  [%expect
    {|
    var $R0:bv64;
    var $R1:bv64;
    var $H2:bv64;
    var $H3:bv64;
    var $PSTATE_N:bv1;
    var $PSTATE_Z:bv1;
    var $PSTATE_C:bv1;
    var $PSTATE_V:bv1;
    proc @main()  -> () {  }
      modifies $PSTATE_C:bv1, $PSTATE_N:bv1, $PSTATE_V:bv1, $PSTATE_Z:bv1
      captures $H2:bv64, $H3:bv64, $PSTATE_C:bv1, $PSTATE_N:bv1, $PSTATE_V:bv1, $PSTATE_Z:bv1, $R0:bv64, $R1:bv64

    [
       block %main [
         $PSTATE_V:bv1 := bvnot(booltobv1(eq(sign_extend(32, bvadd(extract(32,0, $R0), 0x1:bv32)), bvadd(sign_extend(32, extract(32,0, $R0)), 0x1:bv64)))) { .flag_semantics_$PSTATE_V = "(O (Sum (extract(32,0, $R0), 0x1:bv32)))" };
         $PSTATE_V:bv1 := bvnot(booltobv1(eq(sign_extend(32, bvadd(bvadd(extract(32,0, $R0), 0xfffffffd:bv32), 0x1:bv32)), bvadd(bvadd(sign_extend(32, extract(32,0, $R0)), 0xfffffffffffffffd:bv64), 0x1:bv64)))) { .flag_semantics_$PSTATE_V = "(O (Diff (extract(32,0, $R0), 0x2:bv32)))" };
         $PSTATE_V:bv1 := bvnot(booltobv1(eq(sign_extend(32, bvadd(bvadd(extract(32,0, $R0), bvnot(bvshl(extract(32,0, $R1), zero_extend(20, 0x0:bv12)))), 0x1:bv32)), bvadd(bvadd(sign_extend(32, extract(32,0, $R0)), sign_extend(32, bvnot(bvshl(extract(32,0, $R1), zero_extend(20, 0x0:bv12))))), 0x1:bv64)))) { .flag_semantics_$PSTATE_V = "(O (Diff (extract(32,0, $R0), extract(32,0, $R1))))" };
         $PSTATE_V:bv1 := bvnot(booltobv1(eq(sign_extend(32, bvadd(local_31:bv32, bvshl(local_32:bv32, zero_extend(20, 0x0:bv12)))), bvadd(sign_extend(32, local_31:bv32), sign_extend(32, bvshl(local_32:bv32, zero_extend(20, 0x0:bv12))))))) { .flag_semantics_$PSTATE_V = "(O (Sum (local_31:bv32, local_32:bv32)))" };
         $PSTATE_C:bv1 := bvnot(booltobv1(eq(zero_extend(32, bvadd(extract(32,0, $R0), 0x1:bv32)), bvadd(zero_extend(32, extract(32,0, $R0)), 0x1:bv64)))) { .flag_semantics_$PSTATE_C = "(C (Sum (extract(32,0, $R0), 0x1:bv32)))" };
         $PSTATE_C:bv1 := bvnot(booltobv1(eq(zero_extend(32, bvadd(bvadd(extract(32,0, $R0), 0xfffffffd:bv32), 0x1:bv32)), bvadd(bvadd(zero_extend(32, extract(32,0, $R0)), 0xfffffffd:bv64), 0x1:bv64)))) { .flag_semantics_$PSTATE_C = "(C (Diff (extract(32,0, $R0), 0x2:bv32)))" };
         $PSTATE_C:bv1 := bvnot(booltobv1(eq(zero_extend(32, bvadd(bvadd(extract(32,0, $R0), bvnot(bvshl(extract(32,0, $R1), zero_extend(20, 0x0:bv12)))), 0x1:bv32)), bvadd(bvadd(zero_extend(32, extract(32,0, $R0)), zero_extend(32, bvnot(bvshl(extract(32,0, $R1), zero_extend(20, 0x0:bv12))))), 0x1:bv64)))) { .flag_semantics_$PSTATE_C = "(C (Diff (extract(32,0, $R0), extract(32,0, $R1))))" };
         $PSTATE_C:bv1 := bvnot(booltobv1(eq(zero_extend(32, bvadd($H2, bvshl($H3, zero_extend(20, 0x0:bv12)))), bvadd(zero_extend(32, $H2), zero_extend(32, bvshl($H3, zero_extend(20, 0x0:bv12))))))) { .flag_semantics_$PSTATE_C = "(C (Sum ($H2, $H3)))" };
         $PSTATE_Z:bv1 := booltobv1(eq(bvadd($H2, bvshl($H3, zero_extend(20, 0x0:bv12))), 0x0:bv32)) { .flag_semantics_$PSTATE_Z = "(Z (Sum ($H2, $H3)))" };
         $PSTATE_Z:bv1 := booltobv1(eq(bvadd(extract(32,0, $R0), 0x1:bv32), 0x0:bv32)) { .flag_semantics_$PSTATE_Z = "(Z (Sum (extract(32,0, $R0), 0x1:bv32)))" };
         $PSTATE_Z:bv1 := booltobv1(eq(bvadd(bvadd(extract(32,0, $R0), bvnot(bvshl(extract(32,0, $R1), zero_extend(20, 0x0:bv12)))), 0x1:bv32), 0x0:bv32)) { .flag_semantics_$PSTATE_Z = "(Z (Diff (extract(32,0, $R0), extract(32,0, $R1))))" };
         $PSTATE_N:bv1 := extract(32,31, bvadd(extract(32,0, $R0), 0x1:bv32)) { .flag_semantics_$PSTATE_N = "(N (Sum (extract(32,0, $R0), 0x1:bv32)))" };
         $PSTATE_N:bv1 := extract(32,31, bvadd(bvadd(extract(32,0, $R0), bvnot(bvshl(extract(32,0, $R1), zero_extend(20, 0x0:bv12)))), 0x1:bv32)) { .flag_semantics_$PSTATE_N = "(N (Diff (extract(32,0, $R0), extract(32,0, $R1))))" };
         $PSTATE_N:bv1 := extract(32,31, bvadd(bvadd(extract(32,0, $R0), 0xffffffff:bv32), 0x1:bv32)) { .flag_semantics_$PSTATE_N = "(N (Expr extract(32,0, $R0)))" };
         $PSTATE_V:bv1 := 0x0:bv1 { .flag_semantics_$PSTATE_V = "(Const Never)" };
         $PSTATE_C:bv1 := 0x0:bv1 { .flag_semantics_$PSTATE_C = "(Const Never)" };
         $PSTATE_Z:bv1 := 0x1:bv1 { .flag_semantics_$PSTATE_Z = "(Const Always)" };
         $PSTATE_N:bv1 := 0x0:bv1 { .flag_semantics_$PSTATE_N = "(Const Never)" };
         goto (%ret);
       ];
       block %ret [ return; ]
    ];
    prog entry @main;
    |}]

let%expect_test "flag_incorrect" =
  let lst =
    Loader.Loadir.ast_of_string
      {|
var $R0:bv64;
var $R1:bv64;
var $H2:bv64;
var $H3:bv64;
var $PSTATE_N:bv1;
var $PSTATE_Z:bv1;
var $PSTATE_C:bv1;
var $PSTATE_V:bv1;

proc @main() -> ()
[
  block %main [
     // N must extract the top bit, this extracts the second top
     $PSTATE_N:bv1 := extract(31,30, bvadd(extract(32,0, $R0), 0x1:bv32));
     $PSTATE_N:bv1 := extract(31,30, bvadd(bvadd(extract(32,0, $R0), bvnot(bvshl(extract(32,0, $R1), zero_extend(20, 0x0:bv12)))), 0x1:bv32));
     $PSTATE_N:bv1 := extract(31,30, bvadd(bvadd(extract(32,0, $R0), 0xffffffff:bv32), 0x1:bv32));
    goto (%ret);
  ];
  block %ret [ return; ]
];

prog entry @main;
    |}
  in
  let prog =
    lst.prog |> Program.map_procedures (fun _ -> annotate_flag_assign_stmts)
  in
  print_endline
  @@ Containers_pp.Pretty.to_string ~width:800 (Lang.Program.prog_pretty prog);
  [%expect
    {|
    var $R0:bv64;
    var $R1:bv64;
    var $H2:bv64;
    var $H3:bv64;
    var $PSTATE_N:bv1;
    var $PSTATE_Z:bv1;
    var $PSTATE_C:bv1;
    var $PSTATE_V:bv1;
    proc @main()  -> () {  }
      modifies $PSTATE_N:bv1
      captures $PSTATE_N:bv1, $R0:bv64, $R1:bv64

    [ block %main [ $PSTATE_N:bv1 := extract(31,30, bvadd(extract(32,0, $R0), 0x1:bv32)); $PSTATE_N:bv1 := extract(31,30, bvadd(bvadd(extract(32,0, $R0), bvnot(bvshl(extract(32,0, $R1), zero_extend(20, 0x0:bv12)))), 0x1:bv32)); $PSTATE_N:bv1 := extract(31,30, bvadd(bvadd(extract(32,0, $R0), 0xffffffff:bv32), 0x1:bv32)); goto (%ret); ]; block %ret [ return; ] ];
    prog entry @main;
    |}]

let%expect_test "flag_tracking" =
  let lst =
    Loader.Loadir.ast_of_string
      {|
var $R0:bv64;
var $PSTATE_N:bv1;
var $PSTATE_Z:bv1;
var $PSTATE_C:bv1;
var $PSTATE_V:bv1;

proc @main() -> ()
[
  block %main [
     $PSTATE_V:bv1 := bvnot(booltobv1(eq(sign_extend(32, bvadd(extract(32,0, $R0), 0x1:bv32)), bvadd(sign_extend(32, extract(32,0, $R0)), 0x1:bv64))));
     $PSTATE_C:bv1 := bvnot(booltobv1(eq(zero_extend(32, bvadd(extract(32,0, $R0), 0x1:bv32)), bvadd(zero_extend(32, extract(32,0, $R0)), 0x1:bv64))));
     $PSTATE_Z:bv1 := booltobv1(eq(bvadd(extract(32,0, $R0), 0x1:bv32), 0x0:bv32));
     $PSTATE_N:bv1 := extract(32,31, bvadd(extract(32,0, $R0), 0x1:bv32));
     assume booland(eq($PSTATE_N, $PSTATE_V), eq($PSTATE_Z, 0x0:bv1));
    goto (%ret);
  ];
  block %ret [ return; ]
];

prog entry @main;
    |}
  in
  let prog =
    lst.prog |> Program.map_procedures (fun _ -> annotate_assume_flags)
  in
  print_endline
  @@ Containers_pp.Pretty.to_string ~width:800 (Lang.Program.prog_pretty prog);
  [%expect
    {|
    var $R0:bv64;
    var $PSTATE_N:bv1;
    var $PSTATE_Z:bv1;
    var $PSTATE_C:bv1;
    var $PSTATE_V:bv1;
    proc @main()  -> () {  }
      modifies $PSTATE_C:bv1, $PSTATE_N:bv1, $PSTATE_V:bv1, $PSTATE_Z:bv1
      captures $PSTATE_C:bv1, $PSTATE_N:bv1, $PSTATE_V:bv1, $PSTATE_Z:bv1, $R0:bv64

    [
       block %main [
         $PSTATE_V:bv1 := bvnot(booltobv1(eq(sign_extend(32, bvadd(extract(32,0, $R0), 0x1:bv32)), bvadd(sign_extend(32, extract(32,0, $R0)), 0x1:bv64))));
         $PSTATE_C:bv1 := bvnot(booltobv1(eq(zero_extend(32, bvadd(extract(32,0, $R0), 0x1:bv32)), bvadd(zero_extend(32, extract(32,0, $R0)), 0x1:bv64))));
         $PSTATE_Z:bv1 := booltobv1(eq(bvadd(extract(32,0, $R0), 0x1:bv32), 0x0:bv32));
         $PSTATE_N:bv1 := extract(32,31, bvadd(extract(32,0, $R0), 0x1:bv32));
         assume booland(eq($PSTATE_N, $PSTATE_V), eq($PSTATE_Z, 0x0:bv1)) { .flag_semantics_$PSTATE_C = "(C (Sum (extract(32,0, $R0), 0x1:bv32)))"; .flag_semantics_$PSTATE_N = "(N (Sum (extract(32,0, $R0), 0x1:bv32)))"; .flag_semantics_$PSTATE_V = "(O (Sum (extract(32,0, $R0), 0x1:bv32)))"; .flag_semantics_$PSTATE_Z = "(Z (Sum (extract(32,0, $R0), 0x1:bv32)))" };
         goto (%ret);
       ];
       block %ret [ return; ]
    ];
    prog entry @main;
    |}]

let%expect_test "flag_clobbering" =
  let lst =
    Loader.Loadir.ast_of_string
      {|
var $R0:bv64;
var $R1:bv64;
var $PSTATE_Z:bv1;

proc @main() -> ()
[
  block %main [
     $PSTATE_Z:bv1 := booltobv1(eq(bvadd(bvadd(extract(32,0, $R0), bvnot(bvshl(extract(32,0, $R1), zero_extend(20, 0x0:bv12)))), 0x1:bv32), 0x0:bv32));
     assume eq($PSTATE_Z, 0x0:bv1);
     $R0:bv64 := bvadd($R0:bv64, 0xdeadbeef:bv64);
     assume eq($PSTATE_Z, 0x0:bv1);

     $PSTATE_Z:bv1 := booltobv1(eq(bvadd(bvadd(extract(32,0, $R0), bvnot(bvshl(extract(32,0, $R1), zero_extend(20, 0x0:bv12)))), 0x1:bv32), 0x0:bv32));
     assume eq($PSTATE_Z, 0x0:bv1);
     $R1:bv64 := bvadd($R1:bv64, 0xdeadbeef:bv64);
     assume eq($PSTATE_Z, 0x0:bv1);
    goto (%ret);
  ];
  block %ret [ return; ]
];

prog entry @main;
    |}
  in
  let prog =
    lst.prog |> Program.map_procedures (fun _ -> annotate_assume_flags)
  in
  print_endline
  @@ Containers_pp.Pretty.to_string ~width:200 (Lang.Program.prog_pretty prog);
  [%expect
    {|
    var $R0:bv64;
    var $R1:bv64;
    var $PSTATE_Z:bv1;
    proc @main()  -> () {  }
      modifies $PSTATE_Z:bv1, $R0:bv64, $R1:bv64
      captures $PSTATE_Z:bv1, $R0:bv64, $R1:bv64

    [
       block %main [
         $PSTATE_Z:bv1 := booltobv1(eq(bvadd(bvadd(extract(32,0, $R0), bvnot(bvshl(extract(32,0, $R1), zero_extend(20, 0x0:bv12)))), 0x1:bv32), 0x0:bv32));
         assume eq($PSTATE_Z, 0x0:bv1) { .flag_semantics_$PSTATE_Z = "(Z (Diff (extract(32,0, $R0), extract(32,0, $R1))))" };
         $R0:bv64 := bvadd($R0, 0xdeadbeef:bv64);
         assume eq($PSTATE_Z, 0x0:bv1);
         $PSTATE_Z:bv1 := booltobv1(eq(bvadd(bvadd(extract(32,0, $R0), bvnot(bvshl(extract(32,0, $R1), zero_extend(20, 0x0:bv12)))), 0x1:bv32), 0x0:bv32));
         assume eq($PSTATE_Z, 0x0:bv1) { .flag_semantics_$PSTATE_Z = "(Z (Diff (extract(32,0, $R0), extract(32,0, $R1))))" };
         $R1:bv64 := bvadd($R1, 0xdeadbeef:bv64);
         assume eq($PSTATE_Z, 0x0:bv1);
         goto (%ret);
       ];
       block %ret [ return; ]
    ];
    prog entry @main;
    |}]

let%expect_test "flag_not_clobbering" =
  let lst =
    Loader.Loadir.ast_of_string
      {|
var $R0:bv64;
var $PSTATE_Z:bv1;

proc @main() -> ()
[
  block %main [
     $PSTATE_Z:bv1 := 0x1:bv1;
     assume eq($PSTATE_Z, 0x0:bv1);
     $R0:bv64 := bvadd($R0:bv64, 0xdeadbeef:bv64);
     assume eq($PSTATE_Z, 0x0:bv1);
    goto (%ret);
  ];
  block %ret [ return; ]
];

prog entry @main;
    |}
  in
  let prog =
    lst.prog |> Program.map_procedures (fun _ -> annotate_assume_flags)
  in
  print_endline
  @@ Containers_pp.Pretty.to_string ~width:80 (Lang.Program.prog_pretty prog);
  [%expect
    {|
    var $R0:bv64;
    var $PSTATE_Z:bv1;
    proc @main()  -> () {  }
      modifies $PSTATE_Z:bv1, $R0:bv64
      captures $PSTATE_Z:bv1, $R0:bv64

    [
       block %main [
         $PSTATE_Z:bv1 := 0x1:bv1;
         assume eq($PSTATE_Z, 0x0:bv1) { .flag_semantics_$PSTATE_Z = "(Const Always)" };
         $R0:bv64 := bvadd($R0, 0xdeadbeef:bv64);
         assume eq($PSTATE_Z, 0x0:bv1) { .flag_semantics_$PSTATE_Z = "(Const Always)" };
         goto (%ret);
       ];
       block %ret [ return; ]
    ];
    prog entry @main;
    |}]

let%expect_test "rewrites" =
  let lst =
    Loader.Loadir.ast_of_string
      {|
var $R0:bv64;
var $PSTATE_N:bv1;
var $PSTATE_Z:bv1;
var $PSTATE_C:bv1;
var $PSTATE_V:bv1;

proc @main() -> ()
[
  block %main [
     $PSTATE_V:bv1 := bvnot(booltobv1(eq(sign_extend(64, bvadd(bvadd($R0, 0xfffffffffffffffe:bv64), 0x1:bv64)), bvadd(bvadd(sign_extend(64, $R0), 0xfffffffffffffffffffffffffffffffe:bv128), 0x1:bv128))));
     $PSTATE_C:bv1 := bvnot(booltobv1(eq(zero_extend(64, bvadd(bvadd($R0, 0xfffffffffffffffe:bv64), 0x1:bv64)), bvadd(bvadd(zero_extend(64, $R0), 0xfffffffffffffffe:bv128), 0x1:bv128))));
     $PSTATE_Z:bv1 := booltobv1(eq(bvadd(bvadd($R0, 0xfffffffffffffffe:bv64), 0x1:bv64), 0x0:bv64));
     $PSTATE_N:bv1 := extract(64,63, bvadd(bvadd($R0, 0xfffffffffffffffe:bv64), 0x1:bv64));
     assume booland(eq($PSTATE_N, $PSTATE_V), eq($PSTATE_Z, 0x0:bv1));
    goto (%ret);
  ];
  block %ret [ return; ]
];

prog entry @main;
    |}
  in
  let prog = lst.prog |> Program.map_procedures (fun _ -> rewrite_conditions) in
  print_endline
  @@ Containers_pp.Pretty.to_string ~width:200 (Lang.Program.prog_pretty prog);
  [%expect
    {|
    var $R0:bv64;
    var $PSTATE_N:bv1;
    var $PSTATE_Z:bv1;
    var $PSTATE_C:bv1;
    var $PSTATE_V:bv1;
    proc @main()  -> () {  }
      modifies $PSTATE_C:bv1, $PSTATE_N:bv1, $PSTATE_V:bv1, $PSTATE_Z:bv1
      captures $PSTATE_C:bv1, $PSTATE_N:bv1, $PSTATE_V:bv1, $PSTATE_Z:bv1, $R0:bv64

    [
       block %main [
         $PSTATE_V:bv1 := bvnot(booltobv1(eq(sign_extend(64, bvadd(bvadd($R0, 0xfffffffffffffffe:bv64), 0x1:bv64)), bvadd(bvadd(sign_extend(64, $R0), 0xfffffffffffffffffffffffffffffffe:bv128), 0x1:bv128))));
         $PSTATE_C:bv1 := bvnot(booltobv1(eq(zero_extend(64, bvadd(bvadd($R0, 0xfffffffffffffffe:bv64), 0x1:bv64)), bvadd(bvadd(zero_extend(64, $R0), 0xfffffffffffffffe:bv128), 0x1:bv128))));
         $PSTATE_Z:bv1 := booltobv1(eq(bvadd(bvadd($R0, 0xfffffffffffffffe:bv64), 0x1:bv64), 0x0:bv64));
         $PSTATE_N:bv1 := extract(64,63, bvadd(bvadd($R0, 0xfffffffffffffffe:bv64), 0x1:bv64));
         assume bvslt(0x1:bv64, $R0);
         goto (%ret);
       ];
       block %ret [ return; ]
    ];
    prog entry @main;
    |}]
