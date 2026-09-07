(** Naive parameter and SSA transform *)

open Lang.Common
open Lang
open Containers

let debug = ref false
let dbg_print = if !debug then print_endline else fun s -> ()
let dbg f = if !debug then f () else ()

(** How a variable introduced by lambda-lifting relates to the original global
    it stands for. *)
type lifted_kind =
  | In_param
      (** formal in-parameter carrying the global's procedure-entry value *)
  | Out_param
      (** formal out-parameter carrying the global's procedure-exit value *)
  | Body_local  (** body-local that replaced the global at its use sites *)

type proc_lift_map = (lifted_kind * Var.t) VarMap.t
(** Maps each variable {!lift_procedure_params} introduces back to the original
    global it stands for, tagged with how it was introduced. Used to translate
    invariants expressed over the lifted program back into the original
    program's globals (see {!Chc_infer}). *)

type program_lift_map = proc_lift_map IDMap.t
(** Per-procedure {!proc_lift_map}, keyed by procedure id. *)

(** Introduce a self-copy before every assume or assert that contains one
    variable, so that ssa has branch condition flow-sensitivity.

    https://dspace.mit.edu/bitstream/handle/1721.1/86578/48072795-MIT.pdf *)
let intro_ssi_assigns proc (should_lift : Var.t -> bool) =
  let fix_block (_, b) =
    b
    |> Block.flat_map ~phi:id
         Stmt.(
           function
           | (Instr_Assert { body; attrib } | Instr_Assume { body; attrib }) as
             a ->
               let fv =
                 Expr.BasilExpr.free_vars body |> VarSet.filter should_lift
               in
               if VarSet.cardinal fv > 0 then
                 Iter.doubleton
                   (Instr_Assign
                      {
                        al =
                          VarSet.to_list fv
                          |> List.map (fun v -> (v, Expr.BasilExpr.rvar v));
                        attrib;
                      })
                   a
               else Iter.singleton a
           | b -> Iter.singleton b)
  in
  Procedure.map_blocks_nondet fix_block proc

(** Delete unused local var declarations and return used global variables.
    assumes captures/modifies are up to date. *)
let drop_unused_var_declarations_proc p =
  let spec = Procedure.specification p in
  let used = Procedure.free_vars_specification spec |> VarSet.of_iter in
  let used =
    Procedure.fold_blocks_topo_fwd
      (fun acc id bl ->
        Iter.append (Block.read_vars_iter bl) (Block.assigned_vars_iter bl)
        |> Iter.fold (fun acc i -> VarSet.add i acc) acc)
      used p
  in
  Var.Decls.filter_map_inplace
    (fun _ v -> if VarSet.mem v used then Some v else None)
    (Procedure.local_decls p);
  VarSet.filter Var.is_global used

(** Update modsets and delete unused variable definitions *)
let drop_unused_var_declarations_prog (p : Program.t) =
  let p = Spec_modifies.set_modsets p in
  let used =
    Program.procs p
    |> Iter.fold
         (fun acc (i, p) ->
           VarSet.union acc (drop_unused_var_declarations_proc p))
         VarSet.empty
  in
  Program.filter_map_decls
    (fun _ v ->
      match v with
      | Program.(Variable { binding } as b) ->
          if VarSet.mem binding used then Some b else None
      | o -> Some o)
    p

let should_lift ~skip_observable ~skip_maps v =
  let skip =
    (skip_observable && Var.is_shared v)
    || (skip_maps && Var.typ v |> function Map _ -> true | _ -> false)
    || (Var.is_global v && Var.is_constant v)
  in
  not skip

let check_ssa ~skip_observable ~skip_maps proc =
  let add_assign m v =
    VarMap.get_or ~default:0 v m |> fun n -> VarMap.add v (n + 1) m
  in
  let assigns =
    Procedure.fold_blocks_topo_fwd
      (fun acc idbl bl ->
        let acc =
          List.fold_left
            (fun acc (phi : Var.t Block.phi) -> add_assign acc phi.lhs)
            acc bl.phis
        in
        Block.stmts_iter bl
        |> Iter.fold
             (fun acc stmt -> Stmt.iter_lvar stmt |> Iter.fold add_assign acc)
             acc)
      VarMap.empty proc
  in
  assert (
    VarMap.for_all
      (fun v i -> (not (should_lift ~skip_observable ~skip_maps v)) || i = 1)
      assigns)

let param_name suffix g =
  String.drop_while (function '$' -> true | _ -> false) (Var.name g) ^ suffix

let lift_procedure_params prog ~skip_observable ~skip_maps all_lifted procid
    proc =
  let spec = Procedure.specification proc in
  (* We cannot lift variables in rely/guarantee clauses. This check
        assumes that only observable variables appear in these clauses. *)
  if not skip_observable then begin
    if not (List.is_empty spec.rely) then
      failwith
        (Printf.sprintf
           "set_params: procedure %s has non-empty rely clause (unsupported)"
           (ID.name procid));
    if not (List.is_empty spec.guarantee) then
      failwith
        (Printf.sprintf
           "set_params: procedure %s has non-empty guarantee clause \
            (unsupported)"
           (ID.name procid))
  end;
  let captures =
    List.filter (should_lift ~skip_observable ~skip_maps) spec.captures_globs
  in
  let modifies =
    List.filter (should_lift ~skip_observable ~skip_maps) spec.modifies_globs
  in
  (* (param_key, original_global, fresh_param_var) triples *)
  let inparam =
    List.map
      (fun g ->
        let name = param_name "_in" g in
        (name, g, Procedure.fresh_var ~pure:true ~name proc (Var.typ g)))
      captures
  in
  let outparam =
    List.map
      (fun g ->
        let name = param_name "_out" g in
        (name, g, Procedure.fresh_var ~pure:true ~name proc (Var.typ g)))
      modifies
  in
  (* Fresh local variable for each captured global – replaces the global
           in the procedure body so it is no longer referenced as a global. *)
  let glob_to_local =
    List.map
      (fun g ->
        let name = param_name "" g in
        (g, Procedure.fresh_var ~pure:false ~name proc (Var.typ g)))
      captures
  in
  let glob_to_local_map =
    List.fold_left
      (fun m (g, lv) -> StringMap.add (Var.name g) lv m)
      StringMap.empty glob_to_local
  in
  let local_of g = StringMap.find (Var.name g) glob_to_local_map in
  let to_formal triples =
    List.fold_left
      (fun m (name, _, v) -> StringMap.add name v m)
      StringMap.empty triples
  in
  (* %inputs block: g_local := g_in for each captured global *)
  let assigns_in =
    List.map (fun (_, g, v) -> (local_of g, Expr.BasilExpr.rvar v)) inparam
  in
  (* %returns block: g_out := g_local for each modified global *)
  let assigns_out =
    List.map (fun (_, g, v) -> (v, Expr.BasilExpr.rvar (local_of g))) outparam
  in

  let add_input_and_output_vars graph =
    let graph =
      if List.is_empty assigns_in then graph
      else
        let graph, inbl =
          Procedure.fresh_block_graph proc graph ~name:"%inputs"
            ~stmts:
              [ Stmt.Instr_Assign { al = assigns_in; attrib = Attrib.empty } ]
            ()
        in
        let open Procedure.Vert in
        let edges = Procedure.G.succ_e graph Entry in
        let graph = List.fold_left Procedure.G.remove_edge_e graph edges in
        let new_edges = List.map (fun (_, l, e) -> (End inbl, l, e)) edges in
        let graph = List.fold_left Procedure.G.add_edge_e graph new_edges in
        Procedure.G.add_edge graph Entry (Begin inbl)
    in
    let graph =
      if List.is_empty assigns_out then graph
      else
        let graph, outbl =
          Procedure.fresh_block_graph proc graph ~name:"%returns"
            ~stmts:
              [ Stmt.Instr_Assign { al = assigns_out; attrib = Attrib.empty } ]
            ()
        in
        let open Procedure.Vert in
        let edges = Procedure.G.pred_e graph Return in
        let graph = List.fold_left Procedure.G.remove_edge_e graph edges in
        let new_edges = List.map (fun (b, l, _) -> (b, l, Begin outbl)) edges in
        let graph = List.fold_left Procedure.G.add_edge_e graph new_edges in
        Procedure.G.add_edge graph (End outbl) Return
    in
    graph
  in

  let proc = Procedure.map_graph add_input_and_output_vars proc in
  let proc =
    proc
    |> Procedure.map_formal_in_params (fun fip ->
        StringMap.union
          (fun n _ _ -> failwith @@ "Existing param with name: " ^ n)
          fip (to_formal inparam))
    |> Procedure.map_formal_out_params (fun fop ->
        StringMap.union
          (fun n _ _ -> failwith @@ "Existing param with name: " ^ n)
          fop (to_formal outparam))
  in
  (* Maps from global name to in-/out-param vars, used for spec rewriting *)
  let glob_to_inparam =
    List.fold_left
      (fun m (_, g, v) -> StringMap.add (Var.name g) v m)
      StringMap.empty inparam
  in
  let glob_to_outparam =
    List.fold_left
      (fun m (_, g, v) -> StringMap.add (Var.name g) v m)
      StringMap.empty outparam
  in
  let skip_any = skip_observable || skip_maps in
  (* replace all variables with their equivalent in the pre-state *)
  let rewrite_old_expr expr =
    let open Expr.AbstractExpr in
    let open Expr.BasilExpr in
    let alg node =
      match node with
      | UnaryExpr { op = `Old; arg } -> replace [%here] arg
      | RVar { id } when Var.is_constant id -> Keep
      | RVar { id } -> (
          match StringMap.find_opt (Var.name id) glob_to_inparam with
          | Some v -> replace [%here] (rvar v)
          | None (* identity function *)
            when StringMap.exists
                   (fun _ n -> Var.equal id n)
                   (Procedure.formal_in_params proc) ->
              Keep
          | None when skip_any ->
              failwith
                ("Variable in contract but is not a parameter, or global \
                  captured or modified by procedure: " ^ Var.name id)
          | None -> Keep)
      | _ -> Keep
    in
    rewrite ~rw_fun:alg expr
  in
  (* Rewrite requires: replace all captured globals with in-params and
           strip any Old wrappers (all refs already denote the pre-state) *)
  let rewrite_ensures_expr expr =
    let open Expr.AbstractExpr in
    let open Expr.BasilExpr in
    (* Rewrite ensures: Old(g) → g_in (entry value); bare modified g →
           g_out (exit value); bare captured-only g → g_in (unchanged).
           Old(g) is handled first so the bare-g pass doesn't clobber it. *)
    let fvs = Expr.BasilExpr.free_vars expr in
    let alg node =
      match node with
      | UnaryExpr { op = `Old; arg } -> replace [%here] (rewrite_old_expr arg)
      | RVar { id } when Var.is_constant id || (not @@ VarSet.mem id fvs) ->
          Keep
      | RVar { id } -> (
          match StringMap.find_opt (Var.name id) glob_to_outparam with
          | Some v -> replace [%here] (rvar v)
          | None
            when Iter.exists
                   (fun n -> Var.equal id n)
                   (StringMap.values (Procedure.formal_out_params proc)
                   |> Iter.append
                        (Procedure.formal_in_params proc |> StringMap.values))
            ->
              Keep
          | None -> (
              match StringMap.find_opt (Var.name id) glob_to_inparam with
              | Some v -> replace [%here] (rvar v)
              | None when skip_any ->
                  failwith
                    ("Variable in contract but is not captured or modified by \
                      procedure: " ^ Var.name id)
              | None -> Keep))
      | _ -> Keep
    in
    rewrite_down ~rw_fun:alg expr
  in
  let rewrite_internal_expr_old expr =
    let open Expr.AbstractExpr in
    let open Expr.BasilExpr in
    let alg node =
      match node with
      | UnaryExpr { op = `Old; arg } -> replace [%here] (rewrite_old_expr arg)
      | _ -> Keep
    in
    rewrite_down ~rw_fun:alg expr
  in
  let rewrite_requires_expr expr = rewrite_old_expr expr in
  let proc =
    let spec = Procedure.specification proc in
    Procedure.set_specification proc
      {
        spec with
        requires = List.map rewrite_requires_expr spec.requires;
        ensures = List.map rewrite_ensures_expr spec.ensures;
      }
  in
  let proc =
    Procedure.map_blocks_topo_fwd
      (fun _bid b ->
        Block.map ~phi:Fun.id
          (Stmt.map ~f_lvar:Fun.id ~f_expr:rewrite_internal_expr_old
             ~f_rvar:Fun.id)
          b)
      proc
  in
  (* Rewrite call sites using the original p.procs specs, emitting
           g (the global) in args/lhs.  The body substitution below then
           turns those into g_local automatically. *)
  let proc =
    Procedure.map_blocks_topo_fwd
      (fun _bid b ->
        Block.map ~phi:Fun.id
          (function
            | Stmt.Instr_Call { procid; lhs; args; attrib } as stmt -> (
                match Program.proc_opt prog procid with
                | None -> stmt
                | Some callee ->
                    let cspec = Procedure.specification callee in
                    let new_args =
                      List.fold_left
                        (fun m g ->
                          if should_lift ~skip_observable ~skip_maps g then
                            StringMap.add (param_name "_in" g)
                              (Expr.BasilExpr.rvar g) m
                          else m)
                        args cspec.captures_globs
                    in
                    let new_lhs =
                      List.fold_left
                        (fun m g ->
                          if should_lift ~skip_observable ~skip_maps g then
                            StringMap.add (param_name "_out" g) g m
                          else m)
                        lhs cspec.modifies_globs
                    in
                    Stmt.Instr_Call
                      { procid; lhs = new_lhs; args = new_args; attrib })
            | s -> s)
          b)
      proc
  in
  (* Substitute g → g_local throughout the body (including the call
           args/lhs emitted above), eliminating all global references. *)
  let subst_var v =
    Option.value ~default:v (StringMap.find_opt (Var.name v) glob_to_local_map)
  in
  let subst_expr e =
    Expr.BasilExpr.substitute
      (fun v ->
        Option.map Expr.BasilExpr.rvar
          (StringMap.find_opt (Var.name v) glob_to_local_map))
      e
  in
  let proc =
    Procedure.map_blocks_topo_fwd
      (fun _bid b ->
        Block.map ~phi:Fun.id
          (Stmt.map ~f_lvar:subst_var ~f_expr:subst_expr ~f_rvar:subst_var)
          b)
      proc
  in
  (* Record how each introduced variable maps back to its original global, so
     callers can translate invariants over the lifted program back into the
     original program's globals. *)
  let lift_map =
    let add_param kind acc triples =
      List.fold_left (fun m (_, g, v) -> VarMap.add v (kind, g) m) acc triples
    in
    VarMap.empty
    |> Fun.flip (add_param In_param) inparam
    |> Fun.flip (add_param Out_param) outparam
    |> fun m ->
    List.fold_left
      (fun m (g, lv) -> VarMap.add lv (Body_local, g) m)
      m glob_to_local
  in
  (proc, lift_map)

let set_params_with_map ?(skip_observable = true) ?(skip_maps = true)
    (p : Program.t) : Program.t * program_lift_map =
  (* Collect all globals being lifted, for removal from p.globals at the end *)
  let globals_to_param_lift =
    Program.procs p
    |> Iter.fold
         (fun acc (_, proc) ->
           List.fold_left
             (fun s g ->
               if should_lift ~skip_observable ~skip_maps g then g :: s else s)
             acc (Procedure.specification proc).captures_globs)
         []
  in

  (* remove lifted from modifies specification *)
  let fix_specification _ proc =
    let spec = Procedure.specification proc in
    Procedure.set_specification proc
      {
        spec with
        captures_globs =
          List.filter
            (fun g -> not (should_lift ~skip_observable ~skip_maps g))
            spec.captures_globs;
        modifies_globs =
          List.filter
            (fun g -> not (should_lift ~skip_observable ~skip_maps g))
            spec.modifies_globs;
      }
  in

  let lift_maps = ref IDMap.empty in
  let lift procid proc =
    let proc, m =
      lift_procedure_params p ~skip_observable ~skip_maps globals_to_param_lift
        procid proc
    in
    lift_maps := IDMap.add procid m !lift_maps;
    proc
  in
  let p =
    p
    |> Program.map_procedures lift
    |> Program.map_procedures fix_specification
    |> Program.filter_decls (fun _ -> function
      | Program.Variable { binding } ->
          not (List.exists (Var.equal binding) globals_to_param_lift)
      | _ -> true)
  in
  (p, !lift_maps)

(** Lambda-lifting: replace captured globals with explicit parameters. Discards
    the back-translation map; use {!set_params_with_map} to keep it. *)
let set_params ?skip_observable ?skip_maps (p : Program.t) : Program.t =
  fst (set_params_with_map ?skip_observable ?skip_maps p)

let ssa ?(skip_observable = true) ?(skip_maps = true) (in_proc : Program.proc) =
  let in_proc =
    intro_ssi_assigns in_proc (should_lift ~skip_observable ~skip_maps)
  in
  let lives = Livevars.run in_proc in
  let rename r v : Var.t =
    if
      (* don't rename formal out params; should only be assigned once anyway*)
      (not @@ should_lift ~skip_observable ~skip_maps v)
      || Procedure.formal_out_params in_proc
         |> StringMap.exists (fun _ i -> Var.equal i v)
    then v
    else
      let nv =
        Procedure.fresh_var ~pure:true ~name:(Var.name v) in_proc (Var.typ v)
      in
      r := (v, nv) :: !r;
      nv
  in
  let rn_stmt rr (stmt : ('v, 'v, 'e) Stmt.t) :
      Var.t VarMap.t * ('v, 'v, 'e) Stmt.t =
    let read v =
      try VarMap.find v rr with
      | Not_found
        when (not @@ should_lift ~skip_observable ~skip_maps v)
             || StringMap.exists
                  (fun i j -> Var.equal j v)
                  (Procedure.formal_out_params in_proc)
             || StringMap.exists
                  (fun i j -> Var.equal j v)
                  (Procedure.formal_in_params in_proc) ->
          v
      | Not_found ->
          failwith @@ "not found: " ^ Var.to_string v
          ^ " likely a read-uninitialised variable"
    in
    let new_renames = ref [] in
    let stmt =
      Stmt.map ~f_lvar:(rename new_renames) ~f_rvar:read
        ~f_expr:(fun e ->
          Expr.BasilExpr.substitute
            (fun v -> Some (Expr.BasilExpr.rvar @@ read v))
            e)
        stmt
    in
    let vm =
      (List.fold_left (fun m (v, nv) -> VarMap.add v nv m) rr !new_renames, stmt)
    in
    vm
  in
  let st = Hashtbl.create 100 in

  (* map from block -> (orig var  -> (var * (block * var)) list) *)
  (* block -> orig var -> phis list *)
  let (phis
        : ( IDSet.elt,
            (Var.t * (IDSet.elt * Var.t) list) VarMap.t )
          Stdlib.Hashtbl.t) =
    Hashtbl.create 100
  in

  let phi_to_def (joined_phis : (Var.t * (IDSet.elt * Var.t) list) VarMap.t) =
    VarMap.values joined_phis
    |> Iter.map (function lhs, rhs -> Block.{ lhs; rhs })
    |> Iter.to_list
  in

  let merge_existing_phi (target_block : ID.t) (block : ID.t) (v : Var.t) r =
    match r with
    | `Both ((phi, existing_phi_defs), b) ->
        Some (phi, (block, b) :: existing_phi_defs)
    | `Left phi ->
        failwith @@ "undef pred" ^ Var.to_string v ^ "  " ^ ID.to_string block
    | `Right rn ->
        dbg (fun () ->
            print_endline
            @@ "cannot join as no phi defined for variable -> should be dead \
                :: : " ^ Var.to_string v ^ " " ^ " block phi "
            ^ ID.to_string target_block ^ ID.to_string block);
        None
  in

  let merge_phi block v r =
    match r with
    | `Both ((phi, defs), b) -> Some (phi, (block, b) :: defs)
    | `Left phi -> Some phi
    | `Right rn ->
        Some
          ( Procedure.fresh_var ~pure:true in_proc ~name:(Var.name v) (Var.typ v),
            [ (block, rn) ] )
  in
  let delayed_phis = ref IDSet.empty in

  let tf_block proc block_id (b : Program.bloc) =
    let pred = Procedure.blocks_pred proc block_id |> Iter.to_list in
    let get_st_pred id =
      Hashtbl.get st id |> function
      | Some v -> v
      | None ->
          Hashtbl.add phis id VarMap.empty;
          delayed_phis := IDSet.add id !delayed_phis;
          VarMap.empty
    in

    let lives2 = lives (End block_id) in
    let lives2 =
      Block.fold_backwards ~init:lives2 ~phi:const
        ~f:Stmt.(fun init -> free_vars ~init)
        b
    in

    let new_renames = ref [] in
    let cur_phis = b.phis in
    let cur_phis =
      List.fold_left
        (fun acc ({ lhs; rhs } : Var.t Block.phi) ->
          VarMap.add lhs
            ( rename new_renames lhs,
              rhs
              |> List.map (fun (a, b) ->
                  (a, VarMap.get_or ~default:b b (get_st_pred a))) )
            acc)
        VarMap.empty cur_phis
    in

    let renames, bl_phis =
      match pred with
      | [] ->
          Hashtbl.add phis block_id VarMap.empty;
          (VarMap.empty, [])
      | [ (id, _) ] -> (Hashtbl.find st id, [])
      | inc ->
          let joined_phis =
            List.map (fun (id, _) -> (id, get_st_pred id)) inc
            |> List.fold_left
                 (fun phim (block, rn) ->
                   let rn = VarMap.filter (fun v _ -> VarSet.mem v lives2) rn in
                   VarMap.merge_safe ~f:(merge_phi block) phim rn)
                 cur_phis
          in
          (* TODO: this will join everything, we should only join things with diff definitions *)
          Hashtbl.add phis block_id joined_phis;

          let renames = VarMap.mapi (fun i (v, t) -> v) joined_phis in
          (renames, phi_to_def joined_phis)
    in

    let renames, nb =
      Block.map_fold_forwards
        ~phi:(fun i j -> (i, j))
        ~f:(fun i a -> rn_stmt i a)
        renames b
    in
    let renames =
      let l = lives (End block_id) in
      VarMap.filter (fun v a -> VarSet.mem v l) renames
    in
    Hashtbl.add st block_id renames;
    Procedure.update_block proc block_id { nb with phis = bl_phis }
  in

  let proc = Procedure.fold_blocks_topo_fwd tf_block in_proc in_proc in

  let fixup_delayed block_id proc =
    let renames = Hashtbl.find st block_id in
    if IDSet.mem block_id !delayed_phis then
      Procedure.blocks_succ proc block_id
      |> Iter.filter (fun (bid, _) ->
          let pred =
            Procedure.G.pred
              (Option.get_exn_or "unreachable" @@ Procedure.graph proc)
              (Begin bid)
          in
          List.length pred > 1)
      |> Iter.fold
           (fun proc (succ_bid, _) ->
             let eblock =
               Procedure.get_block proc succ_bid
               |> Option.get_exn_or "block not exist"
             in
             dbg (fun f ->
                 print_endline @@ "   updating " ^ ID.to_string succ_bid;
                 print_endline @@ "     phis"
                 ^ Iter.to_string (function a, b ->
                     Var.to_string a ^ "->" ^ Var.to_string b)
                 @@ VarMap.to_iter renames);
             let renames : Var.t VarMap.t = renames in
             let (existing : (Var.t * (ID.t * Var.t) list) VarMap.t) =
               Hashtbl.get_or ~default:VarMap.empty phis succ_bid
             in
             let nphis =
               VarMap.merge_safe
                 ~f:((merge_existing_phi succ_bid) block_id)
                 existing renames
             in
             Hashtbl.add phis succ_bid nphis;
             dbg (fun f ->
                 print_endline @@ " new PHIS "
                 ^ (nphis |> VarMap.to_iter
                   |> Iter.to_string (function v, (v2, defs) ->
                       Var.to_string v ^ "->" ^ Var.to_string v2 ^ "->"
                       ^ List.to_string
                           (function
                             | a, b -> ID.to_string a ^ "->" ^ Var.to_string b)
                           defs)));
             let phis = phi_to_def nphis in
             dbg (fun f ->
                 print_endline @@ " new PHIS "
                 ^ (phis
                   |> List.to_string (fun b -> (Block.show_phi Var.pretty) b)));
             Procedure.update_block proc succ_bid { eblock with phis })
           proc
    else proc
  in
  let proc = IDSet.fold fixup_delayed !delayed_phis proc in
  let check_bl (block_id, (block : Program.bloc)) =
    let pred =
      Procedure.blocks_pred proc block_id |> Iter.map (fun (i, _) -> i)
    in
    let npred = Iter.length pred in
    block.phis
    |> List.map (fun (p : Var.t Block.phi) ->
        List.to_iter p.rhs |> Iter.map (fun (b, _) -> b) |> fun bs ->
        let preg = Iter.length (Iter.inter bs pred) = npred in
        let bad = Iter.diff pred bs |> Iter.to_string ~sep:", " ID.to_string in
        if not preg then
          print_endline @@ "bad: " ^ ID.to_string block_id ^ "; missing " ^ bad;
        preg)
    |> List.for_all id
  in
  assert (Procedure.iter_blocks_topo_fwd proc |> Iter.for_all check_bl);
  check_ssa ~skip_observable ~skip_maps proc;
  proc

let ssa_prog ?(skip_observable = true) ?(skip_maps = true) (p : Program.t) =
  Program.map_procedures (fun _ -> ssa ~skip_observable ~skip_maps) p
