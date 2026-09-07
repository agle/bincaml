open Common
open Containers
open Expr

module Vert = struct
  type t =
    | Begin of ID.t
        (** Beginning of a block within the procedure. This is the target of
            jumps. *)
    | End of ID.t
        (** Immediately after a block within the procedure. This is the source
            of jumps. *)
    | Entry  (** Entry of the procedure when it is called. *)
    | Return  (** Normal return from the procedure, returning to the caller. *)
    | Exit  (** Exiting the program, not returning to the caller. *)
  [@@deriving show { with_path = false }, eq, ord]

  let hash (v : t) =
    let h = Hash.pair Hash.int Hash.int in
    Hash.map
      (function
        | Entry -> (1, 1)
        | Return -> (3, 1)
        | Exit -> (5, 1)
        | Begin i -> (31, ID.hash i)
        | End i -> (37, ID.hash i))
      h v

  let block_id_string = function
    | Begin i -> ID.to_string i
    | End i -> ID.to_string i
    | Entry -> "proc_entry"
    | Return -> "return"
    | Exit -> "exit"
end

module Edge = struct
  type block = (Var.t, BasilExpr.t) Block.t [@@deriving eq, ord]
  type t = Block of block | Jump [@@deriving eq, ord]

  let show = function Block b -> Block.to_string b | Jump -> "goto"
  let to_string = function Block b -> Block.to_string b | Jump -> "goto"
  let default = Jump
end

module Loc = Int

(** A procedure's graph is made up of "positions" as nodes ({!Vert.t}) and edges
    between positions are basic blocks or jumps ({!Edge.t}). *)
module G = struct
  include Graph.Persistent.Digraph.ConcreteBidirectionalLabeled (Vert) (Edge)
end

module RevG = struct
  open G

  type t = G.t

  module E = struct
    include G.E

    let src = G.E.dst
    let dst = G.E.src
  end

  module V = G.V

  let iter_succ = G.iter_pred
  let iter_vertex = G.iter_vertex
  let fold_pred_e = G.fold_succ_e
end

module WTO = Graph.WeakTopological.Make (G)
module RevWTO = Graph.WeakTopological.Make (RevG)

type ('v, 'e) proc_spec = {
  requires : 'e list;
  ensures : 'e list;
  rely : 'e list;
  guarantee : 'e list;
  captures_globs : 'v list;
  modifies_globs : 'v list;
}

module PG : sig
  type ('v, 'e) t
  (** type of procedures *)

  val compare : ('a, 'b) t -> ('c, 'd) t -> int
  (** compare procedure names only *)

  val equal : ('a, 'b) t -> ('c, 'd) t -> bool
  (** compare procedure names only *)

  val id : ('a, 'b) t -> ID.t
  (** Get procedure ID *)

  val map_graph : (G.t -> G.t) -> ('a, 'b) t -> ('a, 'b) t
  (** modify graph *)

  val set_graph : G.t -> ('a, 'b) t -> ('a, 'b) t
  (** set graph *)

  val graph : ('a, 'b) t -> G.t option
  (** return graph of procedure *)

  val make_stub : ('a, 'b) t -> ('a, 'b) t
  (** delete implementation (CF Graph) of procedure to make it an external/stub
      repr *)

  val add_empty_impl : ('a, 'b) t -> ('a, 'b) t
  (** create default implementation implementation (CF Graph) for procedure *)

  val create :
    ID.t ->
    ?is_stub:bool ->
    ?formal_in_params:'a StringMap.t ->
    ?formal_out_params:'a StringMap.t ->
    ?captures_globs:'a list ->
    ?modifies_globs:'a list ->
    ?requires:'b list ->
    ?ensures:'b list ->
    ?rely:'b list ->
    ?guarantee:'b list ->
    ?attrib:Attrib.attrib_map ->
    unit ->
    ('a, 'b) t

  val attrib : ('a, 'b) t -> Attrib.attrib_map
  val set_attrib : ('a, 'b) t -> Attrib.t -> string -> ('a, 'b) t
  val set_attribs : ('a, 'b) t -> Attrib.attrib_map -> ('a, 'b) t

  val set_specification : ('a, 'b) t -> ('a, 'c) proc_spec -> ('a, 'c) t
  (** set the procedure's specification/contract *)

  val specification : ('a, 'b) t -> ('a, 'b) proc_spec
  (** return the procedure's specification/contract if defined *)

  val block_ids : ('a, 'b) t -> ID.generator
  (** return mutable generator for fresh block IDS *)

  val local_ids : ('a, 'b) t -> ID.generator
  (** return mutable generator for fresh local variable IDS *)

  val local_decls : ('a, 'b) t -> 'a Var.Decls.t
  (** return mutable declaration map for local var IDS *)

  val formal_in_params : ('a, 'b) t -> 'a StringMap.t
  (** return formal in parameters *)

  val formal_out_params : ('a, 'b) t -> 'a StringMap.t
  (** return formal out parameters *)

  val set_formal_in_params : 'a StringMap.t -> ('a, 'b) t -> ('a, 'b) t
  (** set the formal in parameters *)

  val set_formal_out_params : 'a StringMap.t -> ('a, 'b) t -> ('a, 'b) t
  (** set the formal out parameters *)

  val map_formal_in_params :
    ('a StringMap.t -> 'a StringMap.t) -> ('a, 'b) t -> ('a, 'b) t
  (** modify formal in parameters *)

  val map_formal_out_params :
    ('a StringMap.t -> 'a StringMap.t) -> ('a, 'b) t -> ('a, 'b) t
  (** modify formal out parameters *)

  val topo_fwd : ('a, 'b) t -> Vert.t Graph.WeakTopological.t
  (** return SCCs in forwards weak topological order from entry *)

  val topo_rev : ('a, 'b) t -> Vert.t Graph.WeakTopological.t
  (** return SCCs in reverse weak topological order from return *)
end = struct
  type ('v, 'e) t = {
    id : ID.t;
    formal_in_params : 'v StringMap.t;
    formal_out_params : 'v StringMap.t;
    graph : G.t option;
    locals : 'v Var.Decls.t;
    topo_fwd : Vert.t Graph.WeakTopological.t lazy_t;
    topo_rev : Vert.t Graph.WeakTopological.t lazy_t;
    local_ids : ID.generator;
    block_ids : ID.generator;
    specification : ('v, 'e) proc_spec;
    attrib : Attrib.attrib_map;
  }

  let attrib p = p.attrib
  let set_attrib p k v = { p with attrib = StringMap.add v k p.attrib }
  let set_attribs p attrib = { p with attrib }
  let set_specification p specification = { p with specification }
  let specification p = p.specification
  let id p = p.id
  let graph p = p.graph
  let block_ids p = p.block_ids
  let local_ids p = p.local_ids
  let local_decls p = p.locals
  let formal_in_params p = p.formal_in_params
  let formal_out_params p = p.formal_out_params
  let topo_fwd p = Lazy.force p.topo_fwd
  let topo_rev p = Lazy.force p.topo_rev
  let compare a b = ID.compare (id a) (id b)
  let equal a b = ID.equal (id a) (id b)

  let map_graph f p =
    let np =
      Option.map
        (fun g ->
          let graph = f g in
          {
            p with
            graph = Some graph;
            topo_fwd = lazy (WTO.recursive_scc graph Entry);
            topo_rev = lazy (RevWTO.recursive_scc graph Return);
          })
        p.graph
    in
    Option.get_or ~default:p np

  let set_graph g p = map_graph (fun _ -> g) p

  let map_formal_in_params f p =
    { p with formal_in_params = f p.formal_in_params }

  let map_formal_out_params f p =
    { p with formal_out_params = f p.formal_out_params }

  let set_formal_in_params f p = map_formal_in_params (fun _ -> f) p
  let set_formal_out_params f p = map_formal_in_params (fun _ -> f) p

  let empty_graph =
    let graph = G.empty in
    let graph = G.add_vertex graph Entry in
    let graph = G.add_vertex graph Exit in
    let graph = G.add_vertex graph Return in
    graph

  let create id ?(is_stub = false) ?(formal_in_params = StringMap.empty)
      ?(formal_out_params = StringMap.empty) ?(captures_globs = [])
      ?(modifies_globs = []) ?(requires = []) ?(ensures = []) ?(rely = [])
      ?(guarantee = []) ?(attrib = Attrib.empty) () =
    let specification =
      { captures_globs; modifies_globs; requires; ensures; rely; guarantee }
    in
    let local_ids = ID.make_gen () in
    let block_ids = ID.make_gen () in
    StringMap.iter (fun k v -> ignore @@ local_ids.decl_exn k) formal_in_params;
    StringMap.iter (fun k v -> ignore @@ local_ids.decl_exn k) formal_out_params;
    let locals = Var.Decls.empty () in
    Var.Decls.add_iter locals
      (Iter.append
         (StringMap.to_iter formal_in_params)
         (StringMap.to_iter formal_out_params));

    let graph = if is_stub then None else Some empty_graph in
    {
      id;
      attrib;
      formal_in_params;
      formal_out_params;
      graph;
      locals;
      local_ids;
      block_ids;
      specification;
      topo_fwd =
        lazy
          (WTO.recursive_scc
             (Option.get_exn_or "no graph to iterate" graph)
             Entry);
      topo_rev =
        lazy
          (RevWTO.recursive_scc
             (Option.get_exn_or "no graph to iterate" graph)
             Return);
    }

  let make_stub p =
    {
      p with
      graph = None;
      topo_fwd = lazy (WTO.recursive_scc G.empty Entry);
      topo_rev = lazy (RevWTO.recursive_scc G.empty Return);
    }

  let add_empty_impl p =
    let graph = empty_graph in
    {
      p with
      graph = Some graph;
      topo_fwd = lazy (WTO.recursive_scc graph Entry);
      topo_rev = lazy (RevWTO.recursive_scc graph Return);
    }
end

include PG

let add_goto p ~(from : ID.t) ~(targets : ID.t list) =
  let open Vert in
  p
  |> map_graph (fun g ->
      let fr = End from in
      List.fold_left (fun g t -> G.add_edge g fr (Begin t)) g targets)

let remove_block p id =
  map_graph
    (fun g ->
      let g = G.remove_vertex g (End id) in
      G.remove_vertex g (Begin id))
    p

let add_block_graph ?(attrib = Attrib.empty) graph id ?(phis = [])
    ~(stmts : ('var, 'var, 'expr) Stmt.t list) ?(successors = []) () =
  let stmts = Vector.of_list stmts in
  let b = Edge.(Block { phis; stmts; attrib }) in
  let open Vert in
  let existing = G.find_all_edges graph (Begin id) (End id) in
  let graph = List.fold_left G.remove_edge_e graph existing in
  let graph = G.add_edge_e graph (Begin id, b, End id) in
  let graph =
    List.fold_left
      (fun graph i -> G.add_edge graph (End id) (Begin i))
      graph successors
  in
  graph

let add_block p id ?(attrib = Attrib.empty) ?(phis = [])
    ~(stmts : ('var, 'var, 'expr) Stmt.t list) ?(successors = []) () =
  assert (Option.is_some (graph p));
  map_graph
    (fun graph -> add_block_graph graph id ~attrib ~phis ~stmts ~successors ())
    p

let fresh_block_graph p graph ?name ?(phis = [])
    ~(stmts : ('var, 'var, 'expr) Stmt.t list) ?(successors = []) () =
  let open Block in
  let name = Option.get_or ~default:"%block" name in
  let id = (block_ids p).fresh ~name () in
  (add_block_graph graph id ~phis ~stmts ~successors (), id)

let fresh_block p ?attrib ?name ?(phis = [])
    ~(stmts : ('var, 'var, 'expr) Stmt.t list) ?(successors = []) () =
  let open Block in
  let name = Option.get_or ~default:"%block" name in
  let id = (block_ids p).fresh ~name () in
  (add_block ?attrib p id ~phis ~stmts ~successors (), id)

let get_blocks_pred p vert =
  try
    graph p |> Option.to_list
    |> List.flat_map (fun g ->
        G.pred g vert
        |> List.filter_map (function Vert.End id -> Some id | _ -> None))
  with Not_found -> []

let get_blocks_succ p vert =
  try
    graph p |> Option.to_list
    |> List.flat_map (fun g ->
        G.succ g vert
        |> List.filter_map (function Vert.Begin id -> Some id | _ -> None))
  with Not_found -> []

let get_entry_block p =
  let id = get_blocks_succ p Entry in
  List.head_opt id

let is_entry_block p id =
  graph p
  |> Option.map (fun g ->
      G.pred g (Vert.Begin id) |> List.mem ~eq:Vert.equal Vert.Entry)
  |> Option.get_or ~default:false

let set_entry_block p id =
  let open Edge in
  let open G in
  p
  |> map_graph (fun g ->
      let g = fold_succ (fun v g -> remove_edge g Entry v) g Entry g in
      add_edge g Entry (Begin id))

(** Get the block for an id

    raise Not_found when the block does not exist. *)
let find_block p id =
  let open Edge in
  let open G in
  let g = graph p |> function Some e -> e | _ -> raise Not_found in
  let _, e, _ = G.find_edge g (Begin id) (End id) in
  match e with Block b -> b | Jump -> raise Not_found

let get_block p id =
  let open Edge in
  let open G in
  try Some (find_block p id) with Not_found -> None

let decl_block_exn p name ?(phis = [])
    ~(stmts : ('var, 'var, 'expr) Stmt.t list) ?(attrib = Attrib.empty)
    ?(successors = []) () =
  let open Block in
  let id = (block_ids p).decl_or_get name in
  assert (Option.is_none (get_block p id));
  let p = add_block p id ~phis ~stmts ~successors ~attrib () in
  (p, id)

let modify_block p id (f : _ Block.t -> _ Block.t) =
  let open Edge in
  let open G in
  let block = f (find_block p id) in
  p
  |> map_graph (fun g ->
      let g = G.remove_edge g (Begin id) (End id) in
      let g = G.add_edge_e g (Begin id, Block block, End id) in
      g)

(** Like {!modify_block}, but the parameters are named so you can specify them
    with labels and pipe in the procedure. *)
let modify_block' p ~id ~f = modify_block p id f

let update_block p id (block : (Var.t, BasilExpr.t) Block.t) =
  modify_block p id (fun _ -> block)

let modify_succs p id ~remove ~add =
  let open Edge in
  let open G in
  p
  |> map_graph (fun g ->
      let g =
        G.succ_e g (End id)
        |> List.filter
             ( G.E.dst %> function
               | Begin e -> List.exists (ID.equal e) remove
               | _ -> false )
        |> List.fold_left G.remove_edge_e g
      in
      let new_succs = List.map (fun s -> Vert.(End id, Jump, Begin s)) add in
      List.fold_left G.add_edge_e g new_succs)

let replace_block_succs p id succs =
  let open Edge in
  let open G in
  p
  |> map_graph (fun g ->
      let g = G.succ_e g (End id) |> List.fold_left G.remove_edge_e g in
      let new_succs = List.map (fun s -> Vert.(End id, Jump, Begin s)) succs in
      List.fold_left G.add_edge_e g new_succs)

let replace_edge p id (block : (Var.t, BasilExpr.t) Block.t) =
  update_block p id block

(** Transfers the outgoing edges of the block ID [from] to instead originate
    from the block ID [to_].

    Returns the modified procedure where [from] now has no successors and [to_]
    [to_] is modified to additionally have the original outgoing edges of
    [from_].

    This includes any edges to [Return] nodes, if they exist on [from_].

    TODO: how does this interact with phi nodes?? probably impossible to handle.
*)
let transplant_outgoing_edges p ~from ~to_ : _ t =
  let replace_outgoing_uses ~from ~to_ g =
    G.fold_succ_e
      (function
        | (_, e, tgt) as edge ->
            Fun.flip G.remove_edge_e edge %> Fun.flip G.add_edge_e (to_, e, tgt))
      g from g
  in
  p |> map_graph (replace_outgoing_uses ~from:(End from) ~to_:(End to_))

(** Like {!transplant_outgoing_edges}, but for incoming edges. *)
let transplant_incoming_edges p ~from ~to_ : _ t =
  let replace_incoming_uses ~from ~to_ g =
    G.fold_pred_e
      (function
        | (src, e, _) as edge ->
            Fun.flip G.remove_edge_e edge %> Fun.flip G.add_edge_e (src, e, to_))
      g from g
  in
  p |> map_graph (replace_incoming_uses ~from:(Begin from) ~to_:(Begin to_))

(** Replaces uses of the old block ID with the new [(first, last)] block IDs.
    The incoming edges to [old] will be redirected to [first] and the outgoing
    edges of [old] will be rebased to originate from [last].

    [first] and [last] may be the same. One or both of [first]/[last] may be the
    same as [old]. If neither is the same as [old], [old] will be removed from
    the procedure. *)
let replace_block ~old ~new_:(new_first, new_last) proc =
  proc
  |> transplant_incoming_edges ~from:old ~to_:new_first
  |> transplant_outgoing_edges ~from:old ~to_:new_last
  |>
  if ID.equal old new_first || ID.equal old new_last then Fun.id
  else Fun.flip remove_block old

let lookup_local_decl p v =
  Var.Decls.find_opt (local_decls p) v
  |> Option.or_lazy ~else_:(fun () ->
      StringMap.find_opt v (formal_out_params p))
  |> Option.or_lazy ~else_:(fun () -> StringMap.find_opt v (formal_in_params p))

let decl_local p v =
  let _ = (local_ids p).decl_or_get (Var.name v) in
  Var.Decls.replace (local_decls p) (Var.name v) v;
  v

let fresh_var p ?(pure = false) ?name typ : Var.t =
  let name = Option.map (String.drop_while (Char.equal '$')) name in
  let name = Option.get_or ~default:"v" name in
  let n = ID.name @@ (local_ids p).fresh ~name () in
  let scope = if pure then Var.LocalConst else LocalVar in
  let v = Var.create n typ ~scope in
  Var.Decls.replace (local_decls p) (Var.name v) v;
  v

let blocks_to_list p =
  let collect_edge edge acc =
    let id = G.V.label (G.E.src edge) in
    let edge = G.E.label edge in
    match edge with Edge.(Block b) -> (id, b) :: acc | _ -> acc
  in
  graph p
  |> Option.map (fun g -> G.fold_edges_e collect_edge g [])
  |> Option.get_or ~default:[]

let iter_blocks p =
  let iter visit =
    let collect_edge edge =
      let id = G.V.label (G.E.src edge) in
      let edge = G.E.label edge in
      match (id, edge) with
      | Vert.(Begin id), Edge.(Block b) -> visit (id, b)
      | _ -> ()
    in
    graph p |> Option.iter (fun g -> G.iter_edges_e collect_edge g)
  in
  Iter.from_iter (fun f -> iter f)

(** Fold over blocks in forwards weak topological order (boundocle). The order
    is *not* stable *)
let fold_blocks_topo_fwd_headers
    (f : 'a -> [ `Vert | `Header ] -> ID.t -> Edge.block -> 'a) init p =
  let open Graph.WeakTopological in
  let f acc v e =
    match e with
    | Vert.Begin id ->
        Option.map (f acc v id) (get_block p id) |> Option.get_or ~default:acc
    | _ -> acc
  in
  let rec ff acc e =
    match e with
    | Vertex a -> f acc `Vert a
    | Component (a, e) ->
        let acc = f acc `Header a in
        Graph.WeakTopological.fold_left ff acc e
  in
  if graph p |> Option.is_some then
    let topo = topo_fwd p in
    Graph.WeakTopological.fold_left ff init topo
  else init

(** Fold over blocks in forwards weak topological order (boundocle). The order
    is *not* stable *)
let fold_blocks_topo_fwd (f : 'a -> ID.t -> Edge.block -> 'a) init p =
  fold_blocks_topo_fwd_headers (fun acc i -> f acc) init p

(** Fold over blocks in reverse weak topological order (boundocle). The order is
    *not* stable *)
let fold_blocks_topo_rev_headers
    (f : 'a -> [ `Vert | `Header ] -> ID.t -> Edge.block -> 'a) init p =
  let open Graph.WeakTopological in
  let f acc h e =
    match e with
    | Vert.Begin id ->
        Option.map (f acc h id) (get_block p id) |> Option.get_or ~default:acc
    | _ -> acc
  in
  let rec ff acc e =
    match e with
    | Vertex a -> f acc `Vert a
    | Component (a, e) ->
        let acc = Graph.WeakTopological.fold_left ff acc e in
        f acc `Header a
  in
  if graph p |> Option.is_some then
    let topo = topo_rev p in
    Graph.WeakTopological.fold_left ff init topo
  else init

(** Fold over blocks in forwards weak topological order (boundocle). The order
    is *not* stable *)
let fold_blocks_topo_rev (f : 'a -> ID.t -> Edge.block -> 'a) init p =
  fold_blocks_topo_rev_headers (fun acc i -> f acc) init p

let map_blocks_nondet f p =
  iter_blocks p
  |> Iter.fold
       (fun (p : ('a, 'b) t) (id, b) ->
         let updated = f (id, b) in
         if not @@ Equal.physical updated b then update_block p id updated
         else p)
       p

let map_blocks_topo_fwd f p =
  fold_blocks_topo_fwd
    (fun p id b ->
      let updated = f id b in
      if not @@ Equal.physical updated b then update_block p id updated else p)
    p p

let blocks_succ p i =
  Option.to_iter (graph p)
  |> Iter.flat_map (fun graph ->
      Iter.from_iter (fun f -> G.iter_succ f graph (End i))
      |> Iter.flat_map (function
        | Vert.Begin i ->
            Iter.singleton
              (i, get_block p i |> Option.get_exn_or "bad cfg sturcture")
        | Return -> Iter.empty
        | Exit -> Iter.empty
        | v -> failwith @@ "bad graph structure " ^ Vert.show v))

let blocks_pred p i =
  Option.to_iter (graph p)
  |> Iter.flat_map (fun graph ->
      Iter.from_iter (fun f -> G.iter_pred f graph (Begin i))
      |> Iter.flat_map (function
        | Vert.End i ->
            Iter.singleton
              (i, get_block p i |> Option.get_exn_or "bad cfg sturcture")
        | Entry -> Iter.empty
        | v -> failwith @@ "bad graph structure  " ^ Vert.show v))

let iter_blocks_topo_fwd p =
  Iter.from_iter (fun f -> fold_blocks_topo_fwd (fun acc a b -> f (a, b)) () p)

let iter_blocks_topo_fwd_headers p =
  Iter.from_iter (fun f ->
      fold_blocks_topo_fwd_headers (fun acc h a b -> f (a, h, b)) () p)

let iter_blocks_topo_rev_headers p =
  Iter.from_iter (fun f ->
      fold_blocks_topo_rev_headers (fun acc h a b -> f (a, h, b)) () p)

let iter_stmt_topo_fwd p =
  iter_blocks_topo_fwd p |> Iter.flat_map (fun (id, b) -> Block.stmts_iter b)

let iter_blocks_topo_rev p =
  Iter.from_iter (fun f -> fold_blocks_topo_rev (fun acc a b -> f (a, b)) () p)

let flat_map_stmts_topo_fwd rewriter p =
  let blocks = iter_blocks_topo_fwd p in
  Iter.fold
    (fun p -> function
      | bid, (b : (Var.t, Expr.BasilExpr.t) Block.t) ->
          update_block p bid (Block.flat_map ~rev:false ~phi:Fun.id rewriter b))
    p blocks

let flat_map_stmts_topo_rev rewriter p =
  let blocks = iter_blocks_topo_rev p in
  Iter.fold
    (fun p -> function
      | bid, (b : (Var.t, Expr.BasilExpr.t) Block.t) ->
          update_block p bid (Block.flat_map ~rev:true ~phi:Fun.id rewriter b))
    p blocks

type ('v, 'e) mapped_stmt =
  [ `Stmts of (Var.t, Var.t, BasilExpr.t) Stmt.t list
    (** Zero or more straight-line statements. *)
  | `Blocks of (Var.t, BasilExpr.t) Block.t list
    (** Zero or more straight-line blocks. *)
  | `Graph of ID.t * ID.t * ('v, 'e) t
    (** Multi-block subgraph. [`Graph (begin, end, proc)] represents
        control-flow entering at [begin] and exiting at the [end], and with any
        control-flow between them.

        [proc] is the procedure modified to include fresh blocks [first] and
        [end], as well as any other blocks or control-flow edges {i between}
        them. [proc] should be unchanged aside from the addition of fresh blocks
        and control-flow between them. [begin] should have no predcessors, and
        dominate all new blocks, including [end]. [end] should have no
        successors.

        [begin] and [end] may be the same block. *) ]
(** Program fragment to replace a statement during {!cfg_concatmap_block}:
    either a list of sequential statements, list of sequential blocks, {i or} a
    the procedure including an additional cfg fragment bounded by fresh entry
    and exit block ids. *)

(** [cfg_concatmap_block ~f bid proc] takes a function [f] from statement to a
    code fragment, and replaces block [bid] in [proc] with the concatenated
    result of mapping its statements through through [f]. [f] may return either
    a statement list, block list, or [proc] modified to include a new CFG
    fragment bounded by a begining or end block. See {!type-mapped_stmt} for
    details about [f]'s return type.

    {b Returns} [(first, last, proc)] where [proc] is the updated procedure and
    [first] / [last] is the first / last block of the concatenated output
    program. *)
let cfg_concatmap_block ~(f : proc:_ t -> _ Stmt.t -> _ mapped_stmt) base_bid
    proc =
  let existing_bids = lazy (IDSet.of_iter (Iter.map fst (iter_blocks proc))) in
  let is_fresh = fun bid -> not (IDSet.mem bid (Lazy.force existing_bids)) in

  (* Applies the [f] function while recording the current block ID for
     [`Stmts] insertion, if available.

     Also normalises the output into either:
     - an iter of already-inserted [(first,last)] bookend IDs, or
     - a [(bid, stmts)] which will be inserted later into the specified [bid]. *)
  let apply_f ~proc (cur_stmts_bid : ID.t option) stmt :
      (_ t * ID.t option)
      * ((ID.t * ID.t) Iter.t, ID.t * _ Stmt.t Iter.t) Either.t =
    match f ~proc stmt with
    | `Blocks [] | `Stmts [] -> ((proc, cur_stmts_bid), Left Iter.empty)
    | `Blocks bs ->
        let[@warning "+missing-record-field-pattern"] proc, bids =
          List.fold_map
            (fun proc { Block.attrib; stmts; phis } ->
              fresh_block proc ~attrib ~phis ~stmts:(CCVector.to_list stmts) ())
            proc bs
        in
        ((proc, None), Left (Iter.map Pair.dup (Iter.of_list bids)))
    | `Graph (first, last, proc) ->
        if is_fresh first && is_fresh last then
          ((proc, None), Left (Iter.singleton (first, last)))
        else failwith "cfg_concatmap_block: `Graph blocks should be fresh"
    | `Stmts stmts ->
        let proc, bid =
          match cur_stmts_bid with
          | None -> fresh_block proc ~name:(ID.name base_bid) ~stmts:[] ()
          | Some bid -> (proc, bid)
        in
        ((proc, Some bid), Right (bid, Iter.of_list stmts))
  in

  (* Map, while generating block names for bare statements returned by the mapping function. *)
  let (proc, _), mapped =
    find_block proc base_bid |> Block.stmts_iter |> Iter.to_list
    |> List.fold_map (fun (proc, b) -> apply_f ~proc b) (proc, Some base_bid)
  in
  (* Collects adjacent bare statements into a basic block, and inserts those statements. *)
  let proc = modify_block proc base_bid Block.clear_stmts in
  let proc, block_id_pairs =
    Extras.group_succ_either mapped
    |> List.fold_flat_map
         (fun proc -> function
           | Either.Left (hd, tl) -> (proc, Iter.(to_list (append_l (hd :: tl))))
           | Either.Right ((bid, hd), rest) ->
               let stmts =
                 Iter.append hd (Iter.flat_map snd (Iter.of_list rest))
                 |> CCVector.of_iter |> CCVector.freeze
               in
               ( modify_block proc bid (fun b -> { b with stmts }),
                 [ (bid, bid) ] ))
         proc
  in
  (* Transplant predecessors and successors of the original block as needed. *)
  let first, last =
    ( List.head_opt block_id_pairs |> Option.map_or fst ~default:base_bid,
      List.last_opt block_id_pairs |> Option.map_or snd ~default:base_bid )
  in
  let proc =
    proc
    |> transplant_outgoing_edges ~from:base_bid ~to_:last
    |>
    if not ID.(equal first base_bid) then
      add_goto ~from:base_bid ~targets:[ first ]
    else Fun.id
  in
  (* Insert gotos between mapped blocks. This must happen after transplanting
     so we do not transplant these edges. *)
  let proc =
    List.combine_gen block_id_pairs (List.drop 1 block_id_pairs)
    |> Iter.of_gen
    |> Iter.fold
         (fun proc ((_, prev), (next, _)) ->
           add_goto proc ~from:prev ~targets:[ next ])
         proc
  in
  (first, last, proc)

let pretty_spec show_var show_expr (p : ('a, 'b) proc_spec) =
  let open Containers_pp in
  let ml f v = if List.is_empty v then [] else [ f v ] in
  nest 2
    (newline
    ^ append_nl
        (ml
           (fun x ->
             text "modifies "
             ^ nest 2 (fill_map (text "," ^ newline) show_var x))
           p.modifies_globs
        @ ml
            (fun x ->
              text "captures "
              ^ nest 2 (fill_map (text "," ^ newline) show_var x))
            p.captures_globs
        @ ml
            (fun x ->
              append_l ~sep:newline
                (List.map (fun v -> text "requires " ^ show_expr v) x))
            p.requires
        @ ml
            (fun x ->
              append_l ~sep:newline
                (List.map (fun v -> text "ensures " ^ show_expr v) x))
            p.ensures
        @ ml
            (fun x ->
              append_l ~sep:newline
                (List.map (fun v -> text "rely " ^ show_expr v) x))
            p.rely
        @ ml
            (fun x ->
              append_l ~sep:newline
                (List.map (fun v -> text "guarantee " ^ show_expr v) x))
            p.guarantee))

let pretty show_lvar show_var show_expr p =
  Trace_core.with_span ~__FILE__ ~__LINE__ "pretty-proc" @@ fun _ ->
  let open Containers_pp in
  let open Containers_pp.Infix in
  let params m =
    StringMap.bindings m |> List.map (function i, p -> show_var p) |> fun s ->
    bracket "(" (fill (text "," ^ newline_or_spaces 1) s) ")"
  in
  let header =
    text "proc "
    ^ text (ID.to_string (id p))
    ^ nest 2
        (fill
           (newline ^ text " -> ")
           [ params (formal_in_params p); params (formal_out_params p) ])
    ^ text " "
    ^ Attrib.attrib_pretty (`Assoc (attrib p))
  in
  let return_stmt = text "return" in
  let spec = pretty_spec show_var show_expr (specification p) in
  let pretty_block graph block_id block =
    let succ = G.succ_e graph (Vert.End block_id) in
    let succ =
      match succ with
      | [] -> [ text "unreachable" ]
      | [ (b, re, Return) ] -> (
          match re with
          | Block { stmts } ->
              let stmts =
                Vector.map
                  (fun s ->
                    Stmt.pretty show_lvar show_var show_expr s ^ text ";")
                  stmts
                |> Vector.to_list
              in
              stmts @ [ return_stmt ]
          | Jump -> [ return_stmt ])
      | succ ->
          let succ =
            List.map
              (fun (b, label, e) ->
                match G.V.label e with
                | Begin i -> text @@ ID.to_string i
                | o ->
                    failwith
                      (String.concat " "
                         [
                           "bad graph structure: goto targets non-block ";
                           Vert.show o;
                         ]))
              succ
          in
          [ text "goto " ^ (fun s -> bracket "(" (fill (text ",") s) ")") succ ]
    in
    Block.pretty show_lvar show_var show_expr ~block_id ~terminator:succ block
  in
  let module Dom = Graph.Dominator.Make (G) in
  let blocks =
    match graph p with
    | Some g ->
        let idom = Dom.compute_idom g Entry in
        let dom_tree = Dom.idom_to_dom_tree g idom in
        let cmp v =
          CCOrd.map (fun succ -> (G.mem_edge g v succ, succ))
          @@ CCOrd.(pair (opp bool) Vert.compare)
        in
        let sorted_dom_tree v = dom_tree v |> List.sort (cmp v) in
        let rec preorder f v =
          f v;
          sorted_dom_tree v |> List.iter (preorder f)
        in
        Iter.from_iter (fun f -> preorder f Entry)
        |> Iter.filter_map (function Vert.Begin id -> Some id | _ -> None)
        |> Iter.map (fun id ->
            (id, get_block p id |> Option.get_exn_or "bad graph"))
        |> Iter.map (fun (id, block) -> pretty_block g id block)
        |> Iter.to_list
        |> fun blocks ->
        newline
        ^ surround (text "[")
            (nest 2 @@ newline ^ append_l ~sep:(text ";" ^ newline) blocks)
            (newline ^ text "]")
    | None -> nil
  in
  header ^ spec ^ newline ^ blocks

(** A simplified graph of block level control flow *)
module BlockGraph = struct
  module Vert = struct
    type t = Block of ID.t | Entry | Return | Exit
    [@@deriving show { with_path = false }, eq, ord]

    let hash = Hashtbl.hash
  end

  module G = Graph.Persistent.Digraph.ConcreteBidirectional (Vert)

  let of_proc p =
    graph p
    |> Option.map (fun _ ->
        let g = G.empty in
        let g =
          iter_blocks p
          |> Iter.flat_map (fun (i, _) ->
              blocks_succ p i |> Iter.map fst |> Iter.map (fun s -> (i, s)))
          |> Iter.fold (fun g (p, s) -> G.add_edge g (Block p) (Block s)) g
        in
        let entr = get_blocks_succ p Entry in
        let ex = get_blocks_pred p Exit in
        let retb = get_blocks_pred p Return in
        let g = List.fold_left (fun g p -> G.add_edge g (Block p) Exit) g ex in
        let g =
          List.fold_left (fun g p -> G.add_edge g (Block p) Return) g retb
        in
        let g =
          List.fold_left (fun g p -> G.add_edge g Entry (Block p)) g entr
        in
        g)
end

(** Iterator of variables mentioned in specification,
    {b may repeat equal varibales}. *)
let free_vars_specification spec =
  let open Iter in
  append_l
    [
      of_list spec.modifies_globs;
      of_list spec.captures_globs;
      of_list spec.requires |> flat_map Expr.BasilExpr.free_vars_iter;
      of_list spec.ensures |> flat_map Expr.BasilExpr.free_vars_iter;
      of_list spec.rely |> flat_map Expr.BasilExpr.free_vars_iter;
      of_list spec.guarantee |> flat_map Expr.BasilExpr.free_vars_iter;
    ]
