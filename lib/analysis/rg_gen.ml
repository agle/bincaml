(** Tools for generating rely-guarantee conditions. *)

open Bincaml_util.Common
open Lattice_types
open Lang
open Expr

module Debug = struct
  let enabled = false
  let print s = if enabled then print_endline s
end

module Util = struct
  (** Derives the powerset of a list-represented set, as a list. Assumes list
      elements are unique. *)
  let rec powerset = function
    | [] -> [ [] ]
    | x :: xs ->
        let sets_without_x = powerset xs in
        let sets_with_x = List.map (fun sublst -> x :: sublst) sets_without_x in
        sets_without_x @ sets_with_x

  (** General function for deriving a fixpoint. *)
  let rec fixpoint equal f x =
    let y = f x in
    if equal y x then y else fixpoint equal f y
end

(** An {!InterferenceStateDomain} is a state domain that is compatible with
    rely-guarantee generation. *)
module type InterferenceStateDomain = sig
  include Intra_analysis.IntraDomain
  (** The state domain we extend. In future, we hope to extend this to
      interprocedural domains. *)

  val meet : t -> t -> t
  (** Derives the greatest lower bound of two domain elements. *)

  val havoc : t -> VarSet.t -> t
  (** Abstracts out a set of variables; minimally weakens the domain element
      such that the vars are not constrained. *)

  val filter : t -> BasilExpr.t -> t
  (** Returns an overapproximation (upper bound) on the states reachable after
      applying the given condition. *)
end

(** An extension of the wrapped intervals domain, to work with the
    InterferenceDomain framework. *)
module InterferenceWrappedIntervalDomain = struct
  open Wrapped_intervals
  include Domain

  let meet t1 t2 =
    Debug.print @@ "Taking the meet of " ^ show t1 ^ " and " ^ show t2;
    let result = bot_binop WrappedIntervalsLattice.meet t1 t2 in
    Debug.print @@ "Result " ^ show result ^ "\n";
    result

  let havoc t var_set =
    Debug.print @@ "Havocing "
    ^ VarSet.to_string ~start:"{" ~stop:"}" ~sep:"," Var.show var_set
    ^ " in " ^ show t;
    let result =
      if Domain.contains_bot t then t
      else
        VarSet.fold
          (fun var acc -> update var WrappedIntervalsLattice.top acc)
          var_set t
    in
    Debug.print @@ "Result " ^ show result ^ "\n";
    result

  let filter t exp =
    transfer t
    @@ Stmt.Instr_Assume { attrib = Attrib.empty; body = exp; branch = false }
end

(** The rely-guarantee conditions we generate are always elements of some
    lattice. The signature for this lattice is defined here. We use this simpler
    signature instead of Lattice_types.Lattice because our analysis does not
    require the 'top', 'widening', or 'narrowing' functions to be defined. *)
module type Interference = sig
  val name : string

  include ORD_TYPE
  include PRETTY with type t := t

  val bottom : t
  val join : t -> t -> t
  val equal : t -> t -> bool
  val leq : t -> t -> bool
end

(** A concrete interference w.r.t. some state domain is a precondition
    represented by that domain, and a simultaneous assignment to global
    variables that may be executed under that precondition. *)
module ConcreteInterference (D : InterferenceStateDomain) = struct
  type t = { pre : D.t; assignments : (Var.t * BasilExpr.t) list }
  [@@deriving eq, ord]

  let show t =
    let show_assignment (var, exp) =
      Printf.sprintf "%s := %s" (Var.show var) (BasilExpr.to_string exp)
    in
    let show_assignments =
      List.to_string ~start:"[" ~stop:"]" ~sep:", " show_assignment
    in
    Printf.sprintf "(%s, %s)" (D.show t.pre) (show_assignments t.assignments)
end

(** Interference domains are like abstract domains except that instead of
    abstracting sets of states, they abstract sets of pairs of states
    representing state transitions. In this way, they can be viewed as abstract
    rely-guarantee conditions. Rather than defining a transfer function,
    interference domains define a 'stabilise' function for applying
    interferences to states, as well as a 'transitions' function for deriving
    elements of the interference domain from precondition-assignment pairs. *)
module type InterferenceDomain = sig
  module D : InterferenceStateDomain
  (** The underlying state domain. We use this to generate reachable states,
      from which we generate RG conditions. *)

  module ConcInt : module type of ConcreteInterference (D)
  (** Concrete interferences are precondition-assignment pairs, where the
      precondition is of type [D.t]. *)

  include Interference
  (** Type [t] represents a set of state transitions, and is typically defined
      with respect to [D.t]. *)

  val stabilise : t -> D.t -> D.t
  (** [stabilise i d] returns an abstract state weaker than [d] that captures
      the set of states reachable by executing any number of steps in [i] from
      any state in [d]. *)

  val transitions : ConcInt.t list -> t
  (** [transitions p] takes a list of concrete interferences [p] - which are
      precondition-assignment pairs - and returns an element of the interference
      domain that over-approximates all transitions reachable by executing any
      of those assignments under their associated precondition. *)
end

(** The conditional-writes domain maps each variable to the set of states under
    which it may be written, called its "write-condition". In case the target
    program contains simultaneous assignments, the domain of this map is sets of
    variables, rather than just variables. The map omits variable sets with
    write-conditions equal to bot.

    For two variable sets x and y mapping to write-conditions P and Q, we
    maintain the invariant that (x U y) maps to a write-condition stronger than
    P /\ Q. Thus P and Q are sufficient over-approximations of the states under
    which x and y can be written to respectively, so we avoid having to look
    through the write-conditions of their supersets when determining the
    conditions under which they can change. Note that (x U y) may map to a
    strictly stronger write-condition than P /\ Q, such as in the case when
    either x or y can change individually but never in the same execution trace
    (i.e. "at the same time"). *)
module ConditionalWritesDomain (D : InterferenceStateDomain) = struct
  module VarSetMap = Map.Make (VarSet)
  module D = D
  module ConcInt = ConcreteInterference (D)

  type t = D.t VarSetMap.t

  let name = "ConditionalWritesDomain"

  (** Variables not appearing in the map are implicitly mapped to D.bottom,
      meaning they are never written to. *)
  let bottom = VarSetMap.empty

  (** Joins are defined component-wise over the map entries. *)
  let join = VarSetMap.union (fun _key d1 d2 -> Some (D.join d1 d2))

  let equal = VarSetMap.equal D.equal

  (** This could probably be optimised. *)
  let leq i1 i2 = equal i2 @@ join i1 i2

  (** For example: "(x) -> P, (y) -> Q, (x, y) -> R, ..." *)
  let show i =
    if VarSetMap.is_empty i then Bincaml_util.Unicode.bot_char
    else
      let entry_to_str =
       fun (var_set, d) ->
        let var_set_str =
          VarSet.to_string ~start:"{" ~stop:"}" ~sep:", " Var.to_string var_set
        in
        let d_str = D.show d in
        Printf.sprintf "%s -> %s" var_set_str d_str
      in
      VarSetMap.to_list i
      |> List.to_string ~start:"" ~stop:"" ~sep:", " entry_to_str

  let pretty i = Containers_pp.text (show i)
  let compare = VarSetMap.compare D.compare

  let stabilise i d =
    Debug.print @@ "Stabilising " ^ D.show d ^ " under " ^ show i;
    (* For each entry (var_set, write_cond) in the map, take the meet of d and write_cond to get the states in which
       all variables in var_set may update in one step. From the resulting intersection, havoc var_set to simulate an
       update. Do this for each entry, then join all the results together with d. This gives you a D.t that
       over-approximates the states that are reachable by applying one transition in i to any state in d. *)
    let apply i d =
      VarSetMap.fold
        (fun var_set write_cond ->
          D.join @@ D.havoc (D.meet d write_cond) var_set)
        i d
    in
    (* The above function simulates a single step of i. To stabilise d, we must derive its least fixpoint. *)
    let result = Util.fixpoint D.equal (apply i) d in
    Debug.print @@ "Result: " ^ D.show result;
    result

  let transitions (lst : ConcInt.t list) =
    Debug.print @@ "Deriving transitions from concrete interferences: "
    ^ List.to_string ~sep:", " ConcInt.show lst;
    (* aux derives a guarantee condition from a single (possibly simultaneous) assignment to global vars *)
    let aux pre assignments =
      (* true iff v := e may modify v under pre *)
      let var_modified (v, e) =
        (* FIXME: create fresh var with type equal to v's type *)
        let v' = Var.create "DUMMY" Types.Integer in
        (* wrap in rvar before using in expr, i think *)
        let v_exp = BasilExpr.rvar v in
        let v'_exp = BasilExpr.rvar v' in
        (* apply v' := e to get the value of v after the assignment *)
        let assign_v' =
          D.transfer pre
            (Stmt.Instr_Assign { attrib = Attrib.empty; al = [ (v', e) ] })
        in
        (* create the expression v' != v *)
        let v_not_eq_v' = BasilExpr.binexp ~op:`NEQ v_exp v'_exp in
        (* apply filter v' != v to the state resulting from v' := e *)
        let filtered = D.filter assign_v' v_not_eq_v' in
        (* if the result is bot, then v' == v must always hold after v' := e, meaning v := e doesn't change v *)
        not @@ D.equal filtered D.bottom
      in
      (* get only those assignments that may modify the assigned variable *)
      List.filter var_modified assignments
      (* get just the variables *)
      |> List.map fst
      (* map each subset of the resulting set of variables to 'pre', creating an interference of type t *)
      |> Util.powerset
      |> List.map (fun sublst -> (VarSet.of_list sublst, pre))
      |> VarSetMap.of_list
    in
    (* apply aux to every assignment in the list, and join the results *)
    let result =
      List.fold_left
        (fun acc ConcInt.{ pre; assignments } ->
          join acc @@ aux pre assignments)
        bottom lst
    in
    Debug.print @@ "Derived: " ^ show result ^ "\n";
    result
end

(** We generate rely-guarantee conditions using state domain D and interference
    domain I via the following process: 1. Create a map from each thread to its
    current guarantee condition. At first, all threads map to I.bottom. 2. For
    each thread: 2.a. Derive a rely condition R by taking the join over all
    environment guarantees. 2.b. Do a forward analysis with domain D to
    over-approximate the reachable states, but use I.stabilise to stabilise each
    derived abstract state under R as we go. 2.c. From the analysis results,
    retrieve all concrete interferences. These are precondition-assignment pairs
    where each assignment may simultaneously assign a set of global variables.
    Note that this means ignoring any local variables that may also be updated
    in the assignment. 2.d. From those concrete interferences, use the
    I.transitions function to derive a guarantee condition (as an I.t) that
    over-approximates the set of state transitions that may be induced by their
    execution. 3. Update each thread's guarantee condition in the map to the new
    one derived from step 2. 4. Repeat steps 2-3 until a fixpoint is reached
    over the derived guarantee conditions. 5. The generated guarantee conditions
    are given by the map. The generated rely conditions for each thread are
    given by the join over all environment guarantee conditions.

    The way in which step 2.c is implemented is somewhat tricky. A naive
    solution is to integrate it with step 2.b, and build a list of
    precondition-assignment pairs simultaneously with the derivation of
    reachable states. The issue here is that the same assignment will be added
    multiple times to the list when encountered in a loop, for example. The
    solution to this problem is to use a map from assignments to their
    preconditions, but the IR does not currently distinguish between two
    identical assignments in different locations, so preconditions of identical
    assignments would have to be merged, which results in precision loss when
    deriving guarantees. To uniquely identify an assignment as required by our
    analysis, we can exploit the fact that basic blocks have unique identifiers,
    and no loops. Thus, an assignment can be identified by the order in which it
    is encountered within its unique block. In our implementation, we choose to
    derive the reachable preconditions for all blocks first, and then do one
    more forward pass over each block to derive a list of its
    precondition-assignment pairs (filtering out the local variables from these
    assignments, thus creating pure concrete interferences). However, we could
    have also integrated this with step 2.b by maintaining a map from blocks to
    lists of (filtered) precondition-assignment pairs, and clearing this list
    upon entering a block. The latter is probably faster, but is a tad more
    complex to implement. *)
module RelyGuaranteeGenerator (I : InterferenceDomain) = struct
  module D = I.D
  module ConcInt = I.ConcInt

  (* returns a first-class module which is essentially D but with stabilisation tacked on before each transfer *)
  let stable_d rely : (module Intra_analysis.IntraDomain with type t = D.t) =
    (module struct
      include D

      let name = D.name ^ " Stabilised"

      (** Stabilise the pre-state before transferring. I believe this may be
          soundly modified such that stabilisation only occurs before a global
          read or write. *)
      let transfer t = D.transfer @@ I.stabilise rely t
      (* todo: what about transfer_phi? *)
    end)

  type interference_collection = {
    state : D.t;
    rely : I.t;
    interferences : ConcInt.t list;
  }

  let collect_interferences { state; rely; interferences } stmt =
    let stable_pre = I.stabilise rely state in
    let post = D.transfer stable_pre stmt in
    let new_interferences =
      match stmt with
      | Stmt.Instr_Assign { attrib; al } ->
          let global_assigns =
            List.filter (fun a -> fst a |> Var.is_global) al
          in
          if List.is_empty global_assigns then interferences
          else
            ConcInt.{ pre = stable_pre; assignments = global_assigns }
            :: interferences
      | _ -> interferences
    in
    { state = post; rely; interferences = new_interferences }

  let derive_guar rely proc =
    let (module StableD) = stable_d rely in
    let module Analysis = Intra_analysis.Forwards (StableD) in
    let analysis_results = Analysis.analyse proc in
    let concrete_interferences =
      Analysis.A.M.fold
        (fun vert state acc ->
          match vert with
          | Begin block_id ->
              (* todo: not sure how to handle phi node things - what should transfer_phi be for this pseudo-domain? *)
              let b = Procedure.find_block proc block_id in
              let collection =
                Block.fold_forwards
                  ~phi:(fun a _ -> a)
                  ~f:collect_interferences
                  { state; rely; interferences = [] }
                  b
              in
              collection.interferences @ acc
          | _ -> acc)
        analysis_results []
    in
    I.transitions concrete_interferences

  let derive_rely thread guars =
    List.fold_left
      (fun acc (t, g) ->
        if ID.equal (Procedure.id thread) (Procedure.id t) then acc
        else I.join g acc)
      I.bottom guars

  let generate_rg_conditions threads =
    let initial_guars = List.map (fun thread -> (thread, I.bottom)) threads in
    let rederive_guars guars =
      List.map
        (fun thread ->
          let rely = derive_rely thread guars in
          let guar = derive_guar rely thread in
          Debug.print @@ "Rely for thread "
          ^ (thread |> Procedure.id |> ID.to_string)
          ^ ": " ^ I.show rely;
          Debug.print @@ "Guar for thread "
          ^ (thread |> Procedure.id |> ID.to_string)
          ^ ": " ^ I.show guar ^ "\n";
          (thread, guar))
        threads
    in
    (* note: this equality function assumes that 'rederive_guars' preserves the ordering of threads in its given list *)
    (* this only holds here because 'initial_guars' orders threads identically to the 'threads' formal parameter *)
    Util.fixpoint
      (List.equal (fun (_, g1) (_, g2) -> I.equal g1 g2))
      rederive_guars initial_guars
end
