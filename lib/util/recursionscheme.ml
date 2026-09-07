open Containers

module type Fix = sig
  type 'e expr
  type t

  val fix : t expr -> t
  val unfix : t -> t expr
  val map_expr : ('b -> 'a) -> 'b expr -> 'a expr
end

module type Recurseable = sig
  module O : Fix

  type 'a alg = 'a O.expr -> 'a
  type 'a coalg = 'a -> 'a O.expr

  (** {1 Recursion schemes}

      Recursion schemes abstract recursion for open-recursive types. This
      enables us to write a function (an [alg]) which only describes how to
      process one level of the type, without also describing the recursion to
      its children.

      Closed recursive types immediately fix the recursion, i.e.
      [type a = A of a * a], whereas open recursive types are parametric in the
      fixpoint type: [type 'child a = A of 'child * 'child | B ... ]. For
      example we may define the fixed point: [type t = E of t expr [@@unboxed]].

      The module type {! Fix} defines

      1. the open recursive type ['a expr] 2. the fixed type [t] 3. an
      [map_expr] function on the open recursive type (note we can use
      [@@deriving map] on [expr] to define this) 4. a [fix] and [unfix] type
      which convert between the back and forth from the open and fixed types.

      With this we can define fucntions which fold a function over the type
      ['a expr], and more. Functions for traversing a generic on ['a expr] for a
      given fix point type [Fix.t].

      See:

      {{:https://arxiv.org/pdf/2202.13633v1} Fantastic Morphisms and Where to
       Find Them}

      {{:https://icfp24.sigplan.org/details/ocaml-2024-papers/11/Recursion-schemes-in-OCaml-An-experience-report}
       Recursion Schemes in Ocaml: An Experience Report} *)

  val cata : 'a alg -> O.t -> 'a
  (** Fold an algebra e -> 'a through the expression, from leaves to nodes to
      return 'a. *)

  val ana : 'a coalg -> 'a -> O.t
  (** ana coalg = Out◦ ◦ fmap_expr (ana coalg) ◦ coalg *)

  val map_fold :
    f:('a -> O.t O.expr -> 'a) -> alg:('a -> 'b O.expr -> 'b) -> 'a -> O.t -> 'b
  (** Apply function ~f to the expression first, then pass it to alg. Its result
      is accumulated down the expression tree. *)

  val mutu :
    ?cata:(('a * 'b) alg -> O.t -> 'a * 'b) ->
    (('a * 'b) O.expr -> 'a) ->
    (('a * 'b) O.expr -> 'b) ->
    (O.t -> 'a) * (O.t -> 'b)
  (** mutual recursion: simultaneously evaluate two catamorphisms which can
      depend on each-other's results. *)

  val zygo :
    ?cata:(('a * 'b) alg -> O.t -> 'a * 'b) ->
    'a alg ->
    (('a * 'b) O.expr -> 'b) ->
    O.t ->
    'b
  (** zygomorphism;

      Perform two recursion simultaneously, passing the result of the first to
      the second *)

  val zygo_l :
    ?cata:(('b * 'a) alg -> O.t -> 'b * 'a) ->
    'a alg ->
    (('b * 'a) O.expr -> 'b) ->
    O.t ->
    'b
  (** zygomorphism;

      Perform two recursion simultaneously, passing the result of the second to
      the first *)

  val map_fold2 :
    f:('a -> O.t O.expr -> 'a) ->
    alg1:('a -> ('b * 'c) O.expr -> 'b) ->
    alg2:'c alg ->
    'a ->
    O.t ->
    'b
  (** Apply function ~f to the expression first, then pass it to alg. Its result
      is accumulated down the expression tree. *)

  val para_f : (('a * 'b) O.expr -> 'b) -> (O.t -> 'a) -> O.t -> 'b
  (** catamorphism that also passes the original expression map_exprped through
      a function argument *)

  val para : ((O.t * 'a) O.expr -> 'a) -> O.t -> 'a
  (** catamorphism that passes through original expression *)

  val iter_children : (O.t O.expr -> unit) -> O.t -> unit
  val children_iter : O.t -> O.t O.expr Iter.t
end

module Recursion (O : Fix) = struct
  open Fun.Infix
  open O
  module O = O

  type 'a alg = 'a expr -> 'a
  type 'a coalg = 'a -> 'a expr

  (** {1 Recursion schemes}

      Recursion schemes abstract recursion for open-recursive types. This
      enables us to write a function (an [alg]) which only describes how to
      process one level of the type, without also describing the recursion to
      its children.

      Closed recursive types immediately fix the recursion, i.e.
      [type a = A of a * a], whereas open recursive types are parametric in the
      fixpoint type: [type 'child a = A of 'child * 'child | B ... ]. For
      example we may define the fixed point: [type t = E of t expr [@@unboxed]].

      The module type {! Fix} defines

      1. the open recursive type ['a expr] 2. the fixed type [t] 3. an
      [map_expr] function on the open recursive type (note we can use
      [@@deriving map] on [expr] to define this) 4. a [fix] and [unfix] type
      which convert between the back and forth from the open and fixed types.

      With this we can define fucntions which fold a function over the type
      ['a expr], and more. Functions for traversing a generic on ['a expr] for a
      given fix point type [Fix.t].

      See:

      {{:https://arxiv.org/pdf/2202.13633v1} Fantastic Morphisms and Where to
       Find Them}

      {{:https://icfp24.sigplan.org/details/ocaml-2024-papers/11/Recursion-schemes-in-OCaml-An-experience-report}
       Recursion Schemes in Ocaml: An Experience Report} *)

  (** Fold an algebra e -> 'a through the expression, from leaves to nodes to
      return 'a. *)
  let rec cata (alg : 'a alg) e = (unfix %> map_expr (cata alg) %> alg) e

  (* ana coalg = Out◦ ◦ fmap_expr (ana coalg) ◦ coalg *)
  let rec ana (coalg : 'a coalg) e = (coalg %> map_expr (ana coalg) %> fix) e

  (** Apply function ~f to the expression first, then pass it to alg. Its result
      is accumulated down the expression tree. *)
  let rec map_fold ~(f : 'a -> t expr -> 'a) ~(alg : 'a -> 'b expr -> 'b) r e =
    let r = f r (unfix e) in
    (unfix %> (map_expr (map_fold ~f ~alg r) %> alg r)) e

  let rec rw_recurse_down ~(f : t expr -> t) (e : t) : t =
    let r = unfix @@ f (unfix e) in
    map_expr (rw_recurse_down ~f) r |> fix

  (* hylo
  let rec hylo ~consume_alg ~produce_coalg e =
    consume_alg
    % AbstractExpr.map_expr (hylo ~consume_alg ~produce_coalg)
    % produce_coalg
    @@ e
    *)

  (** mutual recursion: simultaneously evaluate two catamorphisms which can
      depend on each-other's results. *)
  let mutu ?(cata = cata) (alg1 : ('a * 'b) expr -> 'a)
      (alg2 : ('a * 'b) expr -> 'b) =
    let alg x = (alg1 x, alg2 x) in
    (fst % cata alg, snd % cata alg)

  (** zygomorphism;

      Perform two recursion simultaneously, passing the result of the first to
      the second *)
  let zygo ?(cata = cata) (alg1 : 'a alg) (alg2 : ('a * 'b) expr -> 'b) e =
    snd (mutu ~cata (map_expr fst %> alg1) alg2) e

  (** zygo with the order swapped *)
  let zygo_l ?(cata = cata) (alg2 : 'a alg) (alg1 : ('b * 'a) expr -> 'b) =
    fst (mutu ~cata alg1 (map_expr snd %> alg2))

  let map_fold2 ~f ~(alg1 : 'a -> ('b * 'c) expr -> 'b) ~(alg2 : 'c alg) r e =
    let alg r x = (alg1 r x, alg2 (map_expr snd x)) in
    fst (fst % map_fold ~f ~alg r, snd % map_fold ~f ~alg r) e

  (** catamorphism that also passes the original expression with [map_expr] of a
      supplied function applied to it *)
  let rec para_f (alg : ('a * 'b) expr -> 'b) f e =
    let p f g x = (f x, g x) in
    (alg % map_expr (p f (para_f alg f)) % unfix) e

  (** catamorphism that passes through original expression *)
  let para alg e = para_f alg Fun.id e

  (** catamorphism that passes through original expression unfolded twice *)
  let cata_context alg e = para_f alg (unfix %> map_expr unfix) e

  let iter_children (visit : t expr -> unit) e =
    let alg a = map_expr fst a |> visit in
    para alg e

  let children_iter e = Iter.from_iter (fun f -> iter_children f e)
end
