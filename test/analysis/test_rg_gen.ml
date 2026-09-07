open Bincaml_util.Common
open Lang
open Expr
open Analysis.Rg_gen

let conditional_writes_wrapped_intervals_stabilisation_1 () =
  let test =
    "Stabilising x == 0 under x != 1 ==> x' == x should yield x == 0, "
    ^ "using ConditionalWritesDomain(InterferenceWrappedIntervalDomain)."
  in
  let module I = ConditionalWritesDomain (InterferenceWrappedIntervalDomain) in
  (* create wrapped interval value x = [0,0] *)
  let open Analysis.Wrapped_intervals in
  let x = Var.create "x" (Types.Bitvector 32) in
  let zero = Bitvec.zero ~size:32 in
  let x_eq_0 =
    StateAbstraction.update x
      (WrappedIntervalsLattice.interval zero zero)
      StateAbstraction.top
  in
  (* create rely condition x != 1 ==> x' == x with the conditional writes domain, represented as x -> [x = [1,1]] *)
  let one = Bitvec.one ~size:32 in
  let x_eq_1 =
    StateAbstraction.update x
      (WrappedIntervalsLattice.interval one one)
      StateAbstraction.top
  in
  (* to create the rely condition, transition over the precondition-assignment pair: {x == 1} x := 0 *)
  let zero_expr = BasilExpr.bvconst zero in
  let conc_int = I.ConcInt.{ pre = x_eq_1; assignments = [ (x, zero_expr) ] } in
  let interference = I.transitions [ conc_int ] in
  let stabilised = I.stabilise interference x_eq_0 in
  Alcotest.(check bool) test true (StateAbstraction.equal x_eq_0 stabilised)

let conditional_writes_wrapped_intervals_stabilisation_2 () =
  let test =
    "Stabilising x == 1 under x != 1 ==> x' == x should yield top, "
    ^ "using ConditionalWritesDomain(InterferenceWrappedIntervalDomain)."
  in
  let module I = ConditionalWritesDomain (InterferenceWrappedIntervalDomain) in
  let open Analysis.Wrapped_intervals in
  let x = Var.create "x" (Types.Bitvector 32) in
  (* create rely condition x != 1 ==> x' == x with the conditional writes domain, represented as x -> [x = [1,1]] *)
  let one = Bitvec.one ~size:32 in
  let x_eq_1 =
    StateAbstraction.update x
      (WrappedIntervalsLattice.interval one one)
      StateAbstraction.top
  in
  (* to create the rely condition, transition over the precondition-assignment pair: {x == 1} x := 0 *)
  let zero = Bitvec.zero ~size:32 in
  let zero_expr = BasilExpr.bvconst zero in
  let conc_int = I.ConcInt.{ pre = x_eq_1; assignments = [ (x, zero_expr) ] } in
  let interference = I.transitions [ conc_int ] in
  let stabilised = I.stabilise interference x_eq_1 in
  Alcotest.(check bool)
    test true
    (StateAbstraction.equal StateAbstraction.top stabilised)

let conditional_writes_wrapped_intervals_stabilisation_3 () =
  let test =
    "Stabilising x == 1 under false ==> x' == x should yield top, "
    ^ "using ConditionalWritesDomain(InterferenceWrappedIntervalDomain)."
  in
  let module I = ConditionalWritesDomain (InterferenceWrappedIntervalDomain) in
  let open Analysis.Wrapped_intervals in
  let x = Var.create "x" (Types.Bitvector 32) in
  (* create rely condition false ==> x' == x with the conditional writes domain, represented as x -> top *)
  let one = Bitvec.one ~size:32 in
  let x_eq_1 =
    StateAbstraction.update x
      (WrappedIntervalsLattice.interval one one)
      StateAbstraction.top
  in
  (* to create the rely condition, transition over the precondition-assignment pair: {top} x := 0 *)
  let zero = Bitvec.zero ~size:32 in
  let zero_expr = BasilExpr.bvconst zero in
  let conc_int =
    I.ConcInt.{ pre = StateAbstraction.top; assignments = [ (x, zero_expr) ] }
  in
  let interference = I.transitions [ conc_int ] in
  let stabilised = I.stabilise interference x_eq_1 in
  Alcotest.(check bool)
    test true
    (StateAbstraction.equal StateAbstraction.top stabilised)

let conditional_writes_wrapped_intervals_guarantee_conditions_1 () =
  let test =
    "Basic mutual-exclusion detection using the conditional-writes domain with \
     wrapped intervals."
  in
  let prog_str =
    {|
prog entry @dummy;

memory shared $x: bv32;

proc @dummy () -> ()
[
  block %entry [ goto(%ret); ];
  block %ret [ return (); ]
];

proc @t1 () -> ()
[
  block %entry [
    assume eq($x, 0x1:bv32);
    $x := 0x3:bv32;
    goto(%ret);
  ];
  block %ret [
    return ();
  ]
];

proc @t2 () -> ()
[
  block %entry [
    assume eq($x, 0x2:bv32);
    $x := 0x3:bv32;
    goto(%ret);
  ];
  block %ret [
    return ();
  ]
];
|}
  in
  let ast = Loader.Loadir.ast_of_string prog_str in
  let program = ast.prog in
  let entry_id = Procedure.id @@ Program.entry_proc_exn program in
  let threads =
    Lang.Program.procs program
    (* get a list of all program procedures that are not the entry proc *)
    |> Iter.fold
         (fun acc (id, proc) ->
           if ID.equal id entry_id then acc else proc :: acc)
         []
  in
  let x =
    Program.global_vars program
    |> Iter.find_pred_exn (fun v -> v |> Var.name |> String.equal "$x")
  in
  let x_set = VarSet.singleton x in

  let open Analysis.Wrapped_intervals in
  let module I = ConditionalWritesDomain (InterferenceWrappedIntervalDomain) in
  let module Generator = RelyGuaranteeGenerator (I) in
  let guars = Generator.generate_rg_conditions threads in

  let one = Bitvec.of_int ~size:32 1 in
  let x_eq_1 =
    StateAbstraction.update x
      (WrappedIntervalsLattice.interval one one)
      StateAbstraction.top
  in

  let two = Bitvec.of_int ~size:32 2 in
  let x_eq_2 =
    StateAbstraction.update x
      (WrappedIntervalsLattice.interval two two)
      StateAbstraction.top
  in

  guars
  |> List.iter (fun (proc, guar) ->
      let proc_name = proc |> Procedure.id |> ID.name in
      if String.equal proc_name "@t1" then
        let write_cond = I.VarSetMap.find x_set guar in
        Alcotest.(check bool)
          test true
          (StateAbstraction.equal x_eq_1 write_cond)
      else if String.equal proc_name "@t2" then
        let write_cond = I.VarSetMap.find x_set guar in
        Alcotest.(check bool)
          test true
          (StateAbstraction.equal x_eq_2 write_cond)
      else Alcotest.(check bool) test true (String.equal proc_name "@dummy"))

let conditional_writes_wrapped_intervals_guarantee_conditions_2 () =
  let test =
    "Attempt to fail to infer mutual-exclusion using the conditional-writes \
     domain with wrapped intervals."
  in
  let prog_str =
    {|
prog entry @dummy;

memory shared $x: bv32;

proc @dummy () -> ()
[
  block %entry [ goto(%ret); ];
  block %ret [ return (); ]
];

proc @t1 () -> ()
[
  block %entry [
    assume eq($x, 0x1:bv32);
    $x := 0x3:bv32;
    goto(%ret);
  ];
  block %ret [
    return ();
  ]
];

proc @t2 () -> ()
[
  block %entry [
    assume eq($x, 0x1:bv32);
    $x := 0x3:bv32;
    goto(%ret);
  ];
  block %ret [
    return ();
  ]
];
|}
  in
  let ast = Loader.Loadir.ast_of_string prog_str in
  let program = ast.prog in
  let entry_id = Procedure.id @@ Program.entry_proc_exn program in
  let threads =
    Lang.Program.procs program
    (* get a list of all program procedures that are not the entry proc *)
    |> Iter.fold
         (fun acc (id, proc) ->
           if ID.equal id entry_id then acc else proc :: acc)
         []
  in
  let x =
    Program.global_vars program
    |> Iter.find_pred_exn (fun v -> v |> Var.name |> String.equal "$x")
  in
  let x_set = VarSet.singleton x in

  let open Analysis.Wrapped_intervals in
  let module I = ConditionalWritesDomain (InterferenceWrappedIntervalDomain) in
  let module Generator = RelyGuaranteeGenerator (I) in
  let guars = Generator.generate_rg_conditions threads in

  guars
  |> List.iter (fun (proc, guar) ->
      let proc_name = proc |> Procedure.id |> ID.name in
      if String.equal proc_name "@t1" then
        let write_cond = I.VarSetMap.find x_set guar in
        Alcotest.(check bool)
          test true
          (StateAbstraction.equal StateAbstraction.top write_cond)
      else if String.equal proc_name "@t2" then
        let write_cond = I.VarSetMap.find x_set guar in
        Alcotest.(check bool)
          test true
          (StateAbstraction.equal StateAbstraction.top write_cond)
      else Alcotest.(check bool) test true (String.equal proc_name "@dummy"))

let tests =
  [
    (* ("simple", simple); *)
    ( "conditional_writes_wrapped_intervals_stabilisation_1",
      conditional_writes_wrapped_intervals_stabilisation_1 );
    ( "conditional_writes_wrapped_intervals_stabilisation_2",
      conditional_writes_wrapped_intervals_stabilisation_2 );
    ( "conditional_writes_wrapped_intervals_stabilisation_3",
      conditional_writes_wrapped_intervals_stabilisation_3 );
    ( "conditional_writes_wrapped_intervals_guarantee_conditions_1",
      conditional_writes_wrapped_intervals_guarantee_conditions_1 );
    ( "conditional_writes_wrapped_intervals_guarantee_conditions_2",
      conditional_writes_wrapped_intervals_guarantee_conditions_2 );
  ]
  |> List.map (fun (n, t) -> Alcotest.test_case n `Quick t)
  |> fun cases -> [ ("rg_gen", cases) ]
