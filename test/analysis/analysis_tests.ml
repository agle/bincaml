let () =
  let open Alcotest in
  run "Static Analysis"
    (Test_lattice_collections.tests @ Test_irreducible_loops.tests
   @ Test_wrapped_intervals.tests @ Test_rg_gen.tests @ Test_dsa.tests)
