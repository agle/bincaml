  $ bincaml script branch_conditions.sexp
  (load-il branch_conditions.il)
  (run-transforms aslp-semantics)
  bincaml: [WARNING] Invariants not satisfied during 'aslp-semantics'. Needs [GtirbArm] but only have [].
  (dump-il branch_conditions_pre.il)
  (run-transforms branch-conditions)
  (dump-il branch_conditions_post.il)

  $ diff branch_conditions_pre.il branch_conditions_post.il
  48c48
  <      assume eq($PSTATE_Z, 0x1:bv1);
  ---
  >      assume eq($R3, $R4);
  53c53
  <      assume boolnot(eq($PSTATE_Z, 0x1:bv1));
  ---
  >      assume boolnot(eq($R3, $R4));
  69c69
  <      assume boolnot(eq($PSTATE_Z, 0x1:bv1));
  ---
  >      assume boolnot(eq($R3, $R4));
  74c74
  <      assume boolnot(boolnot(eq($PSTATE_Z, 0x1:bv1)));
  ---
  >      assume eq($R3, $R4);
  90c90
  <      assume eq($PSTATE_C, 0x1:bv1);
  ---
  >      assume bvule($R4, $R3);
  95c95
  <      assume boolnot(eq($PSTATE_C, 0x1:bv1));
  ---
  >      assume bvult($R3, $R4);
  111c111
  <      assume boolnot(eq($PSTATE_C, 0x1:bv1));
  ---
  >      assume bvult($R3, $R4);
  116c116
  <      assume boolnot(boolnot(eq($PSTATE_C, 0x1:bv1)));
  ---
  >      assume bvule($R4, $R3);
  132c132
  <      assume eq($PSTATE_N, 0x1:bv1);
  ---
  >      assume bvslt(bvsub($R3, $R4), 0x0:bv64);
  137c137
  <      assume boolnot(eq($PSTATE_N, 0x1:bv1));
  ---
  >      assume bvsle(0x0:bv64, bvsub($R3, $R4));
  153c153
  <      assume boolnot(eq($PSTATE_N, 0x1:bv1));
  ---
  >      assume bvsle(0x0:bv64, bvsub($R3, $R4));
  158c158
  <      assume boolnot(boolnot(eq($PSTATE_N, 0x1:bv1)));
  ---
  >      assume bvslt(bvsub($R3, $R4), 0x0:bv64);
  216c216
  <      assume booland(eq($PSTATE_C, 0x1:bv1), eq($PSTATE_Z, 0x0:bv1));
  ---
  >      assume bvult($R4, $R3);
  221c221
  <      assume boolnot(booland(eq($PSTATE_C, 0x1:bv1), eq($PSTATE_Z, 0x0:bv1)));
  ---
  >      assume bvule($R3, $R4);
  237c237
  <      assume boolnot(booland(eq($PSTATE_C, 0x1:bv1), eq($PSTATE_Z, 0x0:bv1)));
  ---
  >      assume bvule($R3, $R4);
  242c242
  <      assume boolnot(boolnot(booland(eq($PSTATE_C, 0x1:bv1), eq($PSTATE_Z, 0x0:bv1))));
  ---
  >      assume bvult($R4, $R3);
  258c258
  <      assume eq($PSTATE_N, $PSTATE_V);
  ---
  >      assume bvsle($R4, $R3);
  263c263
  <      assume boolnot(eq($PSTATE_N, $PSTATE_V));
  ---
  >      assume bvslt($R3, $R4);
  279c279
  <      assume boolnot(eq($PSTATE_N, $PSTATE_V));
  ---
  >      assume bvslt($R3, $R4);
  284c284
  <      assume boolnot(boolnot(eq($PSTATE_N, $PSTATE_V)));
  ---
  >      assume bvsle($R4, $R3);
  300c300
  <      assume booland(eq($PSTATE_N, $PSTATE_V), eq($PSTATE_Z, 0x0:bv1));
  ---
  >      assume bvslt($R4, $R3);
  305c305
  <      assume boolnot(booland(eq($PSTATE_N, $PSTATE_V), eq($PSTATE_Z, 0x0:bv1)));
  ---
  >      assume bvsle($R3, $R4);
  321c321
  <      assume boolnot(booland(eq($PSTATE_N, $PSTATE_V), eq($PSTATE_Z, 0x0:bv1)));
  ---
  >      assume bvsle($R3, $R4);
  326,327c326
  <      assume boolnot(boolnot(booland(eq($PSTATE_N, $PSTATE_V),
  <         eq($PSTATE_Z, 0x0:bv1))));
  ---
  >      assume bvslt($R4, $R3);
  [1]
