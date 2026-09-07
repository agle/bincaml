open Bincaml_util.Common
open Lang
module DB = Analysis.Demanded_bits
module Demand = DB.Demand

open struct
  let parse_prog text = (Loader.Loadir.ast_of_string text).prog

  let proc_by_name prog name =
    let name =
      if String.starts_with ~prefix:"@" name then name else "@" ^ name
    in
    Program.get_proc_by_name name prog

  let solve text =
    let prog = parse_prog text in
    let _, results = DB.Analysis.solve prog in
    (prog, results)

  let result_for_proc prog results proc_name =
    let proc = proc_by_name prog proc_name in
    IDMap.find (Procedure.id proc) results

  let demand result name =
    VarMap.to_iter result
    |> Iter.find_map (fun (v, n) ->
        Option.return_if (String.equal (Var.name v) name) n)
    |> Option.get_or ~default:Demand.bottom

  let check_demand result name expected =
    Alcotest.(check int) name expected (demand result name)

  let check_demands result expected =
    List.iter (fun (name, width) -> check_demand result name width) expected

  let all_supported_operations_and_compositions () =
    let prog, results =
      solve
        {|
prog entry @main;

proc @main (
    pass:bv8,
    lshr:bv8,
    ashr:bv8,
    shl:bv8,
    slice:bv8,
    zext:bv8,
    sext:bv8,
    mask:bv8,
    combo:bv8,
    cat_hi:bv8,
    cat_lo:bv8,
    cat_hi2:bv8,
    cat_lo2:bv8,
    notv:bv8,
    negv:bv8,
    sub_l:bv8,
    sub_r:bv8,
    nand_l:bv8,
    nand_r:bv8,
    add_l:bv8,
    add_r:bv8,
    mul_l:bv8,
    mul_r:bv8,
    or_l:bv8,
    or_r:bv8,
    xor_l:bv8,
    xor_r:bv8,
    var_shift_value:bv8,
    var_shift_amount:bv8,
    cmp_l:bv8,
    cmp_r:bv8,
    dead:bv8
) -> (
    pass_o:bv3,
    lshr_o:bv3,
    ashr_o:bv2,
    shl_o:bv5,
    slice_o:bv3,
    zext_o:bv5,
    sext_o:bv12,
    mask_o:bv8,
    combo_o:bv4,
    cat_low_o:bv3,
    cat_high_o:bv4,
    not_o:bv3,
    neg_o:bv3,
    sub_o:bv4,
    nand_o:bv4,
    add_o:bv5,
    mul_o:bv6,
    or_o:bv7,
    xor_o:bv2,
    variable_shift_o:bv1
)
[
    block %entry [
        assert bvule(cmp_l:bv8, cmp_r:bv8);
        return(
            extract(3,0,pass:bv8),
            extract(3,0,bvlshr(lshr:bv8, 3:bv8)),
            extract(2,0,bvashr(ashr:bv8, 2:bv8)),
            extract(5,0,bvshl(shl:bv8, 2:bv8)),
            extract(3,0,extract(6,2,slice:bv8)),
            extract(5,0,zero_extend(8,zext:bv8)),
            extract(12,0,sign_extend(8,sext:bv8)),
            bvand(mask:bv8, 0x3c:bv8),
            extract(4,0,bvand(bvlshr(combo:bv8, 1:bv8), 0x0e:bv8)),
            extract(3,0,bvconcat(cat_hi:bv8, cat_lo:bv8)),
            extract(4,0,bvlshr(bvconcat(cat_hi2:bv8, cat_lo2:bv8), 8:bv16)),
            extract(3,0,bvnot(notv:bv8)),
            extract(3,0,bvneg(negv:bv8)),
            extract(4,0,bvsub(sub_l:bv8, sub_r:bv8)),
            extract(4,0,bvnand(nand_l:bv8, nand_r:bv8)),
            extract(5,0,bvadd(add_l:bv8, add_r:bv8)),
            extract(6,0,bvmul(mul_l:bv8, mul_r:bv8)),
            extract(7,0,bvor(or_l:bv8, or_r:bv8)),
            extract(2,0,bvxor(xor_l:bv8, xor_r:bv8)),
            extract(1,0,bvshl(var_shift_value:bv8, var_shift_amount:bv8))
        );
    ];
];
    |}
    in
    let main = result_for_proc prog results "main" in
    check_demands main
      [
        ("pass", 3);
        ("lshr", 6);
        ("ashr", 4);
        ("shl", 3);
        ("slice", 5);
        ("zext", 5);
        ("sext", 8);
        ("mask", 6);
        ("combo", 5);
        ("cat_hi", 0);
        ("cat_lo", 3);
        ("cat_hi2", 4);
        ("cat_lo2", 8);
        ("notv", 3);
        ("negv", 3);
        ("sub_l", 4);
        ("sub_r", 4);
        ("nand_l", 4);
        ("nand_r", 4);
        ("add_l", 5);
        ("add_r", 5);
        ("mul_l", 6);
        ("mul_r", 6);
        ("or_l", 7);
        ("or_r", 7);
        ("xor_l", 2);
        ("xor_r", 2);
        ("var_shift_value", 8);
        ("var_shift_amount", 8);
        ("cmp_l", 8);
        ("cmp_r", 8);
        ("dead", 0);
      ]

  let call_site_context_sensitivity () =
    let prog, results =
      solve
        {|
prog entry @main;

proc @main (
    hot:bv16,
    cold:bv16,
    witness:bv8,
    guarded:bv16,
    unused_actual:bv16
) -> ()
[
    block %entry [
        var (hot_out:bv8) := call @low8(hot:bv16);
        var (cold_out:bv8) := call @low8(cold:bv16);
        var (unused_out:bv8) := call @low8(unused_actual:bv16);
        call @requires_all(guarded:bv16);
        assert eq(extract(4,0,hot_out:bv8), 0:bv4);
        assert eq(cold_out:bv8, witness:bv8);
        return();
    ];
];

proc @low8 (x:bv16) -> (out:bv8)
[
    block %entry [
        return(extract(8,0,x:bv16));
    ];
];

proc @requires_all (x:bv16) -> ()
[
    block %entry [
        assert bvule(x:bv16, 0xffff:bv16);
        return();
    ];
];
    |}
    in
    let main = result_for_proc prog results "main" in
    let low8 = result_for_proc prog results "low8" in
    let requires_all = result_for_proc prog results "requires_all" in
    check_demands main
      [
        ("hot", 4);
        ("cold", 8);
        ("witness", 8);
        ("guarded", 16);
        ("unused_actual", 0);
        ("hot_out", 4);
        ("cold_out", 8);
        ("unused_out", 0);
      ];
    check_demands low8 [ ("x", 8); ("out", 8) ];
    check_demands requires_all [ ("x", 16) ]

  let statement_approximations_and_int_liveness () =
    let prog, results =
      solve
        {|
memory shared $mem : (bv64 -> bv8);

prog entry @main;

proc @main (
    addr_load:bv64,
    addr_store:bv64,
    store_value:bv32,
    assume_x:bv8,
    assert_x:bv8,
    target:bv64,
    int_a:int,
    int_b:int,
    dead_bv:bv8,
    dead_int:int
) -> ()
[
    block %entry [
        var loaded:bv32 := load le $mem addr_load:bv64 32;
        $mem := store le $mem addr_store:bv64 store_value:bv32 32;
        assume eq(extract(2,0,assume_x:bv8), 0:bv2);
        assert eq(extract(3,0,assert_x:bv8), 0:bv3);
        var int_sum:int := intadd(int_a:int, int_b:int);
        assert intlt(int_sum:int, 10);
        indirect call target:bv64;
        var dead_assign:bv8 := bvadd(dead_bv:bv8, 1:bv8);
        return();
    ];
];
    |}
    in
    let main = result_for_proc prog results "main" in
    check_demands main
      [
        ("$mem", Demand.top);
        ("addr_load", 64);
        ("addr_store", 64);
        ("store_value", 32);
        ("assume_x", 2);
        ("assert_x", 3);
        ("target", 64);
        ("int_a", Demand.top);
        ("int_b", Demand.top);
        ("int_sum", Demand.top);
        ("dead_bv", 0);
        ("dead_int", 0);
        ("dead_assign", 0);
        ("loaded", 0);
      ]

  let solver_terminates_on_left_and_right_shift_recurrence_loops () =
    let prog, results =
      solve
        {|
prog entry @main;

proc @main (x0:bv8, y0:bv8) -> (out:bv8)
[
    block %entry [
        goto(%left_head, %right_head);
    ];
    block %left_head (
        var x:bv8 := phi(%entry -> x0:bv8, %left_body -> x_next:bv8)
    ) [
        goto(%left_body, %ret);
    ];
    block %left_body [
        var x_next:bv8 := bvshl(x:bv8, 1:bv8);
        goto(%left_head);
    ];
    block %right_head (
        var y:bv8 := phi(%entry -> y0:bv8, %right_body -> y_next:bv8)
    ) [
        goto(%right_body, %ret);
    ];
    block %right_body [
        var y_next:bv8 := bvlshr(y:bv8, 1:bv8);
        goto(%right_head);
    ];
    block %ret [
        return(bvor(extract(1,0,x:bv8), extract(1,0,y:bv8)));
    ];
];
    |}
    in
    let main = result_for_proc prog results "main" in
    check_demands main
      [
        ("x0", 1);
        ("x", 1);
        ("x_next", 1);
        ("y0", 8);
        ("y", 8);
        ("y_next", 8);
        ("out", 8);
      ]

  let call_argument_compositions () =
    let prog, results =
      solve
        {|
prog entry @main;

proc @main (
    from_extract_actual:bv32,
    from_lshr_actual:bv32,
    from_shl_actual:bv32,
    masked_actual:bv32,
    unused_actual:bv32
) -> ()
[
    block %entry [
        var (from_extract_out:bv4) :=
            call @low4_8(extract(16,8,from_extract_actual:bv32));
        var (from_lshr_out:bv4) :=
            call @low4_32(bvlshr(from_lshr_actual:bv32, 5:bv32));
        var (from_shl_out:bv4) :=
            call @low4_32(bvshl(from_shl_actual:bv32, 2:bv32));
        var (masked_out:bv4) :=
            call @low4_32(bvand(masked_actual:bv32, 0xf0:bv32));
        var (unused_out:bv4) := call @low4_32(unused_actual:bv32);
        assert eq(from_extract_out:bv4, 0:bv4);
        assert eq(from_lshr_out:bv4, 0:bv4);
        assert eq(from_shl_out:bv4, 0:bv4);
        assert eq(masked_out:bv4, 0:bv4);
        return();
    ];
];

proc @low4_8 (x:bv8) -> (out:bv4)
[
    block %entry [
        return(extract(4,0,x:bv8));
    ];
];

proc @low4_32 (x:bv32) -> (out:bv4)
[
    block %entry [
        return(extract(4,0,x:bv32));
    ];
];
    |}
    in
    let main = result_for_proc prog results "main" in
    let low4_8 = result_for_proc prog results "low4_8" in
    let low4_32 = result_for_proc prog results "low4_32" in
    check_demands main
      [
        ("from_extract_actual", 12);
        ("from_lshr_actual", 9);
        ("from_shl_actual", 2);
        ("masked_actual", 0);
        ("unused_actual", 0);
        ("from_extract_out", 4);
        ("from_lshr_out", 4);
        ("from_shl_out", 4);
        ("masked_out", 4);
        ("unused_out", 0);
      ];
    check_demands low4_8 [ ("x", 4); ("out", 4) ];
    check_demands low4_32 [ ("x", 4); ("out", 4) ]

  let shift_by_width_edges () =
    let prog, results =
      solve
        {|
prog entry @main;

proc @main (lshr_by_width:bv8, ashr_by_width:bv8, shl_by_width:bv8) ->
    (lshr_out:bv1, ashr_out:bv1, shl_out:bv1)
[
    block %entry [
        return(
            extract(1,0,bvlshr(lshr_by_width:bv8, 8:bv8)),
            extract(1,0,bvashr(ashr_by_width:bv8, 8:bv8)),
            extract(1,0,bvshl(shl_by_width:bv8, 8:bv8))
        );
    ];
];
    |}
    in
    let main = result_for_proc prog results "main" in
    check_demands main
      [
        ("lshr_by_width", 0);
        ("ashr_by_width", 8);
        ("shl_by_width", 0);
        ("lshr_out", 1);
        ("ashr_out", 1);
        ("shl_out", 1);
      ]

  let phi_joins_branch_demands () =
    let prog, results =
      solve
        {|
prog entry @main;

proc @main (left_src:bv16, right_src:bv16, assertion_src:bv16) -> (out:bv4)
[
    block %entry [
        goto(%left, %right);
    ];
    block %left [
        var left_value:bv4 := extract(4,0,left_src:bv16);
        goto(%join);
    ];
    block %right [
        var right_value:bv4 := extract(8,4,right_src:bv16);
        goto(%join);
    ];
    block %join (
        var merged:bv4 := phi(%left -> left_value:bv4, %right -> right_value:bv4)
    ) [
        assert eq(extract(1,0,assertion_src:bv16), 0:bv1);
        return(merged:bv4);
    ];
];
    |}
    in
    let main = result_for_proc prog results "main" in
    check_demands main
      [
        ("left_src", 4);
        ("right_src", 8);
        ("assertion_src", 1);
        ("left_value", 4);
        ("right_value", 4);
        ("merged", 4);
        ("out", 4);
      ]

  let indirect_call_target_expression () =
    let prog, results =
      solve
        {|
prog entry @main;

proc @main (target_masked:bv64, target_salt:bv64, unused:bv64) -> ()
[
    block %entry [
        indirect call bvadd(bvand(target_masked:bv64, 0xff0:bv64), target_salt:bv64);
        var dead:bv64 := bvadd(unused:bv64, 1:bv64);
        return();
    ];
];
    |}
    in
    let main = result_for_proc prog results "main" in
    check_demands main
      [ ("target_masked", 12); ("target_salt", 64); ("unused", 0); ("dead", 0) ]

  let post_pass_widths_use_producer_policy () =
    let prog, results =
      solve
        {|
memory shared $mem : (bv64 -> bv8);

prog entry @main;

proc @main (
    addr:bv64,
    general_src:bv32,
    hot:bv16,
    cold:bv16,
    cold_witness:bv6
) -> ()
[
    block %entry [
        var loaded:bv32 := load le $mem addr:bv64 32;
        var general:bv32 := bvadd(general_src:bv32, 1:bv32);
        var (hot_out:bv8) := call @low8(hot:bv16);
        var (cold_out:bv8) := call @low8(cold:bv16);
        assert eq(extract(2,0,loaded:bv32), 0:bv2);
        assert eq(extract(2,0,general:bv32), 0:bv2);
        assert eq(extract(4,0,hot_out:bv8), 0:bv4);
        assert eq(extract(6,0,cold_out:bv8), cold_witness:bv6);
        return();
    ];
];

proc @low8 (x:bv16) -> (out:bv8)
[
    block %entry [
        return(extract(8,0,x:bv16));
    ];
];
    |}
    in
    let widths = DB.Coarse.analyse results prog in
    let var proc_name name =
      result_for_proc prog results proc_name
      |> VarMap.to_iter
      |> Iter.find_map (fun (v, _) ->
          Option.return_if (String.equal (Var.name v) name) v)
      |> Option.get_exn_or ("no such var: " ^ name)
    in
    let var_width proc_name name =
      let proc = proc_by_name prog proc_name in
      DB.Coarse.find_var widths (Procedure.id proc) (var proc_name name)
    in
    let return_width proc_name name =
      let proc = proc_by_name prog proc_name in
      let formal = StringMap.find name (Procedure.formal_out_params proc) in
      DB.Coarse.find_return widths (Procedure.id proc) name formal
    in
    Alcotest.(check int)
      "load result keeps original width" 32
      (var_width "main" "loaded");
    Alcotest.(check int)
      "general assignment narrows" 2
      (var_width "main" "general");
    Alcotest.(check int)
      "callee return width is call-site join" 6
      (return_width "low8" "out");
    Alcotest.(check int)
      "hot call receiver uses joined return width" 6
      (var_width "main" "hot_out");
    Alcotest.(check int)
      "cold call receiver uses joined return width" 6
      (var_width "main" "cold_out")

  let concat_slice_projection () =
    let prog, results =
      solve
        {|
prog entry @main;

proc @main (
    low_hi:bv8, low_mid:bv8, low_lo:bv8,
    mid_hi:bv8, mid_mid:bv8, mid_lo:bv8,
    high_hi:bv8, high_mid:bv8, high_lo:bv8,
    span_hi:bv8, span_mid:bv8, span_lo:bv8
) -> (low_o:bv4, mid_o:bv4, high_o:bv4, span_o:bv12)
[
    block %entry [
        return(
            extract(4,0,bvconcat(low_hi:bv8, low_mid:bv8, low_lo:bv8)),
            extract(12,8,bvconcat(mid_hi:bv8, mid_mid:bv8, mid_lo:bv8)),
            extract(20,16,bvconcat(high_hi:bv8, high_mid:bv8, high_lo:bv8)),
            extract(18,6,bvconcat(span_hi:bv8, span_mid:bv8, span_lo:bv8))
        );
    ];
];
    |}
    in
    let main = result_for_proc prog results "main" in
    check_demands main
      [
        ("low_hi", 0);
        ("low_mid", 0);
        ("low_lo", 4);
        ("mid_hi", 0);
        ("mid_mid", 4);
        ("mid_lo", 8);
        ("high_hi", 4);
        ("high_mid", 8);
        ("high_lo", 8);
        ("span_hi", 2);
        ("span_mid", 8);
        ("span_lo", 8);
      ]

  (** TODO: This is wrong, need IDE fix. Vars shouldn't be dead. *)
  let non_returning_unreachable_and_diverging_paths () =
    let prog, results =
      solve
        {|
prog entry @main;

proc @main (x:bv8, y:bv8, z:bv8) -> ()
[
    block %entry [
        goto(%normal, %abrupt, %diverge);
    ];
    block %normal [
        assert eq(extract(3,0,x:bv8), 0:bv3);
        return();
    ];
    block %abrupt [
        assert eq(extract(2,0,y:bv8), 0:bv2);
        call @exit();
        unreachable;
    ];
    block %diverge [
        var z1:bv8 := bvshl(z:bv8, 1:bv8);
        goto(%diverge);
    ];
];

proc @exit () -> ();
    |}
    in
    let main = result_for_proc prog results "main" in
    check_demands main [ ("x", 3); ("y", 0); ("z", 0); ("z1", 0) ]

  (** TODO: This is also wrong, need IDE fix. [out] should be [8]. *)
  let hi_seed () =
    let prog, results =
      solve
        {|
prog entry @main;

proc @main (
    arg:bv16,
    res:bv16,
) -> ()
[
    block %entry [
        var (res:bv16) := call @mask4(arg:bv16);
        assert eq(extract(8, 0,res:bv16), 0:bv8);
        return();
    ];
];

proc @mask4 (x:bv16) -> (out:bv16)
[
    block %entry [
        return(bvand(x:bv16,0xf:bv16));
    ];
];
    |}
    in
    let main = result_for_proc prog results "main" in
    let mask4 = result_for_proc prog results "mask4" in
    check_demands main [ ("arg", 4); ("res", 8) ];
    check_demands mask4 [ ("x", 4); ("out", 16) ]
end

let tests =
  [
    ( "demanded bits",
      [
        Alcotest.test_case "supported operations and compositions" `Quick
          all_supported_operations_and_compositions;
        Alcotest.test_case "call-site context sensitivity" `Quick
          call_site_context_sensitivity;
        Alcotest.test_case "statement approximations and int liveness" `Quick
          statement_approximations_and_int_liveness;
        Alcotest.test_case
          "solver terminates on left and right shift recurrence loops" `Quick
          solver_terminates_on_left_and_right_shift_recurrence_loops;
        Alcotest.test_case "call argument compositions" `Quick
          call_argument_compositions;
        Alcotest.test_case "shift by width edges" `Quick shift_by_width_edges;
        Alcotest.test_case "phi joins branch demands" `Quick
          phi_joins_branch_demands;
        Alcotest.test_case "indirect call target expression" `Quick
          indirect_call_target_expression;
        Alcotest.test_case "post-pass width producer policy" `Quick
          post_pass_widths_use_producer_policy;
        Alcotest.test_case "concat slice projection" `Quick
          concat_slice_projection;
        Alcotest.test_case "non-returning, unreachable and diverging paths"
          `Quick non_returning_unreachable_and_diverging_paths;
        Alcotest.test_case "issues with init_p2" `Quick hi_seed;
      ] );
  ]
