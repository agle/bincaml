memory shared $mem : (bv64 -> bv8);
var $PC:bv64;
prog entry @main;

proc @main()  -> () {  }
[
    block %main_code [
    assume eq(0x00:bv64, $PC);
    call @_aarch64_eval(0xeb04007f:bv32, 0x00:bv64) { .asm = "cmp x3, x4" };
    call @_aarch64_eval(0x9a820020:bv32, 0x04:bv64) { .asm = "csel x0, x1, x2, eq" };
    call @_aarch64_eval(0x9a821020:bv32, 0x08:bv64) { .asm = "csel x0, x1, x2, ne" };
    call @_aarch64_eval(0x9a822020:bv32, 0x0c:bv64) { .asm = "csel x0, x1, x2, cs" };
    call @_aarch64_eval(0x9a823020:bv32, 0x10:bv64) { .asm = "csel x0, x1, x2, cc" };
    call @_aarch64_eval(0x9a824020:bv32, 0x14:bv64) { .asm = "csel x0, x1, x2, mi" };
    call @_aarch64_eval(0x9a825020:bv32, 0x18:bv64) { .asm = "csel x0, x1, x2, pl" };
    call @_aarch64_eval(0x9a826020:bv32, 0x1c:bv64) { .asm = "csel x0, x1, x2, vs" };
    call @_aarch64_eval(0x9a827020:bv32, 0x20:bv64) { .asm = "csel x0, x1, x2, vc" };
    call @_aarch64_eval(0x9a828020:bv32, 0x24:bv64) { .asm = "csel x0, x1, x2, hi" };
    call @_aarch64_eval(0x9a829020:bv32, 0x28:bv64) { .asm = "csel x0, x1, x2, ls" };
    call @_aarch64_eval(0x9a82a020:bv32, 0x2c:bv64) { .asm = "csel x0, x1, x2, ge" };
    call @_aarch64_eval(0x9a82b020:bv32, 0x30:bv64) { .asm = "csel x0, x1, x2, lt" };
    call @_aarch64_eval(0x9a82c020:bv32, 0x34:bv64) { .asm = "csel x0, x1, x2, gt" };
    call @_aarch64_eval(0x9a82d020:bv32, 0x38:bv64) { .asm = "csel x0, x1, x2, le" };
    goto (%ret_1);
  ];
  block %ret_1 [ return; ]
];
