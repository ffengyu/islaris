Require Import isla.isla_lang.
Require Export isla.dorami.instructions.F2P.a0.
Require Export isla.dorami.instructions.F2P.a4.
Require Export isla.dorami.instructions.F2P.a8.
Require Export isla.dorami.instructions.F2P.ac.
Require Export isla.dorami.instructions.F2P.a10.
Require Export isla.dorami.instructions.F2P.a14.
Require Export isla.dorami.instructions.F2P.a18.
Require Export isla.dorami.instructions.F2P.a1c.
Require Export isla.dorami.instructions.F2P.a20.
Require Export isla.dorami.instructions.F2P.a24.
Require Export isla.dorami.instructions.F2P.a28.
Require Export isla.dorami.instructions.F2P.a2c.

Definition instr_map := [
  (0x0%Z, a0 (* csrci mstatus,8 *));
  (0x4%Z, a4 (* addiw t0,zero,1 *));
  (0x8%Z, a8 (* slli t0,t0,0x1f *));
  (0xc%Z, ac (* csrw mtvec,t0 *));
  (0x10%Z, a10 (* lui t0,0x4dd *));
  (0x14%Z, a14 (* addiw t0,t0,-945 # 4dcc4f <sallyport_entry+0x4dcc4f> *));
  (0x18%Z, a18 (* slli t0,t0,0xc *));
  (0x1c%Z, a1c (* addi t0,t0,-827 *));
  (0x20%Z, a20 (* slli t0,t0,0xd *));
  (0x24%Z, a24 (* addi t0,t0,-738 *));
  (0x28%Z, a28 (* csrw pmpcfg0,t0 *));
  (0x2c%Z, a2c (* j fffffffffffef7ea *))
].
