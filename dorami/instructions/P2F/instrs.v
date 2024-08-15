Require Import isla.isla_lang.
Require Export isla.dorami.instructions.P2F.a0.
Require Export isla.dorami.instructions.P2F.a4.
Require Export isla.dorami.instructions.P2F.a8.
Require Export isla.dorami.instructions.P2F.ac.
Require Export isla.dorami.instructions.P2F.a10.
Require Export isla.dorami.instructions.P2F.a14.
Require Export isla.dorami.instructions.P2F.a18.
Require Export isla.dorami.instructions.P2F.a1c.
Require Export isla.dorami.instructions.P2F.a20.
Require Export isla.dorami.instructions.P2F.a24.
Require Export isla.dorami.instructions.P2F.a28.

Definition instr_map := [
  (0x0%Z, a0 (* lui t0,0x4 *));
  (0x4%Z, a4 (* addiw t0,t0,1 # 4001 <.text+0x4001> *));
  (0x8%Z, a8 (* slli t0,t0,0x11 *));
  (0xc%Z, ac (* csrw mtvec,t0 *));
  (0x10%Z, a10 (* lui t0,0x131 *));
  (0x14%Z, a14 (* addiw t0,t0,883 # 131373 <.text+0x131373> *));
  (0x18%Z, a18 (* slli t0,t0,0xe *));
  (0x1c%Z, a1c (* addi t0,t0,1261 *));
  (0x20%Z, a20 (* slli t0,t0,0xd *));
  (0x24%Z, a24 (* addi t0,t0,-2018 *));
  (0x28%Z, a28 (* csrw pmpcfg0,t0 *))
].
