Require Import isla.isla_lang.
Require Export isla.dorami.instructions.P_entry.a0.
Require Export isla.dorami.instructions.P_entry.a4.
Require Export isla.dorami.instructions.P_entry.a8.
Require Export isla.dorami.instructions.P_entry.ac.
Require Export isla.dorami.instructions.P_entry.a10.
Require Export isla.dorami.instructions.P_entry.a14.
Require Export isla.dorami.instructions.P_entry.a18.

Definition instr_map := [
  (0x0%Z, a0 (* lui t0,0x137 *));
  (0x4%Z, a4 (* addiw t0,t0,787 # 137313 <P_entry_from_F+0x137313> *));
  (0x8%Z, a8 (* slli t0,t0,0xe *));
  (0xc%Z, ac (* addi t0,t0,1221 *));
  (0x10%Z, a10 (* slli t0,t0,0xd *));
  (0x14%Z, a14 (* addi t0,t0,-738 *));
  (0x18%Z, a18 (* csrw pmpcfg0,t0 *))
].
