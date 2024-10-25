Require Import isla.isla_lang.
Require Export isla.instructions.add.a4.
Require Export isla.instructions.add.a8.

Definition instr_map := [
  (0x4%Z, a4 (* beq a0,a1,64 *));
  (0x8%Z, a8 (* jal a0,64 *))
].
