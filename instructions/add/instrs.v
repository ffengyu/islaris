Require Import isla.isla_lang.
Require Export isla.instructions.add.a0.
Require Export isla.instructions.add.a4.
Require Export isla.instructions.add.a8.
Require Export isla.instructions.add.ac.

Definition instr_map := [
  (0x0%Z, a0 (* addi a0,a0,1 *));
  (0x4%Z, a4 (* addi a0,a0,1 *));
  (0x8%Z, a8 (* addi a0,a0,1 *));
  (0xc%Z, ac (* ret *))
].
