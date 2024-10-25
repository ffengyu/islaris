Require Import isla.isla_lang.
Require Export isla.instructions.test.ac.

Definition instr_map := [
  (0xc%Z, ac (* csrw mtvec,t0 *))
].
