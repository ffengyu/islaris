Require Import isla.isla_lang.
Require Export isla.dorami.instructions.exit_firmware.a0.

Definition instr_map := [
  (0x0%Z, a0 (* csrwi pmpcfg0,0 *))
].
