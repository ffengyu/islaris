Require Import Sail.Base.
Require Import Sail.State_monad.
Require Import Sail.State_lifting.
Require Import isla.sail_riscv.sail_opsem.
Require Import isla.sail_riscv.tactics.
Require Import isla.automation.
Require Import isla.riscv64.riscv64.
From isla.instructions.memcpy_riscv64 Require Import instrs.

Lemma sim_instr_a0:
  sim_instr (Uncompressed [BV{32} 0x00060e63]) a0.
Proof.
  move => regs. unfold step_cpu, a0.
  red_sim. unfold execute. red_sim. unfold execute_BTYPE.
  red_sim.
  apply: sim_read_reg_l; [done|]. red_sim. rewrite x12_nextPC.
  destruct (eq_vec (x12 regs) zero_reg) eqn: Hx12; sim_simpl_hyp Hx12; red_sim.
  - apply: (sim_tfork 0); [done|]. red_sim.
    rewrite bit_to_bool_false; [|shelve]. red_sim.
  - apply: (sim_tfork 1); [done|]. red_sim.
  Unshelve. all: sim_simpl_goal.
  + rewrite (eq_vec_to_bv 64) // bool_decide_eq_true in Hx12. by rewrite Hx12.
  + rewrite access_vec_dec_to_bv // bitU_of_bool_B0 //.
    rewrite mword_to_bv_add_vec //=. reduce_closed_mword_to_bv.
    rewrite bv_add_unsigned bv_wrap_spec_low // Z.add_bit1 /=.
    have -> : (Z.testbit (bv_unsigned (mword_to_bv (n2:=64) (PC regs))) 1) = false. {
      rename select (bv_extract 1 1 _ = _) into He.
      bitify_hyp He. move: (He 0 ltac:(done)) => {}He.
      by bits_simplify_hyp He.
    }
    by rewrite andb_false_r.
  + rewrite mword_to_bv_add_vec //.
  + rewrite (eq_vec_to_bv 64) // bool_decide_eq_false in Hx12. done.
  + rewrite mword_to_bv_add_vec //.
Qed.

Lemma sim_instr_a4:
  sim_instr (Uncompressed [BV{32} 0x00058683]) a4.
Proof.
  move => regs. unfold step_cpu, a4.
  red_sim. unfold execute. red_sim. unfold execute_LOAD. red_sim.
  rewrite if_false; [|shelve]. red_sim.
  unfold translateAddr. red_sim. rewrite mstatus_nextPC cur_privilege_nextPC.
  apply sim_effectivePrivilege; [done|]. red_sim.
  unfold translateAddr_priv. red_sim.
  apply: sim_read_reg_l; [done|]. red_sim.
  apply: sim_read_reg_l; [done|]. red_sim.
  unfold translationMode.
  have -> : (cur_privilege regs) = Machine by destruct (cur_privilege regs). red_sim.
  apply: sim_read_reg_l; [done|]. red_sim. rewrite x11_nextPC.
  unfold mem_read. red_sim.
  apply: sim_read_reg_l; [done|]. red_sim.
  apply: sim_read_reg_l; [done|]. red_sim. rewrite mstatus_nextPC.
  apply sim_effectivePrivilege; [done|]. red_sim.
  rewrite Hassume. red_sim.
  rewrite if_false; [|shelve]. rewrite if_true; [|shelve]. red_sim.
  Unshelve. all: sim_simpl_goal.
  - apply check_misaligned_false. rewrite mword_to_bv_add_vec; [|done]. reduce_closed_mword_to_bv.
    by rewrite bv_unsigned_N_0.
  - eapply within_mmio_writable_false.
    + rewrite mword_to_bv_add_vec; [|done]. reduce_closed_mword_to_bv. done.
    + rewrite ->Hassume1, Hassume2, Hassume5, Hassume6, Hassume7, !bv_add_unsigned, !bv_unsigned_BV in *.
      unfold bv_wrap, bv_modulus in *. lia.
  - eapply within_phys_mem_true.
    + rewrite mword_to_bv_add_vec; [|done]. reduce_closed_mword_to_bv. done.
    + rewrite ->Hassume1, Hassume2, !bv_add_unsigned, !bv_unsigned_BV in *.
      unfold bv_wrap, bv_modulus in *. lia.
  - by rewrite mword_to_bv_add_vec.
  - rewrite mword_to_bv_EXTS // mword_to_bv_to_mword //.
  - rewrite mword_to_bv_add_vec //.
    Unshelve. exact: inhabitant.
Qed.

Lemma sim_instr_a8:
  sim_instr (Uncompressed [BV{32} 0x00d50023]) a8.
Proof.
  move => regs. unfold step_cpu, a8.
  red_sim. unfold execute. red_sim. unfold execute_STORE.  red_sim.
  rewrite if_false; [|shelve]. red_sim.
  unfold translateAddr. red_sim. rewrite mstatus_nextPC cur_privilege_nextPC.
  apply sim_effectivePrivilege; [done|]. red_sim.
  unfold translateAddr_priv. red_sim.
  apply: sim_read_reg_l; [done|]. red_sim.
  apply: sim_read_reg_l; [done|]. red_sim.
  unfold translationMode.
  have -> : (cur_privilege regs) = Machine by destruct (cur_privilege regs). red_sim.
  apply: sim_read_reg_l; [done|]. red_sim. rewrite x10_nextPC.
  unfold mem_write_value, mem_write_value_meta. red_sim.
  apply: sim_read_reg_l; [done|]. red_sim.
  apply: sim_read_reg_l; [done|]. red_sim. rewrite mstatus_nextPC cur_privilege_nextPC.
  apply sim_effectivePrivilege; [done|]. red_sim.
  rewrite Hassume. red_sim.
  rewrite if_false; [|shelve]. rewrite if_true; [|shelve]. red_sim.
  Unshelve. all: sim_simpl_goal.
  - apply check_misaligned_false. rewrite mword_to_bv_add_vec; [|done]. reduce_closed_mword_to_bv.
    by rewrite bv_unsigned_N_0.
  - eapply within_mmio_writable_false.
    + rewrite mword_to_bv_add_vec; [|done]. reduce_closed_mword_to_bv. done.
    + rewrite ->Hassume1, Hassume2, Hassume5, Hassume6, Hassume7, !bv_add_unsigned, !bv_unsigned_BV in *.
      unfold bv_wrap, bv_modulus in *. lia.
  - eapply within_phys_mem_true.
    + rewrite mword_to_bv_add_vec; [|done]. reduce_closed_mword_to_bv. done.
    + rewrite ->Hassume1, Hassume2, !bv_add_unsigned, !bv_unsigned_BV in *.
      unfold bv_wrap, bv_modulus in *. lia.
  - by rewrite mword_to_bv_add_vec.
  - by rewrite (mword_to_bv_subrange_vec_dec 7 0 64).
  - by rewrite mword_to_bv_add_vec.
    Unshelve. exact: inhabitant.
Qed.

Lemma sim_instr_ac:
  sim_instr (Uncompressed [BV{32} 0xfff60613]) ac.
Proof.
  move => regs. unfold step_cpu, ac.
  red_sim. unfold execute. red_sim. unfold execute_ITYPE.
  red_sim.
  Unshelve. all: sim_simpl_goal.
  - by rewrite mword_to_bv_add_vec.
  - by rewrite mword_to_bv_add_vec.
Qed.

Lemma sim_instr_a10:
  sim_instr (Uncompressed [BV{32} 0x00150513]) a10.
Proof.
  move => regs. unfold step_cpu, a10.
  red_sim. unfold execute. red_sim. unfold execute_ITYPE.
  red_sim.
  Unshelve. all: sim_simpl_goal.
  all: rewrite mword_to_bv_add_vec//.
Qed.

Lemma sim_instr_a14:
  sim_instr (Uncompressed [BV{32} 0x00158593]) a14.
Proof.
  move => regs. unfold step_cpu, a14.
  red_sim. unfold execute. red_sim. unfold execute_ITYPE.
  red_sim.
  Unshelve. all: sim_simpl_goal.
  all: rewrite mword_to_bv_add_vec//.
Qed.

Lemma sim_instr_a18:
  sim_instr (Uncompressed [BV{32} 0xfe0616e3]) a18.
Proof.
  move => regs. unfold step_cpu, a18.
  red_sim. unfold execute. red_sim. unfold execute_BTYPE.
  red_sim.
  apply: sim_read_reg_l; [done|]. red_sim. rewrite x12_nextPC.
  destruct (neq_vec (x12 regs) zero_reg) eqn: Hx12; unfold neq_vec in Hx12; sim_simpl_hyp Hx12; red_sim.
  - apply: (sim_tfork 0); [done|]. red_sim.
    rewrite bit_to_bool_false; [|shelve]. red_sim.
  - apply: (sim_tfork 1); [done|]. red_sim.
  Unshelve. all: sim_simpl_goal.
  + rewrite (eq_vec_to_bv 64) // bool_decide_eq_false in Hx12. contradict Hx12. by rewrite Hx12.
  + rewrite access_vec_dec_to_bv // bitU_of_bool_B0 //.
    rewrite mword_to_bv_add_vec //=. reduce_closed_mword_to_bv.
    rewrite bv_add_unsigned bv_wrap_spec_low // Z.add_bit1 /=.
    have -> : (Z.testbit (bv_unsigned (mword_to_bv (n2:=64) (PC regs))) 1) = false. {
      rename select (bv_extract 1 1 _ = _) into He.
      bitify_hyp He. move: (He 0 ltac:(done)) => {}He.
      by bits_simplify_hyp He.
    }
    by rewrite andb_false_r.
  + rewrite mword_to_bv_add_vec //.
  + rewrite (eq_vec_to_bv 64) // bool_decide_eq_true in Hx12. done.
  + rewrite mword_to_bv_add_vec //.
Qed.

Lemma sim_instr_a1c:
  sim_instr (Uncompressed [BV{32} 0x00008067]) a1c.
Proof.
  move => regs. unfold step_cpu, a1c.
  red_sim. unfold execute. red_sim. unfold execute_RISCV_JALR.
  red_sim.
  rewrite bit_to_bool_false; [|shelve]. red_sim.
  Unshelve. all: sim_simpl_goal.
  + rewrite access_vec_dec_to_bv // bitU_of_bool_B0 //.
    erewrite mword_to_bv_update_vec_dec => //.
    rewrite mword_to_bv_add_vec //=. reduce_closed_mword_to_bv.
    rewrite bv_or_unsigned bv_and_unsigned bv_not_unsigned Z.lor_spec Z.land_spec.
    rewrite orb_false_r andb_true_l.
    rewrite bv_add_unsigned bv_wrap_spec_low // Z.add_bit1 /=.
    have -> : (Z.testbit (bv_unsigned (mword_to_bv (n2:=64) (x1 regs))) 1) = false. {
      rename select (bv_extract 1 1 _ = _) into He.
      bitify_hyp He. move: (He 0 ltac:(done)) => {}He.
      by bits_simplify_hyp He.
    }
    by rewrite andb_false_r.
  + erewrite mword_to_bv_update_vec_dec => //.
    rewrite mword_to_bv_add_vec //. reduce_closed_mword_to_bv.
    rewrite bv_and_comm.
    f_equal.
    * f_equal. by apply bv_eq.
    * by apply bv_eq.
Qed.