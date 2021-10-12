Require Import Sail.Base.
Require Import Sail.State_monad.
Require Import Sail.State_lifting.
Require Import isla.sail_riscv.sail_opsem.
From isla.instructions.riscv64_test Require Import instrs.

(* Eval hnf in riscv.decode (Ox"00a5b533") >>= execute. *)
(* Eval vm_compute in decodeCompressed (Ox"8526"). *)
(* Goal True. *)
(*   assert (execute (C_MV *)
(*             (Word.WS false *)
(*                (Word.WS true *)
(*                   (Word.WS false (Word.WS true (Word.WS false Word.WO)))), *)
(*             Word.WS true *)
(*               (Word.WS false *)
(*                        (Word.WS false (Word.WS true (Word.WS false Word.WO)))))) = Fail "a"). { *)
(*     unfold execute. simpl. *)
(*     unfold execute_RTYPE. simpl. *)
(*     simpl. *)

(*
Definition _admit {T} : T.
Admitted.

Program Definition initial_state : regstate :=
  {| SEE := 0 |}.
Solve Obligations with try exact: _admit.
Definition init_state : sequential_state regstate := {|
                         ss_regstate := initial_state ;
                         ss_memstate := NatMap.empty _;
                         ss_tagstate := NatMap.empty _;
                       |}.
Eval hnf in (liftState register_accessors (decode64 (Pos.to_nat 32 'h "AA0303F3" : mword 32)) init_state).
 *)

Definition mv_a1_s1_trace : list trc := [
  [
    (* Cycle Mk_annot; *)
    Smt (DeclareConst 88%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "x9" [] (RegVal_Base (Val_Symbolic 88%Z)) Mk_annot;
    Smt (DefineConst 89%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot; Val (Val_Symbolic 88%Z) Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "x11" [] (RegVal_Base (Val_Symbolic 89%Z)) Mk_annot
  ]
].

Definition test_instrs : gmap addr (encoded_instruction * list trc) :=
    <[ [BV{64} 0x0000000010300000] := (Compressed [BV{16} 0x85a6], mv_a1_s1_trace)]> $
    (* <[ [BV{64} 0x0000000010300004] := ([BV{32} 0xaa0003fc], a4)]> $ *)
    (* <[ [BV{64} 0x0000000010300008] := ([BV{32} 0xf900037c], a8)]> $ *)

    (* <[ [BV{64} 0x0000000010300010] := ([BV{32} 0x52800000], a10)]> $ *)
    (* <[ [BV{64} 0x0000000010300014] := ([BV{32} 0xd65f03c0], a14)]> $ *)
    ∅.


(* Ltac arch_red := lazy [ *)
(*                       write_reg read_reg *)
(*                       bind0 name __unconditional_ref PSTATE_ref of_regval regval_of regval_of_bool *)
(*                       undefined_SRType internal_pick *)
(*                       returnm eq_vec Bool.eqb get_word Word.whd *)
(*                       Word.natToWord bin readBinNat readBinAux forceOption *)
(*                       Pos.to_nat Pos.iter_op Init.Nat.add Init.Nat.mul Nat.div2 binDigitToNat *)
(*                       NatLib.mod2 Word.wtl *)
(*                       uint projT1 uint_plain Word.wordToN *)
(*                       N.mul Z.of_N Z.eqb orb andb sumbool_of_bool *)
(*                       and_boolM HaveBTIExt HasArchVersion generic_eq *)
(*                       Decidable_witness Decidable_eq_ArchVersion *)
(*                       Decidable_eq_from_dec bool_of_sumbool ArchVersion_eq_dec *)
(*                       ArchVersion_beq sumbool_rec sumbool_rect proj1_sig *)
(*                       __v85_implemented UsingAArch32 *)
(*                       HaveAnyAArch32 Z.to_nat *)
(*                       CFG_ID_AA64PFR0_EL1_EL1  CFG_ID_AA64PFR0_EL1_EL0 *)
(*                       HighestELUsingAArch32 __highest_el_aarch32_ref SEE_ref *)
(*                       Word.NToWord hex readHexN readHexNAux hexDigitToN *)
(*                       Word.wzero' Word.posToWord N.add negb *)
(*                       Pos.mul Pos.add Pos.pred_double *)
(*                       N.succ Pos.succ *)
(*                       undefined_bool *)
(*                       choose_bool *)
(*                       undefined_LogicalOp *)
(*                       aget_X *)
(*                       neq_int *)
(*                       _R_ref *)
(*                       build_ex *)
(*                       Pos.eqb *)
(*                       __id *)
(*                       (* access_vec_dec *) *)
(*                       (* access_mword_dec *) *)
(*                       (* bitU_of_bool getBit Word.wlsb Word.wrshift' *) *)
(*                       (* subrange_vec_dec *) *)
(*                       (* cast_to_mword cast_T mword_of_nat *) *)
(*                       (* cast_word Word.split1 Word.split2 *) *)
(*                     ]. *)
(*   Ltac do_red := *)
(*     repeat first [ *)
(*         progress arch_red | *)
(*         progress repeat match goal with *)
(*                         | |- context [@subrange_vec_dec ?n ?a ?b ?c ?F1 ?F2] => progress reduce_closed (@subrange_vec_dec n a b c F1 F2) *)
(*                         | |- context [@access_vec_dec ?n ?w ?m] => progress reduce_closed (@access_vec_dec n w m) *)
(*                         | |- context [vec_of_bits ?l] => progress reduce_closed (vec_of_bits l) *)
(*                         | |- context [Word.weqb ?b1 ?b2] => progress reduce_closed (Word.weqb b1 b2) *)
(*                         | |- context [Z.add ?n1 ?n2] => progress reduce_closed (Z.add n1 n2) *)
(*                         | |- context [Z.sub ?n1 ?n2] => progress reduce_closed (Z.sub n1 n2) *)
(*                         end | *)
(*         progress cbn [bind] *)
(*       ]. *)


(*
Axiom AXIOM_sim_TakePendingInterrupts : ∀ n Σ i e1 e2,
  sim n Σ e1 e e2 →
  sim n Σ
(undefined_InterruptReq () >>=
     (λ interrupt_req : InterruptReq,
        try_catch
          (TakePendingInterrupts (i interrupt_req) >>=
           (λ w__0 : bool,
              returnm
                (if sumbool_of_bool w__0
                 then print "Pending interrupt taken
"
                 else ())))
          (λ _ : exception,
             returnm (print "Unhandled exception while pending exceptions
")) >> e1)) e2.
 *)

(*** reduction tactics *)
Ltac hnf_sim :=
  match goal with
  | |- sim _ ?e1 _ _ =>
      let e' := eval hnf in e1 in
      change (e1) with e'
  end.

Ltac reduce_closed_sim :=
  repeat match goal with
   | |- context [@subrange_vec_dec ?n ?a ?b ?c ?F1 ?F2] => progress reduce_closed (@subrange_vec_dec n a b c F1 F2)
   | |- context [@access_vec_dec ?n ?w ?m] => progress reduce_closed (@access_vec_dec n w m)
   | |- context [vec_of_bits ?l] => progress reduce_closed (vec_of_bits l)
   | |- context [Word.weqb ?b1 ?b2] => progress reduce_closed (Word.weqb b1 b2)
   | |- context [@eq_vec ?n ?b1 ?b2] => progress reduce_closed (@eq_vec n b1 b2)
   (* | |- context [cast_unit_vec ?b] => progress reduce_closed (cast_unit_vec b) *)
   | |- context [@neq_vec ?n ?b1 ?b2] => progress reduce_closed (@neq_vec n b1 b2)
   | |- context [Z.ltb ?n1 ?n2] => progress reduce_closed (Z.ltb n1 n2)
   | |- context [Z.leb ?n1 ?n2] => progress reduce_closed (Z.leb n1 n2)
   | |- context [Z.geb ?n1 ?n2] => progress reduce_closed (Z.geb n1 n2)
   | |- context [Z.eqb ?n1 ?n2] => progress reduce_closed (Z.eqb n1 n2)
   | |- context [neq_int ?n1 ?n2] => progress reduce_closed (neq_int n1 n2)
   | |- context [size_bits_backwards_matches ?n] => progress reduce_closed (size_bits_backwards_matches n)
   | |- context [size_bits_backwards ?n] => progress reduce_closed (size_bits_backwards n)
   | |- context [bool_bits_backwards_matches ?n] => progress reduce_closed (bool_bits_backwards_matches n)
   | |- context [bool_bits_backwards ?n] => progress reduce_closed (bool_bits_backwards n)
   | |- context [amo_width_valid ?n] => progress reduce_closed (amo_width_valid n)
   | |- context [encdec_amoop_backwards_matches ?n] => progress reduce_closed (encdec_amoop_backwards_matches n)
   | |- context [encdec_amoop_backwards ?n] => progress reduce_closed (encdec_amoop_backwards n)
   | |- context [encdec_mul_op_backwards_matches ?n] => progress reduce_closed (encdec_mul_op_backwards_matches n)
   | |- context [encdec_mul_op_backwards ?n] => progress reduce_closed (encdec_mul_op_backwards n)
   | |- context [bool_not_bits_backwards_matches ?n] => progress reduce_closed (bool_not_bits_backwards_matches n)
   | |- context [bool_not_bits_backwards ?n] => progress reduce_closed (bool_not_bits_backwards n)
   | |- context [encdec_csrop_backwards_matches ?n] => progress reduce_closed (encdec_csrop_backwards_matches n)
   | |- context [encdec_csrop_backwards ?n] => progress reduce_closed (encdec_csrop_backwards n)
   | |- context [encdec_rounding_mode_backwards_matches ?n] => progress reduce_closed (encdec_rounding_mode_backwards_matches n)
   | |- context [encdec_rounding_mode_backwards ?n] => progress reduce_closed (encdec_rounding_mode_backwards n)
(* Decode cannot be reduced for floating point operations. There one has to do something like the following:
  apply: sim_is_RV32F_or_RV64F => b.
  red_sim.
  have -> : (if b then Done false else Done false) = Done false by destruct b.
  red_sim.
*)
   | |- context [riscv.decode ?i] => progress reduce_closed (riscv.decode i)
   | |- context [decodeCompressed ?i] => progress reduce_closed (decodeCompressed i)
   | |- context [get_config_print_reg ()] => progress reduce_closed (get_config_print_reg ())
   (* | |- context [HaveNV2Ext ()] => progress reduce_closed (HaveNV2Ext ()) *)
   (* | |- context [HaveBTIExt ()] => progress reduce_closed (HaveBTIExt ()) *)
   end.

Ltac cbn_sim :=
  cbn [returnm bind bind0 sim_regs
               (* ProcState_of_regval *)
               x9_ref x10_ref x11_ref misa_ref PC_ref nextPC_ref
               regval_of of_regval read_from write_to regval_from_reg
               Misa_of_regval regval_of_Misa
               ext_control_check_pc
               (* PSTATE_ref _PC_ref HCR_EL2_ref SCTLR_EL1_ref SEE_ref __unconditional_ref _R_ref __currentInstr_ref *)
               bitU_of_bool bool_of_bitU bit_to_bool
       negb sumbool_of_bool set
       projT1 build_ex __id andb orb
       _rec_execute compressed_measure Zwf_guarded
       subst_val_event subst_val_valu subst_val_smt subst_val_exp subst_val_base_val fmap list_fmap eq_var_name Z.eqb Pos.eqb map
    ].

Ltac subst_sim :=
  repeat lazymatch goal with
         | H : ?F (sim_regs ?Σ) = _ |- context [?F (sim_regs ?Σ)] => rewrite H
         end.

Ltac red_monad_sim :=
  repeat lazymatch goal with
         | |- sim _ (_ >>= _) _ _  => apply sim_bind
         | |- sim _ (_ >> _) _ _  => apply sim_bind
         | |- sim _ (and_boolM _ _) _ _  => apply sim_bind
         | |- sim _ (and_boolMP _ _) _ _  => apply sim_bind
         | |- sim _ (projT1_m _) _ _  => apply sim_bind
         | |- sim _ (build_trivial_ex _) _ _  => apply sim_bind
         | |- sim _ (try_catch _ _) _ _  => apply sim_try_catch
         | |- sim _ (Done _) (BindMCtx _ _) _  => apply sim_pop_bind_Done
         | |- sim _ (Done _) (TryMCtx _ _) _  => apply sim_pop_try_Done
         | |- sim _ (assert_exp' _ _) _ _  => apply sim_assert_exp';
              [try done; shelve| let H := fresh in move => H; try clear H]
         | |- sim _ _ _ (Smt (DeclareConst _ (Ty_BitVec _)) _::_)  => apply: sim_DeclareConstBitVec
         | |- sim _ _ _ (Smt (DefineConst _ _) _::_)  => apply: sim_DefineConst; [simpl; done|]
         | |- sim _ _ _ (Smt (Assert _) _::_)  => apply: sim_Assert; [simpl; shelve|]
         | |- sim _ _ _ (Branch _ _ _::_)  => apply: sim_Branch
         | |- sim _ _ _ (Assume _ _::_)  => let H := fresh "Hassume" in apply: sim_Assume => H; simpl in H
         | |- sim _ (read_reg _) _ (ReadReg _ _ _ _::_)  => apply: sim_read_reg; [done | done | try done; shelve|]
         | |- sim _ (write_reg nextPC_ref _) _ _  => apply: sim_write_reg_private; [done..|]
         | |- sim _ (read_reg nextPC_ref) _ _  => apply: sim_read_reg_l; [done..|]
         | |- sim _ (write_reg _ _) _ (WriteReg _ _ _ _::_)  => apply: sim_write_reg; [done | shelve |]
         | |- sim _ (Done _) NilMCtx []  => apply: sim_done
         end.

Ltac unfold_sim :=
  unfold wX_bits, rX_bits, rX, wX, regval_from_reg, regval_into_reg, returnm, set.

Ltac red_sim :=
    repeat first [
        progress unfold_sim |
        progress cbn_sim |
        progress subst_sim |
        progress reduce_closed_sim |
        progress red_monad_sim
      ].

Lemma sim_haveFExt Σ K e2:
  (∀ b, sim Σ (Done b) K e2) →
  sim Σ (haveFExt ()) K e2.
Proof.
  move => Hsim.
  unfold haveFExt. red_sim.
  apply: sim_read_reg_l; [done|]. red_sim.
  case_match => //. red_sim.
  apply: sim_read_reg_l; [done|].
  by red_sim.
Qed.

Lemma sim_is_RV32F_or_RV64F Σ K e2:
  (∀ b, sim Σ (Done b) K e2) →
  sim Σ (is_RV32F_or_RV64F ()) K e2.
Proof.
  move => Hsim.
  unfold is_RV32F_or_RV64F. red_sim.
  apply: sim_haveFExt => -[]; by red_sim.
Qed.

Lemma sim_is_RV64F Σ K e2:
  (∀ b, sim Σ (Done b) K e2) →
  sim Σ (is_RV64F ()) K e2.
Proof.
  move => Hsim.
  unfold is_RV64F. red_sim.
  apply: sim_haveFExt => -[]; by red_sim.
Qed.

Lemma sim_haveDExt Σ K e2:
  (∀ b, sim Σ (Done b) K e2) →
  sim Σ (haveDExt ()) K e2.
Proof.
  move => Hsim.
  unfold haveDExt. red_sim.
  apply: sim_read_reg_l; [done|]. red_sim.
  case_match => //. red_sim.
  apply: sim_read_reg_l; [done|].
  by red_sim.
Qed.

Lemma sim_is_RV32D_or_RV64D Σ K e2:
  (∀ b, sim Σ (Done b) K e2) →
  sim Σ (is_RV32D_or_RV64D ()) K e2.
Proof.
  move => Hsim.
  unfold is_RV32D_or_RV64D. red_sim.
  apply: sim_haveDExt => -[]; by red_sim.
Qed.

Lemma sim_is_RV64D Σ K e2:
  (∀ b, sim Σ (Done b) K e2) →
  sim Σ (is_RV64D ()) K e2.
Proof.
  move => Hsim.
  unfold is_RV64D. red_sim.
  apply: sim_haveDExt => -[]; by red_sim.
Qed.

Lemma sim_instr_mv_a1_s1:
  sim_instr (Compressed [BV{16} 0x85a6]) mv_a1_s1_trace.
Proof.
  move => regs. eexists _. split; [by left|].
  unfold step_cpu. red_sim. unfold execute. red_sim.
  unfold execute_RTYPE. red_sim.
Admitted.
  (* Unshelve. *)
  (* - simpl. rewrite mword_to_bv_add_vec //. *)
(* Qed. *)


Lemma sim_instr_a0:
  sim_instr (Uncompressed [BV{32} 0x00000513]) a0.
Proof.
  move => regs. eexists _. split; [by left|].
  unfold step_cpu. red_sim. unfold execute. red_sim.
  unfold execute_ITYPE. red_sim.
  Unshelve.
  all: try done.
  - simpl. destruct regs => /=. rewrite mword_to_bv_add_vec //.
Qed.

Lemma sim_instr_a4:
  sim_instr (Uncompressed [BV{32} 0x00150513]) a4.
Proof.
  move => regs. eexists _. split; [by left|].
  unfold step_cpu. red_sim. unfold execute. red_sim.
  unfold execute_ITYPE. red_sim.
  Unshelve.
  all: try done.
  - simpl. destruct regs => /=. rewrite mword_to_bv_add_vec //.
  - simpl. destruct regs => /=. rewrite mword_to_bv_add_vec //.
Qed.

Lemma sim_instr_a8:
  sim_instr (Uncompressed [BV{32} 0x00b50463]) a8.
Proof.
  move => regs.
  destruct (eq_vec (x10 regs) (x11 regs)) eqn: Hb1.
  all: eexists _; split; [by left|].
  all: unfold step_cpu; red_sim; unfold execute; red_sim.
  all: unfold execute_BTYPE; red_sim.
  all: apply: sim_read_reg_l; [done|]; red_sim.
Admitted.
(*

  rewrite Hb1; red_sim.
  unfold access_vec_dec, access_mword_dec.
  match goal with
  | |- context [getBit ?w ?n] => destruct (getBit w n) eqn:Hbit
  end.
  all: red_sim.
  all: admit.
  Unshelve.
  all: try done.
  - admit.
  - admit.
  - simpl. rewrite mword_to_bv_add_vec //.
Admitted.
*)
