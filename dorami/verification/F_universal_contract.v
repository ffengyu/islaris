From isla.dorami Require Import model.
From isla.dorami Require Import later_lifting.

(********************** Assumption Definitions Start ***********************)
(** We try to make assumptions decidable(boolean). **)

(* Some events don't have the operational semantics. *)
Fixpoint NoEvent (t: isla_trace) : bool :=
  match t with
  | tcons (Smt (DeclareConst _ (Ty_Array _ _)) _) _ => false
  | tcons (Smt (DefineEnum _ _ _) _) _ => false
  | tcons (CacheOp _ _ _) _ => false
  | tcons (MarkReg _ _ _) _ => false
  | tcons (Cycle _) _ => false
  | tcons (Instr _ _) _ => false
  | tcons (Sleeping _ _) _ => false
  | tcons (WakeRequest _) _ => false
  | tcons (SleepRequest _) _ => false
  | tcons (Call _ _) _ => false
  | tcons (Return _ _) _ => false
  | tcons (FunAssume _ _ _ _) _ => false
  | tcons (UseFunAssume _ _ _ _) _ => false
  | tcons (AbstractCall _ _ _ _) _ => false
  | tcons _ t => NoEvent t
  | tcases ts => forallb NoEvent ts
  | _ => true
  end.

(* The branch of Case event cannot be empty. *)
Fixpoint NoEmptyCases (t: isla_trace) : bool :=
  match t with
  | tcons e tail => NoEmptyCases tail
  | tcases ts => bool_decide(ts ≠ nil) && forallb NoEmptyCases ts
  | _ => true
  end.

(* The expression evaluation of the current event is not stuck. *)
Definition NoStuckEvalNow (t: isla_trace) : Prop :=
  match t with
  | tcons (Smt (DefineConst var exp) _) _ =>
      ∃ v, eval_exp exp = Some v
  | tcons (Smt (Assert exp) _) _ =>
      ∃ b, eval_exp exp = Some (Val_Bool b)
  | _ => True
  end.

(* The expression evaluation in the whole trace t is not stuck. *)
Definition NoStuckEval (t: isla_trace) : Prop :=
  t ≠ tnil -> forall t', rtc (fun t t' => ∃ label regs, trace_step t regs label t' ∧ label ≠ Some (LDone t')) t t' -> NoStuckEvalNow t'.

Scheme Equality for accessor.
Scheme Equality for list.

(* The deciable equality for the accessor list. *)
Definition list_acc_eqb := list_beq accessor accessor_beq.
Definition list_acc_eqb_eq a1 a2 : list_acc_eqb a1 a2 = true -> a1 = a2.
  refine (internal_list_dec_bl _ _ internal_accessor_dec_bl _ _).
Defined.

(* This definition list all the allowed registers in ReadReg which *)
(* contains the PMP and MTVEC because we can read but cannot write it. *)
(* This cumbersome definition is for the LegalRegAcc_R_destruct lemma. *)
(* The problem stems from that the case match/destruct of string and list *)
(* is very inconvenient. *)
(* Here we only shows a small set of registers with different types as *)
(* a proof of concept. *)
(* TODO: With automation support, we support the full registers. *)
Definition LegalRegAcc_R reg acc val : bool :=
  match val with
  | RVal_Bits bv =>
      (String.eqb reg "PC" && list_acc_eqb acc [] && (N.eqb (bvn_n bv) 64))
  | RVal_Bool b =>
      (String.eqb reg "rv_enable_zfinx" && list_acc_eqb acc [])
  | RegVal_Struct ((f, RVal_Bits bv) :: nil) =>
      String.eqb f "bits" && list_acc_eqb acc [Field "bits"] && (
      (String.eqb reg "mtvec" && (N.eqb (bvn_n bv) 64))
      || (String.eqb reg "pmp8cfg" && (N.eqb (bvn_n bv) 8))
      || (String.eqb reg "pmp9cfg" && (N.eqb (bvn_n bv) 8)))
  | _ => false
  end.

(* This definition list all the allowed registers in WriteReg that doesn't *)
(* allow MTVEC or PMP compared with LegalRegAcc_R. *)
Definition LegalRegAcc_W reg acc val : bool :=
  match val with
  | RVal_Bits bv =>
      (String.eqb reg "PC" && list_acc_eqb acc [] && (N.eqb (bvn_n bv) 64))
      || (String.eqb reg "x1" && list_acc_eqb acc [] && (N.eqb (bvn_n bv) 64))
  | RegVal_Struct ((f, RVal_Bits bv) :: nil) =>
      String.eqb f "bits" && list_acc_eqb acc [Field "bits"] &&
      (String.eqb reg "mcause" && (N.eqb (bvn_n bv) 64))
  | _ => false
  end.

(* We requires that the top/head event satisfies the assumption *)
(* LegalRegAcc_R. *)
Definition LegalReadRegNow (t: isla_trace) : bool :=
  match t with
  | tnil => true
  | tcons (ReadReg reg acc val _) t => LegalRegAcc_R reg acc val
  | tcons _ t => true
  | tcases ts => true
  end.

(* This property guaranteees that LegalRegAcc_R always holds during the *)
(* evaluation of trace. *)
Definition LegalReadReg (t: isla_trace) : Prop :=
  t ≠ tnil -> forall t', rtc (fun t t' => ∃ label regs, trace_step t regs label t' ∧ label ≠ Some (LDone t')) t t' -> LegalReadRegNow t'.

Definition LegalWriteRegNow (t: isla_trace) : bool :=
  match t with
  | tnil => true
  | tcons (WriteReg reg acc val _) t => LegalRegAcc_W reg acc val
  | tcons _ t => true
  | tcases ts => true
  end.

Definition LegalWriteReg (t: isla_trace) : Prop :=
  t ≠ tnil -> forall t', rtc (fun t t' => ∃ label regs, trace_step t regs label t' ∧ label ≠ Some (LDone t')) t t' -> LegalWriteRegNow t'.

(* This is the complete the assumptions that F's code can have. *)
(* This restriction makes sense because assume event can only come from *)
(* the user-input constriants. We, the users, can restrict this list the *)
(* registers that never change during the F's execution. *)
Definition assume_regs_map (mtvec: bv 64) : reg_map :=
  <[ "pmpaddr0" := RVal_Bits device_pmpaddr ]> $
  <[ "pmpaddr1" := RVal_Bits P_code_pmpaddr ]> $
  <[ "pmpaddr2" := RVal_Bits F_code_pmpaddr ]> $
  <[ "pmpaddr3" := RVal_Bits SP_code_pmpaddr ]> $
  <[ "pmpaddr4" := RVal_Bits F_data_pmpaddr ]> $
  <[ "pmpaddr5" := RVal_Bits P_data_pmpaddr ]> $
  <[ "pmpaddr8" := RVal_Bits SP_code_pmpaddr ]> $
  <[ "pmp0cfg" := RegVal_Struct [("bits", RVal_Bits device_cfg_when_F)] ]> $
  <[ "pmp1cfg" := RegVal_Struct [("bits", RVal_Bits P_code_cfg_when_F)] ]> $
  <[ "pmp2cfg" := RegVal_Struct [("bits", RVal_Bits F_code_cfg_when_F)] ]> $
  <[ "pmp3cfg" := RegVal_Struct [("bits", RVal_Bits SP_code_cfg_when_F)] ]> $
  <[ "pmp4cfg" := RegVal_Struct [("bits", RVal_Bits F_data_cfg_when_F)] ]> $
  <[ "pmp5cfg" := RegVal_Struct [("bits", RVal_Bits P_data_cfg_when_F)] ]> $
  <[ "pmp6cfg" := RegVal_Struct [("bits", RVal_Bits (BV 64 0))] ]> $
  <[ "pmp7cfg" := RegVal_Struct [("bits", RVal_Bits (BV 64 0))] ]> $
  <[ "pmp8cfg" := RegVal_Struct [("bits", RVal_Bits SP_code_cfg)] ]> $
  <[ "rv_enable_zfinx" := RVal_Bool false ]> $
  <[ "rv_pmp_count" := RegVal_I 0 64 ]> $
  <[ "rv_pmp_grain" := RegVal_I 10 64 ]> $
  <[ "rv_enable_misaligned_access" := RVal_Bool false ]> $
  <[ "rv_ram_base" := RVal_Bits (BV 64 0x0000000080000000) ]> $
  <[ "rv_ram_size" := RVal_Bits (BV 64 0x0000000004000000) ]> $
  <[ "rv_rom_base" := RVal_Bits (BV 64 0x0000000000001000) ]> $
  <[ "rv_rom_size" := RVal_Bits (BV 64 0x0000000000000100) ]> $
  <[ "rv_clint_base" := RVal_Bits (BV 64 0x0000000002000000) ]> $
  <[ "rv_clint_size" := RVal_Bits (BV 64 0x00000000000c0000) ]> $
  <[ "rv_htif_tohost" := RVal_Bits (BV 64 0x0000000040001000) ]> $
  <[ "mseccfg" := RegVal_Struct [("bits", RVal_Bits (BV 64 0x07))] ]> $
  <[ "cur_privilege" := RVal_Enum "Machine" ]> $
  <[ "Machine" := RVal_Enum "Machine" ]> $
  <[ "misa" := RegVal_Struct [("bits", RVal_Bits misa_bits)] ]> $
  <[ "mtvec" := RegVal_Struct [("bits", RVal_Bits mtvec)] ]> $
  ∅.

(* This definition list all the allowed registers in Assume. *)
(* This is again a PoC that covers a small set of registers. *)
Definition LegalAssumeEvent reg acc aval : bool :=
  match aval with
  | AVal_Var reg' acc' =>
      (String.eqb reg "cur_privilege") && (list_acc_eqb acc [])
      && (String.eqb reg' "Machine") && (list_acc_eqb acc' [])
  | AVal_Bits bv =>
      ((String.eqb reg "mseccfg") && (list_acc_eqb acc [Field "bits"])
            && (N.eqb (bvn_n bv) 64) && (Z.eqb (bvn_unsigned bv) 0x7))
      || ((String.eqb reg "misa") && (list_acc_eqb acc [Field "bits"])
            && (N.eqb (bvn_n bv) 64) && (Z.eqb (bvn_unsigned bv) (bv_unsigned misa_bits)))
      || ((String.eqb reg "mtvec") && (list_acc_eqb acc [Field "bits"])
            && (N.eqb (bvn_n bv) 64) && (Z.eqb (bvn_unsigned bv) (bv_unsigned F_mtvec)))
      || ((String.eqb reg "pmpaddr0") && (list_acc_eqb acc [])
            && (N.eqb (bvn_n bv) 64) && (Z.eqb (bvn_unsigned bv) (bv_unsigned device_pmpaddr)))
      || ((String.eqb reg "pmp0cfg") && (list_acc_eqb acc [Field "bits"])
            && (N.eqb (bvn_n bv) 8) && (Z.eqb (bvn_unsigned bv) (bv_unsigned device_cfg_when_F)))
  | _ => false
  end.

Fixpoint LegalAssume (t: isla_trace) :=
  match t with
  | tnil => true
  | tcons (Assume (AExp_Binop Eq (AExp_Val (AVal_Var reg acc) _) (AExp_Val aval _) _) _) t =>
      LegalAssumeEvent reg acc aval && LegalAssume t
  | tcons (Assume _ _) t => false
  | tcons _ t => LegalAssume t
  |tcases ts => forallb LegalAssume ts
  end.

(* This definition lists all the registers in AssumeReg. *)
Definition LegalRegAcc_A reg acc val : bool :=
  match val with
  | RVal_Bits bv =>
      (String.eqb reg "rv_htif_tohost" && list_acc_eqb acc [] && (N.eqb (bvn_n bv) 64) && (Z.eqb (bvn_unsigned bv) 0x0000000040001000))
      || (String.eqb reg "mseccfg" && list_acc_eqb acc [Field "bits"]
       && (N.eqb (bvn_n bv) 64) && (Z.eqb (bvn_unsigned bv) 0x07))
  | _ => false
  end.

Fixpoint LegalAssumeReg (t: isla_trace) : bool :=
  match t with
  | tnil => true
  | tcons (AssumeReg reg acc val _)  t =>
      LegalRegAcc_A reg acc val && LegalAssumeReg t
  | tcons _ t => LegalAssumeReg t
  | tcases ts => forallb LegalAssumeReg ts
  end.

(* This definition gives the restriction in memory access in *)
(* Read/WriteMem events. *)
Definition LegalMemAcc data addr len : bool :=
  (N.eqb (bvn_n addr) 64) && (N.eqb (bvn_n data) (8 * len))%N
  && (N.ltb 0 len)
  && (Z.leb (Z.of_N len) (0x1000 - (bvn_unsigned addr - bv_unsigned F_data_addr)))
  && (Z.leb (bv_unsigned F_data_addr) (bvn_unsigned addr))
  && (Z.leb (bvn_unsigned addr) (bv_unsigned F_data_addr + 0x1000)).

Definition LegalReadMemNow (t: isla_trace) : bool :=
  match t with
  | tnil => true
  | tcons (ReadMem (RVal_Bits data) _ (RVal_Bits addr) len _ _) t =>
      LegalMemAcc data addr len
  | tcons (ReadMem _ _ _ _ _ _) _ => false
  | tcons _ t => true
  | tcases ts => true
  end.

Definition LegalReadMem (t: isla_trace) : Prop :=
  t ≠ tnil -> forall t', rtc (fun t t' => ∃ label regs, trace_step t regs label t' ∧ label ≠ Some (LDone t')) t t' -> LegalReadMemNow t'.

Definition LegalWriteMemNow (t: isla_trace) : bool :=
  match t with
  | tnil => true
  | tcons (WriteMem (RVal_Bool _) _ (RVal_Bits addr) (RVal_Bits data) len _ _) t =>
      LegalMemAcc data addr len
  | tcons (WriteMem _ _ _ _ _ _ _) _ => false
  | tcons _ t => true
  | tcases ts => true
  end.

Definition LegalWriteMem (t: isla_trace) : Prop :=
  t ≠ tnil -> forall t', rtc (fun t t' => ∃ label regs, trace_step t regs label t' ∧ label ≠ Some (LDone t')) t t' -> LegalWriteMemNow t'.

(* When the PC is misalinged or outside the authorized region, PC is *)
(* updated to MTVEC right now. *)
Definition illegal_PC `{!islaG Σ} `{!threadG} : iProp Σ :=
  ∀ i: bv 64, ("PC" ↦ᵣ RVal_Bits i ∗
  ⌜~ (bv_unsigned (bv_extract 0 2 i) = 0 ∧ (bv_unsigned F_code_addr) <= (bv_unsigned i) < (bv_unsigned F_code_end_addr))⌝)
       -∗ "PC" ↦ᵣ RVal_Bits F_mtvec.

(* When cur_privilege is not in Machine, PC is updated to MTVEC right *)
(* now and cur_privilege returns to Machine immediately. *)
(* This is because there is no permission for other modes, which triggers *)
(* the M-mode exception. *)
Definition illegal_Priv `{!islaG Σ} `{!threadG} : iProp Σ :=
  ∀ i, "PC" ↦ᵣ i ∗ ("cur_privilege" ↦ᵣ: λ v, ⌜v ≠ RVal_Enum "Machine"⌝) -∗
  "PC" ↦ᵣ  RVal_Bits F_mtvec ∗ "cur_privilege" ↦ᵣ RVal_Enum "Machine".

(*********************** Assumption Definitions End ************************)

(********************* Properties of Assumptions Start *********************)

(* The stronger induction principle for the proof that the property holds *)
(* after the small-step evaluations. *)
Fixpoint isla_trace_custom_ind (P: isla_trace -> Prop) (Hnil: P tnil)
  (Hcon: ∀ e t, P t -> P (e :t: t))
  (Hcase: ∀ ts, Forall P ts -> P (tcases ts)) (i: isla_trace) {struct i} : P i
  :=
  match i with
  | tnil => Hnil
  | tcons event tail => Hcon event tail (isla_trace_custom_ind P Hnil Hcon Hcase tail)
  | tcases es => Hcase es
                  ((fix forall_list (ts: list isla_trace) :=
                    match ts return Forall P ts with
                    | nil => List.Forall_nil P
                    | x::t => List.Forall_cons P x t
                              (isla_trace_custom_ind P Hnil Hcon Hcase x) (forall_list t)
                    end) es)
  end.

(* The NoEvent assumption holds during evaluation *)
Lemma subst_trace_NoEvent v x t:
  NoEvent t -> NoEvent (subst_trace v x t).
Proof.
  intro.
  induction t as [|e tail IH|es IH] using isla_trace_custom_ind; first done.
  - destruct e; first destruct smt5; first destruct ty5; simpl in H |- *.
    all: first [by apply IH | done ].
  - rewrite /= !Is_true_true in H |- *.
    rewrite Forall_forall in IH.
    rewrite !forallb_forall in H |- *.
    intros st Hin.
    apply elem_of_list_In, elem_of_list_fmap_2 in Hin.
    destruct Hin as (y & -> & Hin).
    rewrite -Is_true_true.
    apply (IH _ Hin).
    by apply Is_true_true, H, elem_of_list_In.
Qed.

Lemma trace_step_NoEvent t regs label t' :
  t ≠ tnil -> trace_step t regs label t' -> NoEvent t -> NoEvent t'.
Proof.
  intros Hneq Hstep Ht.
  destruct Hstep; first [done | by apply subst_trace_NoEvent| trivial].
  rewrite /= !Is_true_true forallb_forall in Ht.
  by apply Is_true_true, Ht, elem_of_list_In.
Qed.

(* The NoEmptyCases assumption holds during evaluation *)
Lemma subst_trace_NoEmptyCases v x t:
  NoEmptyCases t -> NoEmptyCases (subst_trace v x t).
Proof.
  intro.
  induction t as [|e tail IH|es IH] using isla_trace_custom_ind; first done.
  - simpl in H |- *.
    by apply IH.
  - rewrite /= !Is_true_true !andb_true_iff in H |- *.
    destruct H as [Hes Hsubt].
    destruct es;first done.
    split; first done.
    rewrite forallb_forall => Hsub2 Hin2.
    rewrite -elem_of_list_In in Hin2.
    apply elem_of_list_fmap_2 in Hin2.
    destruct Hin2 as (y & -> & Hin2).
    rewrite -Is_true_true.
    rewrite Forall_forall in IH.
    rewrite forallb_forall in Hsubt.
    apply (IH _ Hin2).
    rewrite Is_true_true.
    apply Hsubt.
    by rewrite -elem_of_list_In.
Qed.

Lemma trace_step_NoEmptyCases t regs label t' :
  t ≠ tnil -> trace_step t regs label t' -> NoEmptyCases t -> NoEmptyCases t'.
Proof.
  intros Hneq Hstep Ht.
  destruct Hstep; first [done | by apply subst_trace_NoEmptyCases | trivial].
  rewrite /= !Is_true_true !andb_true_iff in Ht.
  destruct Ht as [Hts Hsub].
  rewrite forallb_forall in Hsub.
  rewrite Is_true_true.
  apply Hsub.
  by rewrite -elem_of_list_In.
Qed.

(* Case match on the possible registers in ReadReg event. *)
Lemma LegalRegAcc_R_destruct reg acc val :
  LegalRegAcc_R reg acc val->
    {bv | reg = "PC" ∧ acc = [] ∧ val = RVal_Bits bv ∧ (N.eqb (bvn_n bv) 64)} +
    {bv | reg = "mtvec" ∧ acc = [Field "bits"] ∧ val = RegVal_Struct [("bits", RVal_Bits bv)] ∧ (N.eqb (bvn_n bv) 64)} +
    {bv | reg = "pmp8cfg" ∧ acc = [Field "bits"] ∧ val = RegVal_Struct [("bits", RVal_Bits bv)] ∧ (N.eqb (bvn_n bv) 8)} +
    {bv | reg = "pmp9cfg" ∧ acc = [Field "bits"] ∧ val = RegVal_Struct [("bits", RVal_Bits bv)] ∧ (N.eqb (bvn_n bv) 8)} +
    {b | reg = "rv_enable_zfinx" ∧ acc = [] ∧ val = RVal_Bool b }.
Proof.
  intro H.
  apply Is_true_true_1 in H.
  destruct val; simpl in H; try done.
  - destruct base_val5; simpl in H; try done.
    + refine (inr _).
      repeat (apply (proj1 (andb_true_iff _ _)) in H; destruct H).
      apply String.eqb_eq in H.
      apply list_acc_eqb_eq in H0.
      simplify_eq.
      by eauto.
    + refine (inl (inl (inl (inl _)))).
      repeat (apply (proj1 (andb_true_iff _ _)) in H; destruct H).
      apply String.eqb_eq in H.
      apply list_acc_eqb_eq in H1.
      simplify_eq.
      by eauto.
  - destruct l; first done.
    destruct p.
    destruct v; try done.
    destruct base_val5; try done.
    destruct l; last done.
    repeat (apply (proj1 (andb_true_iff _ _)) in H; destruct H).
    repeat (apply (orb_true_elim _ _) in H0; destruct H0 as [H0|H0]);
    repeat (apply (proj1 (andb_true_iff _ _)) in H0; destruct H0).
    + refine (inl (inl (inl (inr _)))).
      apply String.eqb_eq in H, H0.
      apply list_acc_eqb_eq in H1.
      simplify_eq.
      by eauto.
    + refine (inl (inl (inr _))).
      apply String.eqb_eq in H, H0.
      apply list_acc_eqb_eq in H1.
      simplify_eq.
      by eauto.
    + refine (inl (inr _)).
      apply String.eqb_eq in H, H0.
      apply list_acc_eqb_eq in H1.
      simplify_eq.
      by eauto.
Qed.

Definition bvn_to_bv' b l : bvn_n b = l -> { b': bv l | bv_to_bvn b' = b }.
  intros.
  exists (eq_rect (bvn_n b) (λ n0 : N, bv n0) (bvn_val b) l H).
  unfold eq_rect.
  destruct H.
  apply bvn_eq.
  unfold bvn_unsigned.
  by split.
Defined.

Definition bvn_to_bv'' b l v :
  bvn_n b = l -> bvn_unsigned b = v ->
    { BvWf : BvWf l v | bv_to_bvn (BV l v) = b }.
  intros.
  refine (exist _ _ _).
  apply bvn_eq.
  refine (match H with eq_refl => match H0 with eq_refl => _ end end); last done.
  destruct b as [blen [bv prf]].
  unfold BvWf in prf |- *.
  unfold bvn_unsigned, bv_unsigned in H0.
  simpl in H0, H.
  by refine (match H with eq_refl => match H0 with eq_refl => _ end end).
Defined.

(* Case match on the possible registers in WriteReg event. *)
Lemma LegalRegAcc_W_destruct reg acc val :
  LegalRegAcc_W reg acc val->
    {bv: bv 64 | reg = "PC" ∧ acc = [] ∧ val = RVal_Bits bv } +
    {bv: bv 64 | reg = "x1" ∧ acc = [] ∧ val = RVal_Bits bv } +
    {bv: bv 64 | reg = "mcause" ∧ acc = [Field "bits"] ∧ val = RegVal_Struct [("bits", RVal_Bits bv)] }.
Proof.
  intro H.
  apply Is_true_true_1 in H.
  destruct val; simpl in H; try done.
  - destruct base_val5; simpl in H; try done.
    repeat (apply (orb_true_elim _ _) in H; destruct H as [H|H]).
    + refine (inl (inl _)).
      repeat (apply (proj1 (andb_true_iff _ _)) in H; destruct H).
      apply String.eqb_eq in H.
      apply list_acc_eqb_eq in H1.
      apply Neqb_ok, bvn_to_bv' in H0.
      destruct H0.
      exists x.
      simplify_eq.
      by auto.
    + refine (inl (inr _)).
      repeat (apply (proj1 (andb_true_iff _ _)) in H; destruct H).
      apply String.eqb_eq in H.
      apply list_acc_eqb_eq in H1.
      apply Neqb_ok, bvn_to_bv' in H0.
      destruct H0.
      exists x.
      simplify_eq.
      by auto.
  - destruct l; first done.
    destruct p.
    destruct v; try done.
    destruct base_val5; try done.
    destruct l; last done.
    repeat (apply (proj1 (andb_true_iff _ _)) in H; destruct H).
    repeat (apply (proj1 (andb_true_iff _ _)) in H0; destruct H0).
    refine (inr _).
    apply String.eqb_eq in H, H0.
    apply list_acc_eqb_eq in H1.
    apply Neqb_ok, bvn_to_bv' in H2.
    destruct H2.
    exists x.
    simplify_eq.
    by auto.
Qed.

Lemma legal_read_accessor_R reg acc val :
  LegalRegAcc_R reg acc val -> ∃ v, read_accessor acc val = Some v.
Proof.
  intros.
  apply LegalRegAcc_R_destruct in H.
  destruct H as [[[[]|]|]|].
  - destruct s as [bv H].
    destruct H as (->&->&->&?).
    by econstructor.
  - destruct s as [bv H].
    destruct H as (->&->&->&?).
    by econstructor.
  - destruct s as [bv H].
    destruct H as (->&->&->&?).
    by econstructor.
  - destruct s as [bv H].
    destruct H as (->&->&->&?).
    by econstructor.
  - destruct s as [bv H].
    destruct H as (->&->&->).
    by econstructor.
Qed.

(* Case matches for registers in AssumeReg. *)
Lemma LegalRegAcc_A_destruct reg acc val :
  LegalRegAcc_A reg acc val->
    {bv | reg = "rv_htif_tohost" ∧ acc = [] ∧ val = RVal_Bits bv ∧ (bvn_n bv) = 64%N ∧ (bvn_unsigned bv) = 0x0000000040001000 } +
    {bv | reg = "mseccfg" ∧ acc = [Field "bits"] ∧ val = RVal_Bits bv ∧ (bvn_n bv) = 64%N ∧ (bvn_unsigned bv) = 0x07}.
Proof.
  intro H.
  apply Is_true_true_1 in H.
  destruct val; simpl in H; try done.
  - destruct base_val5; simpl in H; try done.
    repeat (apply (orb_true_elim _ _) in H; destruct H as [H|H]).
    + refine (inl _).
      repeat (apply (proj1 (andb_true_iff _ _)) in H; destruct H).
      apply String.eqb_eq in H.
      apply Z.eqb_eq in H0.
      apply Neqb_ok in H1.
      apply list_acc_eqb_eq in H2.
      simplify_eq.
      by eauto 6.
    + refine (inr _).
      repeat (apply (proj1 (andb_true_iff _ _)) in H; destruct H).
      apply String.eqb_eq in H.
      apply Z.eqb_eq in H0.
      apply Neqb_ok in H1.
      apply list_acc_eqb_eq in H2.
      simplify_eq.
      by eauto 6.
Qed.

Lemma subst_trace_LegalAssumeReg v x t:
  LegalAssumeReg t -> LegalAssumeReg (subst_trace v x t).
Proof.
  intro.
  induction t as [|e tail IH|es IH] using isla_trace_custom_ind; first done.
  - destruct e; simpl in H |- *.
    all: try by apply IH.
    apply Is_true_true, andb_true_iff in H.
    apply Is_true_true, andb_true_iff.
    destruct H.
    apply Is_true_true in H, H0.
    split; apply Is_true_true ; last by apply IH.
    apply LegalRegAcc_A_destruct in H.
    destruct H as [].
    all: destruct s as [bv (->&->&->&H&H1)]; simpl; by rewrite H H1.
  - rewrite /= !Is_true_true in H |- *.
    rewrite Forall_forall in IH.
    rewrite !forallb_forall in H |- *.
    intros st Hin.
    apply elem_of_list_In, elem_of_list_fmap_2 in Hin.
    destruct Hin as (y & -> & Hin).
    rewrite -Is_true_true.
    apply (IH _ Hin).
    by apply Is_true_true, H, elem_of_list_In.
Qed.

Lemma trace_step_LegalAssumeReg t regs label t' :
  t ≠ tnil -> trace_step t regs label t' -> LegalAssumeReg t -> LegalAssumeReg t'.
Proof.
  intros Hneq Hstep Ht.
  destruct Hstep; first [done | by apply subst_trace_LegalAssumeReg | simpl in Ht |- *].
  - apply Is_true_true, andb_true_iff in Ht.
    destruct Ht.
    by apply Is_true_true.
  - rewrite /= !Is_true_true forallb_forall in Ht.
    by apply Is_true_true, Ht, elem_of_list_In.
Qed.

Definition assume_val_beq x y :=
  match x, y with
  | AVal_Var reg1 acc1, AVal_Var reg2 acc2 => String.eqb reg1 reg2 && list_acc_eqb acc1 acc2
  | AVal_Bool b1, AVal_Bool b2 => eqb b1 b2
  | AVal_Bits bv1, AVal_Bits bv2 => @bool_decide _ (bvn_eq_dec bv1 bv2)
  | AVal_Enum em1, AVal_Enum em2 => String.eqb em1 em2
  | _, _ => false
  end.

Definition assume_val_dec_bl x y : assume_val_beq x y = true -> x = y.
  destruct x, y; simpl; try done.
  - intros.
    apply eq_sym, andb_true_eq in H.
    destruct H.
    apply eq_sym in H, H0.
    apply String.eqb_eq in H.
    apply list_acc_eqb_eq in H0.
    by rewrite H H0.
  - intro.
    apply eqb_prop in H.
    by rewrite H.
  - intro.
    apply bool_decide_eq_true_1 in H.
    by rewrite H.
  - intro.
    apply String.eqb_eq in H.
    by rewrite H.
Defined.

Lemma LegalAssumeEvent_destruct reg acc aval :
  LegalAssumeEvent reg acc aval ->
    { reg = "cur_privilege" ∧ acc = [] ∧ aval = (AVal_Var "Machine" []) }
    + { reg = "mseccfg" ∧ acc = [Field "bits"] ∧ aval = (AVal_Bits (BV 64 0x7)) }
    + { reg = "misa" ∧ acc = [Field "bits"] ∧ aval = (AVal_Bits misa_bits) }
    + { reg = "mtvec" ∧ acc = [Field "bits"] ∧ aval = (AVal_Bits F_mtvec) }
    + { reg = "pmpaddr0" ∧ acc = [] ∧ aval = (AVal_Bits device_pmpaddr) }
    + { reg = "pmp0cfg" ∧ acc = [Field "bits"] ∧ aval = (AVal_Bits device_cfg_when_F) }.
Proof.
  intro H.
  apply Is_true_true_1 in H.
  destruct aval; simpl in H; try done.
  - refine (inleft (inleft (inleft (inleft (left _))))).
    repeat (apply (proj1 (andb_true_iff _ _)) in H; destruct H).
    apply String.eqb_eq in H, H1.
    apply list_acc_eqb_eq in H0, H2.
    simplify_eq.
    by auto.
  - repeat (apply (orb_true_elim _ _) in H; destruct H as [H|H]).
    + refine (inleft (inleft (inleft (inleft (right _))))).
      repeat (apply (proj1 (andb_true_iff _ _)) in H; destruct H).
      apply String.eqb_eq in H.
      apply list_acc_eqb_eq in H2.
      apply Neqb_ok in H1.
      apply Z.eqb_eq in H0.
      destruct (bvn_to_bv'' _ _ _ H1 H0) as [? <-].
      simplify_eq.
      split; first done.
      split; first done.
      do 2 f_equal.
      by apply bv_eq.
    + refine (inleft (inleft (inleft (inright _)))).
      repeat (apply (proj1 (andb_true_iff _ _)) in H; destruct H).
      apply String.eqb_eq in H.
      apply list_acc_eqb_eq in H2.
      apply Neqb_ok in H1.
      apply Z.eqb_eq in H0.
      destruct (bvn_to_bv'' _ _ _ H1 H0) as [? <-].
      simplify_eq.
      split; first done.
      split; first done.
      do 2 f_equal.
      by apply bv_eq.
    + refine (inleft (inleft (inright _))).
      repeat (apply (proj1 (andb_true_iff _ _)) in H; destruct H).
      apply String.eqb_eq in H.
      apply list_acc_eqb_eq in H2.
      apply Neqb_ok in H1.
      apply Z.eqb_eq in H0.
      destruct (bvn_to_bv'' _ _ _ H1 H0) as [? <-].
      simplify_eq.
      split; first done.
      split; first done.
      do 2 f_equal.
      by apply bv_eq.
    + refine (inleft (inright _)).
      repeat (apply (proj1 (andb_true_iff _ _)) in H; destruct H).
      apply String.eqb_eq in H.
      apply list_acc_eqb_eq in H2.
      apply Neqb_ok in H1.
      apply Z.eqb_eq in H0.
      destruct (bvn_to_bv'' _ _ _ H1 H0) as [? <-].
      simplify_eq.
      split; first done.
      split; first done.
      do 2 f_equal.
      by apply bv_eq.
    + refine (inright _).
      repeat (apply (proj1 (andb_true_iff _ _)) in H; destruct H).
      apply String.eqb_eq in H.
      apply list_acc_eqb_eq in H2.
      apply Neqb_ok in H1.
      apply Z.eqb_eq in H0.
      destruct (bvn_to_bv'' _ _ _ H1 H0) as [? <-].
      simplify_eq.
      split; first done.
      split; first done.
      do 2 f_equal.
      by apply bv_eq.
Qed.

Lemma subst_trace_LegalAssume v x t:
  LegalAssume t -> LegalAssume (subst_trace v x t).
Proof.
  intro.
  induction t as [|e tail IH|es IH] using isla_trace_custom_ind; first done.
  - destruct e; simpl in H |- *.
    all: try by apply IH.
    destruct a_exp5; simpl in H |- *; try done.
    destruct binop5; simpl in H |- *; try done.
    destruct a_exp5_1; simpl in H |- *; try done.
    destruct assume_val5; simpl in H |- *; try done.
    destruct a_exp5_2; simpl in H |- *; try done.
    apply Is_true_true, andb_true_iff in H.
    apply Is_true_true, andb_true_iff.
    destruct H.
    apply Is_true_true in H, H0.
    split; apply Is_true_true ; last by apply IH.
    apply LegalAssumeEvent_destruct in H.
    destruct H as [[[[[]|]|]|]|].
    all: destruct a as (->&->&->); by simpl.
  - rewrite /= !Is_true_true in H |- *.
    rewrite Forall_forall in IH.
    rewrite !forallb_forall in H |- *.
    intros st Hin.
    apply elem_of_list_In, elem_of_list_fmap_2 in Hin.
    destruct Hin as (y & -> & Hin).
    rewrite -Is_true_true.
    apply (IH _ Hin).
    by apply Is_true_true, H, elem_of_list_In.
Qed.

Lemma trace_step_LegalAssume t regs label t' :
  t ≠ tnil -> trace_step t regs label t' -> LegalAssume t -> LegalAssume t'.
Proof.
  intros Hneq Hstep Ht.
  destruct Hstep; first [done | by apply subst_trace_LegalAssume | simpl in Ht |- *].
  - destruct e; simpl in Ht |- *; try done.
    destruct binop5; simpl in Ht |- *; try done.
    destruct e1; simpl in Ht |- *; try done.
    destruct assume_val5; simpl in Ht |- *; try done.
    destruct e2; simpl in Ht |- *; try done.
    apply Is_true_true, andb_true_iff in Ht.
    destruct Ht.
    by apply Is_true_true.
  - rewrite /= !Is_true_true forallb_forall in Ht.
    by apply Is_true_true, Ht, elem_of_list_In.
Qed.
(********************* Properties of Assumption End **********************)

(* Because the instruction invariant can only be express by the weakestpre *)
(* directly, we have to add PC permission and alignment and legal range *)
(* conditions. *)
(* The uni_csr and uni_gpr are machine_csr and machine_gpr with existential *)
(* values because they can be changed by F. *)
Definition F_with_PC (i: bv 64) `{!islaG Σ} `{!threadG} : iProp Σ :=
  "PC" ↦ᵣ RVal_Bits i ∗
  ⌜bv_unsigned (bv_extract 0 2 i) = 0⌝ ∗
  ⌜(bv_unsigned F_code_addr) <= (bv_unsigned i) < (bv_unsigned F_code_end_addr)⌝ ∗
  "mtvec" # "bits" ↦ᵣ RVal_Bits F_mtvec ∗
  "pmp0cfg" # "bits" ↦ᵣ RVal_Bits device_cfg_when_F ∗
  "pmp1cfg" # "bits" ↦ᵣ RVal_Bits P_code_cfg_when_F ∗
  "pmp2cfg" # "bits" ↦ᵣ RVal_Bits F_code_cfg_when_F ∗
  "pmp3cfg" # "bits" ↦ᵣ RVal_Bits SP_code_cfg_when_F ∗
  "pmp4cfg" # "bits" ↦ᵣ RVal_Bits F_data_cfg_when_F ∗
  "pmp5cfg" # "bits" ↦ᵣ RVal_Bits P_data_cfg_when_F ∗
  "pmp6cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
  "pmp7cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
  reg_col dorami_sys_regs ∗ reg_col uni_csr ∗ reg_col uni_gpr ∗ reg_col pmp_regs ∗
  (bv_unsigned F_data_addr) ↦ₘ? 0x1000.

Lemma tcons_preservation `{!islaG Σ} `{!threadG} :
  ∀ i e tail,
  NoEvent (e :t: tail) ->
  NoStuckEval (e :t: tail) ->
  LegalReadReg (e :t: tail) ->
  LegalWriteReg (e :t: tail) ->
  LegalReadMem (e :t: tail) ->
  LegalWriteMem (e :t: tail) ->
  LegalAssumeReg (e :t: tail) ->
  LegalAssume (e :t: tail) ->
  □ illegal_PC -∗
  ▷(∀ t', (∃ label regs, ⌜trace_step (e:t:tail) regs label t'⌝) -∗
                    (∃ i, F_with_PC i)  -∗ WPasm t') -∗
  (F_with_PC i -∗ WPasm (e :t: tail)).
Proof.
  iIntros (i e tail HNoEvent HNoStuckEval HReadReg HWriteReg HReadMem HWriteMem HAssumeReg HAssume) "#Htrap Hnext Hstart".
  destruct e; try done.
  - destruct smt5.
    + destruct ty5.
      * iApply wp_declare_const_bool'.
        iIntros (n) "!>".
        iApply ("Hnext" with "[%]"); first by repeat econstructor.
        by iExists i.
      * iApply wp_declare_const_bv'.
        iIntros (n).
        iApply ("Hnext" with "[%]"); first by (repeat econstructor; intros; apply DeclareConstBitVecS').
        by iExists i.
      * iApply wp_declare_const_enum'.
        iIntros (n).
        iApply ("Hnext" with "[%]"); first by repeat econstructor.
        by iExists i.
      * done.
    + iApply wp_define_const'.
      rewrite wp_exp_eq /wp_exp_def.
      unfold NoStuckEval in HNoStuckEval.
      specialize (HNoStuckEval ltac:(done) (Smt (DefineConst vvar5 exp5) annot5 :t: tail) (rtc_refl _ _)).
      destruct HNoStuckEval as (v & Heq).
      iExists v.
      iSplitR; first done.
      iApply ("Hnext" with "[%]"); first by repeat econstructor.
      by iExists i.
    + iApply wp_assert'.
      rewrite wp_exp_eq /wp_exp_def.
      specialize (HNoStuckEval ltac:(done) (Smt (Assert exp5) annot5 :t:
                              tail) (rtc_refl _ _)).
      destruct HNoStuckEval as (v & Heq).
      iExists (Val_Bool v).
      iSplitR; first done.
      iExists v.
      iSplitR; first done.
      iIntros "!> ->".
      iApply ("Hnext" with "[%]"); first by repeat econstructor.
      by iExists i.
    + done.
  - iApply wp_branch'.
    iApply ("Hnext" with "[%]"); first by repeat econstructor.
    by iExists i.
  - specialize (HReadReg ltac:(done) (ReadReg name5 accessor_list5 valu5 annot5 :t: tail) (rtc_refl _ _)).
    destruct (legal_read_accessor_R _ _ _ HReadReg) as [? Hsafe].
    apply LegalRegAcc_R_destruct in HReadReg.
    destruct HReadReg as [[[[]|]|]|].
    + destruct s as [bv (->&->&->&?)].
      iApply (wp_read_reg' _ _ _ _ _ _ Hsafe).
      iSimpl in "Hstart".
      iDestruct "Hstart" as "[HPC Hstart]".
      assert (Hsafe' : ∃ x, read_accessor [] (RVal_Bits i) = Some x) by by exists (RVal_Bits i).
      destruct Hsafe' as [? Hsafe'].
      iApply (read_reg_acc _ _ _ _ _ _ Hsafe' with "[$HPC]").
      iIntros "HPC !> <-".
      iApply ("Hnext" with "[%]"); first by repeat econstructor.
      iExists i.
      iSimpl.
      by iFrame.
    + destruct s as [bv (->&->&->&?)].
      iApply (wp_read_reg' _ _ _ _ _ _ Hsafe).
      iSimpl in "Hstart".
      iDestruct "Hstart" as "(?&?&?&Hmtvec&?)".
      iApply (read_reg_struct with "[$Hmtvec]").
      iIntros "HPC !> ->".
      iApply ("Hnext" with "[%]"); first by repeat econstructor.
      iExists i.
      iSimpl.
      by iFrame.
    + destruct s as [bv (->&->&->&?)].
      iApply (wp_read_reg' _ _ _ _ _ _ Hsafe).
      iDestruct "Hstart" as "(?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&Hpmp&?)".
      assert (Hlk: pmp_regs !! 16%nat = Some (KindReg "pmp8cfg", StructShape [("bits", ExactShape (RVal_Bits SP_code_cfg))])) by done.
      iDestruct ((bi.equiv_entails_1_1 _ _ (reg_col_lookup _ _ _ Hlk)) with "[$Hpmp]") as "(%v & %Hv & Hreg & Hpmp)".
      iSimpl in "Hreg".
      iApply (read_reg_acc with "Hreg").
      { simpl in Hv. destruct v; try done.
        destruct l; first (simpl in Hv; destruct Hv; congruence).
        destruct l; last (simpl in Hv; destruct Hv; congruence).
        simpl in Hv. destruct Hv as (_ & Hv & _). destruct p.
        simpl in Hv. destruct Hv as [-> ->].
        unfold read_accessor.
        simpl.
        decide (decide (s = s)) with (eq_refl s).
        by simpl.
      }
      iIntros "Hreg !> ->".
      iApply ("Hnext" with "[%]"); first by repeat econstructor.
      iPoseProof ((bi.equiv_entails_1_2 _ _ (reg_col_lookup _ _ _ Hlk)) with "[$Hpmp Hreg]") as "Hpmp".
      { iExists v. iSplitR; first by iPureIntro. by iSimpl. }
      iExists i.
      by iFrame.
    + destruct s as [bv (->&->&->&?)].
      iApply (wp_read_reg' _ _ _ _ _ _ Hsafe).
      iDestruct "Hstart" as "(?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&Hpmp&?)".
      assert (Hlk: pmp_regs !! 17%nat = Some (KindReg "pmp9cfg", StructShape [("bits", BitsShape 8)])) by done.
      iDestruct ((bi.equiv_entails_1_1 _ _ (reg_col_lookup _ _ _ Hlk)) with "[$Hpmp]") as "(%v & %Hv & Hreg & Hpmp)".
      iSimpl in "Hreg".
      simpl in Hv. destruct v; try done.
      destruct l; first (simpl in Hv; destruct Hv; congruence).
      destruct l; last (simpl in Hv; destruct Hv; congruence).
      simpl in Hv. destruct Hv as (_ & [Hf Hv] & _). destruct p.
      simpl in Hf, Hv.
      unfold read_accessor.
      unfold valu_has_shape in Hv.
      destruct v; first destruct base_val5; try done.
      iApply (read_reg_acc with "Hreg").
      {
        unfold read_accessor.
        simpl.
        rewrite Hf.
        decide (decide (s = s)) with (eq_refl s).
        by simpl.
      }
      iIntros "Hreg !> ->".
      iApply ("Hnext" with "[%]"); first by repeat econstructor.
      iPoseProof ((bi.equiv_entails_1_2 _ _ (reg_col_lookup _ _ _ Hlk)) with "[$Hpmp Hreg]") as "Hpmp".
      { iExists (RegVal_Struct [("bits", RVal_Bits bv5)]). iSplitR; first by iPureIntro. rewrite Hf. by iSimpl. }
      iExists i.
      by iFrame.
    + destruct s as [bv (->&->&?)].
      iApply (wp_read_reg' _ _ _ _ _ _ Hsafe).
      iDestruct "Hstart" as "(?&?&?&?&?&?&?&?&?&?&?&?&Hsys&?&?&?&?)".
      assert (Hlk: dorami_sys_regs !! 0%nat = Some ((KindReg "rv_enable_zfinx", ExactShape (RVal_Bool false)))) by done.
      iDestruct ((bi.equiv_entails_1_1 _ _ (reg_col_lookup _ _ _ Hlk)) with "[$Hsys]") as "(%v & %Hv & Hreg & Hsys)".
      iSimpl in "Hreg".
      iApply (read_reg_nil with "Hreg").
      iIntros "Hreg !> ->".
      simpl in Hv.
      rewrite Hv.
      iApply ("Hnext" with "[%]"); first by repeat econstructor.
      iPoseProof ((bi.equiv_entails_1_2 _ _ (reg_col_lookup _ _ _ Hlk)) with "[$Hsys Hreg]") as "Hsys".
      { iExists v. iSplitR; first by iPureIntro. iSimpl. by rewrite Hv. }
      iExists i.
      by iFrame.
  - specialize (HWriteReg ltac:(done) (WriteReg name5 accessor_list5 valu5 annot5 :t: tail) (rtc_refl _ _)).
    apply LegalRegAcc_W_destruct in HWriteReg.
    destruct HWriteReg as [[|]|].
    + destruct s as [bv' (->&->&->)].
      iSimpl in "Hstart".
      iDestruct "Hstart" as "[HPC Hstart]".
      iApply (wp_write_reg' with "HPC").
      iIntros "!> HPC".
      iApply ("Hnext" with "[%]"); first by repeat econstructor.
      destruct (Sumbool.sumbool_and _ _ _ _ (BinInt.Z.eq_dec (bv_unsigned (bv_extract 0 2 bv')) 0) (Sumbool.sumbool_and _ _ _ _ (Z_le_dec (bv_unsigned F_code_addr) (bv_unsigned bv')) (Z_lt_dec (bv_unsigned bv')(bv_unsigned F_code_end_addr)))) as [[Hbv'1 Hbv'2]|].
      * iExists bv'.
        iSimpl.
        iDestruct "Hstart" as "(?&?&Hstart)".
        by iFrame.
      * iDestruct "Hstart" as "(%&%&?)".
        iPoseProof ("Htrap" with "[$HPC]") as "HPC"; first (iPureIntro; intuition).
        iFrame.
        iPureIntro.
        by intuition.
    + destruct s as [bv' (->&->&->)].
      iDestruct "Hstart" as "(?&?&?&?&?&?&?&?&?&?&?&?&?&?&Hgpr&?)".
      assert (Hlk: uni_gpr !!1%nat = Some ((KindReg "x1", BitsShape 64))) by done.
      iDestruct ((bi.equiv_entails_1_1 _ _ (reg_col_lookup _ _ _ Hlk)) with "[$Hgpr]") as "(%v & %Hv & Hreg & Hgpr)".
      iApply (wp_write_reg' with "Hreg").
      iIntros "!> Hreg".
      iApply ("Hnext" with "[%]"); first by repeat econstructor.
      iPoseProof ((bi.equiv_entails_1_2 _ _ (reg_col_lookup _ _ _ Hlk)) with "[$Hgpr Hreg]") as "Hgpr".
      { iExists (RVal_Bits bv'). by iFrame. }
      iExists i.
      by iFrame.
   + destruct s as [bv' (->&->&->)].
     iDestruct "Hstart" as "(?&?&?&?&?&?&?&?&?&?&?&?&?&Hcsr&?&?&?)".
     assert (Hlk: uni_csr!!2%nat = Some (KindReg "mcause", StructShape [("bits", BitsShape 64)])) by done.
     iDestruct ((bi.equiv_entails_1_1 _ _ (reg_col_lookup _ _ _ Hlk)) with "[$Hcsr]") as "(%v & %Hv & Hreg & Hcsr)".
     iSimpl in "Hreg".
      simpl in Hv. destruct v; try done.
      destruct l; first (simpl in Hv; destruct Hv; congruence).
      destruct l; last (simpl in Hv; destruct Hv; congruence).
      simpl in Hv. destruct Hv as (_ & [Hf Hv] & _). destruct p.
      simpl in Hf, Hv.
      unfold read_accessor.
      unfold valu_has_shape in Hv.
      destruct v; first destruct base_val5; try done.
     iApply (wp_write_reg_acc' with "Hreg"); first done.
      {
        unfold write_accessor.
        simpl.
        rewrite Hf.
        decide (decide (s = s)) with (eq_refl s).
        by simpl.
      }
     iIntros "!> Hreg".
     iApply ("Hnext" with "[%]"); first by repeat econstructor.
     iPoseProof ((bi.equiv_entails_1_2 _ _ (reg_col_lookup _ _ _ Hlk)) with "[$Hcsr Hreg]") as "Hcsr".
     { iExists (RegVal_Struct [("bits", RVal_Bits bv')]). rewrite Hf. by iFrame. }
     iExists i.
     by iFrame.
  - specialize (HReadMem ltac:(done)(ReadMem valu5 rkind addr num_bytes tag_value5 annot5 :t:
         tail) (rtc_refl _ _)).
    destruct valu5; try done.
    destruct base_val5; try done.
    destruct addr; try done.
    destruct base_val5; try done.
    destruct bv5.
    destruct bv0.
    rewrite /= Is_true_true !andb_true_iff in HReadMem.
    destruct HReadMem as [[[[[H1 H2] H3] H4] H5] H6]; simpl in * |- *.
    apply Neqb_ok in H1, H2.
    apply N.ltb_lt in H3.
    apply Z.leb_le in H4, H5, H6.
    assert (Heq1 : {addr : bv 64 | (bv_to_bvn addr) =  (@bv_to_bvn bvn_n0 bvn_val0)}) by by apply bvn_to_bv'.
    destruct Heq1 as [addr Heq1].
    rewrite -Heq1 in H4, H5, H6 |- *.
    replace (bvn_unsigned addr) with (bv_unsigned addr) in H4, H5, H6 |- * by done.
    assert (Heq2 : {data : bv (num_bytes * 8) | (bv_to_bvn data) =  (@bv_to_bvn bvn_n bvn_val)}).
    {apply bvn_to_bv'. rewrite /= H2; by apply N.mul_comm. }
    destruct Heq2 as [data Heq2].
    rewrite -Heq2.
    iDestruct "Hstart" as "(?&%&%&?&?&?&?&?&?&?&?&?&?&?&?&?&Hmem)".
    iDestruct (mem_mapsto_uninit_split (bvn_unsigned addr - bv_unsigned F_data_addr) (bv_unsigned F_data_addr) _ 0x1000 with "Hmem") as "[HM1 HM2]" ; first lia.
    iDestruct (mem_mapsto_uninit_split (Z.of_N num_bytes) _ _ _ with "HM2") as "[HM2 HM3]"; first lia.
    replace (bv_unsigned F_data_addr +
           (bvn_unsigned addr - bv_unsigned F_data_addr)) with (bvn_unsigned addr) by lia.
    iDestruct (mem_mapsto_uninit_to_mapsto with "HM2") as "(%num_bits&%vmem&Hmem)".
    rewrite N2Z.id.
    iDestruct "Hmem" as "[-> Hmem]".
    iApply (wp_read_mem' with "Hmem"); first [lia|done|trivial].
    iIntros "/= !> -> Hmem".
    iApply ("Hnext" with "[%]"); first by repeat econstructor.
    iPoseProof (mem_mapsto_mapsto_to_uninit with "Hmem") as "HM2".
    replace (Z.of_N ((num_bytes * 8) `div` 8)) with (Z.of_N num_bytes) by lia.
    iPoseProof (mem_mapsto_uninit_combine with "HM2 HM3") as "HM2"; first lia.
    replace (bv_unsigned addr) with (bv_unsigned F_data_addr + (bv_unsigned addr - bv_unsigned F_data_addr)) by lia.
    iPoseProof (mem_mapsto_uninit_combine with "HM1 HM2") as "Hmem"; first lia.
    iExists i.
    unfold F_with_PC.
    liARun.
    by iFrame.
  - specialize (HWriteMem ltac:(done) (WriteMem valu5 wkind addr data num_bytes tag_value5 annot5 :t:
        tail) (rtc_refl _ _)).
    destruct valu5; try done.
    destruct base_val5; try done.
    destruct addr; try done.
    destruct base_val5; try done.
    destruct bv5.
    destruct data; try done.
    destruct base_val5; try done.
    destruct bv5.
    rewrite /= Is_true_true !andb_true_iff in HWriteMem.
    destruct HWriteMem as [[[[[H1 H2] H3] H4] H5] H6]; simpl in * |- *.
    apply Neqb_ok in H1, H2.
    apply N.ltb_lt in H3.
    apply Z.leb_le in H4, H5, H6.
    assert (Heq1 : {addr : bv 64 | (bv_to_bvn addr) =  (@bv_to_bvn bvn_n bvn_val)}) by by apply bvn_to_bv'.
    destruct Heq1 as [addr Heq1].
    rewrite -Heq1 in H4, H5, H6 |- *.
    replace (bvn_unsigned addr) with (bv_unsigned addr) in H4, H5, H6 |- * by done.
    assert (Heq2 : {data : bv (num_bytes * 8) | (bv_to_bvn data) =  (@bv_to_bvn bvn_n0 bvn_val0)}).
    {apply bvn_to_bv'. rewrite /= H2; by apply N.mul_comm. }
    destruct Heq2 as [data Heq2].
    rewrite -Heq2.
    iDestruct "Hstart" as "(?&%&%&?&?&?&?&?&?&?&?&?&?&?&?&?&Hmem)".
    iDestruct (mem_mapsto_uninit_split (bvn_unsigned addr - bv_unsigned F_data_addr) (bv_unsigned F_data_addr) _ 0x1000 with "Hmem") as "[HM1 HM2]" ; first lia.
    iDestruct (mem_mapsto_uninit_split (Z.of_N num_bytes) _ _ _ with "HM2") as "[HM2 HM3]"; first lia.
    replace (bv_unsigned F_data_addr +
           (bvn_unsigned addr - bv_unsigned F_data_addr)) with (bvn_unsigned addr) by lia.
    iDestruct (mem_mapsto_uninit_to_mapsto with "HM2") as "(%num_bits&%vmem&Hmem)".
    rewrite N2Z.id.
    iDestruct "Hmem" as "[-> Hmem]".
    iApply (wp_write_mem' with "Hmem"); first [lia|done|trivial].
    iIntros "/= !> Hmem".
    iApply ("Hnext" with "[%]"); first by repeat econstructor.
    iPoseProof (mem_mapsto_mapsto_to_uninit with "Hmem") as "HM2".
    replace (Z.of_N ((num_bytes * 8) `div` 8)) with (Z.of_N num_bytes) by lia.
    iPoseProof (mem_mapsto_uninit_combine with "HM2 HM3") as "HM2"; first lia.
    replace (bv_unsigned addr) with (bv_unsigned F_data_addr + (bv_unsigned addr - bv_unsigned F_data_addr)) by lia.
    iPoseProof (mem_mapsto_uninit_combine with "HM1 HM2") as "Hmem"; first lia.
    iExists i.
    unfold F_with_PC.
    liARun.
    by iFrame.
  - iApply wp_branch_address'.
    iApply ("Hnext" with "[%]"); first by repeat econstructor.
    by iExists i.
  - iApply wp_barrier'.
    iApply ("Hnext" with "[%]"); first by repeat econstructor.
    by iExists i.
  - iApply wp_assume_reg'.
    rewrite /= Is_true_eq andb_true_iff in HAssumeReg.
    destruct HAssumeReg as [HAssumeReg _].
    apply Is_true_true in HAssumeReg.
    apply LegalRegAcc_A_destruct in HAssumeReg.
    destruct HAssumeReg as [].
    + destruct s as [bv (->&->&->&?&?)].
      iDestruct "Hstart" as "(?&?&?&?&?&?&?&?&?&?&?&?&Hsys&?&?&?&?)".
      assert (Hlk: dorami_sys_regs !! 10%nat = Some (KindReg "rv_htif_tohost", ExactShape (RVal_Bits (BV 64 0x0000000040001000)))) by done.
      iDestruct ((bi.equiv_entails_1_1 _ _ (reg_col_lookup _ _ _ Hlk)) with "[$Hsys]") as "(%v & %Hv & Hreg & Hsys)"; simpl.
      iApply (read_reg_acc with "Hreg"); try done.
      iIntros "Hreg".
      iSplit.
      {iPureIntro. rewrite Hv. do 2 f_equal. by apply bvn_eq; split. }
      iModIntro.
      iApply ("Hnext" with "[%]"); first by repeat econstructor.
      iPoseProof ((bi.equiv_entails_1_2 _ _ (reg_col_lookup _ _ _ Hlk)) with "[$Hsys Hreg]") as "Hsys".
      { iExists v. iSplitR; first by iPureIntro. by iSimpl. }
      iExists i.
      by iFrame.
    + destruct s as [bv (->&->&->&?&?)].
     iDestruct "Hstart" as "(?&?&?&?&?&?&?&?&?&?&?&?&Hsys&?&?&?&?)".
      assert (Hlk: dorami_sys_regs !! 13%nat = Some ((KindReg "mseccfg", ExactShape (RegVal_Struct [("bits", RVal_Bits (BV 64 0x07))])))) by done.
      iDestruct ((bi.equiv_entails_1_1 _ _ (reg_col_lookup _ _ _ Hlk)) with "[$Hsys]") as "(%v & %Hv & Hreg & Hsys)".
      iSimpl in "Hreg".
      iApply (read_reg_acc with "Hreg").
      { simpl in Hv. rewrite Hv. cbv. done. }
      iIntros "Hreg".
      iSplit.
      {iPureIntro. simpl. do 2 f_equal. by apply bvn_eq; split. }
      iModIntro.
      iApply ("Hnext" with "[%]"); first by repeat econstructor.
      iPoseProof ((bi.equiv_entails_1_2 _ _ (reg_col_lookup _ _ _ Hlk)) with "[$Hsys Hreg]") as "Hsys".
      { iExists v. iSplitR; first by iPureIntro. by iSimpl. }
      iExists i.
      by iFrame.
  - iApply wp_assume'.
    destruct a_exp5; try done.
    destruct binop5; try done.
    destruct a_exp5_1; try done.
    destruct assume_val5; try done.
    destruct a_exp5_2; try done.
    simpl in HAssume.
    rewrite /= Is_true_eq andb_true_iff in HAssume.
    destruct HAssume as [HAssume _].
    apply Is_true_true in HAssume.
    apply LegalAssumeEvent_destruct in HAssume.
    destruct HAssume as [[[[[]|]|]|]|].
    all: destruct a as (->&->&->).
    all: iDestruct "Hstart" as "(?&%&%&?&?&?&?&?&?&?&?&?&?&?&?&?&?)".
    all: liARun.
    all: iModIntro.
    all: iApply ("Hnext" with "[%]"); first (econstructor; exists (assume_regs_map F_mtvec); by econstructor).
    all: iExists i.
    all: unfold F_with_PC.
    all: liARun.
    all: iFrame.
    Unshelve.
    all: prepare_sidecond.
    all: bv_solve.
  - iApply wp_abstract_primop'.
    iApply ("Hnext" with "[%]"); first by repeat econstructor.
    by iExists i.

  Unshelve.
  all: by refine (assume_regs_map F_mtvec).
Qed.

Lemma tcases_preservation `{!islaG Σ} `{!threadG} :
  ∀ i es,
  es ≠ [] →
  ▷ (∀ t, ⌜t ∈ es⌝ -∗
        ((∃ i, F_with_PC i) -∗ WPasm t)) -∗
  (F_with_PC i -∗ WPasm (tcases es)).
Proof.
  iIntros (i es ?) "Hnext Hstart".
  iApply wp_cases'; first done.
  iIntros (t) "%Hin !>".
  iApply "Hnext"; first done.
  by iExists i.
Qed.

Definition trace_contract `{!islaG Σ} `{!threadG} :=
  ∀ i t,
  NoEvent t ->
  NoEmptyCases t ->
  NoStuckEval t ->
  LegalReadReg t ->
  LegalWriteReg t ->
  LegalReadMem t ->
  LegalWriteMem t ->
  LegalAssumeReg t ->
  LegalAssume t ->
  □ illegal_PC -∗
  ((∃ i, F_with_PC i) -∗ WPasm tnil) -∗
  (F_with_PC i -∗ WPasm t).

Lemma valid_trace_contract `{!islaG Σ} `{!threadG} : trace_contract.
Proof.
  iLöb as "IH".
  (* iIntros (i t Hnoevent Hnotempty Hnostuck Hreadreg Hwritereg Hreadmem Hwritemem Hassumereg Hassume [Htrace | [Htrace Hpc]] ) "#Htrap Hnext Hfirm"; first destruct t eqn:Heq. *)
  iIntros (i t Hnoevent Hnotempty Hnostuck Hreadreg Hwritereg Hreadmem Hwritemem Hassumereg Hassume) "#Htrap Hnext Hfirm"; first destruct t eqn:Heq.
  - iApply "Hnext".
    by iExists i.
  - iApply (tcons_preservation with "[//] [Hnext]"); try done.
    iIntros (t2) "!> [%label [%regs %Hstep]] [%i' Hfirm]".
    iApply ("IH" with "[%] [%] [%] [%] [%] [%] [%] [%] [%] Htrap Hnext Hfirm").
    + by eapply (trace_step_NoEvent (e:t:i0) _ label t2).
    + by eapply (trace_step_NoEmptyCases (e:t:i0) _ label t2).
    + intros Hnonil t' Hrtc.
      apply (Hnostuck ltac:(done) t').
      refine (rtc_l _ _ _ _ _ Hrtc).
      exists label, regs.

      split; [done | by inversion Hstep].
    + intros Hnonil t' Hrtc.
      apply (Hreadreg ltac:(done) t').
      refine (rtc_l _ _ _ _ _ Hrtc).
      exists label, regs.
      split; [done | by inversion Hstep].
    + intros Hnonil t' Hrtc.
      apply (Hwritereg ltac:(done) t').
      refine (rtc_l _ _ _ _ _ Hrtc).
      exists label, regs.
      split; [done | by inversion Hstep].
    + intros Hnonil t' Hrtc.
      apply (Hreadmem ltac:(done) t').
      refine (rtc_l _ _ _ _ _ Hrtc).
      exists label, regs.
      split; [done | by inversion Hstep].
    + intros Hnonil t' Hrtc.
      apply (Hwritemem ltac:(done) t').
      refine (rtc_l _ _ _ _ _ Hrtc).
      exists label, regs.
      split; [done | by inversion Hstep].
    + by apply (trace_step_LegalAssumeReg (e:t:i0) regs label t2).
    + by apply (trace_step_LegalAssume (e:t:i0) regs label t2).
  - iApply (tcases_preservation with "[Hnext]"); try done.
    { simpl in Hnotempty.
      rewrite /= !Is_true_true !andb_true_iff in Hnotempty.
      destruct Hnotempty as [Hemp _].
      by apply bool_decide_eq_true_1 in Hemp.
      }
    iIntros (subt) "!> %Hin [%y Hfirm]".
    iApply ("IH" with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [//] Hnext Hfirm").
    + rewrite /= !Is_true_true forallb_forall in Hnoevent.
      rewrite Is_true_true.
      by apply Hnoevent, elem_of_list_In.
    + rewrite /= !Is_true_true andb_true_iff in Hnotempty.
      destruct Hnotempty as [_ Hnotempty].
      rewrite forallb_forall in Hnotempty.
      rewrite Is_true_true.
      by apply Hnotempty, elem_of_list_In.
    + rewrite /= /NoStuckEval in Hnostuck.
      intros Hnonil t' Hrtc.
      apply (Hnostuck ltac:(done) t').
      refine (rtc_l _ _ _ _ _ Hrtc).
      eexists. exists (assume_regs_map F_mtvec).
      split; [ by constructor | done] .
    + rewrite /= /LegalReadReg in Hreadreg.
      intros Hnonil t' Hrtc.
      apply (Hreadreg ltac:(done) t').
      refine (rtc_l _ _ _ _ _ Hrtc).
      eexists. exists (assume_regs_map (F_mtvec)).
      split; [ by constructor | done] .
    + rewrite /= /LegalWriteReg in Hwritereg.
      intros Hnonil t' Hrtc.
      apply (Hwritereg ltac:(done) t').
      refine (rtc_l _ _ _ _ _ Hrtc).
      eexists. exists (assume_regs_map F_mtvec).
      split; [ by constructor | done] .
    + rewrite /= /LegalReadMem in Hreadmem.
      intros Hnonil t' Hrtc.
      apply (Hreadmem ltac:(done) t').
      refine (rtc_l _ _ _ _ _ Hrtc).
      eexists. exists (assume_regs_map F_mtvec).
      split; [ by constructor | done] .
    + rewrite /= /LegalWriteMem in Hwritemem.
      intros Hnonil t' Hrtc.
      apply (Hwritemem ltac:(done) t').
      refine (rtc_l _ _ _ _ _ Hrtc).
      eexists. exists (assume_regs_map F_mtvec).
      split; [ by constructor | done] .
    + rewrite /= !Is_true_true forallb_forall in Hassumereg.
      rewrite Is_true_true.
      by apply Hassumereg, elem_of_list_In.
    + rewrite /= !Is_true_true forallb_forall in Hassume.
      rewrite Is_true_true.
      by apply Hassume, elem_of_list_In.
Qed.

(* This represents the instruction permission of F. *)
Definition F_instrs `{!islaG Σ} `{!threadG} : iProp Σ :=
  ([∗ list] i ↦ _ ∈ replicate 1023 (), (∃ t, instr (0x80020000 + i * 4) (Some t) ∗ ⌜NoEmptyCases t ∧ NoEvent t ∧ NoStuckEval t ∧ LegalReadReg t ∧ LegalWriteReg t ∧ LegalReadMem t ∧ LegalWriteMem t ∧ LegalAssumeReg t ∧ LegalAssume t⌝)).

(* The specification of the universal contract of F. *)
Definition universal_spec `{!islaG Σ} `{!threadG} csr gpr mem : iProp Σ :=
  F F_mtvec F_pmpcfgs csr gpr mem ∗
  instr_pre (bv_unsigned SP_code_addr) (
     ∃ csr gpr mem, F F_mtvec SP_pmpcfgs csr gpr mem ∗
     True
).

Lemma bv_extract_divisible {n} l (b : bv n) :
  bv_unsigned (bv_extract 0 l b) = 0 -> ∃ quo, bv_unsigned b = 2 ^ Z.of_N l * quo.
Proof.
  rewrite bv_extract_unsigned /bv_wrap /bv_modulus.
  replace (bv_unsigned b ≫ Z.of_N 0) with (bv_unsigned b) by done.
  intro Hmod.
  apply Z_div_exact_full_2 in Hmod; last lia.
  by exists (bv_unsigned b `div` 2 ^ Z.of_N l).
Qed.

Theorem universal_contract `{!islaG Σ} `{!threadG} :
  ∀ (i: bv 64) csr gpr mem,
  bv_unsigned (bv_extract 0 2 i) = 0 ->
  (bv_unsigned F_code_addr) <= (bv_unsigned i) < (bv_unsigned F_code_end_addr) ->
  length csr = 4%nat ->
  length gpr = 5%nat ->
  □ illegal_PC -∗
  F_instrs -∗
  instr (bv_unsigned F_code_end_addr) (Some exit_firmware.a0.a0) -∗
  instr_body (bv_unsigned i) (universal_spec csr gpr mem).
Proof.
  iLöb as "IH".
  iIntros (i csr gpr mem Hi1 Hi2 Hcsr Hgpr) "#Htrap #Hinsts #Hexit".
  assert (Hlk: (replicate 1023 ()) !! (Z.to_nat (((bv_unsigned i) -  (bv_unsigned F_code_addr)) / 4)) = Some ()).
  { apply lookup_replicate. split; first done.
    rewrite /F_code_addr /F_code_end_addr !bv_unsigned_BV in Hi2 |- *. lia.
  }
  iPoseProof (big_sepL_delete _ _ _ _ Hlk) as "[Helem _]".
  iPoseProof ("Helem" with "[$Hinsts]") as "[#(%t & Hinst & (%HNoEmptyCase & %HNoEvent & %HNoStuck & %HReadReg & %HWriteReg & %HReadMem & %HWriteMem & %HAssumeReg & %HAssume)) _]".
  replace (2147614720 + Z.to_nat ((bv_unsigned i - bv_unsigned F_code_addr) `div` 4) * 4) with (bv_unsigned i).
  2:{
    apply bv_extract_divisible in Hi1.
    destruct Hi1 as [quo Hquo].
    rewrite /F_code_addr !bv_unsigned_BV !Hquo in Hi2 |- *. lia.
  }
  iApply (instr_pre_intro_Some with "Hinst").
  iClear "Helem Hinst".
  iIntros "[Hfirm Hsafe] HPC".
  iApply (valid_trace_contract i t HNoEvent HNoEmptyCase HNoStuck HReadReg HWriteReg HReadMem HWriteMem HAssumeReg HAssume with "[//] [Hsafe]").
  2:{
  do 5 (destruct csr as [|? csr]; try done).
  do 6 (destruct gpr as [|? gpr]; try done).
  iDestruct "Hfirm" as "(Hmtvec&?&?&?&?&?&?&?&?&Hsys&Hcsr&Hgpr&Hpmp&Hmem)".
  unfold F_with_PC.
  iPoseProof (csr_equiv with "[Hcsr]") as "Hcsr"; first by (iExists [b;b0;b1;b2]; iFrame).
  iPoseProof (gpr_equiv with "[Hgpr]") as "Hgpr"; first by (iExists [b3; b4; b5; b6; b7]; iFrame).
  liARun.
  iApply (mem_mapsto_mapsto_to_uninit with "Hmem").
  Unshelve. all: prepare_sidecond; bv_solve. }
  clear i Hi1 Hi2 Hlk t HNoEvent HNoEmptyCase HNoStuck HReadReg HWriteReg HReadMem HWriteMem HAssumeReg HAssume.
  iIntros "[%i (HPC&%Hi1&%Hi2&Hmtvec& Hp0&Hp1&Hp2&Hp3&Hp4&Hp5&Hp6&Hp7&Hsys&Hcsr&Hgpr&Hpmp&Hmem)]".
      assert (Hlk: (replicate 1023 ()) !! (Z.to_nat (((bv_unsigned i) -  (bv_unsigned F_code_addr)) / 4)) = Some ()).
    { apply lookup_replicate. split; first done.
      rewrite /F_code_addr /F_code_end_addr !bv_unsigned_BV in Hi2 |- *; lia.
    }
    iPoseProof (big_sepL_delete _ _ _ _ Hlk) as "[Helem _]".
    iPoseProof ("Helem" with "[$Hinsts]") as "[#(%t & Hinst & (%HNoEmptyCase & %HNoEvent & %HNoStuck & %HReadReg & %HWriteReg & %HReadMem & %HWriteMem & %HAssumeReg & %HAssume)) _]".
    replace (2147614720 + Z.to_nat ((bv_unsigned i - bv_unsigned F_code_addr) `div` 4) * 4) with (bv_unsigned i).
    2:{
      apply bv_extract_divisible in Hi1.
      destruct Hi1 as [quo Hquo].
      rewrite /F_code_addr !bv_unsigned_BV !Hquo in Hi2 |- *. lia.
    }
    iApply (wp_next_instr with "[$HPC] Hinst").
    iIntros "!> HPC".
    iClear "Helem Hinst".
    iApply (valid_trace_contract i t HNoEvent HNoEmptyCase HNoStuck HReadReg HWriteReg HReadMem HWriteMem HAssumeReg HAssume with "[//] [Hsafe]").
    2:{
    unfold F_with_PC.
    liARun; by iFrame. }
    iIntros "Hstate".
    clear i csr gpr mem Hi1 Hi2 Hcsr Hgpr Hlk t HNoEvent HNoEmptyCase HNoStuck HReadReg HWriteReg HReadMem HWriteMem HAssumeReg HAssume.
    iDestruct "Hstate" as "[%i (HPC&%Hi1&%Hi2&Hfirm)]".
          iDestruct "Hfirm" as "(?&?&?&?&?&?&?&?&?&Hsys&Hcsr&Hgpr&Hpmp&Hmem)".
      iPoseProof (csr_equiv with "Hcsr") as "[%csr [%Hcsr ?]]".
      iPoseProof (gpr_equiv with "Hgpr") as "[%gpr [%Hgpr ?]]".
      iDestruct (mem_mapsto_uninit_to_mapsto with "Hmem") as "(%n&%mem&->&Hmem)".
      iSpecialize ("IH" $! i csr gpr mem Hi1 Hi2 _ _ with "Htrap Hinsts Hexit").
      iApply (wp_next_instr_pre with "[$HPC] IH [-]").
      iFrame "Hsafe".
      simpl.
      liARun.
      by iFrame.
      Unshelve.
      1: simpl; by f_equal.
      1: done.
Qed.
