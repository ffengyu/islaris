From iris.program_logic Require Export weakestpre.
From isla Require Export opsem ghost_state.

Inductive AccessType : Set :=
| Read
| ReadWrite
| Execute.

(* TODO: adapt it to support more pmp entries. *)
Definition pmp_regs (entries: list (bv 64 * bv 8)) :=
  match entries with
  | (cfg0, addr0) :: (cfg1, addr1) :: _ => [
      (KindReg "pmpaddr0", ExactShape (RVal_Bits addr0));
      (KindReg "pmpaddr1", ExactShape (RVal_Bits addr1));
      (KindReg "pmpaddr2", BitsShape 64);
      (KindReg "pmpaddr3", BitsShape 64);
      (KindReg "pmp0cfg", ExactShape (RVal_Bits cfg0));
      (KindReg "pmp1cfg", ExactShape (RVal_Bits cfg1));
      (KindReg "pmp2cfg", BitsShape 64);
      (KindReg "pmp3cfg", BitsShape 64)
    ]
  | _ => []
  end.

Definition bv_to_bool {n} (x : bv n) : bool :=
  bool_decide (bv_unsigned x ≠ 0).

(* If the cur_privilege has the write acess, then it only matches the *)
(* ReadWrite branch because we give the full perm to write access and *)
(* half perm to read access. If the write access also matches the read *)
(* branch, then we will have 1.5 perm. *)
Definition pmp_check_rwx (R: bool) (W: bool) (X: bool) (acc: AccessType) :=
  match acc with
  | Read        => R && negb W
  | ReadWrite   => W
  | Execute     => X
  end.

(* Here we assume the mseccfg.MML is 0b1. *)
Definition pmp_check_perm (cfg: bv 8) (p: string) (acc: AccessType): bool :=
  let L := bv_to_bool((bv_extract 7 1 cfg)) in
  let X := bv_to_bool((bv_extract 2 1 cfg)) in
  let W := bv_to_bool((bv_extract 1 1 cfg)) in
  let R := bv_to_bool((bv_extract 0 1 cfg)) in
  match L, R, W, X with
  | true, false, true, _ =>
      match acc with
      | Execute => true
      | Read    => String.eqb p "Machine" && X
      | _       => false
      end
  | false, false, true, _ =>
      match acc with
      | Read    => negb $ String.eqb p "Machine" && negb X
      | ReadWrite   => String.eqb p "Machine" || X
      | _       => false
      end
  | true, true, true, true =>
      match acc with
      | Read    => true
      | _       => false
      end
  | _, _, _, _ =>
    if String.eqb p "Machine" && L
    then pmp_check_rwx R W X acc
    else false
  end.

(* Assume the addr mode is NAPOT which DORAMI uses *)
(* TODO: check if the addr is NAPOT? *)
Definition pmpAddrRange (pmpaddr: bv 64) : Z * Z :=
  let mask := bv_xor pmpaddr (bv_add_Z pmpaddr 1) in
  let lo := bv_add pmpaddr (bv_not mask) in
  let len := bv_add_Z mask 1 in
  (bv_unsigned lo, bv_unsigned len).

Definition interp_pmp_perm `{!heapG Σ} (pmpaddr: bv 64) (acc: AccessType): iProp Σ :=
  let (lo, len) := pmpAddrRange pmpaddr in
  match acc with
  | Read      => lo ↦ₘ{DfracOwn (1 / 2)}? len
  | ReadWrite => lo ↦ₘ? len
  | Execute   => ∃ n, ⌜Z.to_N len = (64 * N.of_nat n)%N⌝ ∗ [∗ list] i ↦ _ ∈ replicate n (),
                    ∃ v, instr (lo + 64 * i) v
  end.

(* First choice: gain big chunk from a pmp rule *)
(* It says that we need the pmpcfg or pmpaddr perm if we want the *)
(* corresponding perms. *)
(* TODO: the user/supervisor mode don't have pmp perm but should have the *)
(* capability to gain the corresponding perms. *)
Definition interp_pmp_addr_access  `{!heapG Σ} (addr: bv 64) (cfg: bv 8) (p: sail_name) (acc: AccessType): iProp Σ :=
  ⌜pmp_check_perm cfg p acc⌝ -∗ interp_pmp_perm addr acc.

(* If we have this def in the precondition, we guarantee that we can *)
(* gain the corresponding ghost state(mem perm or instr) from every *)
(* perm ONCE. If we apply the wand to gain the perms, then we cannot do it *)
(* again. Even if the pmpcfg or pmpaddr change after the application of *)
(* wand, we cannot gain the new perm from them. *)
(* TODO: Provide a way to recover the wand so we can change the pmp rules. *)
(* Probably the reverse wand? *)
(* FIXME: only the first matching one provide the perm. *)
Definition interp_pmp `{!heapG Σ} (entries: list (bv 64 * bv 8)) (p : sail_name) : iProp Σ :=
  [∗ list] ent ∈ entries, let pmpaddr := ent.1 in let pmpcfg := ent.2 in
    interp_pmp_addr_access pmpaddr pmpcfg p Read ∗
    interp_pmp_addr_access pmpaddr pmpcfg p ReadWrite ∗
    interp_pmp_addr_access pmpaddr pmpcfg p Execute.

(* Second choice: check single bytes or instruction. *)
Fixpoint pmp_single_access (entries: list (bv 64 * bv 8)) (a: Z) (p: string) (acc: AccessType): bool :=
  match entries with
  | ent :: entries' =>
    let (pmpaddr, pmpcfg) := ent in
    let (lo, len) := pmpAddrRange pmpaddr in
    let access_len := match acc with Execute => 7 | _ => 0 end in
    if (andb (Z.leb lo a) (Z.leb (a + access_len) (lo + len)))
      then pmp_check_perm pmpcfg p acc
      else pmp_single_access entries' a p acc
  | []             => false
  end.

Definition interp_pmp_single_access `{!heapG Σ} (a: Z) (acc: AccessType) : iProp Σ :=
  match acc with
  | Read      => a ↦ₘ{DfracOwn (1 / 2)}? 1
  | ReadWrite => a ↦ₘ? 1
  | Execute   => ∃ trace, instr a trace
  end.

(* Every time we want to access something, we check if the cur_privilege *)
(* and pmp entries satisfy the pure proposition in the antecedent of the *)
(* wand. *)
Definition interp_pmp' `{!heapG Σ} (entries: list (bv 64 * bv 8)) (p: string) : iProp Σ :=
  [∗ list] a ↦ _ ∈ replicate (2 ^ 64) (),
    (⌜pmp_single_access entries (Z.of_nat a) p Read⌝ -∗ interp_pmp_single_access a Read) ∗
    (⌜pmp_single_access entries (Z.of_nat a) p ReadWrite⌝ -∗ interp_pmp_single_access a ReadWrite) ∗
    (⌜pmp_single_access entries (Z.of_nat a) p Execute⌝ -∗ interp_pmp_single_access a Execute).

(* TODO: *)
(* 1. how to change the pmp after fetching the perm from this def? Give a *)
(* way to recover the wand given the full perms fetched from pmp before? *)
(* 2. how to remove the duplicated perms? For example, in the verification *)
(* of memcpy we have the `src ↦ᵣ srcdata` and from pmp we can infer *)
(* anoterh perms for src. *)
