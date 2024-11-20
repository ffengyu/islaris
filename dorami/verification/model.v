Require Export isla.riscv64.riscv64.
From isla.dorami Require Export P2F.instrs.
From isla.dorami Require Export exit_firmware.instrs.
From isla.dorami Require Export Sally_Port.instrs.
From isla.dorami Require Export P_entry.instrs.

(* PMP grain and pmp addr mode *)
(* | REGION       | ADDRESS    | LEN              | *)
(* |--------------|------------|------------------| *)
(* | DEVICE       | 0x00000000 | 0x80000000(2^31) | *)
(* | P/CODE       | 0x80000000 | 0x20000(2^17)    | *)
(* | F/CODE       | 0x80020000 | 0x1000(2^12)     | *)
(* | SP/CODE      | 0x80021000 | 0x1000(2^12)     | *)
(* | F/DATA       | 0x80022000 | 0x1000(2^12)     | *)
(* | P/DATA       | 0x80040000 | 0x20000(2^17)    | *)
(* | SP/CODE      | 0x80021000 | 0x1000(2^12)     | *)
Definition device_addr := (BV 64 0x00000000).
Definition P_code_addr := (BV 64 0x80000000).
Definition F_code_addr := (BV 64 0x80020000).
Definition F_code_end_addr := (BV 64 0x80020ffc).
Definition SP_code_addr := (BV 64 0x80021000).
Definition F_data_addr := (BV 64 0x80022000).
Definition P_data_addr := (BV 64 0x80040000).

Definition device_pmpaddr := (BV 64 0x7ffffff).
Definition P_code_pmpaddr := (BV 64 0x80001fff).
Definition F_code_pmpaddr := (BV 64 0x800200ff).
Definition SP_code_pmpaddr := (BV 64 0x800210ff).
Definition F_data_pmpaddr := (BV 64 0x800220ff).
Definition P_data_pmpaddr := (BV 64 0x80041fff).

(* PMP cfg when monitor, or osbi, or sally port executes. *)
(* Region [0x0, DEVICE] is S/U-mode only. *)
(* | REGION       | MONITOR EXEC | OSBI EXEC | SP EXEC  | *)
(* |--------------|--------------|-----------|----------| *)
(* | DEVICE       | 1e|AAWR      | 1e|AAWR   | 0        | *)
(* | P/CODE       | 9D|LAAXR     | 98|LAA    | 0        | *)
(* | F/CODE       | 98|LAA       | 9d|LAAXR  | 0        | *)
(* | SP/CODE      | 98|LAA       | 98|LAA    | 0        | *)
(* | F/DATA       | 98|LAA       | 9b|LAAWR  | 0        | *)
(* | P/DATA       | 9b|LAAWR     | 98|LAA    | 0        | *)
(* | SP/CODE      | 9d|LAAXR     | 9d|LAAXR  | 9d|LAAXR | *)

(* PMP configuration in pmpcfg0 when P exec. *)
Definition device_cfg_when_P := (BV 8 0x1e).
Definition P_code_cfg_when_P := (BV 8 0x9d).
Definition F_code_cfg_when_P := (BV 8 0x98).
Definition SP_code_cfg_when_P := (BV 8 0x98).
Definition F_data_cfg_when_P := (BV 8 0x98).
Definition P_data_cfg_when_P := (BV 8 0x9b).

(* PMP configuration in pmpcfg0 when firmware exec. *)
Definition device_cfg_when_F := (BV 8 0x1e).
Definition P_code_cfg_when_F := (BV 8 0x98).
Definition F_code_cfg_when_F := (BV 8 0x9d).
Definition SP_code_cfg_when_F := (BV 8 0x98).
Definition F_data_cfg_when_F := (BV 8 0x9b).
Definition P_data_cfg_when_F := (BV 8 0x98).

(* PMP configuration in pmpcfg0 when sallyport exec. *)
Definition components_cfg_when_SP := (BV 8 0x00).
(* PMP configuration in pmpcfg0 when P_entry exec. *)
Definition SP_code_cfg_when_P_entry := (BV 8 0x9d).
(* PMP configuration of SallyPort in pmpcfg2 *)
Definition SP_code_cfg := (BV 8 0x9d).

Definition P_mtvec := P_code_addr.
Definition P2F_code_size := 0x2c.
Definition P_entry_code_size := 0x1c.
Definition P2F_code_addr := bv_sub F_code_addr (BV 64 P2F_code_size).
Definition F_mtvec := F_code_addr.

(* pmp0cfg - pmp5cfg fields in pmpcfg0 register when P exec. *)
Definition P_pmpcfgs :=
  [device_cfg_when_P; P_code_cfg_when_P;
   F_code_cfg_when_P; SP_code_cfg_when_P;
   F_data_cfg_when_P; P_data_cfg_when_P].

(* pmp0cfg - pmp5cfg fields in pmpcfg0 register when F exec. *)
Definition F_pmpcfgs :=
  [device_cfg_when_F; P_code_cfg_when_F;
   F_code_cfg_when_F; SP_code_cfg_when_F;
   F_data_cfg_when_F; P_data_cfg_when_F].

(* pmp0cfg - pmp5cfg fields in pmpcfg0 register when SallyPort exec. *)
Definition SP_pmpcfgs :=
  [components_cfg_when_SP; components_cfg_when_SP;
   components_cfg_when_SP; components_cfg_when_SP;
   components_cfg_when_SP; components_cfg_when_SP].

(* pmp0cfg - pmp5cfg fields in pmpcfg0 register when P_entry exec. *)
Definition P_entry_pmpcfgs :=
  [device_cfg_when_P; P_code_cfg_when_P;
   F_code_cfg_when_P; SP_code_cfg_when_P_entry;
   F_data_cfg_when_P; P_data_cfg_when_P].

(* PMP registers that can be any value are existential values. *)
(* We can add more existential pmpaddr and pmpcfg *)
(* because the PMP entries with lower number have higher priority. *)
Definition pmp_regs := [
  (KindReg "pmpaddr0", ExactShape (RVal_Bits device_pmpaddr));
  (KindReg "pmpaddr1", ExactShape (RVal_Bits P_code_pmpaddr));
  (KindReg "pmpaddr2", ExactShape (RVal_Bits F_code_pmpaddr));
  (KindReg "pmpaddr3", ExactShape (RVal_Bits SP_code_pmpaddr));
  (KindReg "pmpaddr4", ExactShape (RVal_Bits F_data_pmpaddr));
  (KindReg "pmpaddr5", ExactShape (RVal_Bits P_data_pmpaddr));
  (KindReg "pmpaddr6", ExactShape (RVal_Bits (BV 64 0)));
  (KindReg "pmpaddr7", ExactShape (RVal_Bits (BV 64 0)));
  (KindReg "pmpaddr8", ExactShape (RVal_Bits SP_code_pmpaddr));
  (KindReg "pmpaddr9", BitsShape 64);
  (KindReg "pmpaddr10", BitsShape 64);
  (KindReg "pmpaddr11", BitsShape 64);
  (KindReg "pmpaddr12", BitsShape 64);
  (KindReg "pmpaddr13", BitsShape 64);
  (KindReg "pmpaddr14", BitsShape 64);
  (KindReg "pmpaddr15", BitsShape 64);
  (KindReg "pmp8cfg", StructShape ([("bits", ExactShape (RVal_Bits SP_code_cfg))]));
  (KindReg "pmp9cfg", StructShape ([("bits", BitsShape 8)]));
  (KindReg "pmp10cfg", StructShape ([("bits", BitsShape 8)]));
  (KindReg "pmp11cfg", StructShape ([("bits", BitsShape 8)]));
  (KindReg "pmp12cfg", StructShape ([("bits", BitsShape 8)]));
  (KindReg "pmp13cfg", StructShape ([("bits", BitsShape 8)]));
  (KindReg "pmp14cfg", StructShape ([("bits", BitsShape 8)]));
  (KindReg "pmp15cfg", StructShape ([("bits", BitsShape 8)]))
    ].

(* All the configurations don't change *)
Definition dorami_sys_regs := [
  (KindReg "rv_enable_zfinx", ExactShape (RVal_Bool false));
  (KindReg "rv_pmp_count", ExactShape (RegVal_I 16 64));
  (KindReg "rv_pmp_grain", ExactShape (RegVal_I 10 64));
  (KindReg "rv_enable_misaligned_access" , ExactShape (RVal_Bool false));
  (KindReg "rv_ram_base" , ExactShape (RVal_Bits (BV 64 0x0000000080000000)));
  (KindReg "rv_ram_size" , ExactShape (RVal_Bits (BV 64 0x0000000004000000)));
  (KindReg "rv_rom_base" , ExactShape (RVal_Bits (BV 64 0x0000000000001000)));
  (KindReg "rv_rom_size" , ExactShape (RVal_Bits (BV 64 0x0000000000000100)));
  (KindReg "rv_clint_base" , ExactShape (RVal_Bits (BV 64 0x0000000002000000)));
  (KindReg "rv_clint_size" , ExactShape (RVal_Bits (BV 64 0x00000000000c0000)));
  (KindReg "rv_htif_tohost" , ExactShape (RVal_Bits (BV 64 0x0000000040001000)));
  (KindReg "cur_privilege" , ExactShape (RVal_Enum "Machine"));
  (* TODO: remove this *)
  (KindReg "Machine" , ExactShape (RVal_Enum "Machine"));
  (KindReg "mseccfg", ExactShape (RegVal_Struct [("bits", RVal_Bits (BV 64 0x07))]));
  (KindReg "misa" , ExactShape (RegVal_Struct [("bits", RVal_Bits misa_bits)]))
].

(* All CSR *)
Definition machine_csr (regs: list (bv 64)) :=
  match regs with
  | mstatus :: satp :: mcause :: mepc :: nil => [
  (KindReg "mstatus", StructShape [("bits", ExactShape (RVal_Bits mstatus))]);
  (KindReg "satp" , ExactShape (RVal_Bits satp));
  (KindReg "mcause", StructShape [("bits", ExactShape (RVal_Bits mcause))]);
  (KindReg "mepc", ExactShape (RVal_Bits mepc)) ]
  | _ => nil end.

(* All CSR with exitential values, used in the universal contract of F. *)
(* TODO: remove it  *)
Definition uni_csr := [
  (KindReg "mstatus", StructShape [("bits", BitsShape 64)]);
  (KindReg "satp" , BitsShape 64);
  (KindReg "mcause", StructShape [("bits", BitsShape 64)]);
  (KindReg "mepc", BitsShape 64)
].

(* All GPR *)
Definition machine_gpr (regs: list (bv 64)) :=
  match regs with
  | x0::x1::x5::x10::x11::nil => [
  (KindReg "x0", ExactShape (RVal_Bits x0));
  (KindReg "x1", ExactShape (RVal_Bits x1));
  (KindReg "x5", ExactShape (RVal_Bits x5));
  (KindReg "x10", ExactShape (RVal_Bits x10));
  (KindReg "x11", ExactShape (RVal_Bits x11)) ]
  | _ => nil end.

(* All CSR with exitential values, used in the universal contract of F. *)
(* TODO: remove it  *)
Definition uni_gpr := [
  (KindReg "x0", BitsShape 64);
  (KindReg "x1", BitsShape 64);
  (KindReg "x5", BitsShape 64);
  (KindReg "x10", BitsShape 64);
  (KindReg "x11", BitsShape 64)
].

(* The two sets of definitions are equivalent. *)
Lemma csr_equiv `{!islaG Σ} `{!threadG} :
  reg_col uni_csr ⊣⊢ ∃ csr, ⌜length csr = 4%nat⌝ ∗ reg_col (machine_csr csr).
Proof.
  iSplit; rewrite /machine_csr /reg_col /=.
  - liARun.
    iExists (RegVal_Struct [("bits", RVal_Bits b)], b2, b1, b0, b, ())ₗ.
    liARun.
    iExists (RegVal_Struct [("bits", RVal_Bits b1)], ())ₗ.
    by liARun.
  - iIntros "[%csr [%Hcsr Hres]]".
    do 5 (destruct csr as [|? csr]; try done); simpl.
    iRevert "Hres".
    liARun.
    iExists (RegVal_Struct [("bits", RVal_Bits b)], ())ₗ.
    iFrame.
    by liARun.
Qed.

Lemma gpr_equiv `{!islaG Σ} `{!threadG} :
  reg_col uni_gpr ⊣⊢ ∃ gpr, ⌜length gpr = 5%nat⌝ ∗ reg_col (machine_gpr gpr).
Proof.
  iSplit; rewrite /machine_gpr /reg_col /=.
  - by liARun.
  - iIntros "[%gpr [%Hgpr Hres]]".
    do 6 (destruct gpr as [|? gpr]; try done); simpl.
    iRevert "Hres".
    liARun.
    iExists (RVal_Bits b, ())ₗ.
    iFrame.
    by liARun.
Qed.

(* The Machine Model *)
Definition Machine `{!islaG Σ} `{!threadG} (h: bv 64) (pmpcfgs: list (bv 8)) (csr gpr: list (bv 64)) (Pmem: bv (0x20000 * 8)) (Fmem: bv (0x1000 * 8)) : iProp Σ :=
  match pmpcfgs with
  | device_cfg :: monitor_code_cfg ::
    osbi_code_cfg :: sp_code_cfg ::
    osbi_data_cfg :: monitor_data_cfg :: nil =>
  "mtvec" # "bits" ↦ᵣ RVal_Bits h ∗
  "pmp0cfg" # "bits" ↦ᵣ RVal_Bits device_cfg ∗
  "pmp1cfg" # "bits" ↦ᵣ RVal_Bits monitor_code_cfg  ∗
  "pmp2cfg" # "bits" ↦ᵣ RVal_Bits osbi_code_cfg ∗
  "pmp3cfg" # "bits" ↦ᵣ RVal_Bits sp_code_cfg ∗
  "pmp4cfg" # "bits" ↦ᵣ RVal_Bits osbi_data_cfg ∗
  "pmp5cfg" # "bits" ↦ᵣ RVal_Bits monitor_data_cfg ∗
  "pmp6cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
  "pmp7cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
  reg_col dorami_sys_regs ∗ reg_col (machine_csr csr) ∗
  reg_col (machine_gpr gpr) ∗ reg_col pmp_regs ∗
  (bv_unsigned P_data_addr) ↦ₘ Pmem ∗
  (bv_unsigned F_data_addr) ↦ₘ Fmem
  | _ => emp end.

Arguments Machine /.

(* The P Compartment Model which doesn't have permission to *)
(* F's data region compared with the Machine Model. *)
Definition P `{!islaG Σ} `{!threadG}  (h: bv 64) (pmpcfgs: list (bv 8)) (csr gpr: list (bv 64)) (mem: bv (0x20000 * 8)): iProp Σ :=
  match pmpcfgs, csr with
  | device_cfg :: monitor_code_cfg ::
    osbi_code_cfg :: sp_code_cfg ::
    osbi_data_cfg :: monitor_data_cfg :: nil, mstatus :: other_csr =>
  ⌜bv_extract 3 1 mstatus = (BV 1 0)⌝ ∗
  "mtvec"# "bits" ↦ᵣ RVal_Bits h ∗
  "pmp0cfg" # "bits" ↦ᵣ RVal_Bits device_cfg ∗
  "pmp1cfg" # "bits" ↦ᵣ RVal_Bits monitor_code_cfg ∗
  "pmp2cfg" # "bits" ↦ᵣ RVal_Bits osbi_code_cfg ∗
  "pmp3cfg" # "bits" ↦ᵣ RVal_Bits sp_code_cfg ∗
  "pmp4cfg" # "bits" ↦ᵣ RVal_Bits osbi_data_cfg ∗
  "pmp5cfg" # "bits" ↦ᵣ RVal_Bits monitor_data_cfg ∗
  "pmp6cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
  "pmp7cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
  reg_col dorami_sys_regs ∗ reg_col (machine_csr csr) ∗
  reg_col (machine_gpr gpr) ∗ reg_col pmp_regs ∗
  (bv_unsigned P_data_addr) ↦ₘ mem
  | _, _ => emp end.

Arguments P /.

(* The F Compartment Model which doesn't have permission to *)
(* P's data region compared with the Machine Model. *)
Definition F `{!islaG Σ} `{!threadG}  (h: bv 64) (pmpcfgs: list (bv 8)) (csr gpr: list (bv 64)) (mem: bv (0x1000 * 8)): iProp Σ :=
  match pmpcfgs with
  | device_cfg :: monitor_code_cfg ::
    osbi_code_cfg :: sp_code_cfg ::
    osbi_data_cfg :: monitor_data_cfg :: nil =>
  "mtvec"# "bits" ↦ᵣ RVal_Bits h ∗
  "pmp0cfg" # "bits" ↦ᵣ RVal_Bits device_cfg ∗
  "pmp1cfg" # "bits" ↦ᵣ RVal_Bits monitor_code_cfg ∗
  "pmp2cfg" # "bits" ↦ᵣ RVal_Bits osbi_code_cfg ∗
  "pmp3cfg" # "bits" ↦ᵣ RVal_Bits sp_code_cfg ∗
  "pmp4cfg" # "bits" ↦ᵣ RVal_Bits osbi_data_cfg ∗
  "pmp5cfg" # "bits" ↦ᵣ RVal_Bits monitor_data_cfg ∗
  "pmp6cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
  "pmp7cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
  reg_col dorami_sys_regs ∗ reg_col (machine_csr csr) ∗
  reg_col (machine_gpr gpr) ∗ reg_col pmp_regs ∗
  (bv_unsigned F_data_addr) ↦ₘ mem
  | _ => emp end.

Arguments F /.

(* The SallyPort Model which doesn't have permission to *)
(* P's and F's data regions compared with the Machine Model. *)
Definition SP `{!islaG Σ} `{!threadG} (h: bv 64) (pmpcfgs: list (bv 8)) (mie: bool) (csr gpr: list (bv 64)) : iProp Σ :=
  match pmpcfgs, csr with
  | device_cfg :: monitor_code_cfg ::
    osbi_code_cfg :: sp_code_cfg ::
    osbi_data_cfg :: monitor_data_cfg :: nil, mstatus::_ =>
  ⌜if mie then True else bv_extract 3 1 mstatus = (BV 1 0)⌝ ∗
  "mtvec"# "bits" ↦ᵣ RVal_Bits h ∗
  "pmp0cfg" # "bits" ↦ᵣ RVal_Bits device_cfg ∗
  "pmp1cfg" # "bits" ↦ᵣ RVal_Bits monitor_code_cfg ∗
  "pmp2cfg" # "bits" ↦ᵣ RVal_Bits osbi_code_cfg ∗
  "pmp3cfg" # "bits" ↦ᵣ RVal_Bits sp_code_cfg ∗
  "pmp4cfg" # "bits" ↦ᵣ RVal_Bits osbi_data_cfg ∗
  "pmp5cfg" # "bits" ↦ᵣ RVal_Bits monitor_data_cfg ∗
  "pmp6cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
  "pmp7cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
  reg_col dorami_sys_regs ∗ reg_col (machine_csr csr) ∗
  reg_col (machine_gpr gpr) ∗ reg_col pmp_regs
  | _, _ => emp end.

Arguments SP /.
