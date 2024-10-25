Require Import isla.riscv64.riscv64.
Require isla.dorami.instructions.P2F.instrs.
Require isla.dorami.instructions.exit_firmware.instrs.
Require isla.dorami.instructions.Sally_Port.instrs.
Require isla.dorami.instructions.P_entry.instrs.

(* PMP grain and pmp addr mode *)
(* | REGION       | ADDRESS    | LEN              | *)
(* |--------------|------------|------------------| *)
(* | DEVICE       | 0x00000000 | 0x80000000(2^31) | *)
(* | MONITOR/CODE | 0x80000000 | 0x20000(2^17)    | *)
(* | OSBI/CODE    | 0x80020000 | 0x1000(2^12)     | *)
(* | SP/CODE      | 0x80021000 | 0x1000(2^12)     | *)

(* | OSBI/DATA    | 0x80022000 | 0x1000(2^12)     | *)
(* | MONITOR/DATA | 0x80040000 | 0x20000(2^17)    | *)
(* | SP/CODE      | 0x80021000 | 0x1000(2^12)     | *)
Definition device_addr := (BV 64 0x00000000).
Definition monitor_code_addr := (BV 64 0x80000000).
Definition osbi_code_addr := (BV 64 0x80020000).
Definition osbi_code_end_addr := (BV 64 0x80020ffc).
Definition sp_code_addr := (BV 64 0x80021000).
Definition osbi_data_addr := (BV 64 0x80022000).
Definition monitor_data_addr := (BV 64 0x80040000).
(* TODO: define the length mask? *)
Definition device_pmpaddr := (BV 64 0x7ffffff).
Definition monitor_code_pmpaddr := (BV 64 0x80001fff).
Definition osbi_code_pmpaddr := (BV 64 0x800200ff).
Definition sp_code_pmpaddr := (BV 64 0x800210ff).
Definition osbi_data_pmpaddr := (BV 64 0x800220ff).
Definition monitor_data_pmpaddr := (BV 64 0x80041fff).

(* PMP cfg when monitor, or osbi, or sally port executes. *)
(* Region [0x0, DEVICE] is S/U-mode only. *)
(* | REGION       | MONITOR EXEC | OSBI EXEC | SP EXEC  | *)
(* |--------------|--------------|-----------|----------| *)
(* | DEVICE       | 1e|AAWR      | 1e|AAWR   | 0        | *)
(* | MONITOR/CODE | 9D|LAAXR     | 98|LAA    | 0        | *)
(* | OSBI/CODE    | 98|LAA       | 9d|LAAXR  | 0        | *)
(* | SP/CODE      | 98|LAA       | 98|LAA    | 0        | *)
(* | OSBI/DATA    | 98|LAA       | 9b|LAAWR  | 0        | *)
(* | MONITOR/DATA | 9b|LAAWR     | 98|LAA    | 0        | *)
(* | SP/CODE      | 9d|LAAXR     | 9d|LAAXR  | 9d|LAAXR | *)

(* PMP configuration when Monitor exec. *)
Definition device_cfg_when_mon := (BV 8 0x1e).
Definition monitor_code_cfg_when_mon := (BV 8 0x9d).
Definition osbi_code_cfg_when_mon := (BV 8 0x98).
Definition sp_code_cfg_when_mon := (BV 8 0x98).
Definition osbi_data_cfg_when_mon := (BV 8 0x98).
Definition monitor_data_cfg_when_mon := (BV 8 0x9b).
Definition sp_code_cfg_when_mon' := (BV 8 0x9d).

(* PMP configuration when OSBI exec. *)
Definition device_cfg_when_osbi := (BV 8 0x1e).
Definition monitor_code_cfg_when_osbi := (BV 8 0x98).
Definition osbi_code_cfg_when_osbi := (BV 8 0x9d).
Definition sp_code_cfg_when_osbi := (BV 8 0x98).
Definition osbi_data_cfg_when_osbi := (BV 8 0x9b).
Definition monitor_data_cfg_when_osbi := (BV 8 0x98).
Definition sp_code_cfg_when_osbi' := (BV 8 0x9d).

(* PMP configuration when SP exec. *)
Definition components_cfg_when_sp := (BV 8 0x00).
Definition sp_code_cfg_when_P_entry := (BV 8 0x9d).

Definition monitor_mtvec := monitor_code_addr.
Definition P2F_code_addr := bv_sub osbi_code_addr 0x2c.
Definition firmware_mtvec := osbi_code_addr.

Definition firmware_pmpcfgs :=
  [device_cfg_when_osbi; monitor_code_cfg_when_osbi;
   osbi_code_cfg_when_osbi; sp_code_cfg_when_osbi;
   osbi_data_cfg_when_osbi; monitor_data_cfg_when_osbi].

Definition sp_pmpcfgs :=
  [components_cfg_when_sp; components_cfg_when_sp;
   components_cfg_when_sp; components_cfg_when_sp;
   components_cfg_when_sp; components_cfg_when_sp].

Definition P_entry_pmpcfgs :=
  [device_cfg_when_mon; monitor_code_cfg_when_mon;
   osbi_code_cfg_when_mon; sp_code_cfg_when_P_entry;
   osbi_data_cfg_when_mon; monitor_data_cfg_when_mon].

Definition monitor_pmpcfgs :=
  [device_cfg_when_mon; monitor_code_cfg_when_mon;
   osbi_code_cfg_when_mon; sp_code_cfg_when_mon;
   osbi_data_cfg_when_mon; monitor_data_cfg_when_mon].

(* PMP registers that can be any value are existential values. *)
(* We can add more existential pmpaddr and pmpcfg. *)
Definition pmp_regs := [
  (KindReg "pmpaddr0", ExactShape (RVal_Bits device_pmpaddr));
  (KindReg "pmpaddr1", ExactShape (RVal_Bits monitor_code_pmpaddr));
  (KindReg "pmpaddr2", ExactShape (RVal_Bits osbi_code_pmpaddr));
  (KindReg "pmpaddr3", ExactShape (RVal_Bits sp_code_pmpaddr));
  (KindReg "pmpaddr4", ExactShape (RVal_Bits osbi_data_pmpaddr));
  (KindReg "pmpaddr5", ExactShape (RVal_Bits monitor_data_pmpaddr));
  (KindReg "pmpaddr6", ExactShape (RVal_Bits (BV 64 0)));
  (KindReg "pmpaddr7", ExactShape (RVal_Bits (BV 64 0)));
  (KindReg "pmpaddr8", ExactShape (RVal_Bits sp_code_pmpaddr));
  (KindReg "pmpaddr9", BitsShape 64);
  (KindReg "pmpaddr10", BitsShape 64);
  (KindReg "pmpaddr11", BitsShape 64);
  (KindReg "pmpaddr12", BitsShape 64);
  (KindReg "pmpaddr13", BitsShape 64);
  (KindReg "pmpaddr14", BitsShape 64);
  (KindReg "pmpaddr15", BitsShape 64);
  (KindReg "pmp8cfg", StructShape ([("bits", ExactShape (RVal_Bits sp_code_cfg_when_mon'))]));
  (KindReg "pmp9cfg", StructShape ([("bits", BitsShape 8)]));
  (KindReg "pmp10cfg", StructShape ([("bits", BitsShape 8)]));
  (KindReg "pmp11cfg", StructShape ([("bits", BitsShape 8)]));
  (KindReg "pmp12cfg", StructShape ([("bits", BitsShape 8)]));
  (KindReg "pmp13cfg", StructShape ([("bits", BitsShape 8)]));
  (KindReg "pmp14cfg", StructShape ([("bits", BitsShape 8)]));
  (KindReg "pmp15cfg", StructShape ([("bits", BitsShape 8)]))
    ].

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
  (bv_unsigned monitor_data_addr) ↦ₘ Pmem ∗
  (bv_unsigned osbi_data_addr) ↦ₘ Fmem
  | _ => emp end.

Arguments Machine /.

Definition P `{!islaG Σ} `{!threadG}  (h: bv 64) (pmpcfgs: list (bv 8)) (mie: bool) (csr gpr: list (bv 64)) (mem: bv (0x20000 * 8)): iProp Σ :=
  match pmpcfgs, csr with
  | device_cfg :: monitor_code_cfg ::
    osbi_code_cfg :: sp_code_cfg ::
    osbi_data_cfg :: monitor_data_cfg :: nil, mstatus :: other_csr =>
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
  reg_col (machine_gpr gpr) ∗ reg_col pmp_regs ∗
  (bv_unsigned monitor_data_addr) ↦ₘ mem
  | _, _ => emp end.

Arguments P /.

Definition P' `{!islaG Σ} `{!threadG}  (h: bv 64) (pmpcfgs: list (bv 8)) (mie: bool) (csr gpr: list (bv 64)) (mem: bv (0x20000 * 8)): iProp Σ :=
  match pmpcfgs, csr with
  | device_cfg :: monitor_code_cfg ::
    osbi_code_cfg :: sp_code_cfg ::
    osbi_data_cfg :: monitor_data_cfg :: nil, mstatus :: part_csr =>
  "mstatus" # "bits" ↦ᵣ RVal_Bits mstatus ∗ ⌜if mie then True else bv_extract 3 1 mstatus = (BV 1 0)⌝ ∗
  "mtvec"# "bits" ↦ᵣ RVal_Bits h ∗
  "pmp0cfg" # "bits" ↦ᵣ RVal_Bits device_cfg ∗
  "pmp1cfg" # "bits" ↦ᵣ RVal_Bits monitor_code_cfg ∗
  "pmp2cfg" # "bits" ↦ᵣ RVal_Bits osbi_code_cfg ∗
  "pmp3cfg" # "bits" ↦ᵣ RVal_Bits sp_code_cfg ∗
  "pmp4cfg" # "bits" ↦ᵣ RVal_Bits osbi_data_cfg ∗
  "pmp5cfg" # "bits" ↦ᵣ RVal_Bits monitor_data_cfg ∗
  "pmp6cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
  "pmp7cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
  reg_col dorami_sys_regs ∗ reg_col (part_machine_csr part_csr) ∗
  reg_col (machine_gpr gpr) ∗ reg_col pmp_regs ∗
  (bv_unsigned monitor_data_addr) ↦ₘ mem
  | _, _ => emp end.

Arguments P' /.

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
  (bv_unsigned osbi_data_addr) ↦ₘ mem
  | _ => emp end.

Arguments F /.

Definition F' `{!islaG Σ} `{!threadG}  (h: bv 64) (pmpcfgs: list (bv 8)) (csr gpr: list (bv 64)) (mem: bv (0x1000 * 8)): iProp Σ :=
  match pmpcfgs, csr with
  | device_cfg :: monitor_code_cfg ::
    osbi_code_cfg :: sp_code_cfg ::
    osbi_data_cfg :: monitor_data_cfg :: nil, mstatus :: part_csr =>
  "mstatus" # "bits" ↦ᵣ RVal_Bits mstatus ∗
  "mtvec"# "bits" ↦ᵣ RVal_Bits h ∗
  "pmp0cfg" # "bits" ↦ᵣ RVal_Bits device_cfg ∗
  "pmp1cfg" # "bits" ↦ᵣ RVal_Bits monitor_code_cfg ∗
  "pmp2cfg" # "bits" ↦ᵣ RVal_Bits osbi_code_cfg ∗
  "pmp3cfg" # "bits" ↦ᵣ RVal_Bits sp_code_cfg ∗
  "pmp4cfg" # "bits" ↦ᵣ RVal_Bits osbi_data_cfg ∗
  "pmp5cfg" # "bits" ↦ᵣ RVal_Bits monitor_data_cfg ∗
  "pmp6cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
  "pmp7cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
  reg_col dorami_sys_regs ∗ reg_col (part_machine_csr part_csr) ∗
  reg_col (machine_gpr gpr) ∗ reg_col pmp_regs ∗
  (bv_unsigned osbi_data_addr) ↦ₘ mem
  | _, _ => emp end.

Arguments F' /.

Definition Pmonitor `{!islaG Σ} `{!threadG} :=
  P monitor_mtvec monitor_pmpcfgs false.

Arguments monitor /.

Definition Pfirmware `{!islaG Σ} `{!threadG} :=
  Pview firmware_mtvec firmware_pmpcfgs false.

Arguments Pfirmware /.

Definition Ffirmware `{!islaG Σ} `{!threadG} :=
  Fview firmware_mtvec firmware_pmpcfgs.

Arguments Ffirmware /.
(* TODO: change sp_code_addr to osbi_code_addr can also pove the *)
(* Lemma exit_firmware_inst_WPasm. *)
(* TODO: Are entry points to monitor from OS, enclave, or SallyPort same? *)
(* It's probably not important since we assume they're all safe. *)
Definition Pstart_SP `{!islaG Σ} `{!threadG} :=
  Pview firmware_mtvec sp_pmpcfgs true.

Arguments Pstart_SP /.

Definition Fstart_SP `{!islaG Σ} `{!threadG} :=
  Fview firmware_mtvec sp_pmpcfgs.

Arguments Fstart_SP /.

Definition start_P_entry `{!islaG Σ} `{!threadG} :=
  Pview monitor_mtvec P_entry_pmpcfgs false.

Arguments start_P_entry /.

Definition P2F_spec `{!islaG Σ} `{!threadG} (csr gpr csr' gpr': list (bv 64)) (mem: (bv (0x20000 * 8))) : iProp Σ :=
  monitor csr gpr mem ∗
  instr_pre (bv_unsigned osbi_code_addr) (
    Pfirmware csr' gpr' mem ∗
    True
  ).

Arguments P2F_spec /.

Theorem P2F `{!islaG Σ} `{!threadG} :
  ∀ csr gpr mem,
  length csr = 4%nat ->
  length gpr = 5%nat ->
  instr (bv_unsigned osbi_code_addr - 0x2c) (Some P2F.a0.a0) -∗
  instr (bv_unsigned osbi_code_addr - 0x28) (Some P2F.a4.a4) -∗
  instr (bv_unsigned osbi_code_addr - 0x24) (Some P2F.a8.a8) -∗
  instr (bv_unsigned osbi_code_addr - 0x20) (Some P2F.ac.ac) -∗
  instr (bv_unsigned osbi_code_addr - 0x1c) (Some P2F.a10.a10) -∗
  instr (bv_unsigned osbi_code_addr - 0x18) (Some P2F.a14.a14) -∗
  instr (bv_unsigned osbi_code_addr - 0x14) (Some P2F.a18.a18) -∗
  instr (bv_unsigned osbi_code_addr - 0x10) (Some P2F.a1c.a1c) -∗
  instr (bv_unsigned osbi_code_addr - 0xc) (Some P2F.a20.a20) -∗
  instr (bv_unsigned osbi_code_addr - 0x8) (Some P2F.a24.a24) -∗
  instr (bv_unsigned osbi_code_addr - 0x4) (Some P2F.a28.a28) -∗
  instr_body (bv_unsigned osbi_code_addr - 0x2c) (P2F_spec csr gpr csr (<[2%nat := (BV 64 0x989B989D981E)]>gpr) mem).
Proof.
  intros csr gpr mem Hcsr Hgpr.
  do 5 (destruct csr as [|? csr]; try done).
  do 6 (destruct gpr as [|? gpr]; try done).
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition SP_spec `{!islaG Σ} `{!threadG} (csr gpr csr' gpr': list (bv 64)) (mem: (bv (0x20000 * 8))) :iProp Σ :=
  Pstart_SP csr gpr mem ∗
  instr_pre (bv_unsigned monitor_code_addr) (
    ∃ ms, start_P_entry (ms::tl csr') gpr' mem ∗
    True
  ).

Arguments SP_spec /.

Definition SP_a0_spec `{!islaG Σ} `{!threadG} : iProp Σ :=
  (∃ ms: bv 64, "mstatus" # "bits" ↦ᵣ RVal_Bits ms) ∗
  reg_col dorami_sys_regs ∗
  instr_pre (bv_unsigned sp_code_addr + 4) (
  (∃ ms: bv 64, "mstatus" # "bits" ↦ᵣ RVal_Bits ms ∗ ⌜bv_extract 3 1 ms = (BV 1 0)⌝) ∗
    reg_col dorami_sys_regs
  ).

Arguments SP_a0_spec /.

Lemma a0_spec `{!islaG Σ} `{!threadG} :
  instr (bv_unsigned sp_code_addr) (Some Sally_Port.a0.a0)
  ⊢ instr_body (bv_unsigned sp_code_addr) SP_a0_spec.
Proof.
  iStartProof.
  liARun; iFrame.
  Unshelve. all: prepare_sidecond.
  all: bv_simplify; bitblast.
Qed.

(* TODO: the weried jump instruction. *)
Lemma SP `{!islaG Σ} `{!threadG} :
  ∀ csr gpr mem,
  length csr = 4%nat ->
  length gpr = 5%nat ->
  instr (bv_unsigned sp_code_addr) (Some Sally_Port.a0.a0) -∗
  instr (bv_unsigned sp_code_addr + 0x4) (Some Sally_Port.a4.a4) -∗
  instr (bv_unsigned sp_code_addr + 0x8) (Some Sally_Port.a8.a8) -∗
  instr (bv_unsigned sp_code_addr + 0xc) (Some Sally_Port.ac.ac) -∗
  instr (bv_unsigned sp_code_addr + 0x10) (Some Sally_Port.a10.a10) -∗
  instr (bv_unsigned sp_code_addr + 0x14) (Some Sally_Port.a14.a14) -∗
  instr (bv_unsigned sp_code_addr + 0x18) (Some Sally_Port.a18.a18) -∗
  instr (bv_unsigned sp_code_addr + 0x1c) (Some Sally_Port.a1c.a1c) -∗
  instr (bv_unsigned sp_code_addr + 0x20) (Some Sally_Port.a20.a20) -∗
  instr (bv_unsigned sp_code_addr + 0x24) (Some Sally_Port.a24.a24) -∗
  instr (bv_unsigned sp_code_addr + 0x28) (Some Sally_Port.a28.a28) -∗
  instr (bv_unsigned sp_code_addr + 0x2c) (Some Sally_Port.a2c.a2c) -∗
  instr (bv_unsigned sp_code_addr + 0x30) (Some Sally_Port.a30.a30) -∗
  instr (bv_unsigned sp_code_addr + 0x34) (Some Sally_Port.a34.a34) -∗
  instr_body (bv_unsigned sp_code_addr) (SP_spec csr gpr csr (<[2%nat := (BV 64 0x9B989D989D1E)]>gpr) mem).
Proof.
  intros csr gpr mem Hcsr Hgpr.
  do 5 (destruct csr as [|? csr]; try done).
  do 6 (destruct gpr as [|? gpr]; try done).
  iStartProof.
  iIntros.
  iPoseProof (a0_spec with "[$]") as "Ha0_spec".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition P_entry_spec `{!islaG Σ} `{!threadG} (csr gpr csr' gpr': list (bv 64)) (mem: (bv (0x20000 * 8))) :iProp Σ :=
  start_P_entry csr gpr mem ∗
  instr_pre (bv_unsigned monitor_code_addr + 0x1c) (
    monitor csr' gpr' mem∗
    True
  ).

Arguments P_entry_spec /.

Lemma P_entry_proof `{!islaG Σ} `{!threadG} :
  ∀ csr gpr mem,
  length csr = 4%nat ->
  length gpr = 5%nat ->
  instr (bv_unsigned monitor_code_addr) (Some P_entry.a0.a0) -∗
  instr (bv_unsigned monitor_code_addr + 0x4) (Some P_entry.a4.a4) -∗
  instr (bv_unsigned monitor_code_addr + 0x8) (Some P_entry.a8.a8) -∗
  instr (bv_unsigned monitor_code_addr + 0xc) (Some P_entry.ac.ac) -∗
  instr (bv_unsigned monitor_code_addr + 0x10) (Some P_entry.a10.a10) -∗
  instr (bv_unsigned monitor_code_addr + 0x14) (Some P_entry.a14.a14) -∗
  instr (bv_unsigned monitor_code_addr + 0x18) (Some P_entry.a18.a18) -∗
  instr_body (bv_unsigned monitor_code_addr) (P_entry_spec csr gpr csr (<[2%nat := (BV 64 0x9B9898989D1E)]>gpr) mem).
Proof.
  intros csr gpr mem Hcsr Hgpr.
  do 5 (destruct csr as [|? csr]; try done).
  do 6 (destruct gpr as [|? gpr]; try done).
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition F2P_spec `{!islaG Σ} `{!threadG} (csr gpr csr' gpr': list (bv 64)) (mem: (bv (0x20000 * 8))) : iProp Σ :=
  Pstart_SP csr gpr mem ∗
  instr_pre (bv_unsigned monitor_code_addr + 0x1c) (
    ∃ ms, monitor (ms::tl csr') gpr' mem ∗
    True
  ).

Arguments F2P_spec /.

Theorem F2P `{!islaG Σ} `{!threadG} :
  ∀ csr gpr mem,
  length csr = 4%nat ->
  length gpr = 5%nat ->
  instr (bv_unsigned sp_code_addr) (Some Sally_Port.a0.a0) -∗
  instr (bv_unsigned sp_code_addr + 0x4) (Some Sally_Port.a4.a4) -∗
  instr (bv_unsigned sp_code_addr + 0x8) (Some Sally_Port.a8.a8) -∗
  instr (bv_unsigned sp_code_addr + 0xc) (Some Sally_Port.ac.ac) -∗
  instr (bv_unsigned sp_code_addr + 0x10) (Some Sally_Port.a10.a10) -∗
  instr (bv_unsigned sp_code_addr + 0x14) (Some Sally_Port.a14.a14) -∗
  instr (bv_unsigned sp_code_addr + 0x18) (Some Sally_Port.a18.a18) -∗
  instr (bv_unsigned sp_code_addr + 0x1c) (Some Sally_Port.a1c.a1c) -∗
  instr (bv_unsigned sp_code_addr + 0x20) (Some Sally_Port.a20.a20) -∗
  instr (bv_unsigned sp_code_addr + 0x24) (Some Sally_Port.a24.a24) -∗
  instr (bv_unsigned sp_code_addr + 0x28) (Some Sally_Port.a28.a28) -∗
  instr (bv_unsigned sp_code_addr + 0x2c) (Some Sally_Port.a2c.a2c) -∗
  instr (bv_unsigned sp_code_addr + 0x30) (Some Sally_Port.a30.a30) -∗
  instr (bv_unsigned sp_code_addr + 0x34) (Some Sally_Port.a34.a34) -∗
  instr (bv_unsigned monitor_code_addr) (Some P_entry.a0.a0) -∗
  instr (bv_unsigned monitor_code_addr + 0x4) (Some P_entry.a4.a4) -∗
  instr (bv_unsigned monitor_code_addr + 0x8) (Some P_entry.a8.a8) -∗
  instr (bv_unsigned monitor_code_addr + 0xc) (Some P_entry.ac.ac) -∗
  instr (bv_unsigned monitor_code_addr + 0x10) (Some P_entry.a10.a10) -∗
  instr (bv_unsigned monitor_code_addr + 0x14) (Some P_entry.a14.a14) -∗
  instr (bv_unsigned monitor_code_addr + 0x18) (Some P_entry.a18.a18) -∗
  instr_body (bv_unsigned sp_code_addr) (F2P_spec csr gpr csr (<[2%nat := (BV 64 0x9B9898989D1E)]>gpr) mem).
Proof.
  intros csr gpr mem Hcsr Hgpr.
  do 5 (destruct csr as [|? csr]; try done).
  do 6 (destruct gpr as [|? gpr]; try done).
  iStartProof.
  iIntros.
  iPoseProof (a0_spec with "[$]") as "Ha0_spec".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.
(*
Definition assume_regs_map (mtvec: bv 64) : reg_map :=
  <[ "pmpaddr0" := RVal_Bits device_pmpaddr ]> $
  <[ "pmpaddr1" := RVal_Bits monitor_code_pmpaddr ]> $
  <[ "pmpaddr2" := RVal_Bits osbi_code_pmpaddr ]> $
  <[ "pmpaddr3" := RVal_Bits sp_code_pmpaddr ]> $
  <[ "pmpaddr4" := RVal_Bits osbi_data_pmpaddr ]> $
  <[ "pmpaddr5" := RVal_Bits monitor_data_pmpaddr ]> $
  <[ "pmpaddr8" := RVal_Bits sp_code_pmpaddr ]> $
  <[ "pmp0cfg" := RegVal_Struct [("bits", RVal_Bits device_cfg_when_osbi)] ]> $
  <[ "pmp1cfg" := RegVal_Struct [("bits", RVal_Bits monitor_code_cfg_when_osbi)] ]> $
  <[ "pmp2cfg" := RegVal_Struct [("bits", RVal_Bits osbi_code_cfg_when_osbi)] ]> $
  <[ "pmp3cfg" := RegVal_Struct [("bits", RVal_Bits sp_code_cfg_when_osbi)] ]> $
  <[ "pmp4cfg" := RegVal_Struct [("bits", RVal_Bits osbi_data_cfg_when_osbi)] ]> $
  <[ "pmp5cfg" := RegVal_Struct [("bits", RVal_Bits monitor_data_cfg_when_osbi)] ]> $
  <[ "pmp6cfg" := RegVal_Struct [("bits", RVal_Bits (BV 64 0))] ]> $
  <[ "pmp7cfg" := RegVal_Struct [("bits", RVal_Bits (BV 64 0))] ]> $
  <[ "pmp8cfg" := RegVal_Struct [("bits", RVal_Bits sp_code_cfg_when_osbi')] ]> $
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
*)

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

Fixpoint NoPMPOrMTVECWrite (t: isla_trace) : bool :=
  match t with
  | tcons (WriteReg regname _ _ _) t =>
      negb (String.prefix "pmp" regname) &&
      negb (String.eqb "mtvec" regname) && NoPMPOrMTVECWrite t
  | tcons _ t => NoPMPOrMTVECWrite t
  | tcases ts => forallb NoPMPOrMTVECWrite ts
  | _ => true
  end.

Fixpoint NoEmptyCases (t: isla_trace) : bool :=
  match t with
  | tcons e tail => NoEmptyCases tail
  | tcases ts => bool_decide(ts ≠ nil) && forallb NoEmptyCases ts
  | _ => true
  end.

Definition NoStuckEvalNow (t: isla_trace) : Prop :=
  match t with
  | tcons (Smt (DefineConst var exp) _) _ =>
      ∃ v, eval_exp exp = Some v
  | tcons (Smt (Assert exp) _) _ =>
      ∃ b, eval_exp exp = Some (Val_Bool b)
  | _ => True
  end.

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

Lemma tcons_NoPMPOrMTVECWrite event tail :
  NoPMPOrMTVECWrite (event :t: tail) -> NoPMPOrMTVECWrite tail.
Proof.
  intro.
  unfold NoPMPOrMTVECWrite in H.
  fold NoPMPOrMTVECWrite in H.
  destruct event; try done.
  rewrite Is_true_true in H.
  symmetry in H.
  apply andb_true_eq in H.
  destruct H as (_ & H).
  by apply Is_true_true.
Qed.

Lemma subst_trace_NoPMPOrMTVECWrite v x t:
  NoPMPOrMTVECWrite t -> NoPMPOrMTVECWrite (subst_trace v x t).
Proof.
  intro.
  induction t as [|e tail IH|es IH] using isla_trace_custom_ind; first done.
  - assert (H' := H).
    unfold NoPMPOrMTVECWrite in H.
    fold NoPMPOrMTVECWrite in H.
    unfold subst_trace. fold subst_trace.
    unfold NoPMPOrMTVECWrite. fold NoPMPOrMTVECWrite.
    apply tcons_NoPMPOrMTVECWrite in H'. apply IH in H'.
    destruct e; try done.
    unfold subst_val_event.
    rewrite !Is_true_true !andb_true_iff in H |- *.
    destruct H as [[H1 H2] H3].
    apply Is_true_true in H'.
    split; last done.
    split; done.
  - rewrite Forall_forall in IH.
    rewrite /= !Is_true_true !forallb_forall in H |- * => t Hin.
    rewrite /subst_trace -/subst_trace -elem_of_list_In in Hin.
    apply elem_of_list_fmap_2 in Hin.
    destruct Hin as [y [-> Hin]].
    rewrite -Is_true_true.
    apply IH; first done.
    rewrite Is_true_true.
    apply H.
    by rewrite -elem_of_list_In.
Qed.

Lemma trace_step_NoPMPOrMTVECWrite t regs label t' :
  t ≠ tnil -> trace_step t regs label t' -> NoPMPOrMTVECWrite t -> NoPMPOrMTVECWrite t'.
Proof.
  intros Hneq Hstep Ht.
  destruct Hstep;
    first [done | by apply subst_trace_NoPMPOrMTVECWrite |  by apply tcons_NoPMPOrMTVECWrite in Ht | trivial].
  unfold NoPMPOrMTVECWrite in Ht.
  fold NoPMPOrMTVECWrite in Ht.
  rewrite Is_true_true forallb_forall in Ht.
  rewrite Is_true_true.
  by apply Ht, elem_of_list_In.
Qed.

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

Definition NoStuckEval (t: isla_trace) : Prop :=
  t ≠ tnil -> forall t', rtc (fun t t' => ∃ label regs, trace_step t regs label t' ∧ label ≠ Some (LDone t')) t t' -> NoStuckEvalNow t'.


Lemma bv_extract_divisible {n} l (b : bv n) :
  bv_unsigned (bv_extract 0 l b) = 0 -> ∃ quo, bv_unsigned b = 2 ^ Z.of_N l * quo.
Proof.
  rewrite bv_extract_unsigned /bv_wrap /bv_modulus.
  replace (bv_unsigned b ≫ Z.of_N 0) with (bv_unsigned b) by done.
  intro Hmod.
  apply Z_div_exact_full_2 in Hmod; last lia.
  by exists (bv_unsigned b `div` 2 ^ Z.of_N l).
Qed.

Scheme Equality for accessor.
Scheme Equality for list.

Definition list_acc_eqb := list_beq accessor accessor_beq.
Definition list_acc_eqb_eq a1 a2 : list_acc_eqb a1 a2 = true -> a1 = a2.
  refine (internal_list_dec_bl _ _ internal_accessor_dec_bl _ _).
Defined.

Definition RBits_dec : ∀ v: valu, {bv | v = RVal_Bits bv} + {forall bv, v <> RVal_Bits bv}.
Proof.
 intros.
 destruct v; first destruct base_val5; try by refine (inright _).
 refine (inleft _); by econstructor.
Defined.

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

Definition LegalReadRegNow (t: isla_trace) : bool :=
  match t with
  | tnil => true
  | tcons (ReadReg reg acc val _) t => LegalRegAcc_R reg acc val
  | tcons _ t => true
  | tcases ts => true
  end.

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

Definition LegalMemAcc data addr len : bool :=
  (N.eqb (bvn_n addr) 64) && (N.eqb (bvn_n data) (8 * len))%N
  && (N.ltb 0 len)
  && (Z.leb (Z.of_N len) (0x1000 - (bvn_unsigned addr - bv_unsigned osbi_data_addr)))
  && (Z.leb (bv_unsigned osbi_data_addr) (bvn_unsigned addr))
  && (Z.leb (bvn_unsigned addr) (bv_unsigned osbi_data_addr + 0x1000)).

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

Definition LegalRegAcc_A reg acc val : bool :=
  match val with
  | RVal_Bits bv =>
      (String.eqb reg "rv_htif_tohost" && list_acc_eqb acc [] && (N.eqb (bvn_n bv) 64) && (Z.eqb (bvn_unsigned bv) 0x0000000040001000))
      || (String.eqb reg "mseccfg" && list_acc_eqb acc [Field "bits"]
       && (N.eqb (bvn_n bv) 64) && (Z.eqb (bvn_unsigned bv) 0x07))
  | _ => false
  end.

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

Fixpoint LegalAssumeReg (t: isla_trace) : bool :=
  match t with
  | tnil => true
  | tcons (AssumeReg reg acc val _)  t =>
      LegalRegAcc_A reg acc val && LegalAssumeReg t
  | tcons _ t => LegalAssumeReg t
  | tcases ts => forallb LegalAssumeReg ts
  end.

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
            && (N.eqb (bvn_n bv) 64) && (Z.eqb (bvn_unsigned bv) (bv_unsigned firmware_mtvec)))
      || ((String.eqb reg "pmpaddr0") && (list_acc_eqb acc [])
            && (N.eqb (bvn_n bv) 64) && (Z.eqb (bvn_unsigned bv) (bv_unsigned device_pmpaddr)))
      || ((String.eqb reg "pmp0cfg") && (list_acc_eqb acc [Field "bits"])
            && (N.eqb (bvn_n bv) 8) && (Z.eqb (bvn_unsigned bv) (bv_unsigned device_cfg_when_osbi)))
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

Lemma LegalAssumeEvent_destruct reg acc aval :
  LegalAssumeEvent reg acc aval ->
    { reg = "cur_privilege" ∧ acc = [] ∧ aval = (AVal_Var "Machine" []) }
    + { reg = "mseccfg" ∧ acc = [Field "bits"] ∧ aval = (AVal_Bits (BV 64 0x7)) }
    + { reg = "misa" ∧ acc = [Field "bits"] ∧ aval = (AVal_Bits misa_bits) }
    + { reg = "mtvec" ∧ acc = [Field "bits"] ∧ aval = (AVal_Bits firmware_mtvec) }
    + { reg = "pmpaddr0" ∧ acc = [] ∧ aval = (AVal_Bits device_pmpaddr) }
    + { reg = "pmp0cfg" ∧ acc = [Field "bits"] ∧ aval = (AVal_Bits device_cfg_when_osbi) }.
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


Lemma wp_declare_const_bool' `{!islaG Σ} `{!threadG} v es ann:
  (∀ (b : bool), ▷WPasm (subst_trace (Val_Bool b) v es)) -∗
  WPasm (Smt (DeclareConst v Ty_Bool) ann :t: es).
Proof.
  iIntros "Hcont". setoid_rewrite wp_asm_unfold.
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "(?&Hictx&?)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iSplit. {
    iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
    done.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  iFrame; iSplitL; [|done].
  iApply ("Hcont"); [done..|].
  iFrame.
  Unshelve. exact true.
Qed.

Lemma wp_declare_const_bv' `{!islaG Σ} `{!threadG} v es ann b:
  (∀ (n : bv b), ▷WPasm (subst_trace (Val_Bits n) v es)) -∗
  WPasm (Smt (DeclareConst v (Ty_BitVec b)) ann :t: es).
Proof.
  iIntros "Hcont". setoid_rewrite wp_asm_unfold.
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "(?&Hictx&?)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iSplit. {
    iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by apply DeclareConstBitVecS'|]; simpl.
    done.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  iFrame; iSplitL; [|done].
  iApply ("Hcont"); [done..|].
  iFrame.
  Unshelve. apply: inhabitant.
Qed.

Lemma wp_declare_const_enum' `{!islaG Σ} `{!threadG} v es i ann:
  (∀ c, ▷ WPasm (subst_trace (Val_Enum (c)) v es)) -∗
  WPasm (Smt (DeclareConst v (Ty_Enum i)) ann :t: es).
Proof.
  iIntros "Hcont". setoid_rewrite wp_asm_unfold.
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "(?&Hictx&?)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iSplit. {
    iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
    done.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  iFrame; iSplitL; [|done].
  iApply ("Hcont"); [done..|].
  iFrame.
  Unshelve. exact: inhabitant.
Qed.

Lemma wp_define_const' `{!islaG Σ} `{!threadG} n es ann e:
  WPexp e {{ v, ▷ WPasm (subst_trace v n es) }} -∗
  WPasm (Smt (DefineConst n e) ann :t: es).
Proof.
  rewrite wp_asm_unfold wp_exp_unfold. iDestruct 1 as (v Hv) "Hcont".
  rewrite wp_asm_unfold.
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "(?&Hictx)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iSplit. {
    iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
    done.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  iFrame; iSplitL; [|done].
  iApply ("Hcont"); [done..|].
  iFrame.
Qed.

Lemma wp_assert' `{!islaG Σ} `{!threadG} es ann e:
  WPexp e {{ v, (∃ b, ⌜v = Val_Bool b⌝ ∗ ▷ (⌜b = true⌝ -∗ WPasm es)) }} -∗
  WPasm (Smt (Assert e) ann :t: es).
Proof.
  rewrite wp_exp_unfold. iDestruct 1 as (v Hv b ?) "Hcont". subst v.
  rewrite !wp_asm_unfold.
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "Hctx".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iSplit. {
    iPureIntro. destruct b.
    all: eexists _, _, _, _; econstructor; [done |by econstructor| done].
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  iFrame; iSplit; [|done].
  destruct b => /=; last by iApply wp_value.
  iApply "Hcont"; [done..|iFrame].
Qed.

Lemma wp_branch' `{!islaG Σ} `{!threadG} c desc es ann:
  ▷ WPasm es -∗
  WPasm (Branch c desc ann :t: es).
Proof.
  iIntros "Hcont". setoid_rewrite wp_asm_unfold.
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "(?&Hictx&?)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iSplit. {
    iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
    done.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  iFrame; iSplitL; [|done].
  iApply ("Hcont"); [done..|].
  iFrame.
Qed.

Lemma wp_read_reg' `{!islaG Σ} `{!threadG} r v vread ann es al:
  read_accessor al v = Some vread →
  WPreadreg r @ al {{ v', ▷ (⌜vread = v'⌝ -∗ WPasm es) }} -∗
  WPasm (ReadReg r al v ann :t: es).
Proof.
  rewrite wp_asm_eq wpreadreg_eq. iIntros (?) "Hr".
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "(?&Hictx&?)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iDestruct ("Hr" with "Hθ") as (v' v'' ??) "[? Hcont]".
  iSplit. {
    iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
    eexists _, _, _. split_and! => //. by right.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step. revert select (∃ x, _) => -[?[?[?[?[?[?[?[?[[??]|?]]]]]]]]]; simplify_eq/=. 2: {
    iFrame. iSplitL; [|done]. by iApply wp_value.
  }
  iFrame; iSplitL; [|done].
  iApply ("Hcont" with "[//]"); [done..|].
  iFrame.
Qed.

Lemma wp_write_reg_acc' `{!islaG Σ} `{!threadG} r v v' v'' vnew ann es al:
  read_accessor al v = Some vnew →
  write_accessor al v' vnew = Some v'' →
  r ↦ᵣ v' -∗
  ▷ (r ↦ᵣ v'' -∗ WPasm es) -∗
  WPasm (WriteReg r al v ann :t: es).
Proof.
  iIntros (? ?) "Hr Hcont". setoid_rewrite wp_asm_unfold.
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "(?&Hictx&?)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iDestruct (reg_mapsto_lookup with "Hθ Hr") as %Hr.
  iSplit. {
    iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
    eexists _, _, _. done.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  revert select (∃ _, _) => -[?[?[?[?[?[?[?[??]]]]]]]].
  unfold sail_name in *. simplify_eq.
  iFrame; iSplitL; [|done].
  iMod (reg_mapsto_update with "Hθ Hr") as "[Hθ Hr]".
  iApply ("Hcont" with "Hr"); [done..|].
  iFrame.
Qed.

Lemma wp_write_reg_struct' `{!islaG Σ} `{!threadG} r v v' vnew ann es f:
  read_accessor [Field f] v = Some vnew →
  r # f ↦ᵣ v' -∗
  ▷ (r # f ↦ᵣ vnew -∗ WPasm es) -∗
  WPasm (WriteReg r [Field f] v ann :t: es).
Proof.
  iIntros (?) "Hr Hcont". setoid_rewrite wp_asm_unfold.
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "(?&Hictx&?)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iDestruct (struct_reg_mapsto_lookup with "Hθ Hr") as %(?&?&?&?&?).
  iSplit. {
    iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
    eexists _, _, _. split_and! => //. rewrite /write_accessor/=. by simplify_option_eq.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  revert select (∃ _, _) => -[?[?[?[?[?[?[?[??]]]]]]]].
  unfold sail_name, write_accessor in *. simplify_option_eq.
  iFrame; iSplitL; [|done].
  iMod (struct_reg_mapsto_update with "Hθ Hr") as "[Hθ Hr]"; [done..|].
  iApply ("Hcont" with "Hr"); [done..|].
  iFrame.
Qed.

Lemma wp_write_reg' `{!islaG Σ} `{!threadG} r v v' ann es:
  r ↦ᵣ v' -∗
  ▷ (r ↦ᵣ v -∗ WPasm es) -∗
  WPasm (WriteReg r [] v ann :t: es).
Proof. by apply: wp_write_reg_acc'. Qed.

Lemma wp_read_mem' `{!islaG Σ} `{!threadG} n len a vread (vmem : bv n) es ann kind tag q:
  n = (8 * len)%N →
  0 < Z.of_N len →
  bv_unsigned a ↦ₘ{q} vmem -∗
  ▷ (⌜vread = vmem⌝ -∗ bv_unsigned a ↦ₘ{q} vmem -∗ WPasm es) -∗
  WPasm (ReadMem (RVal_Bits (@bv_to_bvn n vread)) kind (RVal_Bits (@bv_to_bvn 64 a)) len tag ann :t: es).
Proof.
  iIntros (??) "Hm Hcont". setoid_rewrite wp_asm_unfold. subst.
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ????) "(Hctx&Hictx&Hmem)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iDestruct (mem_mapsto_lookup with "Hmem Hm") as %[len' [??]].
  have ? : len' = len by lia. subst.
  iSplit. {
    iPureIntro. eexists _, _, _, _. simpl. econstructor; [done | by econstructor |] => /=.
    eexists _, _, _. simplify_option_eq. naive_solver.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  revert select (∃ _, _) => -[?[?[?[?[?[??]]]]]];
    simplify_option_eq; destruct_and!; destruct_or!; destruct_and?; simplify_eq. 2:{
    iFrame. iSplitL; [|done]. by iApply wp_value.
  }
  iFrame. iSplit; [|done].
  iApply ("Hcont" with "[] [Hm]"); done.
Qed.

Lemma wp_write_mem' `{!islaG Σ} `{!threadG} n len a (vold vnew : bv n) es ann res kind tag:
  n = (8 * len)%N →
  0 < Z.of_N len →
  bv_unsigned a ↦ₘ vold -∗
  ▷ (bv_unsigned a ↦ₘ vnew -∗ WPasm es) -∗
  WPasm (WriteMem (RVal_Bool res) kind (RVal_Bits (@bv_to_bvn 64 a)) (RVal_Bits (@bv_to_bvn n vnew)) len tag ann :t: es).
Proof.
  iIntros (??) "Hm Hcont". subst. setoid_rewrite wp_asm_unfold.
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ????) "(Hctx&Hictx&Hmem)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iDestruct (mem_mapsto_lookup with "Hmem Hm") as %[len' [??]].
  have ? : len' = len by lia. subst.
  iSplit. {
    iPureIntro. eexists _, _, _, _. simpl. econstructor; [done | by econstructor |]. simpl.
    eexists _, _, _. simplify_option_eq. naive_solver.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_".
  inv_seq_step.
  revert select (∃ _, _) => -[?[?[?[?[??]]]]]; simplify_option_eq; destruct_and!; simplify_eq.
  iMod (mem_mapsto_update with "Hmem Hm") as (len' ?) "[Hmem Hm]".
  rewrite Z_to_bv_bv_unsigned. have ? : len' = len by lia. subst. iFrame.
  iModIntro. iSplitL; [|done].
  by iApply ("Hcont" with "Hm").
Qed.

Lemma wp_branch_address' `{!islaG Σ} `{!threadG} v es ann:
  ▷ WPasm es -∗
  WPasm (BranchAddress v ann :t: es).
Proof.
  iIntros "Hcont". setoid_rewrite wp_asm_unfold.
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "(?&Hictx&?)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iSplit. {
    iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
    done.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  iFrame; iSplitL; [|done].
  iApply ("Hcont"); [done..|].
  iFrame.
Qed.

Lemma wp_barrier' `{!islaG Σ} `{!threadG} es v ann:
  ▷ WPasm es -∗
  WPasm (Barrier v ann :t: es).
Proof.
  rewrite wp_asm_eq.
  iIntros "Hcont" ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "Hctx".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iSplit. {
    iPureIntro.
    eexists _, _, _, _; econstructor; [done |by econstructor| done].
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  iFrame; iSplit; [|done].
  iApply "Hcont"; [done..|iFrame].
Qed.

Lemma wp_assume_reg' `{!islaG Σ} `{!threadG} r v ann es al:
  WPreadreg r @ al {{ v', ⌜v = v'⌝ ∗ ▷ WPasm es }} -∗
  WPasm (AssumeReg r al v ann :t: es).
Proof.
  rewrite wp_asm_eq wpreadreg_eq. iIntros "Hr".
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "(?&Hictx&?)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iDestruct ("Hr" with "Hθ") as (v' v'' ??) "[Hr [% Hcont]]"; subst.
  iSplit. {
    iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
    eexists _. split_and! => //.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step. revert select (∃ x, _) => -[?[?[?[?[??]]]]]; simplify_eq/=.
  iFrame; iSplitL; [|done].
  iApply ("Hcont" with "[]"); [done..|].
  iFrame.
Qed.

Lemma wp_assume' `{!islaG Σ} `{!threadG} es ann e:
  WPaexp e {{ v, ⌜v = Val_Bool true⌝ ∗ ▷ WPasm es }} -∗
  WPasm (Assume e ann :t: es).
Proof.
  rewrite wp_a_exp_unfold wp_asm_eq.
  iIntros "Hexp" ([????]) "/= -> -> -> Hθ".
  iDestruct ("Hexp" with "Hθ") as (v ?) "(Hθ&%&Hcont)"; subst.
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "Hctx".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iSplit. {
    iPureIntro.
    eexists _, _, _, _; econstructor; [done | by econstructor|done].
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  iFrame; iSplit; [|done].
  iApply "Hcont"; [done..|iFrame].
Qed.

Lemma wp_abstract_primop' `{!islaG Σ} `{!threadG} es n v args ann:
  ▷ WPasm es -∗
  WPasm (AbstractPrimop n v args ann :t: es).
Proof.
  rewrite wp_asm_eq.
  iIntros "Hcont" ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "Hctx".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iSplit. {
    iPureIntro.
    eexists _, _, _, _; econstructor; [done |by econstructor| done].
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  iFrame; iSplit; [|done].
  iApply "Hcont"; [done..|iFrame].
Qed.

Lemma wp_cases' `{!islaG Σ} `{!threadG} ts:
  ts ≠ [] →
  ▷(∀ t, ⌜t ∈ ts⌝ -∗ WPasm t) -∗
  WPasm (tcases ts).
Proof.
  iIntros (?) "Hwp". setoid_rewrite wp_asm_unfold.
  iIntros ([? regs ? ?]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "Hctx".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iSplit. {
    destruct ts => //.
    iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |econstructor; by left|done].
  }
  iIntros "!>" (????) "_". iMod "HE" as "_".
  inv_seq_step. iModIntro.
  iFrame. iSplitL; [|done].
  by iApply "Hwp".
Qed.

(* Progress! Prove that the WPasm t will definitely eval to WPasm nil. *)
(* Preservation! Prove that the resources after any event still hold *)
(* against the `in_firmware` or `exit_firmware`. *)
(* Since we assume that only at the exit_firmware we can change the PMP *)
(* or MTVEC, we can say that whenever we arrive at the state *)
(* `exit_firmware`, the instruction trace must be the trace of *)
(* exit_firmware_inst. *)
(* exit_firmware state is a trap state which has no next state. How to *)
(* prove this? Because we know the exact value for the pc. *)

Definition illegal_PC `{!islaG Σ} `{!threadG} : iProp Σ :=
  ∀ i: bv 64, ("PC" ↦ᵣ RVal_Bits i ∗
  ⌜~ (bv_unsigned (bv_extract 0 2 i) = 0 ∧ (bv_unsigned osbi_code_addr) <= (bv_unsigned i) < (bv_unsigned osbi_code_end_addr))⌝)
       -∗ "PC" ↦ᵣ RVal_Bits firmware_mtvec.

Definition illegal_Priv `{!islaG Σ} `{!threadG} : iProp Σ :=
  ∀ i, "PC" ↦ᵣ i ∗ ("cur_privilege" ↦ᵣ: λ v, v ≠ RVal_Enum "Machine") -∗
  "PC" ↦ᵣ  RVal_Bits firmware_mtvec ∗ "cur_privilege" ↦ᵣ RVal_Enum "Machine".

Lemma csr_equiv `{!islaG Σ} `{!threadG} :
  reg_col uni_csr ⊣⊢ ∃ csr, ⌜length csr = 3%nat⌝ ∗ reg_col (changed_csr csr).
Proof.
  iSplit; rewrite /changed_csr /reg_col /=.
  - liARun.
    iExists (RegVal_Struct [("bits", RVal_Bits b0)], b1, b0, ())ₗ.
    by liARun.
  - iIntros "[%csr [%Hcsr Hres]]".
    do 4 (destruct csr as [|? csr]; try done); simpl.
    iRevert "Hres".
    liARun.
    iExists (RVal_Bits b, ())ₗ.
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

Lemma instr_agree `{!islaG Σ} `{!threadG} i ins1 ins2 :
  instr i ins1 -∗ instr i ins2 -∗ ⌜ins1 = ins2⌝.
Proof.
  rewrite instr_eq /instr_def.
  iIntros "(%Hinstrs & % & % & % & Htbl)".
  iIntros "(%Hinstrs' & % & % & % & Htbl')".
  iPoseProof (instr_table_agree with "Htbl Htbl'") as "<-".
  by simplify_eq.
Qed.

Definition dorami_firmware (i: bv 64) `{!islaG Σ} `{!threadG} : iProp Σ :=
  "PC" ↦ᵣ RVal_Bits i ∗
  ⌜bv_unsigned (bv_extract 0 2 i) = 0⌝ ∗
  ⌜(bv_unsigned osbi_code_addr) <= (bv_unsigned i) < (bv_unsigned osbi_code_end_addr)⌝ ∗
  (∃ ms: bv 64, "mstatus" # "bits" ↦ᵣ RVal_Bits ms) ∗
  "mtvec" # "bits" ↦ᵣ RVal_Bits firmware_mtvec ∗
  "pmp0cfg" # "bits" ↦ᵣ RVal_Bits device_cfg_when_osbi ∗
  "pmp1cfg" # "bits" ↦ᵣ RVal_Bits monitor_code_cfg_when_osbi ∗
  "pmp2cfg" # "bits" ↦ᵣ RVal_Bits osbi_code_cfg_when_osbi ∗
  "pmp3cfg" # "bits" ↦ᵣ RVal_Bits sp_code_cfg_when_osbi ∗
  "pmp4cfg" # "bits" ↦ᵣ RVal_Bits osbi_data_cfg_when_osbi ∗
  "pmp5cfg" # "bits" ↦ᵣ RVal_Bits monitor_data_cfg_when_osbi ∗
  "pmp6cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
  "pmp7cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
  reg_col dorami_sys_regs ∗ reg_col uni_csr ∗ reg_col uni_gpr ∗ reg_col pmp_regs ∗
  (bv_unsigned osbi_data_addr) ↦ₘ? 0x1000.

Lemma tcons_preservation `{!islaG Σ} `{!threadG} :
  ∀ i e tail,
  NoEvent (e :t: tail) ->
  NoPMPOrMTVECWrite (e :t: tail) ->
  NoStuckEval (e :t: tail) ->
  LegalReadReg (e :t: tail) ->
  LegalWriteReg (e :t: tail) ->
  LegalReadMem (e :t: tail) ->
  LegalWriteMem (e :t: tail) ->
  LegalAssumeReg (e :t: tail) ->
  LegalAssume (e :t: tail) ->
  □ illegal_PC -∗
  ▷(∀ t', (∃ label regs, ⌜trace_step (e:t:tail) regs label t'⌝) -∗
                    (∃ i, dorami_firmware i)  -∗ WPasm t') -∗
  (dorami_firmware i -∗ WPasm (e :t: tail)).
Proof.
  iIntros (i e tail HNoEvent HNoPMP HNoStuckEval HReadReg HWriteReg HReadMem HWriteMem HAssumeReg HAssume) "#Htrap Hnext Hstart".
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
      iDestruct "Hstart" as "(?&?&?&?&Hmtvec&?)".
      iApply (read_reg_struct with "[$Hmtvec]").
      iIntros "HPC !> ->".
      iApply ("Hnext" with "[%]"); first by repeat econstructor.
      iExists i.
      iSimpl.
      by iFrame.
    + destruct s as [bv (->&->&->&?)].
      iApply (wp_read_reg' _ _ _ _ _ _ Hsafe).
      iDestruct "Hstart" as "(?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&Hpmp&?)".
      assert (Hlk: pmp_regs !! 16%nat = Some (KindReg "pmp8cfg", StructShape [("bits", ExactShape (RVal_Bits sp_code_cfg_when_mon'))])) by done.
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
      iDestruct "Hstart" as "(?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&Hpmp&?)".
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
      iDestruct "Hstart" as "(?&?&?&?&?&?&?&?&?&?&?&?&?&Hsys&?&?&?&?)".
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
      destruct (Sumbool.sumbool_and _ _ _ _ (BinInt.Z.eq_dec (bv_unsigned (bv_extract 0 2 bv')) 0) (Sumbool.sumbool_and _ _ _ _ (Z_le_dec (bv_unsigned osbi_code_addr) (bv_unsigned bv')) (Z_lt_dec (bv_unsigned bv')(bv_unsigned osbi_code_end_addr)))) as [[Hbv'1 Hbv'2]|].
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
      iDestruct "Hstart" as "(?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&Hgpr&?)".
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
     iDestruct "Hstart" as "(?&?&?&?&?&?&?&?&?&?&?&?&?&?&Hcsr&?&?&?)".
     assert (Hlk: uni_csr!!1%nat = Some (KindReg "mcause", StructShape [("bits", BitsShape 64)])) by done.
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
    iDestruct "Hstart" as "(Ha&Hb&Hc&Hd&He&Hf&Hg&Hh&Hi&Hj&Hk&Hl&Hm&Hn&Ho&Hp&Hq&Hmem)".
    iDestruct (mem_mapsto_uninit_split (bvn_unsigned addr - bv_unsigned osbi_data_addr) (bv_unsigned osbi_data_addr) _ 0x1000 with "Hmem") as "[HM1 HM2]" ; first lia.
    iDestruct (mem_mapsto_uninit_split (Z.of_N num_bytes) _ _ _ with "HM2") as "[HM2 HM3]"; first lia.
    replace (bv_unsigned osbi_data_addr +
           (bvn_unsigned addr - bv_unsigned osbi_data_addr)) with (bvn_unsigned addr) by lia.
    iDestruct (mem_mapsto_uninit_to_mapsto with "HM2") as "(%num_bits&%vmem&Hmem)".
    rewrite N2Z.id.
    iDestruct "Hmem" as "[-> Hmem]".
    iApply (wp_read_mem' with "Hmem"); first [lia|done|trivial].
    iIntros "/= !> -> Hmem".
    iApply ("Hnext" with "[%]"); first by repeat econstructor.
    iPoseProof (mem_mapsto_mapsto_to_uninit with "Hmem") as "HM2".
    replace (Z.of_N ((num_bytes * 8) `div` 8)) with (Z.of_N num_bytes) by lia.
    iPoseProof (mem_mapsto_uninit_combine with "HM2 HM3") as "HM2"; first lia.
    replace (bv_unsigned addr) with (bv_unsigned osbi_data_addr + (bv_unsigned addr - bv_unsigned osbi_data_addr)) by lia.
    iPoseProof (mem_mapsto_uninit_combine with "HM1 HM2") as "Hmem"; first lia.
    iExists i.
    iSimpl.
    by iFrame "Ha Hb Hc Hd He Hf Hg Hh Hi Hj Hk Hl Hm Hn Ho Hp Hq Hmem".
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
    iDestruct "Hstart" as "(Ha&Hb&Hc&Hd&He&Hf&Hg&Hh&Hi&Hj&Hk&Hl&Hm&Hn&Ho&Hp&Hq&Hmem)".
    iDestruct (mem_mapsto_uninit_split (bvn_unsigned addr - bv_unsigned osbi_data_addr) (bv_unsigned osbi_data_addr) _ 0x1000 with "Hmem") as "[HM1 HM2]" ; first lia.
    iDestruct (mem_mapsto_uninit_split (Z.of_N num_bytes) _ _ _ with "HM2") as "[HM2 HM3]"; first lia.
    replace (bv_unsigned osbi_data_addr +
           (bvn_unsigned addr - bv_unsigned osbi_data_addr)) with (bvn_unsigned addr) by lia.
    iDestruct (mem_mapsto_uninit_to_mapsto with "HM2") as "(%num_bits&%vmem&Hmem)".
    rewrite N2Z.id.
    iDestruct "Hmem" as "[-> Hmem]".
    iApply (wp_write_mem' with "Hmem"); first [lia|done|trivial].
    iIntros "/= !> Hmem".
    iApply ("Hnext" with "[%]"); first by repeat econstructor.
    iPoseProof (mem_mapsto_mapsto_to_uninit with "Hmem") as "HM2".
    replace (Z.of_N ((num_bytes * 8) `div` 8)) with (Z.of_N num_bytes) by lia.
    iPoseProof (mem_mapsto_uninit_combine with "HM2 HM3") as "HM2"; first lia.
    replace (bv_unsigned addr) with (bv_unsigned osbi_data_addr + (bv_unsigned addr - bv_unsigned osbi_data_addr)) by lia.
    iPoseProof (mem_mapsto_uninit_combine with "HM1 HM2") as "Hmem"; first lia.
    iExists i.
    iSimpl.
    by iFrame "Ha Hb Hc Hd He Hf Hg Hh Hi Hj Hk Hl Hm Hn Ho Hp Hq Hmem".
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
     iDestruct "Hstart" as "(?&?&?&?&?&?&?&?&?&?&?&?&?&Hsys&?&?&?&?)".
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
     iDestruct "Hstart" as "(?&?&?&?&?&?&?&?&?&?&?&?&?&Hsys&?&?&?&?)".
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
    all: iDestruct "Hstart" as "(?&?&?&[%mt Hmtvec]&?&?&?&?&?&?&?&?&?&?&?&?&?&?)".
    all: liARun.
    all: iModIntro.
    all: iApply ("Hnext" with "[%]"); first (econstructor; exists (assume_regs_map firmware_mtvec); by econstructor).
    all: iExists i.
    all: iSimpl.
    all: liARun.
    all: iFrame.
    Unshelve.
    all: prepare_sidecond.
    all: bv_solve.
  - iApply wp_abstract_primop'.
    iApply ("Hnext" with "[%]"); first by repeat econstructor.
    by iExists i.

  Unshelve.
  all: by refine (assume_regs_map firmware_mtvec).
Qed.

Lemma tcases_preservation `{!islaG Σ} `{!threadG} :
  ∀ i es,
  es ≠ [] →
  ▷ (∀ t, ⌜t ∈ es⌝ -∗
        ((∃ i, dorami_firmware i) -∗ WPasm t)) -∗
  (dorami_firmware i -∗ WPasm (tcases es)).
Proof.
  iIntros (i es ?) "Hnext Hstart".
  iApply wp_cases'; first done.
  iIntros (t) "%Hin !>".
  iApply "Hnext"; first done.
  by iExists i.
Qed.

(* Should have the "instr i (Some t)" *)
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
  NoPMPOrMTVECWrite t ∨ (t = exit_firmware.a0.a0 ∧ i = osbi_code_end_addr) ->
  □ illegal_PC -∗
  ((∃ i, dorami_firmware i)
    ∨ ("PC" ↦ᵣ RVal_Bits sp_code_addr ∗
       ∃ csr gpr mem,
           ⌜ length csr = 4%nat ∧ length gpr = 5%nat ⌝ ∗
           Fstart_SP csr gpr mem)
      -∗ WPasm tnil) -∗
  (dorami_firmware i -∗ WPasm t).

Lemma valid_trace_contract `{!islaG Σ} `{!threadG} : trace_contract.
Proof.
  iLöb as "IH".
  iIntros (i t Hnoevent Hnotempty Hnostuck Hreadreg Hwritereg Hreadmem Hwritemem Hassumereg Hassume [Htrace | [Htrace Hpc]] ) "#Htrap Hnext Hfirm"; first destruct t eqn:Heq.
  - iApply "Hnext".
    iLeft.
    by iExists i.
  - iApply (tcons_preservation with "[//] [Hnext]"); try done.
    iIntros (t2) "!> [%label [%regs %Hstep]] [%i' Hfirm]".
    iApply ("IH" with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Htrap Hnext Hfirm").
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
    + left. by apply (trace_step_NoPMPOrMTVECWrite (e:t:i0) regs label t2).
  - iApply (tcases_preservation with "[Hnext]"); try done.
    { simpl in Hnotempty.
      rewrite /= !Is_true_true !andb_true_iff in Hnotempty.
      destruct Hnotempty as [Hemp _].
      by apply bool_decide_eq_true_1 in Hemp.
      }
    iIntros (subt) "!> %Hin [%y Hfirm]".
    iApply ("IH" with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [//] Hnext Hfirm").
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
      eexists. exists (assume_regs_map firmware_mtvec).
      split; [ by constructor | done] .
    + rewrite /= /LegalReadReg in Hreadreg.
      intros Hnonil t' Hrtc.
      apply (Hreadreg ltac:(done) t').
      refine (rtc_l _ _ _ _ _ Hrtc).
      eexists. exists (assume_regs_map (firmware_mtvec)).
      split; [ by constructor | done] .
    + rewrite /= /LegalWriteReg in Hwritereg.
      intros Hnonil t' Hrtc.
      apply (Hwritereg ltac:(done) t').
      refine (rtc_l _ _ _ _ _ Hrtc).
      eexists. exists (assume_regs_map firmware_mtvec).
      split; [ by constructor | done] .
    + rewrite /= /LegalReadMem in Hreadmem.
      intros Hnonil t' Hrtc.
      apply (Hreadmem ltac:(done) t').
      refine (rtc_l _ _ _ _ _ Hrtc).
      eexists. exists (assume_regs_map firmware_mtvec).
      split; [ by constructor | done] .
    + rewrite /= /LegalWriteMem in Hwritemem.
      intros Hnonil t' Hrtc.
      apply (Hwritemem ltac:(done) t').
      refine (rtc_l _ _ _ _ _ Hrtc).
      eexists. exists (assume_regs_map firmware_mtvec).
      split; [ by constructor | done] .
    + rewrite /= !Is_true_true forallb_forall in Hassumereg.
      rewrite Is_true_true.
      by apply Hassumereg, elem_of_list_In.
    + rewrite /= !Is_true_true forallb_forall in Hassume.
      rewrite Is_true_true.
      by apply Hassume, elem_of_list_In.
    + left.
      rewrite /= !Is_true_true forallb_forall in Htrace.
      rewrite Is_true_true.
      by apply Htrace, elem_of_list_In.
  - simplify_eq.
    iDestruct "Hfirm" as "(?&?&?&[% ?]&?&?&?&?&?&?&?&?&?&?&Hcsr&Hgpr&?&Hmem)".
    do 400 liAStep; liShow.
    do 10 liAStep; liShow.
    do 10 liAStep; liShow.
    liAStep; liShow.
    liAStep; liShow.
    liAStep; liShow.
    liAStep; liShow.
    iApply "Hnext".
    iRight.
    liAStep; liShow.
    liAStep; liShow.
    liAStep; liShow.
    liAStep; liShow.
    iPoseProof (csr_equiv with "Hcsr") as "[%csr [%Hcsr ?]]".
    iPoseProof (gpr_equiv with "Hgpr") as "[%gpr [%Hgpr ?]]".
    iExists csr, gpr.
    iDestruct (mem_mapsto_uninit_to_mapsto with "Hmem") as "(%n' & %mem & -> & Hmem)".
    iExists mem.
    by destruct csr as [|? csr].
Qed.

Definition universal_instrs `{!islaG Σ} `{!threadG} : iProp Σ :=
  ([∗ list] i ↦ _ ∈ replicate 1023 (), (∃ t, instr (0x80020000 + i * 4) (Some t) ∗ ⌜NoPMPOrMTVECWrite t  ∧ NoEmptyCases t ∧ NoEvent t ∧ NoStuckEval t ∧ LegalReadReg t ∧ LegalWriteReg t ∧ LegalReadMem t ∧ LegalWriteMem t ∧ LegalAssumeReg t ∧ LegalAssume t⌝)).

Definition universal_spec `{!islaG Σ} `{!threadG} csr gpr mem : iProp Σ :=
  Ffirmware csr gpr mem ∗
  instr_pre (bv_unsigned sp_code_addr) (
     ∃ csr gpr mem, Fstart_SP csr gpr mem ∗
     True
).

Theorem universal_contract `{!islaG Σ} `{!threadG} :
  ∀ (i: bv 64) csr gpr mem,
  bv_unsigned (bv_extract 0 2 i) = 0 ->
  (bv_unsigned osbi_code_addr) <= (bv_unsigned i) < (bv_unsigned osbi_code_end_addr) ->
  length csr = 4%nat ->
  length gpr = 5%nat ->
  □ illegal_PC -∗
  universal_instrs -∗
  instr (bv_unsigned osbi_code_end_addr) (Some exit_firmware.a0.a0) -∗
  instr_body (bv_unsigned i) (universal_spec csr gpr mem).
Proof.
  iLöb as "IH".
  iIntros (i csr gpr mem Hi1 Hi2 Hcsr Hgpr) "#Htrap #Hinsts #Hexit".
  assert (Hlk: (replicate 1023 ()) !! (Z.to_nat (((bv_unsigned i) -  (bv_unsigned osbi_code_addr)) / 4)) = Some ()).
  { apply lookup_replicate. split; first done.
    rewrite /osbi_code_addr /osbi_code_end_addr !bv_unsigned_BV in Hi2 |- *. lia.
  }
  iPoseProof (big_sepL_delete _ _ _ _ Hlk) as "[Helem _]".
  iPoseProof ("Helem" with "[$Hinsts]") as "[#(%t & Hinst & (%HNoPMP & %HNoEmptyCase & %HNoEvent & %HNoStuck & %HReadReg & %HWriteReg & %HReadMem & %HWriteMem & %HAssumeReg & %HAssume)) _]".
  replace (2147614720 + Z.to_nat ((bv_unsigned i - bv_unsigned osbi_code_addr) `div` 4) * 4) with (bv_unsigned i).
  2:{
    apply bv_extract_divisible in Hi1.
    destruct Hi1 as [quo Hquo].
    rewrite /osbi_code_addr !bv_unsigned_BV !Hquo in Hi2 |- *. lia.
  }
  iApply (instr_pre_intro_Some with "Hinst").
  iClear "Helem Hinst".
  iIntros "[Hfirm Hsafe] HPC".
  iApply (valid_trace_contract i t HNoEvent HNoEmptyCase HNoStuck HReadReg HWriteReg HReadMem HWriteMem HAssumeReg HAssume with "[//] [Hsafe]"); first by left.
  2:{
  do 5 (destruct csr as [|? csr]; try done).
  do 6 (destruct gpr as [|? gpr]; try done).
  iDestruct "Hfirm" as "(Hmtvec&Hmstatus&?&?&?&?&?&?&?&?&Hsys&Hcsr&Hgpr&Hpmp&Hmem)".
  unfold dorami_firmware.
  iPoseProof (csr_equiv with "[Hcsr]") as "Hcsr"; first by (iExists [b0;b1;b2]; iFrame).
  iPoseProof (gpr_equiv with "[Hgpr]") as "Hgpr"; first by (iExists [b3; b4; b5; b6; b7]; iFrame).
  liARun.
  iApply (mem_mapsto_mapsto_to_uninit with "Hmem").
  Unshelve. all: prepare_sidecond; bv_solve. }
  clear i Hi1 Hi2 Hlk t HNoPMP HNoEvent HNoEmptyCase HNoStuck HReadReg HWriteReg HReadMem HWriteMem HAssumeReg HAssume.
  iIntros "[HRes | [HPC Hsp]]".
  - iDestruct "HRes" as "[%i (HPC&%Hi1&%Hi2&[%mt Hmtvec]& Hmstatus&Hp0&Hp1&Hp2&Hp3&Hp4&Hp5&Hp6&Hp7&Hsys&Hcsr&Hgpr&Hpmp&Hmem)]".
    assert (Hlk: (replicate 1023 ()) !! (Z.to_nat (((bv_unsigned i) -  (bv_unsigned osbi_code_addr)) / 4)) = Some ()).
    { apply lookup_replicate. split; first done.
      rewrite /osbi_code_addr /osbi_code_end_addr !bv_unsigned_BV in Hi2 |- *; lia.
    }
    iPoseProof (big_sepL_delete _ _ _ _ Hlk) as "[Helem _]".
    iPoseProof ("Helem" with "[$Hinsts]") as "[#(%t & Hinst & (%HNoPMP & %HNoEmptyCase & %HNoEvent & %HNoStuck & %HReadReg & %HWriteReg & %HReadMem & %HWriteMem & %HAssumeReg & %HAssume)) _]".
    replace (2147614720 + Z.to_nat ((bv_unsigned i - bv_unsigned osbi_code_addr) `div` 4) * 4) with (bv_unsigned i).
    2:{
      apply bv_extract_divisible in Hi1.
      destruct Hi1 as [quo Hquo].
      rewrite /osbi_code_addr !bv_unsigned_BV !Hquo in Hi2 |- *. lia.
    }
    iApply (wp_next_instr with "[$HPC] Hinst").
    iIntros "!> HPC".
    iClear "Helem Hinst".
    iApply (valid_trace_contract i t HNoEvent HNoEmptyCase HNoStuck HReadReg HWriteReg HReadMem HWriteMem HAssumeReg HAssume with "[//] [Hsafe]"); first by left.
    2:{
    unfold dorami_firmware.
    liARun; by iFrame. }
    iIntros "Hstate".
    clear i csr gpr mem Hi1 Hi2 Hcsr Hgpr Hlk t HNoPMP HNoEvent HNoEmptyCase HNoStuck HReadReg HWriteReg HReadMem HWriteMem HAssumeReg HAssume.
    iDestruct "Hstate" as "[[%i (HPC&%Hi1&%Hi2&Hfirm)] | [HPC Hsp]]".
    +
      iDestruct "Hfirm" as "([%ms Hms]&?&?&?&?&?&?&?&?&?&Hsys&Hcsr&Hgpr&Hpmp&Hmem)".
      iPoseProof (csr_equiv with "Hcsr") as "[%csr [%Hcsr ?]]".
      iPoseProof (gpr_equiv with "Hgpr") as "[%gpr [%Hgpr ?]]".
      iDestruct (mem_mapsto_uninit_to_mapsto with "Hmem") as "(%n&%mem&->&Hmem)".
      iSpecialize ("IH" $! i (ms::csr) gpr mem Hi1 Hi2 _ _ with "Htrap Hinsts Hexit").
      iApply (wp_next_instr_pre with "[$HPC] IH [-]").
      iFrame "Hsafe".
      simpl.
      liARun.
      by iFrame.
      Unshelve.
      1: simpl; by f_equal.
      1: done.
    + iApply (wp_next_instr_pre with "[$HPC] Hsafe [Hsp]").
      iDestruct "Hsp" as "(%csr & %gpr & %mem & ? & Hres)".
      iExists csr, gpr, mem.
      by iFrame.
  - iApply (wp_next_instr_pre with "[$HPC] Hsafe [Hsp]").
    iDestruct "Hsp" as "(%csr' & %gpr' & %mem' & ? & Hres)".
    iExists csr', gpr', mem'.
    by iFrame.
Qed.

(* The security comes from rigid information flow, or three things *)
(* deriving the rigid info flow: *)
(* 1. Rigid Control Flow *)
(* 2. Memory Separation *)
(* 3. Well-Defined Context Switch(Well-Defined Input and Output of Regs)  *)

(* The security of SM is the precondition of that of enclave because *)
(* enclave is managed by SM. We can assume the property about the enclave *)
(* program and SM, then prove that the enclave execution holds the *)
(* integrity and confidentiality. *)
(*                                                                        *)
(*                                                                        *)
(* INTEGRITY in the view point of enclave execution: *)
(* Assumptions: *)
(* 1. Monitor's control flow is fixed when P is entered from P_entry. *)
(* 2. User / Enclave / OS / RT can effect SM only by specified input *)
(*    (arguments of function call?). *)
(* 3. Enclave program only read/write the enclave's internal state and *)
(*    enclave's input, including mem and registers ( and randomness? ). *)
(* Prove: User / Other Enclave / OS / Firmware can effect Enclave's *)
(*        state and output only by specified inputs. *)
(*                                                                        *)
(*                                                                        *)
(* CONFIDENTIALITY in the view point of attacker(consider only Firmware): *)
(* Assumptions: *)
(* 1. Monitor's state can not be inferred by firmware. *)
(* 2. Enclave Program outputs is well-defined. *)
(* Prove: *)
(* 1. Firmware's state transition is only determined by its own initial *)
(*    state and I_P(The non-determinism includes randomness from entropy *)
(*    sources, direct memory accesses from I/O peripherals, etc.) *)
(*    Or we say, Enclave's state can not be inferred by firmware. *)

(* Since monitor disables interrupt and have no exception by design, *)
(* the monitor only needs to guarantee that the firmware's resulting *)
(* state have no effect on the control flow after P_entry. Considering *)
(* the rigid control transfer, we only need to guarantee that the *)
(* resulting state of monitor starting from P_entry depends only on the *)
(* Monitor's mem. *)
(*                                                                        *)

(* Specific Well-defined Ecall *)
(* Here the well-definedness means the input, arguments to ecall and *)
(* ouput, return value, are well defined, two specified subsets of regs. *)
(* Save the Non-input and Restore the trusted version. *)
(* Attention: the intersection of Input and Ouput. *)
Section ctx_switch.

Context `{!islaG Σ} `{!threadG}.
Variable f_restore_firm_csr : bv (0x20000 * 8) -> list (bv 64).
Variable f_restore_firm_gpr : bv 64 -> bv 64 -> bv (0x20000 * 8) -> list (bv 64).

Hypothesis f_restore_firm_csr_prop :
  ∀ mem,
    length (f_restore_firm_csr mem) = 4%nat
    ∧ ∃ ms, (f_restore_firm_csr mem) !! 0%nat = Some ms
    ∧ (bv_extract 3 1 ms) = (BV 1 0).

Hypothesis f_restore_firm_gpr_prop :
  ∀ mem x10 x11,
    length (f_restore_firm_gpr x10 x11 mem) = 5%nat.

Variable f_restore_encl_csr : bv 64 -> bv (0x20000 * 8) -> list (bv 64).
Variable f_restore_encl_gpr : bv 64 -> bv (0x20000 * 8) -> list (bv 64).

Hypothesis f_restore_encl_csr_prop :
  ∀ mem satp,
    length (f_restore_encl_csr satp mem) = 4%nat
    ∧ ∃ ms, (f_restore_encl_csr satp mem) !! 0%nat = Some ms
    ∧ (bv_extract 3 1 ms) = (BV 1 0).

Hypothesis f_restore_encl_gpr_prop :
  ∀ mem x10,
    length (f_restore_encl_gpr x10 mem) = 5%nat.

Variable start_encl_addr : bv 64.
Variable end_encl_addr : bv 64.

Definition restore_firm_ctx_spec (x10 x11: bv 64) (csr gpr: list (bv 64)) (mem: bv (0x20000 * 8)) : iProp Σ :=
  monitor csr (<[3%nat := x10]> $ <[4%nat := x11]> $ gpr) mem ∗
  instr_pre (bv_unsigned P2F_code_addr) (
    ∃ mem', monitor (f_restore_firm_csr mem) (f_restore_firm_gpr x10 x11 mem) mem'
  ).

Arguments restore_firm_ctx_spec /.

Definition restore_encl_ctx_spec (x10 satp: bv 64) (csr gpr: list (bv 64)) (mem: bv (0x20000 * 8)): iProp Σ :=
  monitor (<[1%nat := satp]> csr) (<[3%nat := x10]> gpr) mem ∗
  instr_pre (bv_unsigned start_encl_addr) (
    ∃ mem', monitor (f_restore_encl_csr satp mem) (f_restore_encl_gpr x10 mem) mem'
  ).

Arguments restore_encl_ctx_spec /.

(* Save the Non-ouput and Restore the untrusted version. *)
Hypothesis restore_firm_ctx : ∀ (x10 x11: bv 64) (csr gpr: list (bv 64)) (mem: bv (0x20000 * 8)), ⊢ instr_body (bv_unsigned end_encl_addr) (restore_firm_ctx_spec x10 x11 csr gpr mem).

Hypothesis restore_encl_ctx : ∀ (x10 satp: bv 64) (csr gpr: list (bv 64)) (mem: bv (0x20000 * 8)), ⊢ instr_body (bv_unsigned monitor_code_addr + 0x1c) (restore_encl_ctx_spec x10 satp csr gpr mem).

Definition end_encl x10 x11 csr gpr Pmem Fmem :=
  Machine monitor_mtvec monitor_pmpcfgs csr (<[3%nat := x10]> $ <[4%nat := x11]> $ gpr) Pmem Fmem.

Arguments end_encl /.

Definition start_firmware x10 x11 Pmem Pmem' Fmem :=
  Machine firmware_mtvec firmware_pmpcfgs (f_restore_firm_csr Pmem) (<[2%nat := (BV 64 0x989B989D981E)]>(f_restore_firm_gpr x10 x11 Pmem)) Pmem' Fmem.

Arguments start_firmware /.

Definition end_firmware x10 satp csr gpr Pmem Fmem :=
  Machine firmware_mtvec sp_pmpcfgs (<[1%nat := satp]> $ csr) (<[3%nat := x10]> $ gpr) Pmem Fmem.

Arguments end_firmware /.

Definition start_encl x10 satp Pmem Fmem :=
  Machine monitor_mtvec monitor_pmpcfgs (f_restore_encl_csr satp Pmem) (f_restore_encl_gpr x10 Pmem) Pmem Fmem.

Arguments start_encl /.

Theorem confidentiality :
  ∀ (x10 x11: bv 64) (csr gpr: list (bv 64)) (Pmem: bv (0x20000 * 8)) (Fmem: bv (0x1000 * 8)),
  length csr = 4%nat ->
  length gpr = 5%nat ->
  (∃ v, csr !! 0%nat = Some v ∧ (bv_extract 3 1 v) = (BV 1 0x0)) ->
  ⊢
  instr (bv_unsigned osbi_code_addr - 0x2c) (Some P2F.a0.a0) -∗
  instr (bv_unsigned osbi_code_addr - 0x28) (Some P2F.a4.a4) -∗
  instr (bv_unsigned osbi_code_addr - 0x24) (Some P2F.a8.a8) -∗
  instr (bv_unsigned osbi_code_addr - 0x20) (Some P2F.ac.ac) -∗
  instr (bv_unsigned osbi_code_addr - 0x1c) (Some P2F.a10.a10) -∗
  instr (bv_unsigned osbi_code_addr - 0x18) (Some P2F.a14.a14) -∗
  instr (bv_unsigned osbi_code_addr - 0x14) (Some P2F.a18.a18) -∗
  instr (bv_unsigned osbi_code_addr - 0x10) (Some P2F.a1c.a1c) -∗
  instr (bv_unsigned osbi_code_addr - 0xc) (Some P2F.a20.a20) -∗
  instr (bv_unsigned osbi_code_addr - 0x8) (Some P2F.a24.a24) -∗
  instr (bv_unsigned osbi_code_addr - 0x4) (Some P2F.a28.a28) -∗
  instr_body (bv_unsigned end_encl_addr) (
    Machine monitor_mtvec monitor_pmpcfgs csr (<[3%nat := x10]> $ <[4%nat := x11]> $ gpr) Pmem Fmem ∗
    instr_pre (bv_unsigned osbi_code_addr)
      (∃ Pmem', Machine firmware_mtvec firmware_pmpcfgs (f_restore_firm_csr Pmem) (<[2%nat := (BV 64 0x989B989D981E)]>(f_restore_firm_gpr x10 x11 Pmem)) Pmem' Fmem)
  ).
Proof using restore_firm_ctx f_restore_firm_csr f_restore_firm_csr_prop f_restore_firm_gpr f_restore_firm_gpr_prop end_encl_addr.
  intros x10 x11 csr gpr Pmem Fmem Hcsr Hgpr.
  do 5 (destruct csr as [|? csr]; try inversion Hcsr).
  do 6 (destruct gpr as [|? gpr]; try inversion Hgpr).
  clear H1 H2 H3 H4 H5 H6 H7 H8 H9 Hcsr Hgpr.
  intros [ms [[= <-] Hms]].
  iStartProof.
  iIntros.
  iPoseProof (restore_firm_ctx x10 x11 [b; b0; b1; b2] [b3; b4; b5; b6; b7] Pmem) as "Hctx".
  unfold restore_firm_ctx_spec.
  destruct (f_restore_firm_csr_prop Pmem) as [Hcsr [ms [Heqms Hmie]]].
  specialize (f_restore_firm_gpr_prop Pmem x10 x11) as Hgpr.
  remember (f_restore_firm_csr Pmem) as csr.
  remember (f_restore_firm_gpr x10 x11 Pmem) as gpr.
  do 5 (destruct csr as [|? csr]; try inversion Hcsr).
  do 6 (destruct gpr as [|? gpr]; try inversion Hgpr).
  clear H1 H2 H3 H4 H5 H6 H7 H8 H9 Hcsr Hgpr.
  do 50 liAStep; liShow.
  do 20 liAStep; liShow.
  liAStep;liShow.
  liAStep;liShow.
  liAStep;liShow.
  liAStep;liShow.
  liAStep;liShow.
  liAStep;liShow.
  liAStep;liShow.
  iClear (Pmem Heqcsr Heqgpr ms Hms Hmie Heqms) "Hctx".
  rewrite {2}instr_pre'_eq /instr_pre'_def.
  iIntros "!> [%Pmem Hstate]".
  iPoseProof (P2F [b8; b9; b10; b11] [b12; b13; b14; b15; b16] Pmem with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]") as "HP2F"; try done.
  rewrite {2}instr_pre'_eq /instr_pre'_def.
  iSimpl in "HP2F".
  replace (bv_unsigned osbi_code_addr - 44) with ((bv_unsigned P2F_code_addr)) by by simpl.
  iApply "HP2F".
  iRevert "Hstate".
  liARun.
  by iFrame.
Qed.

Theorem integrity :
  ∀ (x10 satp: bv 64) (csr gpr: list (bv 64)) Pmem Fmem,
  length csr = 4%nat ->
  length gpr = 5%nat ->
  ⊢
  instr (bv_unsigned sp_code_addr) (Some Sally_Port.a0.a0) -∗
  instr (bv_unsigned sp_code_addr + 0x4) (Some Sally_Port.a4.a4) -∗
  instr (bv_unsigned sp_code_addr + 0x8) (Some Sally_Port.a8.a8) -∗
  instr (bv_unsigned sp_code_addr + 0xc) (Some Sally_Port.ac.ac) -∗
  instr (bv_unsigned sp_code_addr + 0x10) (Some Sally_Port.a10.a10) -∗
  instr (bv_unsigned sp_code_addr + 0x14) (Some Sally_Port.a14.a14) -∗
  instr (bv_unsigned sp_code_addr + 0x18) (Some Sally_Port.a18.a18) -∗
  instr (bv_unsigned sp_code_addr + 0x1c) (Some Sally_Port.a1c.a1c) -∗
  instr (bv_unsigned sp_code_addr + 0x20) (Some Sally_Port.a20.a20) -∗
  instr (bv_unsigned sp_code_addr + 0x24) (Some Sally_Port.a24.a24) -∗
  instr (bv_unsigned sp_code_addr + 0x28) (Some Sally_Port.a28.a28) -∗
  instr (bv_unsigned sp_code_addr + 0x2c) (Some Sally_Port.a2c.a2c) -∗
  instr (bv_unsigned sp_code_addr + 0x30) (Some Sally_Port.a30.a30) -∗
  instr (bv_unsigned sp_code_addr + 0x34) (Some Sally_Port.a34.a34) -∗
  instr (bv_unsigned monitor_code_addr) (Some P_entry.a0.a0) -∗
  instr (bv_unsigned monitor_code_addr + 0x4) (Some P_entry.a4.a4) -∗
  instr (bv_unsigned monitor_code_addr + 0x8) (Some P_entry.a8.a8) -∗
  instr (bv_unsigned monitor_code_addr + 0xc) (Some P_entry.ac.ac) -∗
  instr (bv_unsigned monitor_code_addr + 0x10) (Some P_entry.a10.a10) -∗
  instr (bv_unsigned monitor_code_addr + 0x14) (Some P_entry.a14.a14) -∗
  instr (bv_unsigned monitor_code_addr + 0x18) (Some P_entry.a18.a18) -∗
  (∃ ins, instr ((bv_unsigned monitor_code_addr + 0x1c)) (Some ins)) -∗
  instr_body (bv_unsigned sp_code_addr) (
    Machine firmware_mtvec sp_pmpcfgs (<[1%nat := satp]> $ csr) (<[3%nat := x10]> $ gpr) Pmem Fmem ∗
    instr_pre (bv_unsigned start_encl_addr)
      (∃ Pmem', Machine monitor_mtvec monitor_pmpcfgs (f_restore_encl_csr satp Pmem) (f_restore_encl_gpr x10 Pmem) Pmem' Fmem)
  ).
Proof using restore_encl_ctx f_restore_encl_csr f_restore_encl_csr_prop f_restore_encl_gpr f_restore_encl_gpr_prop start_encl_addr.
  intros x10 satp csr gpr Pmem Fmem Hcsr Hgpr.
  do 5 (destruct csr as [|? csr]; try inversion Hcsr).
  do 6 (destruct gpr as [|? gpr]; try inversion Hgpr).
  clear H1 H2 H3 H4 H5 H6 H7 H8 H9 Hcsr Hgpr.
  iStartProof.
  iIntros "? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? [%ins #Hencl]".
  iPoseProof (F2P [b; satp; b1; b2] [b3; b4; b5; x10; b7] Pmem with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]") as "HF2P".
  1,2:done.
  do 10 liAStep; liShow.
  do 10 liAStep; liShow.
  do 10 liAStep; liShow.
  do 10 liAStep; liShow.
  do 10 liAStep; liShow.
  do 10 liAStep; liShow.
  do 10 liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  iPoseProof (restore_encl_ctx x10 satp [ms; b0; b1; b2] [b3; b4; (BV 64 0x9B9898989D1E); b6; b7] Pmem) as "Hctx".
  iIntros "Hstate".
  rewrite {1}instr_pre'_eq /instr_pre'_def.
  iSimpl in "Hctx".
  iSpecialize ("Hctx" with "[-]").
  { iRevert "Hstate".
    liARun.
    destruct (f_restore_encl_csr_prop Pmem satp) as [Hcsr [ms' [Hms' Hmie]]].
    remember (f_restore_encl_csr satp Pmem) as csr.
    do 5 (destruct csr as [|? csr]; try inversion Hcsr).
    clear H2 H3 H4 H5.
    liARun.
    by iFrame. }
  iDestruct "Hctx" as "(%ins' & #Hinstr' & Hsafe)".
  by iPoseProof (instr_agree with "Hencl Hinstr'") as "<-".
Qed.

End ctx_switch.

(* Information Flow: *)
(* Ecall Enclave -> SM : Ecall Arguments by regs *)
(* Ocall Enclave -> SM : Ecall Arguments by regs and host shared mem *)
(* OS -> SM : Ecall Arguments by regs and host shared mem *)
(* Firmware -> SM : well-defined subset of regs *)
(* SM -> Firmware : Ecall Arguments / Exception No. / Int No. *)
(* SM -> Enclave: *)
(* Ecall / Non-Timer Trap : well-defined subset of regs *)
(* Enclave Mgmt / Ocall Case: well-defined subset of regs and host shared *)
(* mem *)


(* Intgrity Guarantee: Enclave execution is fully decided by the Input *)
(* and Enclave's Internal State. => the internal Enclave State are still *)
(* same after the same Enclave instruction and Input and State even other *)
(* things are different. *)
(* => Input Seq and Init Config fully determines Enclave Execution. *)
(* Input(OS via SM): subset of regs, host shared mem. *)
(* Input(FM via SM): subset of regs. *)
(* Input(Env via SM): subset of regs, host shared mem. *)

(* Confidentiality: Firmware's execution is fully decided by the public *)
(* State Vars. => the puibc State Vars are still same after the same *)
(* Firmware instructions if they are same before, even the enclave state *)
(* is different. *)
(* => Public State Seq and Init fully determines the Firmware Execution. *)
(* Output: the whole resulting machine State. The condition is that the *)
(* observable part of State cannot leak. => same as before. *)
(* observable part. *)

(* Requirement: state after P_entry is fully determined by enclave's data *)
(* region, the mem part except the general registers. *)
(* Integrity: the firmware's state and input non-intefere the enclave's *)
(* state. *)
(* Confidentiality: the enclave's state and input non-interfere the *)
(* resulting states observable by firmware. *)
(* Inherit GPR and recover CSR. *)
