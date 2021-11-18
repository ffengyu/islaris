(****************************************************************************)
(* BSD 2-Clause License                                                     *)
(*                                                                          *)
(* Copyright (c) 2019-2021 The Islaris Developers                           *)
(*                                                                          *)
(* Michael Sammler                                                          *)
(* Rodolphe Lepigre                                                         *)
(* Angus Hammond                                                            *)
(* Brian Campbell                                                           *)
(* Jean Pichon-Pharabod                                                     *)
(* Peter Sewell                                                             *)
(*                                                                          *)
(* All rights reserved.                                                     *)
(*                                                                          *)
(* This was in part funded from the European Research Council (ERC) under   *)
(* the European Union's Horizon 2020 research and innovation programme      *)
(* (grant agreement No 789108, "ELVER"), in part supported by the UK        *)
(* Government Industrial Strategy Challenge Fund (ISCF) under the Digital   *)
(* Security by Design (DSbD) Programme, to deliver a DSbDtech enabled       *)
(* digital platform (grant 105694), and in part funded by Google.           *)
(*                                                                          *)
(*                                                                          *)
(* Redistribution and use in source and binary forms, with or without       *)
(* modification, are permitted provided that the following conditions are   *)
(* met:                                                                     *)
(*                                                                          *)
(* 1. Redistributions of source code must retain the above copyright        *)
(* notice, this list of conditions and the following disclaimer.            *)
(*                                                                          *)
(* 2. Redistributions in binary form must reproduce the above copyright     *)
(* notice, this list of conditions and the following disclaimer in the      *)
(* documentation and/or other materials provided with the distribution.     *)
(*                                                                          *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS      *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT        *)
(* LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR    *)
(* A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT     *)
(* HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,   *)
(* SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT         *)
(* LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,    *)
(* DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY    *)
(* THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT      *)
(* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE    *)
(* OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.     *)
(*                                                                          *)
(*                                                                          *)
(* Exceptions to this license are detailed in THIRD_PARTY_FILES.md          *)
(****************************************************************************)

Require Import isla.aarch64.aarch64.
Require Import isla.instructions.instr_str.

Definition spec `{!islaG Σ} `{!threadG} a : iProp Σ :=
  "R1" ↦ᵣ RVal_Bits [BV{64} 0x0000000000000008] ∗
  0x0000000000000008 ↦ₘ [BV{64} 0x00000000deadbeef] ∗
  "R9" ↦ᵣ RVal_Bits [BV{64} 0x00000000cafebabe] ∗
  reg_col sys_regs ∗
  instr_pre a (
    "R1" ↦ᵣ RVal_Bits [BV{64} 0x0000000000000008] ∗
    0x0000000000000008 ↦ₘ [BV{64} 0x00000000cafebabe] ∗
    "R9" ↦ᵣ RVal_Bits [BV{64} 0x00000000cafebabe] ∗
    reg_col sys_regs ∗
    True).

Lemma store_wp `{!islaG Σ} `{!threadG}:
  instr 0x0000000010300000 (Some instr_str) -∗
  instr_body 0x0000000010300000 (spec 0x0000000010300004).
Proof.
  iStartProof.
  unfold spec.
  repeat liAStep; liShow.
Qed.
