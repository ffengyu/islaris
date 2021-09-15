(* generated by Ott 0.31 from: isla_lang.ott *)

Require Export isla.base isla.bitvector.










Definition var_name : Set := Z.
Definition eq_var_name (v w : var_name) : bool := Z.eqb v w.

Definition register_name : Set := string.

Inductive enum_id : Type :=
| Mk_enum_id : nat -> enum_id.

Inductive enum_ctor : Type :=
| Mk_enum_ctor : nat -> enum_ctor.

Inductive annot : Type :=
| Mk_annot : annot.

Definition enum : Set := (enum_id*enum_ctor).

Inductive bvarith : Set := 
 | Bvnand : bvarith
 | Bvnor : bvarith
 | Bvxnor : bvarith
 | Bvsub : bvarith
 | Bvudiv : bvarith
 | Bvudivi : bvarith
 | Bvsdiv : bvarith
 | Bvsdivi : bvarith
 | Bvurem : bvarith
 | Bvsrem : bvarith
 | Bvsmod : bvarith
 | Bvshl : bvarith
 | Bvlshr : bvarith
 | Bvashr : bvarith.

Inductive bvcomp : Set := 
 | Bvult : bvcomp
 | Bvslt : bvcomp
 | Bvule : bvcomp
 | Bvsle : bvcomp
 | Bvuge : bvcomp
 | Bvsge : bvcomp
 | Bvugt : bvcomp
 | Bvsgt : bvcomp.

Inductive bvmanyarith : Set := 
 | Bvand : bvmanyarith
 | Bvor : bvmanyarith
 | Bvxor : bvmanyarith
 | Bvadd : bvmanyarith
 | Bvmul : bvmanyarith.

Inductive binop : Set := 
 | Eq : binop
 | Bvarith (bvarith5:bvarith)
 | Bvcomp (bvcomp5:bvcomp).

Inductive manyop : Set := 
 | And : manyop
 | Or : manyop
 | Bvmanyarith (bvmanyarith5:bvmanyarith)
 | Concat : manyop.

Inductive base_val : Set := 
 | Val_Symbolic (vvar5:var_name)
 | Val_Bool (bool5:bool)
 | Val_Bits (bv5:bvn)
 | Val_Enum (enum5:enum).

Inductive unop : Set := 
 | Not : unop
 | Bvnot : unop
 | Bvredand : unop
 | Bvredor : unop
 | Bvneg : unop
 | Extract (nat5:N) (nat':N)
 | ZeroExtend (nat5:N)
 | SignExtend (nat5:N).

Inductive ty : Set := 
 | Ty_Bool : ty
 | Ty_BitVec (nat5:N)
 | Ty_Enum (enum_ty5:enum_id)
 | Ty_Array (ty1:ty) (ty2:ty).

Inductive exp : Set := 
 | Val (base_val5:base_val) (annot5:annot)
 | Unop (unop5:unop) (exp5:exp) (annot5:annot)
 | Binop (binop5:binop) (exp1:exp) (exp2:exp) (annot5:annot)
 | Manyop (manyop5:manyop) (_:list exp) (annot5:annot)
 | Ite (exp1:exp) (exp2:exp) (exp3:exp) (annot5:annot).

Inductive valu : Set := 
 | RegVal_Base (base_val5:base_val)
 | RegVal_I (bvi5:Z) (int5:Z)
 | RegVal_String (str5:string)
 | RegVal_Unit : valu
 | RegVal_NamedUnit (name5:register_name)
 | RegVal_Vector (_:list valu)
 | RegVal_List (_:list valu)
 | RegVal_Struct (_:list (register_name * valu))
 | RegVal_Poison : valu.

Inductive accessor : Set := 
 | Field (name5:register_name).

Inductive smt : Set := 
 | DeclareConst (vvar5:var_name) (ty5:ty)
 | DefineConst (vvar5:var_name) (exp5:exp)
 | Assert (exp5:exp)
 | DefineEnum (int5:Z).

Definition valu_option : Set := option valu.

Definition accessor_list : Set := list accessor.

Inductive event : Set := 
 | Smt (smt5:smt) (annot5:annot)
 | Branch (int5:Z) (str5:string) (annot5:annot) (*r Sail trace fork *)
 | ReadReg (name5:register_name) (accessor_list5:accessor_list) (valu5:valu) (annot5:annot) (*r read value `valu` from register `name` *)
 | WriteReg (name5:register_name) (accessor_list5:accessor_list) (valu5:valu) (annot5:annot) (*r write value `valu` to register `name` *)
 | ReadMem (valu5:valu) (rkind:valu) (addr:valu) (num_bytes:N) (tag_value:valu_option) (annot5:annot) (*r read value `valu` from memory address `addr`, with read kind `rkind`, byte width `byte_width`, and `tag_value` is the optional capability tag *)
 | WriteMem (valu5:valu) (wkind:valu) (addr:valu) (data:valu) (num_bytes:N) (tag_value:valu_option) (annot5:annot) (*r write value `valu` to memory address `addr`, with write kind `wkind`, byte width `byte_width`, `tag_value` is the optional capability tag, and success flag `vvar` *)
 | BranchAddress (addr:valu) (annot5:annot) (*r announce branch address `addr`, to induce ctrl dependency in the concurrency model *)
 | Barrier (bkind:valu) (annot5:annot) (*r memory barrier of kind `bkind` *)
 | CacheOp (ckind:valu) (addr:valu) (annot5:annot) (*r cache maintenance effect of kind `ckind`, at address `addr`, for data-cache clean etc. *)
 | MarkReg (name5:register_name) (str5:string) (annot5:annot) (*r instrumentation to tell concurrency model to ignore certain dependencies (TODO: support marking multiple registers). Currently the str is ignore-edge or ignore-write *)
 | Cycle (annot5:annot) (*r instruction boundary *)
 | Instr (opcode:valu) (annot5:annot) (*r records the instruction `opcode` that was fetched *)
 | Sleeping (vvar5:var_name) (annot5:annot) (*r Arm sleeping predicate *)
 | WakeRequest (annot5:annot) (*r Arm wake request *)
 | SleepRequest (annot5:annot) (*r Arm sleep request *).

Definition trc : Set := list event.

Definition trcs : Set := list (list event).
(** induction principles *)
Section exp_rect.

Variables
  (P_list_exp : list exp -> Prop)
  (P_exp : exp -> Prop).

Hypothesis
  (H_Val : forall (base_val5:base_val), forall (annot5:annot), P_exp (Val base_val5 annot5))
  (H_Unop : forall (unop5:unop), forall (exp5:exp), P_exp exp5 -> forall (annot5:annot), P_exp (Unop unop5 exp5 annot5))
  (H_Binop : forall (binop5:binop), forall (exp1:exp), P_exp exp1 -> forall (exp2:exp), P_exp exp2 -> forall (annot5:annot), P_exp (Binop binop5 exp1 exp2 annot5))
  (H_Manyop : forall (exp_list:list exp), P_list_exp exp_list -> forall (manyop5:manyop), forall (annot5:annot), P_exp (Manyop manyop5 exp_list annot5))
  (H_Ite : forall (exp1:exp), P_exp exp1 -> forall (exp2:exp), P_exp exp2 -> forall (exp3:exp), P_exp exp3 -> forall (annot5:annot), P_exp (Ite exp1 exp2 exp3 annot5))
  (H_list_exp_nil : P_list_exp nil)
  (H_list_exp_cons : forall (exp0:exp), P_exp exp0 -> forall (exp_l:list exp), P_list_exp exp_l -> P_list_exp (cons exp0 exp_l)).

Fixpoint exp_ott_ind (n:exp) : P_exp n :=
  match n as x return P_exp x with
  | (Val base_val5 annot5) => H_Val base_val5 annot5
  | (Unop unop5 exp5 annot5) => H_Unop unop5 exp5 (exp_ott_ind exp5) annot5
  | (Binop binop5 exp1 exp2 annot5) => H_Binop binop5 exp1 (exp_ott_ind exp1) exp2 (exp_ott_ind exp2) annot5
  | (Manyop manyop5 exp_list annot5) => H_Manyop exp_list (((fix exp_list_ott_ind (exp_l:list exp) : P_list_exp exp_l := match exp_l as x return P_list_exp x with nil => H_list_exp_nil | cons exp1 xl => H_list_exp_cons exp1(exp_ott_ind exp1)xl (exp_list_ott_ind xl) end)) exp_list) manyop5 annot5
  | (Ite exp1 exp2 exp3 annot5) => H_Ite exp1 (exp_ott_ind exp1) exp2 (exp_ott_ind exp2) exp3 (exp_ott_ind exp3) annot5
end.

End exp_rect.

(** substitutions *)
Definition subst_val_base_val (base_val5:base_val) (vvar_6:var_name) (base_val_6:base_val) : base_val :=
  match base_val_6 with
  | (Val_Symbolic vvar5) => (if eq_var_name vvar5 vvar_6 then base_val5 else (Val_Symbolic vvar5))
  | (Val_Bool bool5) => Val_Bool bool5
  | (Val_Bits bv5) => Val_Bits bv5
  | (Val_Enum enum5) => Val_Enum enum5
end.

Fixpoint subst_val_exp (base_val_6:base_val) (vvar5:var_name) (exp_6:exp) {struct exp_6} : exp :=
  match exp_6 with
  | (Val base_val5 annot5) => Val (subst_val_base_val base_val_6 vvar5 base_val5) annot5
  | (Unop unop5 exp5 annot5) => Unop unop5 (subst_val_exp base_val_6 vvar5 exp5) annot5
  | (Binop binop5 exp1 exp2 annot5) => Binop binop5 (subst_val_exp base_val_6 vvar5 exp1) (subst_val_exp base_val_6 vvar5 exp2) annot5
  | (Manyop manyop5 exp_list annot5) => Manyop manyop5 (map (fun (exp_:exp) => (subst_val_exp base_val_6 vvar5 exp_)) exp_list) annot5
  | (Ite exp1 exp2 exp3 annot5) => Ite (subst_val_exp base_val_6 vvar5 exp1) (subst_val_exp base_val_6 vvar5 exp2) (subst_val_exp base_val_6 vvar5 exp3) annot5
end.

Definition subst_val_smt (base_val5:base_val) (vvar_6:var_name) (smt5:smt) : smt :=
  match smt5 with
  | (DeclareConst vvar5 ty5) => DeclareConst vvar5 ty5
  | (DefineConst vvar5 exp5) => DefineConst vvar5 (subst_val_exp base_val5 vvar_6 exp5)
  | (Assert exp5) => Assert (subst_val_exp base_val5 vvar_6 exp5)
  | (DefineEnum int5) => DefineEnum int5
end.

Fixpoint subst_val_valu (base_val_6:base_val) (vvar5:var_name) (addr5:valu) {struct addr5} : valu :=
  match addr5 with
  | (RegVal_Base base_val5) => RegVal_Base (subst_val_base_val base_val_6 vvar5 base_val5)
  | (RegVal_I bvi5 int5) => RegVal_I bvi5 int5
  | (RegVal_String str5) => RegVal_String str5
  | RegVal_Unit => RegVal_Unit 
  | (RegVal_NamedUnit name5) => RegVal_NamedUnit name5
  | (RegVal_Vector valu_list) => RegVal_Vector (map (fun (valu_:valu) => (subst_val_valu base_val_6 vvar5 valu_)) valu_list)
  | (RegVal_List valu_list) => RegVal_List (map (fun (valu_:valu) => (subst_val_valu base_val_6 vvar5 valu_)) valu_list)
  | (RegVal_Struct selem_list) => RegVal_Struct selem_list
  | RegVal_Poison => RegVal_Poison 
end.

Definition subst_val_event (base_val5:base_val) (vvar_6:var_name) (event5:event) : event :=
  match event5 with
  | (Smt smt5 annot5) => Smt (subst_val_smt base_val5 vvar_6 smt5) annot5
  | (Branch int5 str5 annot5) => Branch int5 str5 annot5
  | (ReadReg name5 accessor_list5 valu5 annot5) => ReadReg name5 accessor_list5 (subst_val_valu base_val5 vvar_6 valu5) annot5
  | (WriteReg name5 accessor_list5 valu5 annot5) => WriteReg name5 accessor_list5 (subst_val_valu base_val5 vvar_6 valu5) annot5
  | (ReadMem valu5 rkind addr num_bytes tag_value annot5) => ReadMem (subst_val_valu base_val5 vvar_6 valu5) (subst_val_valu base_val5 vvar_6 rkind) (subst_val_valu base_val5 vvar_6 addr) num_bytes tag_value annot5
  | (WriteMem valu5 wkind addr data num_bytes tag_value annot5) => WriteMem (subst_val_valu base_val5 vvar_6 valu5) (subst_val_valu base_val5 vvar_6 wkind) (subst_val_valu base_val5 vvar_6 addr) (subst_val_valu base_val5 vvar_6 data) num_bytes tag_value annot5
  | (BranchAddress addr annot5) => BranchAddress (subst_val_valu base_val5 vvar_6 addr) annot5
  | (Barrier bkind annot5) => Barrier (subst_val_valu base_val5 vvar_6 bkind) annot5
  | (CacheOp ckind addr annot5) => CacheOp (subst_val_valu base_val5 vvar_6 ckind) (subst_val_valu base_val5 vvar_6 addr) annot5
  | (MarkReg name5 str5 annot5) => MarkReg name5 str5 annot5
  | (Cycle annot5) => Cycle annot5
  | (Instr opcode annot5) => Instr (subst_val_valu base_val5 vvar_6 opcode) annot5
  | (Sleeping vvar5 annot5) => Sleeping vvar5 annot5
  | (WakeRequest annot5) => WakeRequest annot5
  | (SleepRequest annot5) => SleepRequest annot5
end.


Coercion RegVal_Base : base_val >-> valu.
Definition base_val_to_exp (v : base_val) : exp := Val v Mk_annot.
Coercion base_val_to_exp : base_val >-> exp.



