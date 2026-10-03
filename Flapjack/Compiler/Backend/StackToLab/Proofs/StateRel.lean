import Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Compiler.Backend.LabSem.Updates
import Flapjack.Compiler.Backend.StackProps.CallArgs
import Flapjack.Compiler.Backend.StackProps.OrderedLabels
import Flapjack.Misc.GoodDimindex

/-! The simulation relation `state_rel` of `stack_to_labProofScript.sml`
(lines 600-645) and its state-update lemmas (lines 647-736), between the
native StackSem state and the native LabSem state. -/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled

/-- Same-module re-export of the canonical StackSem state roundtrip;
infrastructure for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Complete original StackSem/LabSem simulation relation, conjunct for
conjunct. HOL sets are Bool predicates; `domain s.code = set (MAP Section_num
t.code)` is pointwise membership equivalence. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "state_rel_def"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs])
  (words_as_type_indexed_bitvec)]
def stateRel {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F)
    (t : Flapjack.Compiler.Backend.LabSem.State width C F) : Prop :=
  (∀ n v, s.regs.lookup n = some v → t.regs n = v) ∧
  (∀ n v, s.fpRegs.lookup n = some v → t.fpRegs n = v) ∧
  t.memory = s.memory ∧
  t.memDomain = s.mdomain ∧
  t.sharedMemDomain = s.shMdomain ∧
  t.be = s.be ∧
  t.ffi = s.ffi ∧
  t.clock = s.clock ∧
  (∀ n prog, sptLookup n s.code = some prog →
    StackProps.callArgs prog t.ptrReg t.lenReg t.ptr2Reg t.len2Reg t.linkReg ∧
    ∃ pc, codeInstalled pc
        (appListAppend (flattenHOL true prog n
          (Compiler.Backend.StackAlloc.nextLabHOL prog 2) [] []).1) t.code ∧
      locToPc n 0 t.code = some pc) ∧
  (∀ x, sptDomain s.code x ↔ x ∈ t.code.map (·.sectionId)) ∧
  (∀ sec ∈ t.code, LabProps.secLabelsOk sec) ∧
  ¬t.failed = true ∧
  t.linkReg ≠ t.lenReg ∧ t.linkReg ≠ t.ptrReg ∧
  t.linkReg ≠ t.len2Reg ∧ t.linkReg ≠ t.ptr2Reg ∧
  ¬s.ffiSaveRegs t.linkReg = true ∧
  (∀ k i n, s.ffiSaveRegs k = true → t.ioRegs n i k = none) ∧
  (∀ k n, s.ffiSaveRegs k = true → t.ccRegs n k = none) ∧
  (∀ x : BitVec width, s.mdomain x = true → x.toNat % (width / 8) = 0) ∧
  (∀ x : BitVec width, s.shMdomain x = true → x.toNat % (width / 8) = 0) ∧
  s.codeBuffer = t.codeBuffer ∧
  s.compile = (fun c p => t.compile c (p.map progToSectionHOL)) ∧
  t.compileOracle = (fun n =>
    ((s.compileOracle n).1, (s.compileOracle n).2.1.map progToSectionHOL)) ∧
  (∀ k, (∀ np ∈ (s.compileOracle k).2.1,
      StackProps.callArgs np.2 t.ptrReg t.lenReg t.ptr2Reg t.len2Reg t.linkReg ∧
      (∀ l ∈ StackPropsCodeLabels.extractLabels np.2, l.1 = np.1 ∧ l.2 ≠ 0 ∧ l.2 ≠ 1) ∧
      (StackPropsCodeLabels.extractLabels np.2).Nodup) ∧
    ((s.compileOracle k).2.1.map Prod.fst).Nodup) ∧
  ¬s.useStack = true ∧
  ¬s.useStore = true ∧
  ¬s.useAlloc = true ∧
  goodDimindex width

/-- A checked StackSem location resolves to a LabSem program position. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "loc_check_IMP_loc_to_pc"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs])
  (words_as_type_indexed_bitvec)]
theorem locCheckImpLocToPc {width : Nat} [NeZero width] {C F : Type}
    {s : StackSemStateFiniteExact width C F}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {l1 l2 : Nat} :
    StackSem.locCheckExact s.code (l1, l2) ∧ stateRel s t1 →
      ∃ v, locToPc l1 l2 t1.code = some v := by
  rintro ⟨check, rel⟩
  have code := rel.2.2.2.2.2.2.2.2.1
  rcases check with ⟨zero, mem⟩ | ⟨key, prog, found, labels⟩
  · simp only at zero mem
    subst zero
    obtain ⟨prog, found⟩ := Option.isSome_iff_exists.mp mem
    obtain ⟨_, pc, _, entry⟩ := code l1 prog found
    exact ⟨pc, entry⟩
  · obtain ⟨_, pc, installed, _⟩ := code key prog found
    exact CodeInstalled.codeInstalledGetLabelsImp _ _ _ _ _ _ pc ⟨installed, labels⟩

/-- Decrementing both clocks preserves the relation. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "state_rel_dec_clock"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs])
  (words_as_type_indexed_bitvec)]
theorem stateRelDecClock {width : Nat} [NeZero width] {C F : Type}
    {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} :
    stateRel s t → stateRel (StackSemStateOps.decClock s) (LabSem.decClock t) := by
  rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, by simp [StackSemStateOps.decClock, LabSem.decClock, h8],
    h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
    h27, h28, h29⟩

/-- Changing the LabSem program counter preserves the relation. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "state_rel_with_pc"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs])
  (words_as_type_indexed_bitvec)]
theorem stateRelWithPc {width : Nat} [NeZero width] {C F : Type}
    {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} {pc : Nat} :
    stateRel s t → stateRel s (updPc pc t) := id

/-- Setting both clocks to the same value preserves the relation. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "state_rel_with_clock"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs])
  (words_as_type_indexed_bitvec)]
theorem stateRelWithClock {width : Nat} [NeZero width] {C F : Type}
    {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} {k : Nat} :
    stateRel s t → stateRel { s with clock := k } { t with clock := k } := by
  rintro ⟨h1, h2, h3, h4, h5, h6, h7, _, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, rfl, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩

/-- Writing the same value to a source variable and target register
preserves the relation. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "set_var_upd_reg"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs])
  (words_as_type_indexed_bitvec)]
theorem setVarUpdReg {width : Nat} [NeZero width] {C F : Type}
    {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} {a : Nat} {b : WordLocW width} :
    stateRel s t → stateRel (StackSemStateOps.setVar a b s) (updReg a b t) := by
  rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩
  refine ⟨?_, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩
  intro n v found
  simp only [StackSemStateOps.setVar, HolFiniteMapExact.updateEq, FUPDATE_HOL, updReg] at found ⊢
  split_ifs at found ⊢ with eq
  · cases found; rfl
  · exact h1 n v found

/-- The literal-word instance of `set_var_upd_reg`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "set_var_Word_upd_reg"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs])
  (words_as_type_indexed_bitvec)]
theorem setVarWordUpdReg {width : Nat} [NeZero width] {C F : Type}
    {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} {a : Nat} {b : BitVec width} :
    stateRel s t →
      stateRel (StackSemStateOps.setVar a (.word b) s) (updReg a (.word b) t) :=
  setVarUpdReg

/-- Writing the same value to a source and target FP register preserves the
relation. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "set_fp_var_upd_fp_reg"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs])
  (words_as_type_indexed_bitvec)]
theorem setFpVarUpdFpReg {width : Nat} [NeZero width] {C F : Type}
    {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} {a : Nat} {b : BitVec 64} :
    stateRel s t → stateRel (StackSemStateOps.setFpVar a b s) (updFpReg a b t) := by
  rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩
  refine ⟨h1, ?_, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩
  intro n v found
  simp only [StackSemStateOps.setFpVar, HolFiniteMapExact.updateEq, FUPDATE_HOL,
    updFpReg] at found ⊢
  split_ifs at found ⊢ with eq
  · cases found; rfl
  · exact h2 n v found

/-- A successful source memory store is simulated by the target update. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "mem_store_upd_mem"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs])
  (words_as_type_indexed_bitvec)]
theorem memStoreUpdMem {width : Nat} [NeZero width] {C F : Type}
    {s s1 : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} {x : BitVec width}
    {y : WordLocW width} :
    stateRel s t ∧ StackSemStateOps.memStore x y s = some s1 → stateRel s1 (updMem x y t) := by
  rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩, store⟩
  unfold StackSemStateOps.memStore at store
  split_ifs at store
  cases store
  exact ⟨h1, h2, by simp [updMem, h3], h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩

/-- A defined source register agrees with the target register. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "state_rel_read_reg_FLOOKUP_regs"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs])
  (words_as_type_indexed_bitvec)]
theorem stateRelReadRegFlookupRegs {width : Nat} [NeZero width] {C F : Type}
    {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} {x : Nat} {y : WordLocW width} :
    stateRel s t ∧ s.regs.lookup x = some y → y = t.regs x := by
  rintro ⟨rel, found⟩
  exact (rel.1 x y found).symm

/-- A defined source FP register agrees with the target FP register. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "state_rel_read_fp_reg_FLOOKUP_fp_regs"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs])
  (words_as_type_indexed_bitvec)]
theorem stateRelReadFpRegFlookupFpRegs {width : Nat} [NeZero width] {C F : Type}
    {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} {n : Nat} {x : BitVec 64} :
    stateRel s t ∧ StackSemStateOps.getFpVar n s = some x → x = readFpReg n t := by
  rintro ⟨rel, found⟩
  exact (rel.2.1 n x found).symm

/-- A defined source register-or-immediate operand agrees with the target
operand. The StackSem `get_var_imm` mirror reads the accepted
`WordRegImm` form of the same `asm$reg_imm` operand, through the checked
`HolRegImm.toWordRegImm` codec used by the StackSem evaluator. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "state_rel_get_var_imm"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs])
  (words_as_type_indexed_bitvec)]
theorem stateRelGetVarImm {width : Nat} [NeZero width] {C F : Type}
    {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} {r : HolRegImm width}
    {x : WordLocW width} :
    stateRel s t ∧ StackSemStateOps.getVarImm (HolRegImm.toWordRegImm r) s = some x →
      regImm r t = x := by
  rintro ⟨rel, found⟩
  cases r with
  | reg name =>
      exact rel.1 name x found
  | imm value =>
      simp only [HolRegImm.toWordRegImm, StackSemStateOps.getVarImm] at found
      cases found
      rfl

end Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
