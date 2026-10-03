import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenSemantics
import Flapjack.Compiler.Backend.StackRemove.Compile
import Flapjack.Compiler.Backend.StackNames.ProgramNames
import Flapjack.Misc.WordList
import Flapjack.Misc.Alignment
import Flapjack.HolArb

/-! `make_init_def`, `memory_assumption_def`, `halt_assum_lemma`,
`FLOOKUP_regs` and `state_rel_make_init`
(`stack_to_labProofScript.sml:3027-3192`): the StackSem state built from a
LabSem state, the memory layout assumption on that LabSem state, the halting
procedure of compiled code, and `state_rel` of the built state. -/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.MakeInit
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCallCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

/-- Genuine canonical roundtrip for the imported actual state carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Canonical owning-state roundtrip; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

-- Inhabitedness of the original HOL field types, not chosen values.
private instance {α β : Type} : Nonempty (HolFiniteMapExact α β) := ⟨HolFiniteMapExact.empty⟩
private instance {width : Nat} [NeZero width] : Nonempty (WordSemBuffer width width) :=
  ⟨⟨0, [], 0⟩⟩
private instance {width : Nat} [NeZero width] : Nonempty (WordSemGcFun width) :=
  ⟨fun _ => none⟩

/-- HOL `make_init_def`. The record literal `<| ... |>` leaves `store`,
`stack`, `stack_space`, `bitmaps`, `data_buffer` and `gc_fun` as the fields of
HOL's `ARB` state; each is the shared opaque `holArb` of its (C/F-free) field
type. `FEMPTY |++ MAP (λr. (r, read_reg r s)) regs` is `updateListEq` from
`empty`, with the LabSem overload `read_reg r s = s.regs r`; the `num set`
`save_regs` is a Bool predicate, as `ffi_save_regs`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "make_init_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
noncomputable def makeInit {width : Nat} [NeZero width] {C F : Type}
    (code : Spt (HolProg width))
    (coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (regs : List Nat) (saveRegs : Nat → Bool)
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    StackSemStateFiniteExact width C F where
  regs := HolFiniteMapExact.empty.updateListEq (regs.map fun r => (r, s.regs r))
  fpRegs := HolFiniteMapExact.empty
  store := holArb _
  stack := holArb _
  stackSpace := holArb Nat
  memory := s.memory
  mdomain := s.memDomain
  shMdomain := s.sharedMemDomain
  bitmaps := holArb _
  compile := fun c p => s.compile c (p.map progToSectionHOL)
  compileOracle := coracle
  codeBuffer := s.codeBuffer
  dataBuffer := holArb _
  gcFun := holArb _
  useStack := false
  useStore := false
  useAlloc := false
  clock := s.clock
  code := code
  ffi := s.ffi
  ffiSaveRegs := saveRegs
  be := s.be

/-- HOL `make_init_semantics` (`val`, line 3047): `flatten_semantics` at
`s1 := make_init code coracle regs save_regs s`, `s2 := s`, with the built
state's code evaluated to `code`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "make_init_semantics"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs])
  (words_as_type_indexed_bitvec)]
theorem makeInitSemantics {width : Nat} [NeZero width] {C F : Type}
    {code : Spt (HolProg width)}
    {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {regs : List Nat} {saveRegs : Nat → Bool}
    {s : Flapjack.Compiler.Backend.LabSem.State width C F} {start : Nat} :
    haltAssum C F code ∧
    stateRel (makeInit code coracle regs saveRegs s : StackSemStateFiniteExact width C F) s ∧
    locToPc start 0 s.code = some s.pc ∧
    StackSemEvaluate.semantics start (makeInit code coracle regs saveRegs s) ≠ .fail →
    semantics s = StackSemEvaluate.semantics start (makeInit code coracle regs saveRegs s) :=
  fun h => FlattenSemantics.flattenSemantics h

/-- HOL `memory_assumption_def`. `read_reg r t` is the LabSem overload
`t.regs r`; `find_name` over the `num_map` of register names is
`findNameSpt`; `≤₊` is unsigned `BitVec` order; the separating `*` is
left-associated `SetSep.star`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "memory_assumption_def"
  (words_as_type_indexed_bitvec)]
noncomputable def memoryAssumption {width : Nat} [NeZero width] {C F : Type}
    (rnames : Spt Nat) (bitmaps : List (BitVec width)) (dataSp : Nat)
    (t : Flapjack.Compiler.Backend.LabSem.State width C F) : Prop :=
  ∃ ptr2 ptr3 ptr4 bitmapPtr : BitVec width,
    t.regs (StackNames.findNameSpt rnames 2) = .word ptr2 ∧
    t.regs (StackNames.findNameSpt rnames 3) = .word ptr3 ∧
    t.regs (StackNames.findNameSpt rnames 4) = .word ptr4 ∧
    t.memory ptr2 = .word bitmapPtr ∧
    t.memory (ptr2 + StackRemove.bytesInWord width) =
      .word (bitmapPtr + StackRemove.bytesInWord width * BitVec.ofNat width bitmaps.length) ∧
    t.memory (ptr2 + 2 * StackRemove.bytesInWord width) =
      .word (bitmapPtr + StackRemove.bytesInWord width * BitVec.ofNat width dataSp +
        StackRemove.bytesInWord width * BitVec.ofNat width bitmaps.length) ∧
    t.memory (ptr2 + 3 * StackRemove.bytesInWord width) = .word t.codeBuffer.position ∧
    t.memory (ptr2 + 4 * StackRemove.bytesInWord width) =
      .word (t.codeBuffer.position + BitVec.ofNat width t.codeBuffer.spaceLeft) ∧
    t.codeBuffer.buffer = [] ∧
    ptr2 ≤ ptr4 ∧ holByteAligned ptr2 = true ∧
    holByteAligned ptr4 = true ∧ holByteAligned bitmapPtr = true ∧
    1024 * StackRemove.bytesInWord width ≤ ptr4 - ptr2 ∧
    SetSep.star
      (SetSep.star (Misc.wordList bitmapPtr (bitmaps.map WordLocW.word))
        (Misc.wordListExists
          (bitmapPtr + StackRemove.bytesInWord width * BitVec.ofNat width bitmaps.length) dataSp))
      (Misc.wordListExists ptr2
        ((-1 * ptr2 + ptr4).toNat / (StackRemove.bytesInWord width).toNat))
      (SetSep.fun2Set (t.memory, fun a => t.memDomain a = true))

/-- HOL `halt_assum_lemma` (local): procedure 1 of the stack_names renaming of
stack_remove's compiled code halts with `Word 0w`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "halt_assum_lemma"
  (words_as_type_indexed_bitvec)]
theorem haltAssumLemma {width : Nat} [NeZero width] {C F : Type} {f : Spt Nat} {jump : Bool}
    {off : BitVec width × BitVec width} {gen : Bool} {maxHeap k l : Nat}
    {code : List (Nat × HolProg width)} :
    haltAssum C F (sptFromAList (StackNames.compileHOL f
      (StackRemove.compileHOL jump off gen maxHeap k l code))) := by
  rintro s ⟨hsub, h0⟩
  have h1 : sptLookup 1 (sptFromAList (StackNames.compileHOL f
      (StackRemove.compileHOL jump off gen maxHeap k l code))) =
      some (StackNames.progCompHOL f (StackRemove.haltInst (0 : BitVec width))) := by
    simp [sptLookup_sptFromAList, StackNames.compileHOL, StackRemove.compileHOL,
      StackRemove.initStubs, StackNames.progCompEntryHOL, sptAListLookup]
  obtain ⟨-, hl⟩ := hsub 1 ((sptMem_iff_lookup _ _).2 ⟨_, h1⟩)
  rw [h1] at hl
  rw [StackSemEvaluate.evaluate_call]
  simp only [StackSemControl.findCode, hl, if_neg h0, StackSemEvaluateClock.fixClockEvaluate]
  simp only [StackRemove.haltInst, StackNames.progCompHOL, StackSemEvaluate.evaluate_seq,
    StackSemEvaluate.evaluate_inst, StackNames.instFindNameHOL]
  simp [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    StackSemExpressions.assign, StackSemExpressions.wordExp,
    StackSemControl.fixClock, StackSemEvaluate.evaluate_halt, StackSemStateOps.getVar,
    StackSemStateOps.setVar, StackSemControl.badFunReturn, StackSemStateOps.emptyEnv,
    StackSemStateOps.decClock, FUPDATE_HOL]

/-- HOL `FLOOKUP_regs` (local). The HOL binder `f`, of an unconstrained type
and not occurring in the statement, is vacuous and omitted. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "FLOOKUP_regs"
  (words_as_type_indexed_bitvec)]
theorem flookupRegs {width : Nat} [NeZero width] {C F : Type} :
    ∀ (regs : List Nat) (n : Nat) (v : WordLocW width)
      (s : Flapjack.Compiler.Backend.LabSem.State width C F),
      (HolFiniteMapExact.empty.updateListEq (regs.map fun r => (r, s.regs r))).lookup n =
        some v → s.regs n = v := by
  intro regs n v s
  simp only [HolFiniteMapExact.updateListEq]
  suffices h : ∀ (m : FiniteMap Nat (WordLocW width)), (∀ v, m n = some v → s.regs n = v) →
      FUPDATE_LIST_HOL m (regs.map fun r => (r, s.regs r)) n = some v → s.regs n = v from
    h _ (fun v hv => by simp [HolFiniteMapExact.empty] at hv)
  induction regs with
  | nil => intro m hm h; exact hm v h
  | cons r rs ih =>
    intro m hm h
    rw [List.map_cons, FUPDATE_LIST_HOL_cons] at h
    refine ih _ (fun v' hv' => ?_) h
    simp only [FUPDATE_HOL] at hv'
    split at hv'
    · rename_i e; subst e; simpa using hv'
    · exact hm v' hv'

/-- HOL `state_rel_make_init`: `state_rel` of the built state reduces to the
conjuncts of `state_rel_def` that `make_init` does not establish. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "state_rel_make_init"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs])
  (words_as_type_indexed_bitvec)]
theorem stateRelMakeInit {width : Nat} [NeZero width] {C F : Type}
    {code : Spt (HolProg width)}
    {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {regs : List Nat} {saveRegs : Nat → Bool}
    {s : Flapjack.Compiler.Backend.LabSem.State width C F} :
    stateRel (makeInit code coracle regs saveRegs s : StackSemStateFiniteExact width C F) s ↔
      (∀ n prog, sptLookup n code = some prog →
        StackProps.callArgs prog s.ptrReg s.lenReg s.ptr2Reg s.len2Reg s.linkReg ∧
        ∃ pc, codeInstalled pc
            (appListAppend (flattenHOL true prog n
              (Compiler.Backend.StackAlloc.nextLabHOL prog 2) [] []).1) s.code ∧
          locToPc n 0 s.code = some pc) ∧
      ¬s.failed = true ∧
      s.compileOracle = (fun n => ((coracle n).1, (coracle n).2.1.map progToSectionHOL)) ∧
      (∀ k, (∀ np ∈ (coracle k).2.1,
          StackProps.callArgs np.2 s.ptrReg s.lenReg s.ptr2Reg s.len2Reg s.linkReg ∧
          (∀ l ∈ StackPropsCodeLabels.extractLabels np.2, l.1 = np.1 ∧ l.2 ≠ 0 ∧ l.2 ≠ 1) ∧
          (StackPropsCodeLabels.extractLabels np.2).Nodup) ∧
        ((coracle k).2.1.map Prod.fst).Nodup) ∧
      s.linkReg ≠ s.lenReg ∧ s.linkReg ≠ s.ptrReg ∧
      s.linkReg ≠ s.len2Reg ∧ s.linkReg ≠ s.ptr2Reg ∧
      ¬saveRegs s.linkReg = true ∧
      (∀ x, sptDomain code x ↔ x ∈ s.code.map (·.sectionId)) ∧
      (∀ sec ∈ s.code, LabProps.secLabelsOk sec) ∧
      (∀ k i n, saveRegs k = true → s.ioRegs n i k = none) ∧
      (∀ k n, saveRegs k = true → s.ccRegs n k = none) ∧
      (∀ x : BitVec width, s.memDomain x = true → x.toNat % (width / 8) = 0) ∧
      (∀ x : BitVec width, s.sharedMemDomain x = true → x.toNat % (width / 8) = 0) ∧
      goodDimindex width := by
  constructor
  · rintro ⟨-, -, -, -, -, -, -, -, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
      h21, -, -, h24, h25, -, -, -, h29⟩
    exact ⟨h9, h12, h24, h25, h13, h14, h15, h16, h17, h10, h11, h18, h19, h20, h21, h29⟩
  · rintro ⟨h9, h12, h24, h25, h13, h14, h15, h16, h17, h10, h11, h18, h19, h20, h21, h29⟩
    exact ⟨fun n v h => flookupRegs regs n v s h,
      fun n v h => by simp [makeInit, HolFiniteMapExact.empty] at h,
      rfl, rfl, rfl, rfl, rfl, rfl, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
      h21, rfl, rfl, h24, h25, by simp [makeInit], by simp [makeInit], by simp [makeInit], h29⟩

end Flapjack.Compiler.Backend.StackToLab.Proofs.MakeInit
