import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapBounds
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAFixInconsistenciesProps

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Full Seq case with the original guarded second-program IH followed by the
first-program IH. The actual produced first state discharges its guard. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransPropsSeq {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (ih :
      (∀ (firstOut : WordLangProgHOL (BitVec width)) (firstTree : Spt Nat) (firstCounter : Nat),
        (firstOut, firstTree, firstCounter) = ssaCcTrans first ssa next tables →
        ∀ (bodyOut : WordLangProgHOL (BitVec width)) (treeOut : Spt Nat) (counterOut : Nat),
          ssaCcTrans second firstTree firstCounter tables = (bodyOut, treeOut, counterOut) →
          ssaMapOK firstCounter firstTree ∧ isAllocVar firstCounter →
          firstCounter ≤ counterOut ∧ isAllocVar counterOut ∧ ssaMapOK counterOut treeOut) ∧
      (∀ (bodyOut : WordLangProgHOL (BitVec width)) (treeOut : Spt Nat) (counterOut : Nat),
        ssaCcTrans first ssa next tables = (bodyOut, treeOut, counterOut) →
        ssaMapOK next ssa ∧ isAllocVar next →
        next ≤ counterOut ∧ isAllocVar counterOut ∧ ssaMapOK counterOut treeOut))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.seq first second) ssa next tables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  generalize firstEq : ssaCcTrans first ssa next tables = firstResult
  rcases firstResult with ⟨firstOut, firstTree, firstCounter⟩
  have firstFrame := ih.2 firstOut firstTree firstCounter firstEq h
  generalize secondEq : ssaCcTrans second firstTree firstCounter tables = secondResult
  rcases secondResult with ⟨secondOut, secondTree, secondCounter⟩
  have secondFrame := ih.1 firstOut firstTree firstCounter firstEq.symm
    secondOut secondTree secondCounter secondEq ⟨firstFrame.2.2, firstFrame.2.1⟩
  simp only [ssaCcTrans, firstEq, secondEq, Prod.mk.injEq] at produced
  obtain ⟨_, rfl, rfl⟩ := produced
  exact ⟨Nat.le_trans firstFrame.1 secondFrame.1, secondFrame.2.1, secondFrame.2.2⟩

/-- Full MustTerminate case with exactly the original same-context body IH. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransPropsMustTerminate {width : Nat} [NeZero width]
    (body : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (ih : ∀ (bodyOut : WordLangProgHOL (BitVec width)) (treeOut : Spt Nat) (counterOut : Nat),
      ssaCcTrans body ssa next tables = (bodyOut, treeOut, counterOut) →
      ssaMapOK next ssa ∧ isAllocVar next →
      next ≤ counterOut ∧ isAllocVar counterOut ∧ ssaMapOK counterOut treeOut)
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.mustTerminate body) ssa next tables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  generalize bodyEq : ssaCcTrans body ssa next tables = result
  rcases result with ⟨bodyOut, bodyTree, bodyCounter⟩
  have frame := ih bodyOut bodyTree bodyCounter bodyEq h
  simp only [ssaCcTrans, bodyEq, Prod.mk.injEq] at produced
  obtain ⟨_, rfl, rfl⟩ := produced
  exact frame

/-- Full If case retains both original renamed-condition guards and the
actual first-branch producer guard. The second branch uses the original map at
the produced counter. Its input validity and final reconciliation are derived. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransPropsIf {width : Nat} [NeZero width]
    (cmp : Cmp) (condition : Nat) (right : WordRegImm (BitVec width))
    (yes no : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (ih :
      (∀ (conditionOut : Nat) (rightOut : WordRegImm (BitVec width))
        (yesOut : WordLangProgHOL (BitVec width)) (yesTree : Spt Nat) (yesCounter : Nat),
        conditionOut = optionLookup ssa condition ∧
        rightOut = (match right with | .reg r => .reg (optionLookup ssa r) | .imm v => .imm v) ∧
        (yesOut, yesTree, yesCounter) = ssaCcTrans yes ssa next tables →
        ∀ (bodyOut : WordLangProgHOL (BitVec width)) (treeOut : Spt Nat) (counterOut : Nat),
          ssaCcTrans no ssa yesCounter tables = (bodyOut, treeOut, counterOut) →
          ssaMapOK yesCounter ssa ∧ isAllocVar yesCounter →
          yesCounter ≤ counterOut ∧ isAllocVar counterOut ∧ ssaMapOK counterOut treeOut) ∧
      (∀ (conditionOut : Nat) (rightOut : WordRegImm (BitVec width)),
        conditionOut = optionLookup ssa condition ∧
        rightOut = (match right with | .reg r => .reg (optionLookup ssa r) | .imm v => .imm v) →
        ∀ (bodyOut : WordLangProgHOL (BitVec width)) (treeOut : Spt Nat) (counterOut : Nat),
          ssaCcTrans yes ssa next tables = (bodyOut, treeOut, counterOut) →
          ssaMapOK next ssa ∧ isAllocVar next →
          next ≤ counterOut ∧ isAllocVar counterOut ∧ ssaMapOK counterOut treeOut))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.ite cmp condition right yes no) ssa next tables =
      (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  let conditionOut := optionLookup ssa condition
  let rightOut : WordRegImm (BitVec width) :=
    match right with | .reg r => .reg (optionLookup ssa r) | .imm v => .imm v
  generalize yesEq : ssaCcTrans yes ssa next tables = yesResult
  rcases yesResult with ⟨yesOut, yesTree, yesCounter⟩
  have yesFrame := ih.2 conditionOut rightOut ⟨rfl, by cases right <;> rfl⟩ yesOut yesTree yesCounter yesEq h
  generalize noEq : ssaCcTrans no ssa yesCounter tables = noResult
  rcases noResult with ⟨noOut, noTree, noCounter⟩
  have noFrame := ih.1 conditionOut rightOut yesOut yesTree yesCounter
    ⟨rfl, by cases right <;> rfl, yesEq.symm⟩ noOut noTree noCounter noEq
    ⟨ssaMapOKMore next ssa yesCounter ⟨h.1, yesFrame.1⟩, yesFrame.2.1⟩
  generalize fixEq : fixInconsistencies (width := width) (mkPrio yesOut noOut)
      yesTree noTree noCounter = fixed
  rcases fixed with ⟨yesCons, noCons, finalCounter, finalTree⟩
  have finalFrame := fixInconsistenciesProps (mkPrio yesOut noOut) yesTree noTree
    noCounter yesCons noCons finalCounter finalTree fixEq
    ⟨noFrame.2.1, ssaMapOKMore yesCounter yesTree noCounter ⟨yesFrame.2.2, noFrame.1⟩,
      noFrame.2.2⟩
  simp only [ssaCcTrans, yesEq, noEq, fixEq, Prod.mk.injEq] at produced
  obtain ⟨_, rfl, rfl⟩ := produced
  exact ⟨Nat.le_trans yesFrame.1 (Nat.le_trans noFrame.1 finalFrame.1),
    finalFrame.2.1, finalFrame.2.2⟩

end Flapjack.Compiler.Backend.WordAlloc
