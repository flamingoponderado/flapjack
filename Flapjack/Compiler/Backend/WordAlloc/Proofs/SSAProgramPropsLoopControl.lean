import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenamePropertyWrappers
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapPreservation
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapBounds

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack proof factoring for the two actual native loop-setup rename
producers. No independent HOL declaration; this is the setup reasoning inside
the original resumed program-invariant Loop proof. -/
private theorem loopSetupAllocationFrame {width : Nat} [NeZero width]
    (names exitNames : Spt Unit) (ssa : Spt Nat) (next : Nat)
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    let setup := loopSetup (width := width) names exitNames ssa next
    next ≤ setup.2.2 ∧ isAllocVar setup.2.2 ∧ ssaMapOK setup.2.2 setup.2.1 := by
  let allNames := (sptToAList (sptUnion names exitNames)).map Prod.fst
  let freshNames := allNames.filter fun name => (sptLookup name ssa).isNone
  let refreshNames := allNames.filter fun name => (sptLookup name ssa).isSome
  generalize freshRename : listNextVarRename freshNames ssa next = fresh
  rcases fresh with ⟨freshRegisters, freshTree, freshCounter⟩
  have freshFrame := listNextVarRenameProps freshNames ssa next freshRegisters
    freshTree freshCounter freshRename ⟨Or.inl h.2, h.1⟩
  have freshClass := freshFrame.2.1 h.2
  generalize refreshRename : listNextVarRenameMove (width := width)
      freshTree freshCounter refreshNames = refreshed
  rcases refreshed with ⟨refreshMove, refreshTree, refreshCounter⟩
  have refreshFrame := listNextVarRenameMoveProps refreshNames freshTree freshCounter
    refreshMove refreshTree refreshCounter refreshRename ⟨Or.inl freshClass, freshFrame.2.2.2⟩
  dsimp only [freshNames, refreshNames, allNames] at freshRename refreshRename
  simp only [loopSetup, freshRename, refreshRename]
  exact ⟨Nat.le_trans freshFrame.1 refreshFrame.1,
    refreshFrame.2.1 freshClass, refreshFrame.2.2.2⟩

/-- Full original resumed Loop case. The body IH retains all original setup
binders and four guard equalities from the specialized native functional
induction rule, then precisely the original body counter/map property at its
actual refreshed context. Caller bounds and the output exit-map cut are proved;
no arbitrary-context body predicate or desired whole-loop invariant is assumed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTransPropsLoop {width : Nat} [NeZero width]
    (names : Spt Unit) (body : WordLangProgHOL (BitVec width)) (exitNames : Spt Unit)
    (ssa : Spt Nat) (next : Nat) (loopTables : List (Spt Nat × Spt Unit × Spt Unit))
    (bodyIH :
      ∀ (setupProg : WordLangProgHOL (BitVec width)) (refreshed : Spt Nat)
        (counter : Nat) (ssaNames ssaExit : Spt Unit) (bodyMap : Spt Nat),
        (setupProg, refreshed, counter) = loopSetup names exitNames ssa next ∧
          ssaNames = Flapjack.WordAlloc.applyNummapKey (optionLookup refreshed) names ∧
          ssaExit = Flapjack.WordAlloc.applyNummapKey (optionLookup refreshed) exitNames ∧
          bodyMap = sptInter refreshed names →
        ∀ (bodyOut : WordLangProgHOL (BitVec width)) (mapOut : Spt Nat) (counterOut : Nat),
          ssaCcTrans body bodyMap counter ((refreshed, names, exitNames) :: loopTables) =
              (bodyOut, mapOut, counterOut) →
          ssaMapOK counter bodyMap ∧ isAllocVar counter →
          counter ≤ counterOut ∧ isAllocVar counterOut ∧ ssaMapOK counterOut mapOut)
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.loop names body exitNames) ssa next loopTables =
      (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  have setupFrame := loopSetupAllocationFrame (width := width) names exitNames ssa next h
  generalize setupEq : loopSetup (width := width) names exitNames ssa next = setup at setupFrame bodyIH
  rcases setup with ⟨setupProg, refreshedTree, refreshedCounter⟩
  dsimp only at setupFrame bodyIH
  have bodyInput := ssaMapOKInter refreshedCounter refreshedTree names setupFrame.2.2
  generalize bodyEq : ssaCcTrans body (sptInter refreshedTree names) refreshedCounter
      ((refreshedTree, names, exitNames) :: loopTables) = result
  rcases result with ⟨bodyOut, bodyTree, bodyCounter⟩
  have bodyFrame := bodyIH setupProg refreshedTree refreshedCounter
    (Flapjack.WordAlloc.applyNummapKey (optionLookup refreshedTree) names)
    (Flapjack.WordAlloc.applyNummapKey (optionLookup refreshedTree) exitNames)
    (sptInter refreshedTree names) ⟨rfl, rfl, rfl, rfl⟩
    bodyOut bodyTree bodyCounter bodyEq ⟨bodyInput, setupFrame.2.1⟩
  have exitFrame := ssaMapOKInter bodyCounter refreshedTree exitNames
    (ssaMapOKMore refreshedCounter refreshedTree bodyCounter ⟨setupFrame.2.2, bodyFrame.1⟩)
  simp only [ssaCcTrans, setupEq, bodyEq, Prod.mk.injEq] at produced
  obtain ⟨_, rfl, rfl⟩ := produced
  exact ⟨Nat.le_trans setupFrame.1 bodyFrame.1, bodyFrame.2.1, exitFrame⟩

/-- Full original resumed Break case. Arbitrary loop-table lookup/reconcile
branches preserve the original map/counter; no loop-map validity premise or
induction hypothesis is added to the original compiler equality/map/allocation
premises. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTransPropsBreak {width : Nat} [NeZero width]
    (label : Nat) (ssa : Spt Nat) (next : Nat)
    (loopTables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.break label) ssa next loopTables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  simp only [ssaCcTrans] at produced
  split at produced
  all_goals try (split at produced)
  all_goals simp only [Prod.mk.injEq] at produced
  all_goals obtain ⟨_, rfl, rfl⟩ := produced
  all_goals exact ⟨Nat.le_refl _, h.2, h.1⟩

/-- Full original resumed Continue case. Arbitrary loop-table lookup/reconcile
branches preserve the original map/counter; no loop-map validity premise or
induction hypothesis is added to the original compiler equality/map/allocation
premises. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTransPropsContinue {width : Nat} [NeZero width]
    (label : Nat) (ssa : Spt Nat) (next : Nat)
    (loopTables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.continue label) ssa next loopTables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  simp only [ssaCcTrans] at produced
  split at produced
  all_goals try (split at produced)
  all_goals simp only [Prod.mk.injEq] at produced
  all_goals obtain ⟨_, rfl, rfl⟩ := produced
  all_goals exact ⟨Nat.le_refl _, h.2, h.1⟩

end Flapjack.Compiler.Backend.WordAlloc
