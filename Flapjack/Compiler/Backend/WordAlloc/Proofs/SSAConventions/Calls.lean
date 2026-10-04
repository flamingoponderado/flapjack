import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.Allocation
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramProps
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameShiftedProperties
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapBounds
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapPreservation

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack Boolean conjunction factoring with no separately named original. -/
private theorem preAlloc_seq {width : Nat} [NeZero width]
    (a b : WordLangProgHOL (BitVec width))
    (ha : preAllocConventionsHOL a = true) (hb : preAllocConventionsHOL b = true) :
    preAllocConventionsHOL (.seq a b) = true := by
  simp only [preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL,
    Bool.and_eq_true] at ha hb ⊢
  exact ⟨⟨ha.1, hb.1⟩, ha.2, hb.2⟩

/-- Original tail Call case retains the arbitrary exception handler, which
the original convention predicate ignores under NONE return. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTrans_preAllocTailCall {width : Nat} [NeZero width]
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : isAllocVar next ∧ ssaMapOK next ssa) :
    preAllocConventionsHOL (ssaCcTrans (.call none dest args handler) ssa next tables).1 = true := by
  simp [ssaCcTrans, preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL]

/-- Original returning Call case, including both exception-handler options.
Structurally generalized source subprogram induction hypotheses are added; actual handler
map bounds and stack classes are derived from the original producers. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTrans_preAllocReturningCall {width : Nat} [NeZero width]
    (ret : List Nat) (cutsets : WordLangCutsetsHOL)
    (retHandler : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (retIH : ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      isAllocVar next ∧ ssaMapOK next ssa →
        preAllocConventionsHOL (ssaCcTrans retHandler ssa next tables).1 = true)
    (handlerIH : match handler with
      | none => True
      | some (_, body, _, _) =>
        ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
          isAllocVar next ∧ ssaMapOK next ssa →
            preAllocConventionsHOL (ssaCcTrans body ssa next tables).1 = true)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : isAllocVar next ∧ ssaMapOK next ssa) :
    preAllocConventionsHOL
      (ssaCcTrans (.call (some (ret, cutsets, retHandler, l1, l2)) dest args handler)
        ssa next tables).1 = true := by
  let allNames := sptUnion cutsets.1 cutsets.2
  let keys := (sptToAList allNames).map Prod.fst
  generalize stackEq : listNextVarRenameMove (width := width) ssa (next + 2) keys = stacked
  rcases stacked with ⟨stackMov, stackTree, stackCounter⟩
  have stackFrame := listNextVarRenameMoveProps2 keys ssa next stackMov stackTree stackCounter
    stackEq ⟨Or.inl h.1, h.2⟩
  have stackClass := stackFrame.2.1 h.1
  have cutFrame := ssaMapOKInter stackCounter stackTree allNames stackFrame.2.2.2
  have stackNames := ssaRenamedStackNames ssa next cutsets stackMov stackTree stackCounter stackEq h.1
  have stackPre := ssaRenameMove_preAlloc (width := width) ssa (next + 2) keys
  rw [stackEq] at stackPre
  generalize retEq : listNextVarRenameMove (width := width)
    (sptInter stackTree allNames) (stackCounter + 2) keys = returned
  rcases returned with ⟨retMov, retTree, retCounter⟩
  have retFrame := listNextVarRenameMoveProps2 keys (sptInter stackTree allNames) stackCounter
    retMov retTree retCounter retEq ⟨Or.inr stackClass, cutFrame⟩
  have retClass := retFrame.2.2.1 stackClass
  have retPre := ssaRenameMove_preAlloc (width := width)
    (sptInter stackTree allNames) (stackCounter + 2) keys
  rw [retEq] at retPre
  generalize rawEq : listNextVarRename ret retTree retCounter = raw
  rcases raw with ⟨retRegisters, retInputTree, retInputCounter⟩
  have rawFrame := listNextVarRenameProps ret retTree retCounter retRegisters retInputTree
    retInputCounter rawEq ⟨Or.inl retClass, retFrame.2.2.2⟩
  have bodyPre := retIH retInputTree retInputCounter tables
    ⟨rawFrame.2.1 retClass, rawFrame.2.2.2⟩
  generalize bodyEq : ssaCcTrans retHandler retInputTree retInputCounter tables = body
  rcases body with ⟨renRetHandler, retOutTree, retOutCounter⟩
  rw [bodyEq] at bodyPre
  have bodyFrame := ssaCcTransProps retHandler retInputTree retInputCounter tables
    renRetHandler retOutTree retOutCounter bodyEq ⟨rawFrame.2.2.2, rawFrame.2.1 retClass⟩
  let regs := (List.range ret.length).map (fun x => 2 * (x + 1))
  let movRetHandler : WordLangProgHOL (BitVec width) :=
    .seq retMov (.seq (.move 1 (retRegisters.zip regs)) renRetHandler)
  have returnPre : preAllocConventionsHOL movRetHandler = true :=
    preAlloc_seq retMov _ retPre (preAlloc_seq _ _ (by rfl) bodyPre)
  cases handler with
  | none =>
      dsimp only [keys, allNames] at stackEq retEq
      simp only [ssaCcTrans, stackEq, retEq, rawEq, bodyEq]
      dsimp only [movRetHandler] at returnPre
      simp only [preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL,
        Bool.and_eq_true] at stackPre returnPre ⊢
      simp_all only [true_and, and_true]
      constructor <;> simp
  | some exc =>
      rcases exc with ⟨name, excHandler, excL1, excL2⟩
      have retTreeLater := ssaMapOKMore retCounter retTree retOutCounter
        ⟨retFrame.2.2.2, Nat.le_trans rawFrame.1 bodyFrame.1⟩
      generalize freshEq : nextVarRename name retTree retOutCounter = fresh
      rcases fresh with ⟨freshLabel, freshTree, freshCounter⟩
      have freshFrame := nextVarRenameProps name retTree retOutCounter freshLabel freshTree
        freshCounter freshEq ⟨Or.inl bodyFrame.2.1, retTreeLater⟩
      have excPre := handlerIH freshTree freshCounter tables
        ⟨freshFrame.2.1 bodyFrame.2.1, freshFrame.2.2.2⟩
      generalize excEq : ssaCcTrans excHandler freshTree freshCounter tables = excBody
      rcases excBody with ⟨renExcHandler, excOutTree, excOutCounter⟩
      rw [excEq] at excPre
      let movExcHandler : WordLangProgHOL (BitVec width) :=
        .seq retMov (.seq (.move 1 [(freshLabel, 2)]) renExcHandler)
      have exceptionPre : preAllocConventionsHOL movExcHandler = true :=
        preAlloc_seq retMov _ retPre (preAlloc_seq _ _ (by rfl) excPre)
      have fixed := fixInconsistencies_conventions (width := width)
        retOutTree excOutTree excOutCounter (mkPrio movRetHandler movExcHandler)
      generalize fixEq : fixInconsistencies (width := width) (mkPrio movRetHandler movExcHandler)
        retOutTree excOutTree excOutCounter = fixResult
      rcases fixResult with ⟨leftFix, rightFix, finalNext, finalMap⟩
      rw [fixEq] at fixed
      have leftPre : preAllocConventionsHOL leftFix = true := by
        simp only [preAllocConventionsHOL, Bool.and_eq_true]
        exact ⟨fixed.1, fixed.2.2.1⟩
      have rightPre : preAllocConventionsHOL rightFix = true := by
        simp only [preAllocConventionsHOL, Bool.and_eq_true]
        exact ⟨fixed.2.1, fixed.2.2.2⟩
      have fullReturn := preAlloc_seq movRetHandler leftFix returnPre leftPre
      have fullException := preAlloc_seq movExcHandler rightFix exceptionPre rightPre
      dsimp only [keys, allNames] at stackEq retEq
      simp only [ssaCcTrans, stackEq, retEq, rawEq, bodyEq, freshEq, excEq]
      simp only [regs, movRetHandler, movExcHandler] at fixEq fullReturn fullException
      rw [fixEq]
      simp only [preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL,
        Bool.and_eq_true] at stackPre fullReturn fullException ⊢
      simp [stackNames, stackPre, fullReturn, fullException]

end Flapjack.WordAlloc
