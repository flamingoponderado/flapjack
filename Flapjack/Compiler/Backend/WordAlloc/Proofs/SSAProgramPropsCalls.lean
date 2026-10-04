import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameShiftedProperties
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapPreservation
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapBounds
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAFixInconsistenciesProps

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Original tail-Call invariant case, with no recursive induction hypothesis. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTransPropsTailCall {width : Nat} [NeZero width]
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.call none dest args handler) ssa next tables =
      (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  simp only [ssaCcTrans, Prod.mk.injEq] at produced
  obtain ⟨_, rfl, rfl⟩ := produced
  exact ⟨Nat.le_refl _, h.2, h.1⟩

/-- Original returning-Call invariant case. The exception IH precedes the
return IH, with exactly the native functional-induction binders and guards.
The actual handler input bounds and final reconciled map are derived. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTransPropsReturningCall {width : Nat} [NeZero width]
    (ret : List Nat) (cutsets : WordLangCutsetsHOL)
    (retHandler : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (handlerIH :
      (
      ∀ (allNames : Spt Unit) (ls : List Nat)
        (stackMov : WordLangProgHOL (BitVec width)) (stackTree : Spt Nat) (stackCounter : Nat)
        (stackSet : WordLangCutsetsHOL) (names convArgs : List Nat)
        (moveArgs : WordLangProgHOL (BitVec width)) (cutTree : Spt Nat)
        (retMov : WordLangProgHOL (BitVec width)) (retTree : Spt Nat) (retCounter : Nat)
        (retRegisters : List Nat) (retInputTree : Spt Nat) (retInputCounter : Nat)
        (renRetHandler : WordLangProgHOL (BitVec width)) (retOutTree : Spt Nat) (retOutCounter : Nat)
        (regs : List Nat) (movRetHandler : WordLangProgHOL (BitVec width))
        (v : Nat × WordLangProgHOL (BitVec width) × Nat × Nat) (n : Nat)
        (v2 : WordLangProgHOL (BitVec width) × Nat × Nat)
        (excHandler : WordLangProgHOL (BitVec width)) (v4 : Nat × Nat) (excL1 excL2 : Nat)
        (freshLabel : Nat) (freshTree : Spt Nat) (freshCounter : Nat),
        allNames = sptUnion cutsets.1 cutsets.2 ∧
        ls = (sptToAList allNames).map Prod.fst ∧
        (stackMov, stackTree, stackCounter) = listNextVarRenameMove ssa (next + 2) ls ∧
        stackSet = Flapjack.WordAlloc.applyNummapsKey (optionLookup stackTree) cutsets ∧
        names = args.map (optionLookup ssa) ∧
        convArgs = (List.range names.length).map (fun x => 2 * (x + 1)) ∧
        moveArgs = .move 1 (convArgs.zip names) ∧
        cutTree = sptInter stackTree allNames ∧
        (retMov, retTree, retCounter) = listNextVarRenameMove cutTree (stackCounter + 2) ls ∧
        (retRegisters, retInputTree, retInputCounter) = listNextVarRename ret retTree retCounter ∧
        (renRetHandler, retOutTree, retOutCounter) =
          ssaCcTrans retHandler retInputTree retInputCounter tables ∧
        regs = (List.range ret.length).map (fun x => 2 * (x + 1)) ∧
        movRetHandler = .seq retMov (.seq (.move 1 (retRegisters.zip regs)) renRetHandler) ∧
        handler = some v ∧ v = (n, v2) ∧ v2 = (excHandler, v4) ∧ v4 = (excL1, excL2) ∧
        (freshLabel, freshTree, freshCounter) = nextVarRename n retTree retOutCounter →
      ∀ (bodyOut : WordLangProgHOL (BitVec width)) (mapOut : Spt Nat) (counterOut : Nat),
        ssaCcTrans excHandler freshTree freshCounter tables = (bodyOut, mapOut, counterOut) →
        ssaMapOK freshCounter freshTree ∧ isAllocVar freshCounter →
        freshCounter ≤ counterOut ∧ isAllocVar counterOut ∧ ssaMapOK counterOut mapOut)
      ∧ (
      ∀ (allNames : Spt Unit) (ls : List Nat)
        (stackMov : WordLangProgHOL (BitVec width)) (stackTree : Spt Nat) (stackCounter : Nat)
        (stackSet : WordLangCutsetsHOL) (names convArgs : List Nat)
        (moveArgs : WordLangProgHOL (BitVec width)) (cutTree : Spt Nat)
        (retMov : WordLangProgHOL (BitVec width)) (retTree : Spt Nat) (retCounter : Nat)
        (retRegisters : List Nat) (retInputTree : Spt Nat) (retInputCounter : Nat),
        allNames = sptUnion cutsets.1 cutsets.2 ∧
        ls = (sptToAList allNames).map Prod.fst ∧
        (stackMov, stackTree, stackCounter) = listNextVarRenameMove ssa (next + 2) ls ∧
        stackSet = Flapjack.WordAlloc.applyNummapsKey (optionLookup stackTree) cutsets ∧
        names = args.map (optionLookup ssa) ∧
        convArgs = (List.range names.length).map (fun x => 2 * (x + 1)) ∧
        moveArgs = .move 1 (convArgs.zip names) ∧
        cutTree = sptInter stackTree allNames ∧
        (retMov, retTree, retCounter) = listNextVarRenameMove cutTree (stackCounter + 2) ls ∧
        (retRegisters, retInputTree, retInputCounter) = listNextVarRename ret retTree retCounter →
      ∀ (bodyOut : WordLangProgHOL (BitVec width)) (mapOut : Spt Nat) (counterOut : Nat),
        ssaCcTrans retHandler retInputTree retInputCounter tables = (bodyOut, mapOut, counterOut) →
        ssaMapOK retInputCounter retInputTree ∧ isAllocVar retInputCounter →
        retInputCounter ≤ counterOut ∧ isAllocVar counterOut ∧ ssaMapOK counterOut mapOut))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.call (some (ret, cutsets, retHandler, l1, l2)) dest args handler)
      ssa next tables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  let allNames := sptUnion cutsets.1 cutsets.2
  let ls := (sptToAList allNames).map Prod.fst
  generalize stackEq : listNextVarRenameMove (width := width) ssa (next + 2) ls = stacked
  rcases stacked with ⟨stackMov, stackTree, stackCounter⟩
  have stackFrame := listNextVarRenameMoveProps2 ls ssa next stackMov stackTree
    stackCounter stackEq ⟨Or.inl h.2, h.1⟩
  have stackClass := stackFrame.2.1 h.2
  have cutFrame := ssaMapOKInter stackCounter stackTree allNames stackFrame.2.2.2
  generalize retEq : listNextVarRenameMove (width := width)
      (sptInter stackTree allNames) (stackCounter + 2) ls = returned
  rcases returned with ⟨retMov, retTree, retCounter⟩
  have retFrame := listNextVarRenameMoveProps2 ls (sptInter stackTree allNames)
    stackCounter retMov retTree retCounter retEq ⟨Or.inr stackClass, cutFrame⟩
  have retClass := retFrame.2.2.1 stackClass
  generalize rawEq : listNextVarRename ret retTree retCounter = raw
  rcases raw with ⟨retRegisters, retInputTree, retInputCounter⟩
  have rawFrame := listNextVarRenameProps ret retTree retCounter retRegisters
    retInputTree retInputCounter rawEq ⟨Or.inl retClass, retFrame.2.2.2⟩
  generalize bodyEq : ssaCcTrans retHandler retInputTree retInputCounter tables = body
  rcases body with ⟨renRetHandler, retOutTree, retOutCounter⟩
  let stackSet := Flapjack.WordAlloc.applyNummapsKey (optionLookup stackTree) cutsets
  let names := args.map (optionLookup ssa)
  let convArgs := (List.range names.length).map (fun x => 2 * (x + 1))
  let moveArgs : WordLangProgHOL (BitVec width) := .move 1 (convArgs.zip names)
  let regs := (List.range ret.length).map (fun x => 2 * (x + 1))
  let movRetHandler : WordLangProgHOL (BitVec width) :=
    .seq retMov (.seq (.move 1 (retRegisters.zip regs)) renRetHandler)
  have returnGuards :
      allNames = sptUnion cutsets.1 cutsets.2 ∧
      ls = (sptToAList allNames).map Prod.fst ∧
      (stackMov, stackTree, stackCounter) = listNextVarRenameMove ssa (next + 2) ls ∧
      stackSet = Flapjack.WordAlloc.applyNummapsKey (optionLookup stackTree) cutsets ∧
      names = args.map (optionLookup ssa) ∧
      convArgs = (List.range names.length).map (fun x => 2 * (x + 1)) ∧
      moveArgs = .move 1 (convArgs.zip names) ∧
      sptInter stackTree allNames = sptInter stackTree allNames ∧
      (retMov, retTree, retCounter) =
        listNextVarRenameMove (sptInter stackTree allNames) (stackCounter + 2) ls ∧
      (retRegisters, retInputTree, retInputCounter) = listNextVarRename ret retTree retCounter :=
    ⟨rfl, rfl, stackEq.symm, rfl, rfl, rfl, rfl, rfl, retEq.symm, rawEq.symm⟩
  have bodyFrame := handlerIH.2 allNames ls stackMov stackTree stackCounter stackSet
    names convArgs moveArgs (sptInter stackTree allNames) retMov retTree retCounter
    retRegisters retInputTree retInputCounter returnGuards
    renRetHandler retOutTree retOutCounter bodyEq ⟨rawFrame.2.2.2, rawFrame.2.1 retClass⟩
  have nextBody : next ≤ retOutCounter := by
    have := stackFrame.1; have := retFrame.1; have := rawFrame.1; have := bodyFrame.1
    omega
  cases handler with
  | none =>
      dsimp only [ls, allNames] at stackEq retEq
      simp only [ssaCcTrans, stackEq, retEq, rawEq, bodyEq, Prod.mk.injEq] at produced
      obtain ⟨_, rfl, rfl⟩ := produced
      exact ⟨nextBody, bodyFrame.2.1, bodyFrame.2.2⟩
  | some exc =>
      rcases exc with ⟨n, excHandler, excL1, excL2⟩
      have retTreeLater := ssaMapOKMore retCounter retTree retOutCounter
        ⟨retFrame.2.2.2, Nat.le_trans rawFrame.1 bodyFrame.1⟩
      generalize freshEq : nextVarRename n retTree retOutCounter = fresh
      rcases fresh with ⟨freshLabel, freshTree, freshCounter⟩
      have freshFrame := nextVarRenameProps n retTree retOutCounter freshLabel freshTree
        freshCounter freshEq ⟨Or.inl bodyFrame.2.1, retTreeLater⟩
      generalize excEq : ssaCcTrans excHandler freshTree freshCounter tables = excBody
      rcases excBody with ⟨renExcHandler, excTree, excCounter⟩
      have excFrame := handlerIH.1 allNames ls stackMov stackTree stackCounter stackSet
        names convArgs moveArgs (sptInter stackTree allNames) retMov retTree retCounter
        retRegisters retInputTree retInputCounter renRetHandler retOutTree retOutCounter
        regs movRetHandler (n, excHandler, excL1, excL2) n (excHandler, excL1, excL2)
        excHandler (excL1, excL2) excL1 excL2 freshLabel freshTree freshCounter
        ⟨returnGuards.1, returnGuards.2.1, returnGuards.2.2.1,
          returnGuards.2.2.2.1, returnGuards.2.2.2.2.1, returnGuards.2.2.2.2.2.1,
          returnGuards.2.2.2.2.2.2.1, returnGuards.2.2.2.2.2.2.2.1,
          returnGuards.2.2.2.2.2.2.2.2.1, returnGuards.2.2.2.2.2.2.2.2.2,
          bodyEq.symm, rfl, rfl, rfl, rfl, rfl, rfl, freshEq.symm⟩
        renExcHandler excTree excCounter excEq
        ⟨freshFrame.2.2.2, freshFrame.2.1 bodyFrame.2.1⟩
      let movExcHandler : WordLangProgHOL (BitVec width) :=
        .seq retMov (.seq (.move 1 [(freshLabel, 2)]) renExcHandler)
      generalize fixEq : fixInconsistencies (width := width) (mkPrio movRetHandler movExcHandler)
          retOutTree excTree excCounter = fixed
      rcases fixed with ⟨retCons, excCons, finalCounter, finalTree⟩
      have fixedFrame := fixInconsistenciesProps (mkPrio movRetHandler movExcHandler)
        retOutTree excTree excCounter retCons excCons finalCounter finalTree fixEq
        ⟨excFrame.2.1, ssaMapOKMore retOutCounter retOutTree excCounter
          ⟨bodyFrame.2.2, Nat.le_trans freshFrame.1 excFrame.1⟩, excFrame.2.2⟩
      dsimp only [ls, allNames] at stackEq retEq
      dsimp only [movRetHandler, movExcHandler, regs] at fixEq
      simp only [ssaCcTrans, stackEq, retEq, rawEq, bodyEq, freshEq, excEq, fixEq,
        Prod.mk.injEq] at produced
      obtain ⟨_, rfl, rfl⟩ := produced
      exact ⟨Nat.le_trans nextBody (Nat.le_trans freshFrame.1
        (Nat.le_trans excFrame.1 fixedFrame.1)), fixedFrame.2.1, fixedFrame.2.2⟩

end Flapjack.Compiler.Backend.WordAlloc
