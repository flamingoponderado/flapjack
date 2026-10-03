import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.ControlInstructionValidity
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameShiftedProperties

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Encoders.Asm

/-- Flapjack proof factoring of source register-bound monotonicity; no
separately named original is claimed. -/
private theorem boundMore {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (old next : Nat) (increase : old ≤ next)
    (bound : everyVarHOL (fun x => decide (x < old)) program = true) :
    everyVarHOL (fun x => decide (x < next)) program = true := by
  apply everyVarMono _ program _
  refine ⟨?_, bound⟩
  intro x hx
  simp only [decide_eq_true_eq] at hx ⊢
  omega

/-- Flapjack conjunction factoring; HOL has this clause inside its definition. -/
private theorem fullInst_seq {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (a b : WordLangProgHOL (BitVec width))
    (ha : fullInstOkLessExact config a = true) (hb : fullInstOkLessExact config b = true) :
    fullInstOkLessExact config (.seq a b) = true := by
  rw [fullInstOkLessExactSeq, ha, hb]
  rfl

/-- Flapjack factoring of the original reconciliation proof; no separately
named HOL declaration is claimed for this helper. -/
private theorem fix_fullInst {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (prio : Option (Unit ⊕ Unit)) (l r : Spt Nat) (next : Nat) :
    let (a, b, _, _) := fixInconsistencies (width := width) prio l r next
    fullInstOkLessExact config a = true ∧ fullInstOkLessExact config b = true := by
  unfold fixInconsistencies
  generalize hm : mergeMoves ((sptToAList (sptUnion l r)).map Prod.fst) l r next = merged
  rcases merged with ⟨lmov, rmov, count, left, right⟩
  generalize hf : fakeMoves (width := width) prio ((sptToAList (sptUnion l r)).map Prod.fst)
    left right count = result
  rcases result with ⟨a, b, final, leftOut, rightOut⟩
  have facts := fakeMoves_instructionConventions config prio _ left right count a b final leftOut rightOut hf
  simpa [hm, hf, fullInstOkLessExact, fullInstOkLessWith] using And.intro facts.1 facts.2.1

/-- Flapjack factoring of the literal Move-producing renamer; no separate original. -/
private theorem ssaRenameMove_fullInst {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (ssa : Spt Nat) (next : Nat) (keys : List Nat) :
    fullInstOkLessExact config (listNextVarRenameMove (width := width) ssa next keys).1 = true := by
  simp [listNextVarRenameMove, fullInstOkLessExact, fullInstOkLessWith]

/-- Original tail Call case retains the arbitrary exception handler, which
the original convention predicate ignores under NONE return. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_full_inst_ok_less" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_fullInstTailCall {width : Nat} [NeZero width]
    (config : AsmConfigExact width)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : everyVarHOL (fun x => decide (x < next)) (.call none dest args handler : WordLangProgHOL (BitVec width)) = true ∧ isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config (.call none dest args handler) = true) :
    fullInstOkLessExact config (ssaCcTrans (.call none dest args handler) ssa next tables).1 = true := by
  simp [ssaCcTrans, fullInstOkLessExact, fullInstOkLessWith]

/-- Original returning Call case, including both exception-handler options.
Structurally generalized source subprogram induction hypotheses are added; actual handler
map bounds and stack classes are derived from the original producers. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_full_inst_ok_less" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_fullInstReturningCall {width : Nat} [NeZero width]
    (config : AsmConfigExact width)
    (ret : List Nat) (cutsets : WordLangCutsetsHOL)
    (retHandler : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (retIH : ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      everyVarHOL (fun x => decide (x < next)) retHandler = true ∧ isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config retHandler = true →
        fullInstOkLessExact config (ssaCcTrans retHandler ssa next tables).1 = true)
    (handlerIH : match handler with
      | none => True
      | some (_, body, _, _) =>
        ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
          everyVarHOL (fun x => decide (x < next)) body = true ∧ isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config body = true →
            fullInstOkLessExact config (ssaCcTrans body ssa next tables).1 = true)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : everyVarHOL (fun x => decide (x < next)) (.call (some (ret, cutsets, retHandler, l1, l2)) dest args handler) = true ∧ isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config (.call (some (ret, cutsets, retHandler, l1, l2)) dest args handler) = true) :
    fullInstOkLessExact config
      (ssaCcTrans (.call (some (ret, cutsets, retHandler, l1, l2)) dest args handler)
        ssa next tables).1 = true := by
  have returnBound : everyVarHOL (fun x => decide (x < next)) retHandler = true := by
    have bound := h.1
    cases handler with
    | none => simp only [everyVarHOL, Bool.and_eq_true] at bound; aesop
    | some exc =>
        rcases exc with ⟨name, body, l1, l2⟩
        simp only [everyVarHOL, Bool.and_eq_true] at bound
        aesop
  have returnValid : fullInstOkLessExact config retHandler = true := by
    have valid := h.2.2.2
    cases handler with
    | none => simpa only [fullInstOkLessExact, fullInstOkLessWith, Bool.and_true] using valid
    | some exc =>
        rcases exc with ⟨name, body, l1, l2⟩
        simp only [fullInstOkLessExact, fullInstOkLessWith, Bool.and_eq_true] at valid
        exact valid.1
  let allNames := sptUnion cutsets.1 cutsets.2
  let keys := (sptToAList allNames).map Prod.fst
  generalize stackEq : listNextVarRenameMove (width := width) ssa (next + 2) keys = stacked
  rcases stacked with ⟨stackMov, stackTree, stackCounter⟩
  have stackFrame := listNextVarRenameMoveProps2 keys ssa next stackMov stackTree stackCounter
    stackEq ⟨Or.inl h.2.1, h.2.2.1⟩
  have stackClass := stackFrame.2.1 h.2.1
  have cutFrame := ssaMapOKInter stackCounter stackTree allNames stackFrame.2.2.2
  have stackPre := ssaRenameMove_fullInst config ssa (next + 2) keys
  rw [stackEq] at stackPre
  generalize retEq : listNextVarRenameMove (width := width)
    (sptInter stackTree allNames) (stackCounter + 2) keys = returned
  rcases returned with ⟨retMov, retTree, retCounter⟩
  have retFrame := listNextVarRenameMoveProps2 keys (sptInter stackTree allNames) stackCounter
    retMov retTree retCounter retEq ⟨Or.inr stackClass, cutFrame⟩
  have retClass := retFrame.2.2.1 stackClass
  have retPre := ssaRenameMove_fullInst config
    (sptInter stackTree allNames) (stackCounter + 2) keys
  rw [retEq] at retPre
  generalize rawEq : listNextVarRename ret retTree retCounter = raw
  rcases raw with ⟨retRegisters, retInputTree, retInputCounter⟩
  have rawFrame := listNextVarRenameProps ret retTree retCounter retRegisters retInputTree
    retInputCounter rawEq ⟨Or.inl retClass, retFrame.2.2.2⟩
  have bodyPre := retIH retInputTree retInputCounter tables
    ⟨boundMore retHandler next retInputCounter (by have a := stackFrame.1; have b := retFrame.1; have c := rawFrame.1; omega) returnBound, rawFrame.2.1 retClass, rawFrame.2.2.2, returnValid⟩
  generalize bodyEq : ssaCcTrans retHandler retInputTree retInputCounter tables = body
  rcases body with ⟨renRetHandler, retOutTree, retOutCounter⟩
  rw [bodyEq] at bodyPre
  have bodyFrame := ssaCcTransProps retHandler retInputTree retInputCounter tables
    renRetHandler retOutTree retOutCounter bodyEq ⟨rawFrame.2.2.2, rawFrame.2.1 retClass⟩
  let regs := (List.range ret.length).map (fun x => 2 * (x + 1))
  let movRetHandler : WordLangProgHOL (BitVec width) :=
    .seq retMov (.seq (.move 1 (retRegisters.zip regs)) renRetHandler)
  have returnPre : fullInstOkLessExact config movRetHandler = true :=
    fullInst_seq config retMov _ retPre (fullInst_seq config _ _ (by rfl) bodyPre)
  cases handler with
  | none =>
      dsimp only [keys, allNames] at stackEq retEq
      simp only [ssaCcTrans, stackEq, retEq, rawEq, bodyEq]
      simpa [movRetHandler, fullInstOkLessExact, fullInstOkLessWith] using
        fullInst_seq config stackMov movRetHandler stackPre returnPre
  | some exc =>
      rcases exc with ⟨name, excHandler, excL1, excL2⟩
      have excBound : everyVarHOL (fun x => decide (x < next)) excHandler = true := by
        have bound := h.1
        simp only [everyVarHOL, Bool.and_eq_true] at bound
        aesop
      have excValid : fullInstOkLessExact config excHandler = true := by
        have valid := h.2.2.2
        simp only [fullInstOkLessExact, fullInstOkLessWith, Bool.and_eq_true] at valid
        exact valid.2

      have retTreeLater := ssaMapOKMore retCounter retTree retOutCounter
        ⟨retFrame.2.2.2, Nat.le_trans rawFrame.1 bodyFrame.1⟩
      generalize freshEq : nextVarRename name retTree retOutCounter = fresh
      rcases fresh with ⟨freshLabel, freshTree, freshCounter⟩
      have freshFrame := nextVarRenameProps name retTree retOutCounter freshLabel freshTree
        freshCounter freshEq ⟨Or.inl bodyFrame.2.1, retTreeLater⟩
      have excPre := handlerIH freshTree freshCounter tables
        ⟨boundMore excHandler next freshCounter (by have a := stackFrame.1; have b := retFrame.1; have c := rawFrame.1; have d := bodyFrame.1; have e := freshFrame.1; omega) excBound, freshFrame.2.1 bodyFrame.2.1, freshFrame.2.2.2, excValid⟩
      generalize excEq : ssaCcTrans excHandler freshTree freshCounter tables = excBody
      rcases excBody with ⟨renExcHandler, excOutTree, excOutCounter⟩
      rw [excEq] at excPre
      let movExcHandler : WordLangProgHOL (BitVec width) :=
        .seq retMov (.seq (.move 1 [(freshLabel, 2)]) renExcHandler)
      have exceptionPre : fullInstOkLessExact config movExcHandler = true :=
        fullInst_seq config retMov _ retPre (fullInst_seq config _ _ (by rfl) excPre)
      have fixed := fix_fullInst config (mkPrio movRetHandler movExcHandler) retOutTree excOutTree excOutCounter
      generalize fixEq : fixInconsistencies (width := width) (mkPrio movRetHandler movExcHandler)
        retOutTree excOutTree excOutCounter = fixResult
      rcases fixResult with ⟨leftFix, rightFix, finalNext, finalMap⟩
      rw [fixEq] at fixed
      have leftPre := fixed.1
      have rightPre := fixed.2
      have fullReturn := fullInst_seq config movRetHandler leftFix returnPre leftPre
      have fullException := fullInst_seq config movExcHandler rightFix exceptionPre rightPre
      dsimp only [keys, allNames] at stackEq retEq
      simp only [ssaCcTrans, stackEq, retEq, rawEq, bodyEq, freshEq, excEq]
      simp only [regs, movRetHandler, movExcHandler] at fixEq fullReturn fullException
      rw [fixEq]
      simp only [fullInstOkLessExact, fullInstOkLessWith, Bool.and_eq_true, true_and] at stackPre fullReturn fullException ⊢
      exact ⟨stackPre, fullReturn, fullException⟩

end Flapjack.WordAlloc
