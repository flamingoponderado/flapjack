import Flapjack.Compiler.Backend.WordAlloc.FullSSA
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAControlCodec
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSADataCodec

namespace Flapjack.Compiler.Backend.WordAlloc

/-! Flapjack carrier-boundary assembly. Availability of the partial production
program decoder has no independent HOL original and is not a pass simulation. -/

@[simp] theorem ssaCodec_move {width : Nat} (priority : Nat) (moves : List (Nat × Nat)) :
    (wordLangProgFromHOL (WordLangProgHOL.move (α := BitVec width) priority moves)).isSome = true := rfl

@[simp] theorem ssaCodec_seq {width : Nat} (left right : WordLangProgHOL (BitVec width)) :
    (wordLangProgFromHOL (.seq left right)).isSome =
      ((wordLangProgFromHOL left).isSome && (wordLangProgFromHOL right).isSome) := by
  cases hl : wordLangProgFromHOL left <;> cases hr : wordLangProgFromHOL right <;>
    simp [wordLangProgFromHOL, hl, hr]

@[simp] theorem ssaCodec_ite {width : Nat} (cmp : Cmp) (register : Nat)
    (right : WordRegImm (BitVec width)) (yes no : WordLangProgHOL (BitVec width)) :
    (wordLangProgFromHOL (.ite cmp register right yes no)).isSome =
      ((wordLangProgFromHOL yes).isSome && (wordLangProgFromHOL no).isSome) := by
  cases hy : wordLangProgFromHOL yes <;> cases hn : wordLangProgFromHOL no <;>
    simp [wordLangProgFromHOL, hy, hn]

@[simp] theorem ssaCodec_call {width : Nat}
    (returns : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (target : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    (wordLangProgFromHOL (.call returns target arguments handler)).isSome =
      ((match returns with | none => true | some (_, _, body, _, _) => (wordLangProgFromHOL body).isSome) &&
       (match handler with | none => true | some (_, body, _, _) => (wordLangProgFromHOL body).isSome)) := by
  cases returns with
  | none =>
    cases handler with
    | none => rfl
    | some h =>
      rcases h with ⟨name, body, l1, l2⟩
      cases hb : wordLangProgFromHOL body <;> simp [wordLangProgFromHOL, hb]
  | some r =>
    rcases r with ⟨values, sets, body, l1, l2⟩
    cases handler with
    | none =>
      cases hb : wordLangProgFromHOL body <;> simp [wordLangProgFromHOL, hb]
    | some h =>
      rcases h with ⟨name, hbody, h1, h2⟩
      cases hb : wordLangProgFromHOL body <;> cases hh : wordLangProgFromHOL hbody <;>
        simp [wordLangProgFromHOL, hb, hh]

@[simp] theorem ssaCodec_loop {width : Nat} (names exits : Spt Unit)
    (body : WordLangProgHOL (BitVec width)) :
    (wordLangProgFromHOL (.loop names body exits)).isSome = (wordLangProgFromHOL body).isSome := by
  cases hb : wordLangProgFromHOL body <;> simp [wordLangProgFromHOL, hb]

@[simp] theorem ssaCodec_mustTerminate {width : Nat} (body : WordLangProgHOL (BitVec width)) :
    (wordLangProgFromHOL (.mustTerminate body)).isSome = (wordLangProgFromHOL body).isSome := by
  simp [wordLangProgFromHOL]

/-- Complete native SSA output decoder availability from accepted input only.
Maps, counters, loop contexts and positive width are unrestricted. This is a
Flapjack carrier property, not a tagged HOL theorem or production switch. -/
theorem ssaCcTrans_decoderClosure {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (next : Nat)
    (contexts : List (Spt Nat × Spt Unit × Spt Unit))
    (accepted : (wordLangProgFromHOL program).isSome = true) :
    (wordLangProgFromHOL (ssaCcTrans program ssa next contexts).1).isSome = true := by
  revert accepted
  induction program, ssa, next, contexts using ssaCcTrans.induct
  all_goals intro accepted
  all_goals try (solve
    | apply ssaCcTrans_data_decoderClosure <;> first | assumption | simp [ssaDataLeaf]
    | apply ssaCcTrans_break_decoderClosure
    | apply ssaCcTrans_continue_decoderClosure)
  case case8 left right map n tables outL mapL nextL hL outR mapR nextR hR ihL ihR =>
    simp_all [ssaCcTrans]
  case case9 body map n tables out map2 n2 h ih =>
    simp_all [ssaCcTrans]
  case case10 cmp r ri left right map n tables outL mapL nL hL outR mapR nR hR prio consL consR nf mf hFix ihL ihR =>
    dsimp only [prio] at hFix
    have helpers := fixInconsistencies_decoderClosure (width := width) prio mapL mapR nR
    dsimp only [prio] at helpers
    simp_all [ssaCcTrans]
  case case22 target arguments handler map n tables =>
    simpa [ssaCcTrans] using accepted
  case case23 ret sets body l1 l2 target arguments map n tables allNames names mapStack nStack cut
      returnMove mapRet nRet hRet namesRet mapNames nNames hNames out mapOut nOut hOut stackMove hStack ih =>
    dsimp only [allNames, names, cut] at hStack hRet
    have stack := listNextVarRenameMove_decoderClosure (width := width) map (n + 2) names
    have back := listNextVarRenameMove_decoderClosure (width := width) cut (nStack + 2) names
    dsimp only [allNames, names, cut] at stack back
    simp_all [ssaCcTrans]
  case case24 ret sets retBody l1 l2 target arguments map n tables allNames names mapStack nStack cut
      retMove mapRet nRet hRetMove retNames mapNames nNames hRetNames outRet mapRetOut nRetOut hRetOut
      regs movRet exception excBody excL1 excL2 stackMove exceptionReg mapExc nExc hExcRename
      outExc mapExcOut nExcOut hExcOut movExc prio consRet consExc nf mf hFix hStack ihRet ihExc =>
    dsimp only [allNames, names, cut] at hStack hRetMove
    dsimp only [regs, movRet, movExc, prio] at hFix
    have stack := listNextVarRenameMove_decoderClosure (width := width) map (n + 2) names
    have back := listNextVarRenameMove_decoderClosure (width := width) cut (nStack + 2) names
    have helpers := fixInconsistencies_decoderClosure (width := width) prio mapRetOut mapExcOut nExcOut
    dsimp only [allNames, names, cut] at stack back
    dsimp only [regs, movRet, movExc, prio] at helpers
    simp_all [ssaCcTrans]
  case case27 names body exits map n tables setup mapSetup nSetup hSetup bodyMap out mapOut nOut hOut ih =>
    dsimp only [bodyMap] at hOut ih
    have setupAccepted := loopSetup_decoderClosure (width := width) names exits map n
    have backAccepted := ssaReconcile_decoderClosure (width := width) mapOut mapSetup names
    simp only [hSetup] at setupAccepted
    have outputAccepted : (wordLangProgFromHOL out).isSome = true := by
      simpa only [hOut] using ih (by simpa using accepted)
    simp only [ssaCcTrans, hSetup, hOut]
    generalize hb : ssaReconcile (width := width) mapOut mapSetup names = moves at backAccepted ⊢
    cases moves <;> simp_all
  all_goals simp_all


/-- Entire native full SSA result is decodable whenever the source input is.
This proves availability at the production carrier boundary, without asserting
semantic transport or replacing the executed compiler caller. -/
theorem fullSsaCcTrans_decoderClosure {width : Nat} [NeZero width]
    (parameterCount : Nat) (program : WordLangProgHOL (BitVec width))
    (accepted : (wordLangProgFromHOL program).isSome = true) :
    (wordLangProgFromHOL (fullSsaCcTrans parameterCount program)).isSome = true := by
  have prologue := setupSSA_decoderClosure (outputWidth := width) parameterCount (limitVar program) program
  unfold fullSsaCcTrans
  dsimp only
  generalize hs : setupSSA (outputWidth := width) parameterCount (limitVar program) program = setup at prologue ⊢
  rcases setup with ⟨entry, map, next⟩
  have output := ssaCcTrans_decoderClosure program map next [] accepted
  generalize ho : ssaCcTrans program map next [] = result at output ⊢
  rcases result with ⟨body, finalMap, finalNext⟩
  exact ssaGeneratedSeq_decoderClosure _ _ prologue output

end Flapjack.Compiler.Backend.WordAlloc
