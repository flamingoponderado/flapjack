import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.InstructionValidity
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramProps
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapBounds
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapPreservation
import Flapjack.Pancake.WordConvs.ProgramMonotonicity

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

/-- Original Seq case with only the structurally generalized source-subprogram IH. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_full_inst_ok_less" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_fullInstSeq {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (first second : WordLangProgHOL (BitVec width))
    (firstIH : ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      everyVarHOL (fun x => decide (x < next)) first = true ∧ isAllocVar next ∧
      ssaMapOK next ssa ∧ fullInstOkLessExact config first = true →
        fullInstOkLessExact config (ssaCcTrans first ssa next tables).1 = true)
    (secondIH : ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      everyVarHOL (fun x => decide (x < next)) second = true ∧ isAllocVar next ∧
      ssaMapOK next ssa ∧ fullInstOkLessExact config second = true →
        fullInstOkLessExact config (ssaCcTrans second ssa next tables).1 = true)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : everyVarHOL (fun x => decide (x < next)) (.seq first second) = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config (.seq first second) = true) :
    fullInstOkLessExact config (ssaCcTrans (.seq first second) ssa next tables).1 = true := by
  have bounds : everyVarHOL (fun x => decide (x < next)) first = true ∧
      everyVarHOL (fun x => decide (x < next)) second = true := by
    simpa only [everyVarHOL, Bool.and_eq_true] using h.1
  have valids : fullInstOkLessExact config first = true ∧ fullInstOkLessExact config second = true := by
    simpa only [fullInstOkLessExactSeq, Bool.and_eq_true] using h.2.2.2
  generalize firstEq : ssaCcTrans first ssa next tables = firstResult
  rcases firstResult with ⟨a, middle, nextA⟩
  have properties := ssaCcTransProps first ssa next tables a middle nextA firstEq ⟨h.2.2.1, h.2.1⟩
  have ha := firstIH ssa next tables ⟨bounds.1, h.2.1, h.2.2.1, valids.1⟩
  rw [firstEq] at ha
  have hb := secondIH middle nextA tables
    ⟨boundMore second next nextA properties.1 bounds.2, properties.2.1, properties.2.2, valids.2⟩
  generalize secondEq : ssaCcTrans second middle nextA tables = secondResult
  rcases secondResult with ⟨b, final, nextB⟩
  rw [secondEq] at hb
  simpa only [ssaCcTrans, firstEq, secondEq] using fullInst_seq config a b ha hb

/-- Original MustTerminate case with a structurally generalized body IH. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_full_inst_ok_less" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_fullInstMustTerminate {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (body : WordLangProgHOL (BitVec width))
    (bodyIH : ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      everyVarHOL (fun x => decide (x < next)) body = true ∧ isAllocVar next ∧
      ssaMapOK next ssa ∧ fullInstOkLessExact config body = true →
        fullInstOkLessExact config (ssaCcTrans body ssa next tables).1 = true)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : everyVarHOL (fun x => decide (x < next)) (.mustTerminate body) = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config (.mustTerminate body) = true) :
    fullInstOkLessExact config (ssaCcTrans (.mustTerminate body) ssa next tables).1 = true := by
  have bound : everyVarHOL (fun x => decide (x < next)) body = true := by
    simpa only [everyVarHOL] using h.1
  have valid : fullInstOkLessExact config body = true := by
    simpa only [fullInstOkLessExact, fullInstOkLessWith] using h.2.2.2
  have result := bodyIH ssa next tables ⟨bound, h.2.1, h.2.2.1, valid⟩
  generalize produced : ssaCcTrans body ssa next tables = output
  rcases output with ⟨target, map, counter⟩
  rw [produced] at result
  simpa [ssaCcTrans, produced, fullInstOkLessExact, fullInstOkLessWith] using result

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

/-- Original If case with the two structurally generalized source-branch induction hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_full_inst_ok_less" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_fullInstIf {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (cmp : Cmp) (condition : Nat) (right : WordRegImm (BitVec width))
    (yes no : WordLangProgHOL (BitVec width))
    (yesIH : ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      everyVarHOL (fun x => decide (x < next)) yes = true ∧ isAllocVar next ∧
      ssaMapOK next ssa ∧ fullInstOkLessExact config yes = true →
        fullInstOkLessExact config (ssaCcTrans yes ssa next tables).1 = true)
    (noIH : ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      everyVarHOL (fun x => decide (x < next)) no = true ∧ isAllocVar next ∧
      ssaMapOK next ssa ∧ fullInstOkLessExact config no = true →
        fullInstOkLessExact config (ssaCcTrans no ssa next tables).1 = true)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : everyVarHOL (fun x => decide (x < next)) (.ite cmp condition right yes no) = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config (.ite cmp condition right yes no) = true) :
    fullInstOkLessExact config (ssaCcTrans (.ite cmp condition right yes no) ssa next tables).1 = true := by
  have bounds := h.1
  simp only [everyVarHOL, Bool.and_eq_true] at bounds
  have valids : fullInstOkLessExact config yes = true ∧ fullInstOkLessExact config no = true := by
    simpa only [fullInstOkLessExact, fullInstOkLessWith, Bool.and_eq_true] using h.2.2.2
  generalize yesEq : ssaCcTrans yes ssa next tables = yesResult
  rcases yesResult with ⟨a, leftMap, nextA⟩
  have properties := ssaCcTransProps yes ssa next tables a leftMap nextA yesEq ⟨h.2.2.1, h.2.1⟩
  have ha := yesIH ssa next tables ⟨bounds.1.2, h.2.1, h.2.2.1, valids.1⟩
  rw [yesEq] at ha
  have hb := noIH ssa nextA tables
    ⟨boundMore no next nextA properties.1 bounds.2, properties.2.1,
      ssaMapOKMore next ssa nextA ⟨h.2.2.1, properties.1⟩, valids.2⟩
  generalize noEq : ssaCcTrans no ssa nextA tables = noResult
  rcases noResult with ⟨b, rightMap, nextB⟩
  rw [noEq] at hb
  have fixed := fix_fullInst config (mkPrio a b) leftMap rightMap nextB
  generalize fixEq : fixInconsistencies (width := width) (mkPrio a b) leftMap rightMap nextB = fixResult
  rcases fixResult with ⟨leftFix, rightFix, finalNext, finalMap⟩
  rw [fixEq] at fixed
  have leftAll := fullInst_seq config a leftFix ha fixed.1
  have rightAll := fullInst_seq config b rightFix hb fixed.2
  simp only [ssaCcTrans, yesEq, noEq, fixEq, fullInstOkLessExact, fullInstOkLessWith,
    Bool.and_eq_true] at leftAll rightAll ⊢
  exact ⟨leftAll, rightAll⟩

/-- Flapjack factoring of literal Skip/Move reconciliation; no separate original. -/
private theorem fullInst_reconcile {width : Nat} [NeZero width] {β : Type}
    (config : AsmConfigExact width) (current target : Spt Nat) (names : Spt β) :
    fullInstOkLessExact config (ssaReconcile (width := width) current target names) = true := by
  unfold ssaReconcile
  dsimp only
  split <;> simp [fullInstOkLessExact, fullInstOkLessWith]

/-- Original Loop case with full source hypotheses and a structurally generalized body IH. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_full_inst_ok_less" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_fullInstLoop {width : Nat} [NeZero width]
    (config : AsmConfigExact width)
    (names exitNames : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (bodyIH : ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      everyVarHOL (fun x => decide (x < next)) body = true ∧ isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config body = true →
        fullInstOkLessExact config (ssaCcTrans body ssa next tables).1 = true)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : everyVarHOL (fun x => decide (x < next)) (.loop names body exitNames) = true ∧ isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config (.loop names body exitNames) = true) :
    fullInstOkLessExact config (ssaCcTrans (.loop names body exitNames) ssa next tables).1 = true := by
  have bounds := h.1
  simp only [everyVarHOL, Bool.and_eq_true] at bounds
  have valid : fullInstOkLessExact config body = true := by
    simpa only [fullInstOkLessExact, fullInstOkLessWith] using h.2.2.2
  generalize setupEq : loopSetup (width := width) names exitNames ssa next = setupResult
  rcases setupResult with ⟨setup, refreshed, nextRefreshed⟩
  have properties := loopSetup_propsLocal names exitNames ssa next setup refreshed nextRefreshed
    ⟨setupEq, h.2.2.1, h.2.1⟩
  have setupPre := loopSetup_fullInstOkLess config names exitNames ssa next setup refreshed nextRefreshed setupEq
  have bodyPre := bodyIH (sptInter refreshed names) nextRefreshed
    ((refreshed, names, exitNames) :: tables)
    ⟨boundMore body next nextRefreshed properties.2.2 bounds.1.2, properties.1, ssaMapOKInter nextRefreshed refreshed names properties.2.1, valid⟩
  generalize bodyEq : ssaCcTrans body (sptInter refreshed names) nextRefreshed
    ((refreshed, names, exitNames) :: tables) = bodyResult
  rcases bodyResult with ⟨output, bodyMap, nextOut⟩
  rw [bodyEq] at bodyPre
  have backPre := fullInst_reconcile config bodyMap refreshed names
  generalize backEq : ssaReconcile (width := width) bodyMap refreshed names = back
  rw [backEq] at backPre
  cases back <;>
    simp only [ssaCcTrans, setupEq, bodyEq, backEq, fullInstOkLessExact, fullInstOkLessWith,
      Bool.and_eq_true, and_true] at setupPre bodyPre backPre ⊢ <;>
    first | exact ⟨setupPre, bodyPre⟩ | exact ⟨setupPre, bodyPre, backPre⟩

/-- Original Break case with full source hypotheses and a structurally generalized body IH. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_full_inst_ok_less" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_fullInstBreak {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (index : Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : everyVarHOL (fun x => decide (x < next)) (.break index : WordLangProgHOL (BitVec width)) = true ∧ isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config (.break index) = true) :
    fullInstOkLessExact config (ssaCcTrans (.break index : WordLangProgHOL (BitVec width)) ssa next tables).1 = true := by
  cases selected : tables[index]? with
  | none => simp [ssaCcTrans, selected, fullInstOkLessExact, fullInstOkLessWith]
  | some entry =>
      rcases entry with ⟨target, names, exits⟩
      have pre := fullInst_reconcile config ssa target exits
      generalize eq : ssaReconcile (width := width) ssa target exits = back
      rw [eq] at pre
      simp only [ssaCcTrans, selected, eq]
      cases back <;> first | rfl | exact fullInst_seq config _ _ pre (by rfl)

/-- Original Continue case with full source hypotheses and a structurally generalized body IH. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_full_inst_ok_less" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_fullInstContinue {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (index : Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : everyVarHOL (fun x => decide (x < next)) (.continue index : WordLangProgHOL (BitVec width)) = true ∧ isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config (.continue index) = true) :
    fullInstOkLessExact config (ssaCcTrans (.continue index : WordLangProgHOL (BitVec width)) ssa next tables).1 = true := by
  cases selected : tables[index]? with
  | none => simp [ssaCcTrans, selected, fullInstOkLessExact, fullInstOkLessWith]
  | some entry =>
      rcases entry with ⟨target, names, exits⟩
      have pre := fullInst_reconcile config ssa target names
      generalize eq : ssaReconcile (width := width) ssa target names = back
      rw [eq] at pre
      simp only [ssaCcTrans, selected, eq]
      cases back <;> first | rfl | exact fullInst_seq config _ _ pre (by rfl)

end Flapjack.WordAlloc
