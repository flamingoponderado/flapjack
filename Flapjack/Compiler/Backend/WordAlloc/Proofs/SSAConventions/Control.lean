import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramProps
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapBounds
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapPreservation

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack Boolean factoring of the source pre-convention conjunction;
no separately declared HOL original exists for this proof helper. -/
private theorem preAlloc_seq {width : Nat} [NeZero width]
    (a b : WordLangProgHOL (BitVec width))
    (ha : preAllocConventionsHOL a = true) (hb : preAllocConventionsHOL b = true) :
    preAllocConventionsHOL (.seq a b) = true := by
  simp only [preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL,
    Bool.and_eq_true] at ha hb ⊢
  exact ⟨⟨ha.1, hb.1⟩, ha.2, hb.2⟩

/-- Original Seq case, with only the genuine induction hypotheses added. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocSeq {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width))
    (firstIH : ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      isAllocVar next ∧ ssaMapOK next ssa →
        preAllocConventionsHOL (ssaCcTrans first ssa next tables).1 = true)
    (secondIH : ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      isAllocVar next ∧ ssaMapOK next ssa →
        preAllocConventionsHOL (ssaCcTrans second ssa next tables).1 = true)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : isAllocVar next ∧ ssaMapOK next ssa) :
    preAllocConventionsHOL (ssaCcTrans (.seq first second) ssa next tables).1 = true := by
  generalize firstEq : ssaCcTrans first ssa next tables = firstResult
  rcases firstResult with ⟨a, middle, nextA⟩
  have properties := ssaCcTransProps first ssa next tables a middle nextA firstEq ⟨h.2, h.1⟩
  have ha := firstIH ssa next tables h
  rw [firstEq] at ha
  have hb := secondIH middle nextA tables ⟨properties.2.1, properties.2.2⟩
  generalize secondEq : ssaCcTrans second middle nextA tables = secondResult
  rcases secondResult with ⟨b, final, nextB⟩
  rw [secondEq] at hb
  simpa only [ssaCcTrans, firstEq, secondEq] using preAlloc_seq a b ha hb

/-- Original MustTerminate case with the source body induction hypothesis. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocMustTerminate {width : Nat} [NeZero width]
    (body : WordLangProgHOL (BitVec width))
    (bodyIH : ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      isAllocVar next ∧ ssaMapOK next ssa →
        preAllocConventionsHOL (ssaCcTrans body ssa next tables).1 = true)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : isAllocVar next ∧ ssaMapOK next ssa) :
    preAllocConventionsHOL (ssaCcTrans (.mustTerminate body) ssa next tables).1 = true := by
  have pre := bodyIH ssa next tables h
  generalize produced : ssaCcTrans body ssa next tables = result
  rcases result with ⟨output, map, counter⟩
  rw [produced] at pre
  simpa [ssaCcTrans, produced, preAllocConventionsHOL, everyStackVarHOL,
    callArgConventionHOL] using pre

/-- Original If case with the two genuine branch induction hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocIf {width : Nat} [NeZero width]
    (cmp : Cmp) (condition : Nat) (right : WordRegImm (BitVec width))
    (yes no : WordLangProgHOL (BitVec width))
    (yesIH : ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      isAllocVar next ∧ ssaMapOK next ssa →
        preAllocConventionsHOL (ssaCcTrans yes ssa next tables).1 = true)
    (noIH : ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      isAllocVar next ∧ ssaMapOK next ssa →
        preAllocConventionsHOL (ssaCcTrans no ssa next tables).1 = true)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : isAllocVar next ∧ ssaMapOK next ssa) :
    preAllocConventionsHOL (ssaCcTrans (.ite cmp condition right yes no) ssa next tables).1 = true := by
  generalize yesEq : ssaCcTrans yes ssa next tables = yesResult
  rcases yesResult with ⟨a, leftMap, nextA⟩
  have properties := ssaCcTransProps yes ssa next tables a leftMap nextA yesEq ⟨h.2, h.1⟩
  have ha := yesIH ssa next tables h
  rw [yesEq] at ha
  have hb := noIH ssa nextA tables
    ⟨properties.2.1, ssaMapOKMore next ssa nextA ⟨h.2, properties.1⟩⟩
  generalize noEq : ssaCcTrans no ssa nextA tables = noResult
  rcases noResult with ⟨b, rightMap, nextB⟩
  rw [noEq] at hb
  have fixed := fixInconsistencies_conventions (width := width) leftMap rightMap nextB (mkPrio a b)
  generalize fixEq : fixInconsistencies (width := width) (mkPrio a b) leftMap rightMap nextB = fixResult
  rcases fixResult with ⟨leftFix, rightFix, finalNext, finalMap⟩
  rw [fixEq] at fixed
  have leftPre : preAllocConventionsHOL leftFix = true := by
    simp only [preAllocConventionsHOL, Bool.and_eq_true]
    exact ⟨fixed.1, fixed.2.2.1⟩
  have rightPre : preAllocConventionsHOL rightFix = true := by
    simp only [preAllocConventionsHOL, Bool.and_eq_true]
    exact ⟨fixed.2.1, fixed.2.2.2⟩
  have leftAll := preAlloc_seq a leftFix ha leftPre
  have rightAll := preAlloc_seq b rightFix hb rightPre
  simp only [ssaCcTrans, yesEq, noEq, fixEq, preAllocConventionsHOL,
    everyStackVarHOL, callArgConventionHOL, Bool.and_eq_true] at leftAll rightAll ⊢
  exact ⟨⟨leftAll.1, rightAll.1⟩, leftAll.2, rightAll.2⟩

/-- Flapjack factoring of the literal reconciliation's Skip/Move outputs;
there is no separately named HOL theorem for this Boolean helper. -/
private theorem preAlloc_reconcile {width : Nat} [NeZero width] {β : Type}
    (current target : Spt Nat) (names : Spt β) :
    preAllocConventionsHOL (ssaReconcile (width := width) current target names) = true := by
  unfold ssaReconcile
  dsimp only
  split <;> simp [preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL]

/-- Original Loop case with the source body's genuine induction hypothesis. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocLoop {width : Nat} [NeZero width]
    (names exitNames : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (bodyIH : ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      isAllocVar next ∧ ssaMapOK next ssa →
        preAllocConventionsHOL (ssaCcTrans body ssa next tables).1 = true)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : isAllocVar next ∧ ssaMapOK next ssa) :
    preAllocConventionsHOL (ssaCcTrans (.loop names body exitNames) ssa next tables).1 = true := by
  generalize setupEq : loopSetup (width := width) names exitNames ssa next = setupResult
  rcases setupResult with ⟨setup, refreshed, nextRefreshed⟩
  have properties := loopSetup_propsLocal names exitNames ssa next setup refreshed nextRefreshed
    ⟨setupEq, h.2, h.1⟩
  have setupPre := loopSetup_preAllocConventions names exitNames ssa next setup refreshed nextRefreshed setupEq
  have bodyPre := bodyIH (sptInter refreshed names) nextRefreshed
    ((refreshed, names, exitNames) :: tables)
    ⟨properties.1, ssaMapOKInter nextRefreshed refreshed names properties.2.1⟩
  generalize bodyEq : ssaCcTrans body (sptInter refreshed names) nextRefreshed
    ((refreshed, names, exitNames) :: tables) = bodyResult
  rcases bodyResult with ⟨output, bodyMap, nextOut⟩
  rw [bodyEq] at bodyPre
  have backPre := preAlloc_reconcile (width := width) bodyMap refreshed names
  generalize backEq : ssaReconcile (width := width) bodyMap refreshed names = back
  rw [backEq] at backPre
  have finalPre : preAllocConventionsHOL
      (match back with | .skip => output | _ => .seq output back) = true := by
    cases back <;> first | exact bodyPre | exact preAlloc_seq _ _ bodyPre backPre
  have loopPre : preAllocConventionsHOL (.loop (applyNummapKey (optionLookup refreshed) names)
      (match back with | .skip => output | _ => .seq output back)
      (applyNummapKey (optionLookup refreshed) exitNames)) = true := by
    simpa [preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL] using finalPre
  cases back <;>
    simpa only [ssaCcTrans, setupEq, bodyEq, backEq] using preAlloc_seq setup _ setupPre loopPre

/-- Original Break case over the complete arbitrary loop context. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocBreak {width : Nat} [NeZero width] (index : Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : isAllocVar next ∧ ssaMapOK next ssa) :
    preAllocConventionsHOL (ssaCcTrans (.break index : WordLangProgHOL (BitVec width)) ssa next tables).1 = true := by
  cases selected : tables[index]? with
  | none => simp [ssaCcTrans, selected, preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL]
  | some entry =>
      rcases entry with ⟨target, names, exits⟩
      have pre := preAlloc_reconcile (width := width) ssa target exits
      generalize eq : ssaReconcile (width := width) ssa target exits = back
      rw [eq] at pre
      simp only [ssaCcTrans, selected, eq]
      cases back <;> first | rfl | exact preAlloc_seq _ _ pre (by rfl)

/-- Original Continue case over the complete arbitrary loop context. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocContinue {width : Nat} [NeZero width] (index : Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : isAllocVar next ∧ ssaMapOK next ssa) :
    preAllocConventionsHOL (ssaCcTrans (.continue index : WordLangProgHOL (BitVec width)) ssa next tables).1 = true := by
  cases selected : tables[index]? with
  | none => simp [ssaCcTrans, selected, preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL]
  | some entry =>
      rcases entry with ⟨target, names, exits⟩
      have pre := preAlloc_reconcile (width := width) ssa target names
      generalize eq : ssaReconcile (width := width) ssa target names = back
      rw [eq] at pre
      simp only [ssaCcTrans, selected, eq]
      cases back <;> first | rfl | exact preAlloc_seq _ _ pre (by rfl)

end Flapjack.WordAlloc
