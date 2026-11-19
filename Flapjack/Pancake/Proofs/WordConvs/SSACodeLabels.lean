module

public import Flapjack.Pancake.Proofs.WordConvs.GoodHandlersSSA
public import Flapjack.Pancake.Proofs.WordConvs.SSALabelHelpers
public import Flapjack.Pancake.WordConvs.CodeLabels

@[expose] public section

/-!
Code-label preservation through the native SSA passes, the
`word_get_code_labels_ssa_cc_trans` family of
`wordConvsProofScript.sml:1243-1309`. Kept in a sibling module so the
`Set`-based statements stay out of `GoodHandlersTail`'s environment.
-/

namespace Flapjack.WordConvs

open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.WordAlloc

/-- Flapjack-only label analogue of the handler-predicate invariant: every
`ssa_cc_trans` output keeps exactly its input's code labels, for arbitrary
knowledge maps, counters and cut-set list. -/
private def programLabels {width : Nat} [NeZero width]
    (prog : WordLangProgHOL (BitVec width)) : Prop :=
  ∀ ssa next tables,
    getCodeLabelsHOL (ssaCcTrans prog ssa next tables).1 = getCodeLabelsHOL prog

/-- Flapjack-only projection corollary of `getCodeLabels_fakeMoves` for the
left output. -/
private theorem fakeMovesLabels1 {width : Nat} [NeZero width]
    (prio : Option (Unit ⊕ Unit)) (names : List Nat) (ssaL ssaR : Spt Nat) (next : Nat) :
    getCodeLabelsHOL (fakeMoves (width := width) prio names ssaL ssaR next).1 = ∅ :=
  (getCodeLabels_fakeMoves prio names ssaL ssaR next
    (fakeMoves prio names ssaL ssaR next).1
    (fakeMoves prio names ssaL ssaR next).2.1
    (fakeMoves prio names ssaL ssaR next).2.2.1
    (fakeMoves prio names ssaL ssaR next).2.2.2.1
    (fakeMoves prio names ssaL ssaR next).2.2.2.2 rfl).1

/-- Flapjack-only projection corollary of `getCodeLabels_fakeMoves` for the
right output. -/
private theorem fakeMovesLabels2 {width : Nat} [NeZero width]
    (prio : Option (Unit ⊕ Unit)) (names : List Nat) (ssaL ssaR : Spt Nat) (next : Nat) :
    getCodeLabelsHOL (fakeMoves (width := width) prio names ssaL ssaR next).2.1 = ∅ :=
  (getCodeLabels_fakeMoves prio names ssaL ssaR next
    (fakeMoves prio names ssaL ssaR next).1
    (fakeMoves prio names ssaL ssaR next).2.1
    (fakeMoves prio names ssaL ssaR next).2.2.1
    (fakeMoves prio names ssaL ssaR next).2.2.2.1
    (fakeMoves prio names ssaL ssaR next).2.2.2.2 rfl).2

/-- Flapjack-only label analogue of `fixGood1`: both branches produced by
`fix_inconsistencies` are move/fake-move sequences, hence label-free. -/
private theorem fixLabels1 {width : Nat} [NeZero width]
    (prio : Option (Unit ⊕ Unit)) (l r : Spt Nat) (next : Nat) :
    getCodeLabelsHOL (fixInconsistencies (width := width) prio l r next).1 = ∅ := by
  unfold fixInconsistencies
  dsimp only
  simp only [getCodeLabelsHOL, fakeMovesLabels1, Set.empty_union]

/-- Flapjack-only label analogue of `fixGood2` for the right branch. -/
private theorem fixLabels2 {width : Nat} [NeZero width]
    (prio : Option (Unit ⊕ Unit)) (l r : Spt Nat) (next : Nat) :
    getCodeLabelsHOL (fixInconsistencies (width := width) prio l r next).2.1 = ∅ := by
  unfold fixInconsistencies
  dsimp only
  simp only [getCodeLabelsHOL, fakeMovesLabels2, Set.empty_union]

/-- Flapjack-only label analogue of `loopSetupGood'`: the setup program that
precedes a loop body has no code labels, from the actual producer equation. -/
private theorem loopSetupLabels {width : Nat} [NeZero width]
    (names exitNames : Spt Unit) (ssa : Spt Nat) (na : Nat) :
    getCodeLabelsHOL (loopSetup (width := width) names exitNames ssa na).1 = ∅ :=
  loopSetup_codeLabels names exitNames ssa na _ _ _ rfl

set_option linter.unusedSimpArgs false in
/-- Flapjack-only `ssa_cc_trans` first-component invariant, proved by structural
recursion mirroring the HOL `recInduct ssa_cc_trans_ind` walk. -/
private theorem codeLabels_ssaCcTrans_fst {width : Nat} [NeZero width] :
    ∀ (prog : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (next : Nat)
      (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      getCodeLabelsHOL (ssaCcTrans prog ssa next lt).1 = getCodeLabelsHOL prog := by
  intro p
  apply WordLangProgHOL.rec
    (motive_1 := programLabels)
    (motive_2 := fun ret => match ret with | none => True | some r => programLabels r.2.2.1)
    (motive_3 := fun exc => match exc with | none => True | some r => programLabels r.2.1)
    (motive_4 := fun r => programLabels r.2.2.1)
    (motive_5 := fun r => programLabels r.2.1)
    (motive_6 := fun r => programLabels r.2.1)
    (motive_7 := fun r => programLabels r.1) (t := p)
  all_goals dsimp only [programLabels]
  all_goals intros
  all_goals try simp_all [ssaCcTrans, getCodeLabelsHOL, nextVarRename, listNextVarRenameMove]
  case inst =>
    rename_i instruction ssa next tables
    fun_cases ssaCcTransInst instruction ssa next <;> simp [getCodeLabelsHOL]
  case ite =>
    simp only [fixLabels1, fixLabels2, Set.union_empty]
  case loop =>
    rename_i names body exits bodyIH ssa next tables
    split
    · simp only [getCodeLabelsHOL, loopSetupLabels, Set.empty_union, Set.union_empty]
      rw [bodyIH _ _ _]
    · simp only [getCodeLabelsHOL, loopSetupLabels, getCodeLabels_ssaReconcile,
        Set.empty_union, Set.union_empty]
      rw [bodyIH _ _ _]
  case «break» | «continue» =>
    split
    · rfl
    · dsimp only
      split
      · rfl
      · simp only [getCodeLabelsHOL, getCodeLabels_ssaReconcile, Set.empty_union]
  case shareInst =>
    split <;> simp [getCodeLabelsHOL]
  case call =>
    rename_i returns target arguments handler retIH excIH ssa next tables
    cases returns with
    | none =>
      cases handler with
      | none => simp_all [ssaCcTrans, getCodeLabelsHOL]
      | some exc =>
        rcases exc with ⟨excName, excBody, e1, e2⟩
        simp_all [ssaCcTrans, getCodeLabelsHOL]
    | some ret =>
      rcases ret with ⟨retNames, cutsets, retBody, l1, l2⟩
      cases handler with
      | none =>
        simp_all [ssaCcTrans, getCodeLabelsHOL, listNextVarRenameMove]
      | some exc =>
        rcases exc with ⟨excName, excBody, e1, e2⟩
        simp_all [ssaCcTrans, getCodeLabelsHOL, listNextVarRenameMove, nextVarRename,
          fixLabels1, fixLabels2, Set.empty_union]

/-- Original code-label equality of the whole `ssa_cc_trans` pass: the program
component keeps exactly its input's labels. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_get_code_labels_ssa_cc_trans" (words_as_type_indexed_bitvec)]
theorem codeLabels_ssaCcTrans {width : Nat} [NeZero width] :
    ∀ (x : WordLangProgHOL (BitVec width)) (y : Spt Nat) (z : Nat)
      (lt : List (Spt Nat × Spt Unit × Spt Unit)) (a : WordLangProgHOL (BitVec width))
      (b : Spt Nat) (c : Nat),
      ssaCcTrans x y z lt = (a, b, c) → getCodeLabelsHOL a = getCodeLabelsHOL x := by
  intro x y z lt a b c h
  have := codeLabels_ssaCcTrans_fst x y z lt
  rw [h] at this
  exact this

/-- Original code-label equality of the complete `full_ssa_cc_trans` pass. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_get_code_labels_full_ssa_cc_trans" (words_as_type_indexed_bitvec)]
theorem codeLabels_fullSsaCcTrans {width : Nat} [NeZero width] :
    ∀ (m : Nat) (p : WordLangProgHOL (BitVec width)),
      getCodeLabelsHOL (fullSsaCcTrans m p) = getCodeLabelsHOL p := by
  intro m p
  generalize produced : setupSSA (outputWidth := width) m (limitVar p) p = result
  rcases result with ⟨move, ssa, next⟩
  have hm : getCodeLabelsHOL move = ∅ := by
    unfold setupSSA at produced
    generalize listNextVarRename (evenList m) .ln (limitVar p) = renamed at produced
    rcases renamed with ⟨names, tree, counter⟩
    cases produced
    simp [getCodeLabelsHOL]
  have hb := codeLabels_ssaCcTrans_fst p ssa next []
  generalize bodyEq : ssaCcTrans p ssa next [] = bodyResult
  rcases bodyResult with ⟨body, finalMap, finalNext⟩
  rw [bodyEq] at hb
  simp only [fullSsaCcTrans, produced, bodyEq, getCodeLabelsHOL, hm, hb,
    Set.empty_union]

end Flapjack.WordConvs
