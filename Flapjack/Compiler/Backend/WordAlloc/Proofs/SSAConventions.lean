import Flapjack.Compiler.Backend.WordAlloc.SSAFixInconsistencies
import Flapjack.Compiler.Backend.WordAlloc.SSAHelpers
import Flapjack.Pancake.WordConvs

/-! Original SSA reconciliation convention group from word_allocProof. -/
namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc

/-- Original four conventions for both fake-move outputs. No freshness,
map validity, or register bound is assumed by the HOL statement. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "fake_moves_conventions" (words_as_type_indexed_bitvec)]
theorem fakeMoves_conventions {width : Nat} [NeZero width]
    (prio : Option (Unit ⊕ Unit)) (ls : List Nat) (ssaL ssaR : Spt Nat) (na : Nat) :
    let (a, b, _, _, _) : WordLangProgHOL (BitVec width) ×
      WordLangProgHOL (BitVec width) × Nat × Spt Nat × Spt Nat :=
      fakeMoves prio ls ssaL ssaR na
    everyStackVarHOL isStackVar (a : WordLangProgHOL (BitVec width)) = true ∧
    everyStackVarHOL isStackVar b = true ∧
    callArgConventionHOL a = true ∧ callArgConventionHOL b = true := by
  induction ls generalizing ssaL ssaR na with
  | nil => simp [fakeMoves, everyStackVarHOL, callArgConventionHOL]
  | cons x xs ih =>
      generalize he : fakeMoves (width := width) prio xs ssaL ssaR na = result
      rcases result with ⟨a, b, next, left, right⟩
      have previous := ih ssaL ssaR na
      rw [he] at previous
      simp only [fakeMoves, he]
      cases hl : sptLookup x left <;> cases hr : sptLookup x right <;>
        simp_all [fakeMove, everyStackVarHOL, callArgConventionHOL,
          instArgConvention]

/-- Original conventions for the actual reconciliation result, including
both initial merge moves and subsequent fake moves. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "fix_inconsistencies_conventions" (words_as_type_indexed_bitvec)]
theorem fixInconsistencies_conventions {width : Nat} [NeZero width]
    (ssaL ssaR : Spt Nat) (na : Nat) (prio : Option (Unit ⊕ Unit)) :
    let (a, b, _, _) : WordLangProgHOL (BitVec width) ×
      WordLangProgHOL (BitVec width) × Nat × Spt Nat :=
      fixInconsistencies prio ssaL ssaR na
    everyStackVarHOL isStackVar (a : WordLangProgHOL (BitVec width)) = true ∧
    everyStackVarHOL isStackVar b = true ∧
    callArgConventionHOL a = true ∧ callArgConventionHOL b = true := by
  unfold fixInconsistencies
  generalize hm : mergeMoves ((sptToAList (sptUnion ssaL ssaR)).map Prod.fst)
    ssaL ssaR na = merged
  rcases merged with ⟨lmov, rmov, next, left, right⟩
  have moves := fakeMoves_conventions (width := width) prio
    ((sptToAList (sptUnion ssaL ssaR)).map Prod.fst) left right next
  generalize hf : fakeMoves (width := width) prio
    ((sptToAList (sptUnion ssaL ssaR)).map Prod.fst) left right next = result
  rcases result with ⟨a, b, fresh, leftOut, rightOut⟩
  rw [hf] at moves
  simpa [hm, hf, everyStackVarHOL, callArgConventionHOL] using moves

/-- Original conventions for the complete source fake-move sequence. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "fake_seq_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem fakeSeq_preAllocConventions {width : Nat} [NeZero width] (ls : List Nat) :
    preAllocConventionsHOL
      ((ls.map (fakeMove : Nat → WordLangProgHOL (BitVec width))).foldr .seq .skip :
        WordLangProgHOL (BitVec width)) = true := by
  induction ls with
  | nil => simp [preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL]
  | cons x xs ih =>
      simpa [preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL,
        fakeMove, instArgConvention] using ih

/-- Original loop setup implication, retaining its actual output equation. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "loop_setup_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem loopSetup_preAllocConventions {width : Nat} [NeZero width]
    (names exitNames : Spt Unit) (ssa : Spt Nat) (na : Nat)
    (setupProg : WordLangProgHOL (BitVec width)) (ssaRefreshed : Spt Nat)
    (naRefreshed : Nat)
    (setup : loopSetup names exitNames ssa na = (setupProg, ssaRefreshed, naRefreshed)) :
    preAllocConventionsHOL setupProg = true := by
  unfold loopSetup at setup
  generalize hr : listNextVarRename
    (((sptToAList (sptUnion names exitNames)).map Prod.fst).filter
      fun v => (sptLookup v ssa).isNone) ssa na = renamed at setup
  rcases renamed with ⟨fresh, extended, next⟩
  generalize hm : listNextVarRenameMove (width := width) extended next
    (((sptToAList (sptUnion names exitNames)).map Prod.fst).filter
      fun v => (sptLookup v ssa).isSome) = moved at setup
  rcases moved with ⟨moves, refreshed, nextOut⟩
  simp only [hr, hm] at setup
  have fake := fakeSeq_preAllocConventions (width := width) fresh
  have moveConvention : preAllocConventionsHOL moves = true := by
    unfold listNextVarRenameMove at hm
    have projected := congrArg Prod.fst hm
    simp only at projected
    rw [← projected]
    simp [preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL]
  have output := congrArg Prod.fst setup
  simp only at output
  rw [← output]
  simp only [preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL,
    Bool.and_eq_true] at fake moveConvention ⊢
  exact ⟨⟨fake.1, moveConvention.1⟩, fake.2, moveConvention.2⟩

end Flapjack.WordAlloc
