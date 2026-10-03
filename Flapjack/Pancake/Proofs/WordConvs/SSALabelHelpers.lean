import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions
import Flapjack.Pancake.WordConvs

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Encoders.Asm

/-- Original unconditional fake-sequence empty extracted labels, with arbitrary
source list. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "fake_seq_no_labs" (words_as_type_indexed_bitvec)]
theorem fakeSeq_noLabels {width : Nat} [NeZero width]
    (names : List Nat) :
    extractLabels
      ((names.map (fakeMove : Nat → WordLangProgHOL (BitVec width))).foldr .seq .skip) = [] := by
  induction names with
  | nil => simp [extractLabels]
  | cons name names ih =>
      simpa [extractLabels, fakeMove] using ih

/-- Original loop setup empty extracted labels with the actual producer equation as sole
premise; no SSA map or register-bound assumptions are added. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "loop_setup_no_labs" (words_as_type_indexed_bitvec)]
theorem loopSetup_noLabels {width : Nat} [NeZero width]
    (names exitNames : Spt Unit) (ssa : Spt Nat) (na : Nat)
    (setupProg : WordLangProgHOL (BitVec width)) (ssaRefreshed : Spt Nat)
    (naRefreshed : Nat)
    (setup : loopSetup names exitNames ssa na = (setupProg, ssaRefreshed, naRefreshed)) :
    extractLabels setupProg = [] := by
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
  have fake := fakeSeq_noLabels (width := width) fresh
  have moveConvention : extractLabels moves = [] := by
    unfold listNextVarRenameMove at hm
    have projected := congrArg Prod.fst hm
    simp only at projected
    rw [← projected]
    simp [extractLabels]
  have output := congrArg Prod.fst setup
  simp only at output
  rw [← output]
  simp only [extractLabels, fake, moveConvention, List.nil_append]

/-- Original reconciliation empty-label pair conclusion,
with the actual fake-move producer equality as the sole premise. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "fake_moves_no_labs" (words_as_type_indexed_bitvec)]
theorem fakeMoves_noLabels {width : Nat} [NeZero width]
    (prio : Option (Unit ⊕ Unit)) (names : List Nat)
    (ssaL ssaR : Spt Nat) (next : Nat)
    (left right : WordLangProgHOL (BitVec width)) (finalNext : Nat)
    (finalL finalR : Spt Nat)
    (produced : fakeMoves prio names ssaL ssaR next = (left, right, finalNext, finalL, finalR)) :
    extractLabels left = [] ∧ extractLabels right = [] := by
  have all : ∀ (ls : List Nat) (l r : Spt Nat) (na : Nat),
      let (a, b, _, _, _) := fakeMoves (width := width) prio ls l r na
      extractLabels a = [] ∧ extractLabels b = [] := by
    intro ls
    induction ls with
    | nil => intro l r na; simp [fakeMoves, extractLabels]
    | cons x xs ih =>
        intro l r na
        generalize he : fakeMoves (width := width) prio xs l r na = result
        rcases result with ⟨a, b, count, treeL, treeR⟩
        have previous := ih l r na
        rw [he] at previous
        simp only [fakeMoves, he]
        cases hl : sptLookup x treeL <;> cases hr : sptLookup x treeR <;>
          simp_all [extractLabels, fakeMove]
  have result := all names ssaL ssaR next
  rw [produced] at result
  exact result

/-- Original unconditional reconciliation empty extracted labels. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "ssa_reconcile_no_labs" (words_as_type_indexed_bitvec)]
theorem ssaReconcile_noLabels {width : Nat} [NeZero width] {β : Type}
    (current target : Spt Nat) (names : Spt β) :
    extractLabels (ssaReconcile current target names : WordLangProgHOL (BitVec width)) = [] := by
  unfold ssaReconcile
  dsimp only
  split <;> rfl

end Flapjack.WordAlloc
