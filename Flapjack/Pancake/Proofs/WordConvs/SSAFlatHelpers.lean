import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions
import Flapjack.Pancake.WordConvs

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Encoders.Asm

/-- Original unconditional fake-sequence flat-expression conventions, with arbitrary
source list. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "fake_seq_flat_exp_conventions" (words_as_type_indexed_bitvec)]
theorem fakeSeq_flatExpConventions {width : Nat} [NeZero width]
    (names : List Nat) :
    flatExpConventions
      ((names.map (fakeMove : Nat → WordLangProgHOL (BitVec width))).foldr .seq .skip) = true := by
  induction names with
  | nil => simp [flatExpConventions]
  | cons name names ih =>
      simpa [flatExpConventions, fakeMove] using ih

/-- Original loop setup flat-expression conventions with the actual producer equation as sole
premise; no SSA map or register-bound assumptions are added. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "loop_setup_flat_exp_conventions" (words_as_type_indexed_bitvec)]
theorem loopSetup_flatExpConventions {width : Nat} [NeZero width]
    (names exitNames : Spt Unit) (ssa : Spt Nat) (na : Nat)
    (setupProg : WordLangProgHOL (BitVec width)) (ssaRefreshed : Spt Nat)
    (naRefreshed : Nat)
    (setup : loopSetup names exitNames ssa na = (setupProg, ssaRefreshed, naRefreshed)) :
    flatExpConventions setupProg = true := by
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
  have fake := fakeSeq_flatExpConventions (width := width) fresh
  have moveConvention : flatExpConventions moves = true := by
    unfold listNextVarRenameMove at hm
    have projected := congrArg Prod.fst hm
    simp only at projected
    rw [← projected]
    simp [flatExpConventions]
  have output := congrArg Prod.fst setup
  simp only at output
  rw [← output]
  rw [flatExpConventions, fake, moveConvention]
  rfl

/-- HOL quantifies a vacuous configuration binder; it is omitted because it
does not occur in the premise or conclusion. Original reconciliation flat-expression conventions pair conclusion,
with the actual fake-move producer equality as the sole premise. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "flat_exp_conventions_fake_moves" (words_as_type_indexed_bitvec)]
theorem fakeMoves_flatExpConventions {width : Nat} [NeZero width]
    (prio : Option (Unit ⊕ Unit)) (names : List Nat)
    (ssaL ssaR : Spt Nat) (next : Nat)
    (left right : WordLangProgHOL (BitVec width)) (finalNext : Nat)
    (finalL finalR : Spt Nat)
    (produced : fakeMoves prio names ssaL ssaR next = (left, right, finalNext, finalL, finalR)) :
    flatExpConventions left = true ∧ flatExpConventions right = true := by
  have all : ∀ (ls : List Nat) (l r : Spt Nat) (na : Nat),
      let (a, b, _, _, _) := fakeMoves (width := width) prio ls l r na
      flatExpConventions a = true ∧ flatExpConventions b = true := by
    intro ls
    induction ls with
    | nil => intro l r na; simp [fakeMoves, flatExpConventions]
    | cons x xs ih =>
        intro l r na
        generalize he : fakeMoves (width := width) prio xs l r na = result
        rcases result with ⟨a, b, count, treeL, treeR⟩
        have previous := ih l r na
        rw [he] at previous
        simp only [fakeMoves, he]
        cases hl : sptLookup x treeL <;> cases hr : sptLookup x treeR <;>
          simp_all [flatExpConventions, fakeMove]
  have result := all names ssaL ssaR next
  rw [produced] at result
  exact result

/-- Original unconditional reconciliation flat-expression conventions. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "ssa_reconcile_flat_exp_conventions" (words_as_type_indexed_bitvec)]
theorem ssaReconcile_flatExpConventions {width : Nat} [NeZero width] {β : Type}
    (current target : Spt Nat) (names : Spt β) :
    flatExpConventions (ssaReconcile current target names : WordLangProgHOL (BitVec width)) = true := by
  unfold ssaReconcile
  dsimp only
  split <;> rfl

end Flapjack.WordAlloc
