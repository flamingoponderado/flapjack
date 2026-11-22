module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.NumSize
public import Flapjack.Compiler.Backend.WordBignum.Proofs.WordSemClauses

@[expose] public section

/-! `AnyArith_thm`, first steps: the operand sizes are summed into a temporary.
Flapjack-only helpers for the `AnyArith_thm` port; each follows a segment of
the HOL proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.WordSemStateFiniteExact.BignumClauses

/-- The size word computed by the first four statements of `AnyArith_code`. -/
def sizeWord (width : Nat) [NeZero width] (i j : Int) : BitVec width :=
  4 + BitVec.ofNat width (4 * (Misc.Multiword.i2mw i : Bool × List (BitVec width)).2.length) +
    BitVec.ofNat width (4 * (Misc.Multiword.i2mw j : Bool × List (BitVec width)).2.length)

/-- The first four statements of `AnyArith_code` (HOL proof up to the
`AllocVar` call). -/
theorem evaluate_prefix {width : Nat} [NeZero width] {C F : Type} {c : Config} {l1 l2 : Nat}
    {s : DataSem.State C F} {t : WordSemStateFiniteExact width C F} {locs : List (Nat × Nat)}
    {i j : Int} (rel : stateRel c l1 l2 s t none locs)
    (hi : DataSem.getVar 0 s.locals = some (.number i))
    (hj : DataSem.getVar 1 s.locals = some (.number j)) (rest : WordLangProgHOL (BitVec width)) :
    WordSemStateFiniteExact.evaluate
        (.seq (.assign 1 (.const 4)) (.seq (addNumSize c 0) (.seq (addNumSize c 1)
          (.seq (.set (.temp 29) (.var 1)) rest)))) t =
      WordSemStateFiniteExact.evaluate rest
        ((t.setVar 1 (.word (sizeWord width i j))).setStore (.temp 29)
          (.word (sizeWord width i j))) := by
  rw [evaluate_seq_of_none _ (t.setVar 1 (.word 4)) _ _
    (by simp [evaluate_assign, WordSemStateFiniteExact.wordExp])]
  rw [evaluate_seq_of_none _ _ _ _ (evaluateAddNumSize 0 c l1 l2 s t locs i 4 ⟨rel, hi⟩)]
  rw [evaluate_seq_of_none _ _ _ _ (evaluateAddNumSize 1 c l1 l2 s t locs j _ ⟨rel, hj⟩)]
  rw [evaluate_seq_of_none _ _ _ _ (by
    rw [evaluate_set]
    simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]; rfl)]
  rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
