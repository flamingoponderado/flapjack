import Flapjack.HolRef
import Flapjack.Pancake.CrepArith
import Flapjack.Pancake.Semantics.CrepRuntimeTarget
import Flapjack.Pancake.Semantics.CrepSem.Eval
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect

/-! Theorem counterparts and Flapjack support for CakeML's
    `crep_arithProofScript.sml`. The tagged `dest_const_thm` uses the exact
    width-indexed `CrepExpHOL` carrier with `[NeZero width]`. -/

namespace Flapjack


/-- Exact port of CakeML's `dest_const_thm` (`crep_arithProofScript.sml:64`).
    `width` ranges over every positive HOL word dimension. `BitVec width` is
    the canonical `Fin width → Bool` representation; any HOL finite word
    index of cardinality `width` is related by reindexing, and this theorem
    only inverts the root constructor. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "dest_const_thm"]
theorem crepDestConstHOL_eq_const {width : Nat} [NeZero width]
    (expression : CrepExpHOL width)
    (value : BitVec width)
    (h : crepDestConstHOL expression = some value) :
    expression = .const value := by
  cases expression <;> simp_all [crepDestConstHOL]


/-- Exact generic list-success monotonicity helper from HOL's local
    `OPT_MMAP_EQ_SOME_MONO` (`crep_arithProofScript.sml:93`).  `List.mapM` with
    the `Option` monad is the Lean encoding of HOL's `OPT_MMAP`; this lemma is
    independent of the Crep evaluator and is used for pointwise successful
    result preservation in the arithmetic simplifier proof. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "OPT_MMAP_EQ_SOME_MONO" 93]
theorem optMmapEqSomeMono {α β : Type} (f g : α → Option β)
    (xs : List α) (ys : List β)
    (hf : xs.mapM f = some ys)
    (hmono : ∀ x z, x ∈ xs → f x = some z → g x = some z) :
    xs.mapM g = some ys := by
  induction xs generalizing ys with
  | nil =>
      simp_all
  | cons x xs ih =>
      simp only [List.mapM_cons] at hf ⊢
      cases hfx : f x with
      | none => simp [hfx] at hf
      | some z =>
          cases htail : xs.mapM f with
          | none => simp [hfx, htail] at hf
          | some tail =>
              have hys : z :: tail = ys := by
                simpa [hfx, htail] using hf
              have hgx : g x = some z :=
                hmono x z (by simp) hfx
              have hgtail : xs.mapM g = some tail :=
                ih tail htail (by
                  intro y value hy hvalue
                  exact hmono y value (by simp [hy]) hvalue)
              simp [hgx, hgtail, hys]




end Flapjack
