import Flapjack.HolRef
import Flapjack.Pancake.Proofs.CrepInline

/-!
# `stack_allocProof` finite-map `SUBMAP` lemmas

`SUBMAP_DOMSUB_both` and `SUBMAP_FUPDATE_both` of
`cakeml/compiler/backend/proofs/stack_allocProofScript.sml`, over the canonical
finite-support carrier and its untagged `submap` rendering of HOL `SUBMAP`
(`Flapjack/Pancake/Proofs/CrepInline.lean`).  HOL `\\` and `|+` are the
HOL-equality `eraseEq`/`updateEq`. `[DecidableEq κ]` supplies lawful Lean
equality for those operations, not a Boolean-equality assumption or key
restriction: every key type admits it through Classical.decEq, matching HOL's
classical equality. No additional logical premise is introduced.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack

/-- Exact HOL `SUBMAP_DOMSUB_both` (`stack_allocProofScript.sml:5206-5212`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "SUBMAP_DOMSUB_both"
  (fmap_as_finite_support_relation := [A, B])]
theorem submap_domsub_both {κ : Type} {β : Type} [DecidableEq κ]
    {A : HolFiniteMapExact κ β} {B : HolFiniteMapExact κ β} {c : κ} :
    A.submap B → (A.eraseEq c).submap (B.eraseEq c) :=
  fun h => submap_imp_domsub_submap_exact A B c h

/-- Exact HOL `SUBMAP_FUPDATE_both` (`stack_allocProofScript.sml:5214-5220`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "SUBMAP_FUPDATE_both"
  (fmap_as_finite_support_relation := [A, B])]
theorem submap_fupdate_both {κ : Type} {β : Type} [DecidableEq κ]
    {A : HolFiniteMapExact κ β} {B : HolFiniteMapExact κ β} {n : κ} {v : β} :
    A.submap B → (A.updateEq (n, v)).submap (B.updateEq (n, v)) :=
  fun h => submap_imp_fupdate_submap_exact A B n v h

end Flapjack.Compiler.Backend.StackAlloc
