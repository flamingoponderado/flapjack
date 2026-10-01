import Flapjack.Compiler.Backend.WordAlloc.Proofs.RemoveDead
import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate
import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd
import Flapjack.Pancake.WordConvs

/-!
# `evaluate_remove_dead` statement

The conclusion of `word_allocProofScript.sml:3900-4472` `evaluate_remove_dead` for
one result, and its per-program goal, so that the HOL case proofs and the Loop
helper can be stated as genuine cases of the same theorem. These are Flapjack
infrastructure for the case split, not separate HOL declarations. HOL `oEL` is
`sptOel` and `I` is `id`.
-/

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

/-- The post-condition of HOL `evaluate_remove_dead` for a result: `NONE`: the
live locals and the store outside `nlive`; `Break n`/`Continue n`: equal stores
and the `n`-th loop table entry's exit/entry names when present; any other
result: equal locals and stores. -/
def removeDeadPost {width : Nat} [NeZero width] {C F : Type} (live : NumSet)
    (nlive : List WordStoreHOL) (lt : List (NumSet × NumSet)) (res : Option (WordSemResult width))
    (rst : WordSemStateFiniteExact width C F) (t' : Spt (WordLocW width))
    (tstore' : HolFiniteMapExact WordStoreHOL (WordLocW width)) : Prop :=
  match res with
  | none => strongLocalsRel id (sptDomain live) rst.locals t' ∧ liveStoreRel nlive rst.store tstore'
  | some (.break n) =>
      rst.store = tstore' ∧
        match sptOel n lt with
        | some (_, exitNames) => strongLocalsRel id (sptDomain exitNames) rst.locals t'
        | none => True
  | some (.continue n) =>
      rst.store = tstore' ∧
        match sptOel n lt with
        | some (names, _) => strongLocalsRel id (sptDomain names) rst.locals t'
        | none => True
  | some _ => rst.locals = t' ∧ rst.store = tstore'

/-- HOL `evaluate_remove_dead`'s statement for one program, in HOL's quantifier
order after `prog`. -/
def removeDeadGoal {width : Nat} [NeZero width] (C F : Type)
    (prog : WordLangProgHOL (BitVec width)) : Prop :=
  ∀ (live : NumSet) (nlive : List WordStoreHOL) (lt : List (NumSet × NumSet))
    (prog' : WordLangProgHOL (BitVec width)) (livein : NumSet) (nlivein : List WordStoreHOL)
    (st : WordSemStateFiniteExact width C F) (t : Spt (WordLocW width))
    (tstore : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (res : Option (WordSemResult width)) (rst : WordSemStateFiniteExact width C F),
    strongLocalsRel id (sptDomain livein) st.locals t ∧
      liveStoreRel nlivein st.store tstore ∧
      evaluate prog st = (res, rst) ∧
      flatExpConventions prog = true ∧
      removeDead prog live nlive lt = (prog', livein, nlivein) ∧
      res ≠ some .error →
    ∃ (t' : Spt (WordLocW width)) (tstore' : HolFiniteMapExact WordStoreHOL (WordLocW width)),
      evaluate prog' { st with locals := t, store := tstore } =
        (res, { rst with locals := t', store := tstore' }) ∧
      removeDeadPost live nlive lt res rst t' tstore'

/-- `strong_locals_rel I` is reflexive (Flapjack infrastructure). -/
theorem strongLocalsRelIdRefl {α : Type} (live : Nat → Prop) (m : Spt α) :
    strongLocalsRel id live m m := fun _ _ h => h.2

end Flapjack.WordAlloc
