import Flapjack.Compiler.Backend.WordAlloc.Colour
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ColouringOk
import Flapjack.Compiler.Backend.WordAlloc.Proofs.StateRelation
import Flapjack.Compiler.Backend.WordAlloc.Proofs.StrongLocalsRel
import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate

/-!
# `evaluate_apply_colour` statement

The statement of `word_allocProofScript.sml:1105-1130` `evaluate_apply_colour`,
split into its per-program conclusion and its per-program goal so that the
HOL `Resume` case proofs can be stated as genuine cases of the same theorem.
These two definitions are Flapjack infrastructure for the case split, not
separate HOL declarations: the tagged assembly theorem states the HOL result
itself.
-/

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

/-- The live-scoped locals obligation of HOL `evaluate_apply_colour` for a
result: `NONE`: `live`; `Break n`/`Continue n`: the `n`-th loop table entry's
exit/entry names when present; any other result: equal locals. -/
def applyColourLocals {width : Nat} [NeZero width] (f : Nat → Nat) (live : NumSet)
    (lt : List (NumSet × NumSet)) (res : Option (WordSemResult width))
    (sloc tloc : Spt (WordLocW width)) : Prop :=
  match res with
  | none => strongLocalsRel f (sptDomain live) sloc tloc
  | some (.break n) =>
      match sptOel n lt with
      | some (_, exitNames) => strongLocalsRel f (sptDomain exitNames) sloc tloc
      | none => True
  | some (.continue n) =>
      match sptOel n lt with
      | some (names, _) => strongLocalsRel f (sptDomain names) sloc tloc
      | none => True
  | some _ => sloc = tloc

open Classical in
/-- HOL `evaluate_apply_colour`'s conclusion for one program, colour and live
set: some source permutation oracle either yields `SOME Error`, or the source
and coloured runs agree on the result, satisfy `word_state_eq_rel`, and keep
the live-scoped locals relation `applyColourLocals`. -/
def applyColourPost {width : Nat} [NeZero width] {C F : Type} (f : Nat → Nat)
    (prog : WordLangProgHOL (BitVec width)) (live : NumSet) (lt : List (NumSet × NumSet))
    (st cst : WordSemStateFiniteExact width C F) : Prop :=
  ∃ perm',
    let (res, rst) := evaluate prog { st with permute := perm' }
    if res = some .error then True
    else
      let (res', rcst) := evaluate (applyColour f prog) cst
      res = res' ∧ wordStateEqRel rst rcst ∧ applyColourLocals f live lt res rst.locals rcst.locals

/-- Introduction rule for `applyColourPost` from explicit source and coloured
runs. -/
theorem applyColourPost_intro {width : Nat} [NeZero width] {C F : Type} (f : Nat → Nat)
    (prog : WordLangProgHOL (BitVec width)) (live : NumSet) (lt : List (NumSet × NumSet))
    (st cst : WordSemStateFiniteExact width C F) (perm' : Nat → Nat → Nat)
    (res res' : Option (WordSemResult width)) (rst rcst : WordSemStateFiniteExact width C F)
    (h1 : evaluate prog { st with permute := perm' } = (res, rst))
    (h2 : res ≠ some .error → evaluate (applyColour f prog) cst = (res', rcst) ∧
      res = res' ∧ wordStateEqRel rst rcst ∧
      applyColourLocals f live lt res rst.locals rcst.locals) :
    applyColourPost f prog live lt st cst := by
  classical
  refine ⟨perm', ?_⟩
  rw [h1]
  simp only
  by_cases he : res = some .error
  · rw [if_pos he]; trivial
  · rw [if_neg he]
    obtain ⟨h2, h3⟩ := h2 he
    rw [h2]
    exact h3

/-- `applyColourPost` with the source's own permutation oracle (the HOL
`exists_tac` of the permute-insensitive cases). -/
theorem applyColourPost_self {width : Nat} [NeZero width] {C F : Type} (f : Nat → Nat)
    (prog : WordLangProgHOL (BitVec width)) (live : NumSet) (lt : List (NumSet × NumSet))
    (st cst : WordSemStateFiniteExact width C F)
    (h : (evaluate prog st).1 ≠ some .error →
      (evaluate prog st).1 = (evaluate (applyColour f prog) cst).1 ∧
      wordStateEqRel (evaluate prog st).2 (evaluate (applyColour f prog) cst).2 ∧
      applyColourLocals f live lt (evaluate prog st).1 (evaluate prog st).2.locals
        (evaluate (applyColour f prog) cst).2.locals) :
    applyColourPost f prog live lt st cst :=
  applyColourPost_intro f prog live lt st cst st.permute _ _ _ _ rfl
    (fun he => ⟨rfl, h he⟩)

/-- HOL `evaluate_apply_colour` at one program, universally over the remaining
HOL binders `st cst f live lt` with the three HOL premises. -/
def applyColourGoal {width : Nat} [NeZero width] (C F : Type)
    (prog : WordLangProgHOL (BitVec width)) : Prop :=
  ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
    (lt : List (NumSet × NumSet)),
    colouringOk f prog live lt ∧
      wordStateEqRel st cst ∧
      strongLocalsRel f (sptDomain (getLive prog live lt)) st.locals cst.locals →
    applyColourPost f prog live lt st cst

end Flapjack.WordAlloc
