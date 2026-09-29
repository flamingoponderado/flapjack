import Flapjack.Pancake.CrepToLoop.StateRel
import Flapjack.FfiHOL
import Flapjack.Misc.LprefixLub

/-!
# crep_to_loop `semantics_run_res` over the exact carrier

`cakeml/pancake/proofs/crep_to_loopProofScript.sml:4127-4130` declares a fresh,
polymorphic `semantics_run_res` datatype

```
semantics_run_res = RunError | CompleteResult 'a | Incomplete
```

used by the pass-result wrapper `semantics_wrapper_def` (line 4132) and the
`state_rel_imp_semantics` wrapper.  Its text is identical to
`panPropsScript.sml:1818`'s same-named datatype, but every HOL `Datatype`
command introduces its own type constant, so the two are *distinct* types.  The
`panProps` declaration is ported separately as `SemanticsRunResHOL`
(`Flapjack/Pancake/Semantics/PanProps.lean`); this module ports the
`crep_to_loop` one as the distinct carrier `CrepToLoopSemanticsRunRes`.

Constructor order, arity, and the arbitrary result payload type match HOL
exactly, so no carrier qualifier is required.  Direct Lean constructor
observations are included below.
-/

namespace Flapjack

/-- Exact port of the `crep_to_loopProofScript.sml:4127` datatype
    `semantics_run_res = RunError | CompleteResult 'a | Incomplete`.

    This is a *separate* type constant from the structurally identical
    `panPropsScript.sml:1818` `semantics_run_res` (ported as
    `SemanticsRunResHOL`): matching constructor text does not make them the same
    HOL type.  Constructor names are Lean-qualified by this type only; the
    payload arity and order match HOL. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "semantics_run_res"]
inductive CrepToLoopSemanticsRunRes (α : Type u) where
  | RunError
  | CompleteResult (result : α)
  | Incomplete
  deriving DecidableEq, Repr

/-! Direct Lean constructor observations: the three constructors have HOL's
    nullary / one-payload / nullary arities, and the payload type is arbitrary. -/
example : CrepToLoopSemanticsRunRes Nat := .RunError
example (result : Nat) : CrepToLoopSemanticsRunRes Nat := .CompleteResult result
example : CrepToLoopSemanticsRunRes Nat := .Incomplete


open Classical in
/-- Exact HOL `semantics_wrapper_def` (`crep_to_loopProofScript.sml:4132-4136`):
    `semantics_wrapper f = (if ?k v. f k = (RunError, v) then Fail
       else case some res. ?k r ev. f k = (CompleteResult r, ev) /\ res = Terminate r ev
         of SOME res => res
          | NONE => Diverge (LUB (IMAGE (fromList o SND o f) (UNIV : num set))))`.
    HOL's arbitrary `f : num -> outcome semantics_run_res # io_event list` is kept with
    no chain premise.  `some` is `holOptionSome` (HOL `some P = if ?x. P x then
    SOME (@x. P x) else NONE`, Hilbert choice rendered by `Classical.choose` on the
    same predicate), `LUB` is HOL's overload for `build_lprefix_lub`, rendered by
    the chain-free `HolLList.buildLprefixLub` over HOL's exact `llist` subtype
    `HolLList` (as in the tagged loopSem/crepSem `semantics_def`), and
    `IMAGE g UNIV` is the predicate `fun l => ∃ k, l = g k`.

    Caveat (choice translation): HOL `@` and Lean `Classical.choose` are the standard
    translation of one another, and this definition states the same choice formula
    as HOL.  The value each selects when the predicate has several witnesses is
    unspecified in both logics, and no cross-language equality of those selections
    is proved.  This matters for non-chain event families, where
    `buildLprefixLub`'s per-index choice and `holOptionSome`'s choice among several
    completed runs may pick different witnesses than HOL.  Such equality is outside
    scope (see `docs/SOUNDNESS.md`, "HOL-to-Lean trust boundary"); the tag records a representation port of the
    same formula over the exact `lrep_ok` lazy-list subtype `HolLList`, not an
    extensional agreement on unspecified choices.  On `lprefixChain` families the LUB
    is characterised uniquely by `buildLprefixLub_thm` in both logics. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "semantics_wrapper_def"]
noncomputable def crepToLoopSemanticsWrapper
    (f : Nat → CrepToLoopSemanticsRunRes HolOutcome × List HolIoEvent) : HolBehaviour :=
  if ∃ k v, f k = (.RunError, v) then .fail
  else
    match holOptionSome (fun res => ∃ k r ev,
        f k = (.CompleteResult r, ev) ∧ res = HolBehaviour.terminate r ev) with
    | some res => res
    | none => .diverge (HolLList.buildLprefixLub (fun l => ∃ k, l = HolLList.fromList (f k).2))
end Flapjack
