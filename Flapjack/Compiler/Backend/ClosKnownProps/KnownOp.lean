module

public import Flapjack.Compiler.Backend.ClosKnown.KnownOp
public import Flapjack.Compiler.Backend.ClosKnown.Total
public import Flapjack.Compiler.Backend.ClosKnownProps.Merge

@[expose] public section

/-! Global approximation ordering for the known-operation pass. -/
namespace Flapjack.Compiler.Backend.ClosKnownProps
open ClosKnown ClosLang

private theorem betterDefinedGInsert (key : Nat) (value : ValApprox) (tree : Spt ValApprox) :
    betterDefinedG tree
      (sptInsert key (match sptLookup key tree with
        | none => value
        | some old => mergeHOL old value) tree) := by
  intro k member
  obtain ⟨old, lookup⟩ := (sptMem_iff_lookup k tree).1 member
  by_cases same : k = key
  · subst k
    simp only [lookup]
    have newLookup := sptLookup_sptInsert_same key (mergeHOL old value) tree
    constructor
    · exact (sptMem_iff_lookup key _).2 ⟨_, newLookup⟩
    · simp only [newLookup, Flapjack.holThe]
      exact (subapproxMerge old value).1
  · have newLookup := sptLookup_sptInsert_ne key k
      (match sptLookup key tree with | none => value | some old => mergeHOL old value) tree same
    constructor
    · exact (sptMem_iff_lookup k _).2 ⟨old, newLookup.trans lookup⟩
    · rw [newLookup]
      exact subapproxRefl _

/-- The known-operation pass never makes its global approximation less defined. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownPropsScript.sml" "known_op_better_definedg"]
theorem knownOpBetterDefinedG (op : Op) (apxs : List ValApprox)
    (g0 : Spt ValApprox) (a : ValApprox) (g : Spt ValApprox)
    (run : knownOpHOL op apxs g0 = (a, g)) : betterDefinedG g0 g := by
  unfold knownOpHOL at run
  repeat' first | split at run | simp_all [betterDefinedGRefl]
  case h_1 =>
    obtain ⟨_, rfl⟩ := run
    rename_i op args key value tail x lookup left
    simpa only [lookup] using betterDefinedGInsert key value g0
  case h_2 =>
    obtain ⟨_, rfl⟩ := run
    rename_i op args key value tail x old lookup left
    simpa only [lookup] using betterDefinedGInsert key value g0

private theorem knownExprBetterDefinedG (c : Config) (e : Exp)
    (env : List ValApprox) (globals : Spt ValApprox) :
    betterDefinedG globals (knownExprTotal c e env globals).2.2 := by
  induction c, e, env, globals using knownExprTotal.induct
    (motive2 := fun _ _ _ _ _ => True)
    (motive3 := fun c xs env globals =>
      betterDefinedG globals (knownListTotal c xs env globals).2) <;>
    simp_all [knownExprTotal, knownListTotal, betterDefinedGRefl]
  all_goals try (split <;> simp_all)
  all_goals try (rw [knownExprTotal.eq_def]; simp_all)
  all_goals grind [betterDefinedGTrans, knownOpBetterDefinedG]

/-- Traversing any list of expressions only improves the global approximation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownPropsScript.sml" "known_better_definedg"]
theorem knownBetterDefinedG (c : Config) (es : List Exp) (apxs : List ValApprox)
    (g0 : Spt ValApprox) (alist : List (Exp × ValApprox)) (g : Spt ValApprox)
    (run : knownListTotal c es apxs g0 = (alist, g)) : betterDefinedG g0 g := by
  have h := knownExprBetterDefinedG c (.call BackendCommon.orphanTrace 0 0 es) apxs g0
  simpa [knownExprTotal, run] using h

end Flapjack.Compiler.Backend.ClosKnownProps
