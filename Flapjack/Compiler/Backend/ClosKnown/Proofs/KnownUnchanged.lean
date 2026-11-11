module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.KnownGlobals
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.ApproxGlobalSafety

@[expose] public section

/-! Structural global-tree preservation when there are no writes. -/
namespace Flapjack.Compiler.Backend.ClosKnown.KnownUnchanged
open ClosProps

/-- An operation with an empty write bag leaves the approximation tree
structurally unchanged. This is Flapjack proof infrastructure. -/
private theorem knownOpEmpty (op : ClosLang.Op) (args : List ValApprox) (g0 : Spt ValApprox)
    (a : ValApprox) (g : Spt ValApprox) (run : knownOpHOL op args g0 = (a, g))
    (empty : opGlobalBag op = FlatProps.emptyGlobalBag) : g = g0 := by
  have noWrite : ∀ index, op ≠ .globOp (.setGlobal index) := by
    intro index same
    subst op
    have zero := congrFun empty index
    simp [opGlobalBag, FlatProps.emptyGlobalBag, Flapjack.emptyBag] at zero
  unfold knownOpHOL at run
  split at run <;> simp_all
  all_goals split at run <;> simp_all

/-- A write-free expression leaves the complete approximation tree unchanged.
This is Flapjack induction infrastructure. -/
theorem knownExprTotalEmpty (c : Config) (e : ClosLang.Exp) (env : List ValApprox) (g : Spt ValApprox) :
    setGlobals e = FlatProps.emptyGlobalBag → (knownExprTotal c e env g).2.2 = g := by
  induction c, e, env, g using knownExprTotal.induct
    (motive2 := fun _ _ _ _ _ => True)
    (motive3 := fun c xs env g => elistGlobals xs = FlatProps.emptyGlobalBag →
      (knownListTotal c xs env g).2 = g) <;>
    simp_all [knownExprTotal, knownListTotal, setGlobals, elistGlobals, FlatProps.unionGlobalBag_eq_empty]
  case case8 =>
    intro opEmpty argsEmpty
    rename_i c env g0 t op xs out mid h a final opRun ih
    have midEq := ih argsEmpty
    subst mid
    have r := congrArg Prod.snd opRun
    simp only at r
    exact r.trans (knownOpEmpty op (out.map Prod.snd).reverse g0 a final opRun opEmpty)
  all_goals try (intros; simp_all)
  all_goals try (split <;> simp_all)
  all_goals try (rw [knownExprTotal.eq_def]; simp_all)
  all_goals grind

/-- A write-free list leaves the complete approximation tree unchanged.
This is Flapjack induction infrastructure. -/
theorem knownListTotalEmpty (c : Config) (xs : List ClosLang.Exp) (env : List ValApprox)
    (g : Spt ValApprox) (empty : elistGlobals xs = FlatProps.emptyGlobalBag) :
    (knownListTotal c xs env g).2 = g := by
  have h := knownExprTotalEmpty c (.call BackendCommon.orphanTrace 0 0 xs) env g
    (by simpa [setGlobals] using empty)
  simpa [knownExprTotal] using h

/-- A known traversal of a program with no global writes leaves the original
approximation tree exactly unchanged. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_unchanged_globals"]
theorem knownUnchangedGlobals (c : Config) (xs : List ClosLang.Exp) (env : List ValApprox)
    (g0 : Spt ValApprox) (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (h : knownListTotal c xs env g0 = (eas, g) ∧ elistGlobals xs = FlatProps.emptyGlobalBag) :
    g0 = g := by
  have result := knownListTotalEmpty c xs env g0 h.2
  rw [h.1] at result
  exact result.symm

/-- An inlineable safe closure body leaves the incoming approximation tree
unchanged. This is Flapjack infrastructure for the application case. -/
theorem inlineBodyGlobalsUnchanged (c : Config) (approx : ValApprox) (loc : Option Nat)
    (arity : Nat) (body : ClosLang.Exp) (env : List ValApprox) (g : Spt ValApprox)
    (eas : List (ClosLang.Exp × ValApprox)) (after : Spt ValApprox)
    (safe : valApproxSgcFree approx)
    (decision : decideInlineHOL c approx loc arity = .letInline body)
    (run : knownListTotal (decInlineFactor c) [body] env g = (eas, after)) : g = after := by
  obtain ⟨n, size, eq⟩ := decideInlineLetInlineImpClos c approx loc arity body decision
  have emptyBody : setGlobals body = FlatProps.emptyGlobalBag := by
    simpa [eq, valApproxSgcFree] using safe
  apply knownUnchangedGlobals (decInlineFactor c) [body] env g eas after
  refine ⟨run, ?_⟩
  funext i
  simp [elistGlobals, FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, emptyBody, Flapjack.bagUnion, Flapjack.emptyBag]

end Flapjack.Compiler.Backend.ClosKnown.KnownUnchanged
