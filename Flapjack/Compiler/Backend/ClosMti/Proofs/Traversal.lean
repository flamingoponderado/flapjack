module

public import Flapjack.Compiler.Backend.ClosMti
public import Flapjack.Compiler.Backend.ClosLang.Proofs.Budget

@[expose] public section

/-! A generic preservation step for the fuel-bounded multi-argument
introduction traversal.

The traversal recurses over `ClosLang.Exp` and every consumer predicate is
preserved by the same case skeleton: descend into each sub-expression, keep the
induction hypotheses, and rebuild the constructor. This module proves that
skeleton once, parameterised by the relation `R` the caller wants to preserve,
so the per-predicate proofs only supply the constructor rules. It is Flapjack
infrastructure with no HOL original; the HOL script proves each invariant
separately by its own induction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open ClosLang

/-- The per-entry traversal applied to recursive function bundles; this is the
`collected` map used by the `letrec` clause of `introMultiFuel`. Flapjack
infrastructure. -/
def collectEntry (maxApp fuel : Nat) (entry : Nat × Exp) : Option (Nat × Exp) := do
  let (arity, rest) := collectArgs maxApp entry.1 entry.2
  pure (arity, ← introMultiFuel fuel maxApp rest)

/-- One step of `introMultiFuel` preserves a relation `R` that is stable under
each constructor, with `RList`/`RFuns` its list and recursive-bundle forms.
Flapjack infrastructure: the HOL development repeats this induction for every
invariant separately. -/
theorem introMultiFuel_step (fuel maxApp : Nat)
    {R : Exp → Exp → Prop} {RList : List Exp → List Exp → Prop}
    {RFuns : List (Nat × Exp) → List (Nat × Exp) → Prop}
    (hVar : ∀ t n, R (.var t n) (.var t n))
    (hIf : ∀ t c c' y y' z z', R c c' → R y y' → R z z' →
      R (.ifThenElse t c y z) (.ifThenElse t c' y' z'))
    (hLet : ∀ t xs xs' b b', RList xs xs' → R b b' → R (.let t xs b) (.let t xs' b'))
    (hRaise : ∀ t b b', R b b' → R (.raise t b) (.raise t b'))
    (hHandle : ∀ t b b' h h', R b b' → R h h' → R (.handle t b h) (.handle t b' h'))
    (hTick : ∀ t b b', R b b' → R (.tick t b) (.tick t b'))
    (hCall : ∀ t k l xs xs', RList xs xs' → R (.call t k l xs) (.call t k l xs'))
    (hAppSome : ∀ t l b b' xs xs', R b b' → RList xs xs' →
      R (.app t (some l) b xs) (.app t (some l) b' xs'))
    (hAppNone : ∀ t args head argsC headC head' args',
      collectApps maxApp args head = (argsC, headC) → args'.length = argsC.length →
      R headC head' → RList argsC args' → R (.app t none head args) (.app t none head' args'))
    (hFnSomeLoc : ∀ t l v a b b', R b b' → R (.fn t (some l) v a b) (.fn t (some l) v a b'))
    (hFnSomeVars : ∀ t v a b b', R b b' → R (.fn t none (some v) a b) (.fn t none (some v) a b'))
    (hFnNone : ∀ t a b c rest b', collectArgs maxApp a b = (c, rest) → R rest b' →
      R (.fn t none none a b) (.fn t none none c b'))
    (hLetrecNone : ∀ t fs fs' b b', RFuns fs fs' → R b b' →
      R (.letrec t none none fs b) (.letrec t none none fs' b'))
    (hLetrecSomeLoc : ∀ t l v fs b b', R b b' →
      R (.letrec t (some l) v fs b) (.letrec t (some l) v fs b'))
    (hLetrecSomeVars : ∀ t v fs b b', R b b' →
      R (.letrec t none (some v) fs b) (.letrec t none (some v) fs b'))
    (hOp : ∀ t o xs xs', RList xs xs' → R (.op t o xs) (.op t o xs'))
    (hList : ∀ xs ys, xs.mapM (introMultiFuel fuel maxApp) = some ys → RList xs ys)
    (hFuns : ∀ xs ys, xs.mapM (collectEntry maxApp fuel) = some ys → RFuns xs ys)
    (ih : ∀ e r, introMultiFuel fuel maxApp e = some r → R e r)
    (run : introMultiFuel (fuel + 1) maxApp e = some r) : R e r := by
  cases e with
  | var trace index =>
    simp [introMultiFuel] at run
    subst r
    exact hVar trace index
  | raise trace body =>
    cases step : introMultiFuel fuel maxApp body with
    | none => simp [introMultiFuel, step] at run
    | some next =>
      have equal : .raise trace next = r := by simpa [introMultiFuel, step] using run
      subst r
      exact hRaise trace body next (ih body next step)
  | tick trace body =>
    cases step : introMultiFuel fuel maxApp body with
    | none => simp [introMultiFuel, step] at run
    | some next =>
      have equal : .tick trace next = r := by simpa [introMultiFuel, step] using run
      subst r
      exact hTick trace body next (ih body next step)
  | ifThenElse trace condition yes no =>
    cases hc : introMultiFuel fuel maxApp condition with
    | none => simp [introMultiFuel, hc] at run
    | some condition' =>
      cases hy : introMultiFuel fuel maxApp yes with
      | none => simp [introMultiFuel, hc, hy] at run
      | some yes' =>
        cases hn : introMultiFuel fuel maxApp no with
        | none => simp [introMultiFuel, hc, hy, hn] at run
        | some no' =>
          have equal : .ifThenElse trace condition' yes' no' = r := by
            simpa [introMultiFuel, hc, hy, hn] using run
          subst r
          exact hIf trace condition condition' yes yes' no no'
            (ih condition condition' hc) (ih yes yes' hy) (ih no no' hn)
  | handle trace body handler =>
    cases hb : introMultiFuel fuel maxApp body with
    | none => simp [introMultiFuel, hb] at run
    | some body' =>
      cases hh : introMultiFuel fuel maxApp handler with
      | none => simp [introMultiFuel, hb, hh] at run
      | some handler' =>
        have equal : .handle trace body' handler' = r := by
          simpa [introMultiFuel, hb, hh] using run
        subst r
        exact hHandle trace body body' handler handler' (ih body body' hb) (ih handler handler' hh)
  | «let» trace bindings body =>
    cases hs : bindings.mapM (introMultiFuel fuel maxApp) with
    | none => simp [introMultiFuel, hs] at run
    | some bindings' =>
      cases hb : introMultiFuel fuel maxApp body with
      | none => simp [introMultiFuel, hs, hb] at run
      | some body' =>
        have equal : .let trace bindings' body' = r := by simpa [introMultiFuel, hs, hb] using run
        subst r
        exact hLet trace bindings bindings' body body'
          (hList bindings bindings' hs) (ih body body' hb)
  | call trace ticks location args =>
    cases hs : args.mapM (introMultiFuel fuel maxApp) with
    | none => simp [introMultiFuel, hs] at run
    | some args' =>
      have equal : .call trace ticks location args' = r := by simpa [introMultiFuel, hs] using run
      subst r
      exact hCall trace ticks location args args' (hList args args' hs)
  | op trace op args =>
    cases hs : args.mapM (introMultiFuel fuel maxApp) with
    | none => simp [introMultiFuel, hs] at run
    | some args' =>
      have equal : .op trace op args' = r := by simpa [introMultiFuel, hs] using run
      subst r
      exact hOp trace op args args' (hList args args' hs)
  | app trace location head args =>
    cases location with
    | some location =>
      cases hh : introMultiFuel fuel maxApp head with
      | none => simp [introMultiFuel, hh] at run
      | some head' =>
        cases ha : args.mapM (introMultiFuel fuel maxApp) with
        | none => simp [introMultiFuel, hh, ha] at run
        | some args' =>
          have equal : .app trace (some location) head' args' = r := by
            simpa [introMultiFuel, hh, ha] using run
          subst r
          exact hAppSome trace location head head' args args'
            (ih head head' hh) (hList args args' ha)
    | none =>
      cases collected : collectApps maxApp args head with
      | mk collectedArgs collectedHead =>
        cases hh : introMultiFuel fuel maxApp collectedHead with
        | none => simp [introMultiFuel, collected, hh] at run
        | some head' =>
          cases ha : collectedArgs.mapM (introMultiFuel fuel maxApp) with
          | none => simp [introMultiFuel, collected, hh, ha] at run
          | some args' =>
            have equal : .app trace none head' args' = r := by
              simpa [introMultiFuel, collected, hh, ha] using run
            subst r
            exact hAppNone trace args head collectedArgs collectedHead head' args' collected
              (mapM_length collectedArgs (introMultiFuel fuel maxApp) args' ha)
              (ih collectedHead head' hh) (hList collectedArgs args' ha)
  | fn name location vars arity body =>
    cases location with
    | some location =>
      cases hb : introMultiFuel fuel maxApp body with
      | none =>
        cases vars with
        | some vars => simp [introMultiFuel, hb] at run
        | none => simp [introMultiFuel, hb] at run
      | some body' =>
        cases vars with
        | some vars =>
          have equal : .fn name (some location) (some vars) arity body' = r := by
            simpa [introMultiFuel, hb] using run
          subst r
          exact hFnSomeLoc name location (some vars) arity body body' (ih body body' hb)
        | none =>
          have equal : .fn name (some location) none arity body' = r := by
            simpa [introMultiFuel, hb] using run
          subst r
          exact hFnSomeLoc name location none arity body body' (ih body body' hb)
    | none =>
      cases vars with
      | some vars =>
        cases hb : introMultiFuel fuel maxApp body with
        | none => simp [introMultiFuel, hb] at run
        | some body' =>
          have equal : .fn name none (some vars) arity body' = r := by
            simpa [introMultiFuel, hb] using run
          subst r
          exact hFnSomeVars name vars arity body body' (ih body body' hb)
      | none =>
        cases collected : collectArgs maxApp arity body with
        | mk count remaining =>
          cases hb : introMultiFuel fuel maxApp remaining with
          | none => simp [introMultiFuel, collected, hb] at run
          | some body' =>
            have equal : .fn name none none count body' = r := by
              simpa [introMultiFuel, collected, hb] using run
            subst r
            exact hFnNone name arity body count remaining body' collected (ih remaining body' hb)
  | letrec names location vars functions body =>
    cases location with
    | some location =>
      cases vars with
      | some vars =>
        cases hb : introMultiFuel fuel maxApp body with
        | none => simp [introMultiFuel, hb] at run
        | some body' =>
          have equal : .letrec names (some location) (some vars) functions body' = r := by
            simpa [introMultiFuel, hb] using run
          subst r
          exact hLetrecSomeLoc names location (some vars) functions body body' (ih body body' hb)
      | none =>
        cases hb : introMultiFuel fuel maxApp body with
        | none => simp [introMultiFuel, hb] at run
        | some body' =>
          have equal : .letrec names (some location) none functions body' = r := by
            simpa [introMultiFuel, hb] using run
          subst r
          exact hLetrecSomeLoc names location none functions body body' (ih body body' hb)
    | none =>
      cases vars with
      | some vars =>
        cases hb : introMultiFuel fuel maxApp body with
        | none => simp [introMultiFuel, hb] at run
        | some body' =>
          have equal : .letrec names none (some vars) functions body' = r := by
            simpa [introMultiFuel, hb] using run
          subst r
          exact hLetrecSomeVars names vars functions body body' (ih body body' hb)
      | none =>
        change (do
          let fs ← functions.mapM (collectEntry maxApp fuel)
          let b ← introMultiFuel fuel maxApp body
          pure (.letrec names none none fs b)) = some r at run
        cases hf : functions.mapM (collectEntry maxApp fuel) with
        | none => simp [hf] at run
        | some functions' =>
          cases hb : introMultiFuel fuel maxApp body with
          | none => simp [hf, hb] at run
          | some body' =>
            simp [hf, hb] at run
            subst r
            exact hLetrecNone names functions functions' body body'
              (hFuns functions functions' hf) (ih body body' hb)

end Flapjack.Compiler.Backend.ClosMti
