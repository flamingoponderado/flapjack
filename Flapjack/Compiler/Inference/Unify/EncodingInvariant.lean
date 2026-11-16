module

public import Flapjack.Compiler.Inference.Unify.Unification
public import Flapjack.Compiler.Inference.Unify.Walkstar

@[expose] public section

/-! Full encoding invariant for the proof-side inference unifier. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

private theorem encodeSubstUpdate (s : HolFiniteMapExact Nat InferT) (v : Nat) (t : InferT) :
    encodeSubst (s.updateEq (v, t)) = (encodeSubst s).updateEq (v, encodeInferT t) := by
  apply HolFiniteMapExact.ext_lookup
  intro k
  simp only [encodeSubst, HolFiniteMapExact.lookup_map2]
  by_cases h : k = v <;> simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, h]

private theorem encodedUpdateRoundtrip (s : HolFiniteMapExact Nat InferT) (v : Nat) (t : InferT) :
    encodeSubst (decodeSubst ((encodeSubst s).updateEq (v, encodeInferT t))) =
      (encodeSubst s).updateEq (v, encodeInferT t) := by
  rw [← encodeSubstUpdate, decodeEncodeSubst]

private theorem appModel (s : HolFiniteMapExact Nat InferT) (hw : tWfs s)
    (xs ys : List InferT) (tag : Nat) :
    tUnifyModel s (.app xs tag) (.app ys tag) =
      (tunifyAux (encodeSubst s) (encodeInferTs xs) (encodeInferTs ys)).map decodeSubst := by
  have hws : wfs (encodeSubst s) := hw
  unfold tUnifyModel
  rw [specifiedUnifyEqAux _ _ _ hws]
  simp only [encodeInferT]
  rw [tunifyAuxEquation _ _ _ hws]
  simp only [walk, tunifyAuxSelf _ _ hws, Option.bind]
  rw [tunifyAuxEquation _ _ _ hws]
  simp only [walk, tunifyAuxSelf _ _ hws, Option.bind]

/-- The four source argument shapes, with a shared arbitrary application tag. -/
def EncodeUnifyShapes (tag : Nat) (t1 t2 : Term Atom) (u1 u2 : InferT) : Prop :=
  (t1 = encodeInferT u1 ∧ t2 = encodeInferT u2) ∨
  (∃ c, t1 = .const c ∧ t2 = .const c ∧ u1 = u2) ∨
  (∃ c xs ys, t1 = .pair (.const c) (encodeInferTs xs) ∧
    t2 = .pair (.const c) (encodeInferTs ys) ∧
    u1 = .app xs tag ∧ u2 = .app ys tag) ∨
  (∃ xs ys, t1 = encodeInferTs xs ∧ t2 = encodeInferTs ys ∧
    u1 = .app xs tag ∧ u2 = .app ys tag)

/-- Full four-shape encoding invariant for the proof-side unifier, including
    both failure and successful substitutions. This is not yet tagged as the
    HOL theorem: correspondence with HOL's specified unifier and the optional
    finite-map representation remain to be established. -/
theorem encodeUnifyModelAll (tag : Nat) :
    ∀ (s : HolFiniteMapExact Nat (Term Atom)) (t1 t2 : Term Atom)
      (s' : HolFiniteMapExact Nat InferT) (u1 u2 : InferT),
      s = encodeSubst s' ∧ EncodeUnifyShapes tag t1 t2 u1 u2 ∧ tWfs s' →
      tunifyAux s t1 t2 = (tUnifyModel s' u1 u2).map encodeSubst := by
  intro s t1 t2
  induction s, t1, t2 using tunifyAuxInd with
  | step s t1 t2 ih =>
    intro s' u1 u2 hs
    rcases hs with ⟨rfl, shapes, hw⟩
    have hws : wfs (encodeSubst s') := hw
    rcases shapes with full | constant | tagged | lists
    · rcases full with ⟨rfl, rfl⟩
      cases hh : tunifyAux (encodeSubst s') (encodeInferT u1) (encodeInferT u2) with
      | none => simp [tUnifyModel, specifiedUnifyEqAux _ _ _ hws, hh]
      | some mid =>
        suffices himage : encodeSubst (decodeSubst mid) = mid by
          simp [tUnifyModel, specifiedUnifyEqAux _ _ _ hws, hh, himage]
        have equation := tunifyAuxEquation (encodeSubst s') (encodeInferT u1) (encodeInferT u2) hws
        rw [hh] at equation
        have ew1 : walk (encodeSubst s') (encodeInferT u1) = encodeInferT (tWalk s' u1) :=
          encodeWalk s' hw u1
        have ew2 : walk (encodeSubst s') (encodeInferT u2) = encodeInferT (tWalk s' u2) :=
          encodeWalk s' hw u2
        rw [ew1, ew2] at equation
        cases a : tWalk s' u1 <;> cases b : tWalk s' u2 <;>
          simp only [a, b, encodeInferT] at equation
        case varDb.varDb =>
          split at equation
          · simp only [Option.some.injEq] at equation
            rw [equation, decodeEncodeSubst]
          · contradiction
        case varDb.app | app.varDb => contradiction
        case varDb.uvar =>
          rename_i db v
          split at equation
          · contradiction
          · simp only [Option.some.injEq] at equation
            rw [equation]
            simpa only [encodeInferT] using encodedUpdateRoundtrip s' v (.varDb db)
        case uvar.varDb =>
          rename_i v db
          split at equation
          · contradiction
          · simp only [Option.some.injEq] at equation
            rw [equation]
            simpa only [encodeInferT] using encodedUpdateRoundtrip s' v (.varDb db)
        case app.uvar =>
          rename_i xs tc v
          split at equation
          · contradiction
          · simp only [Option.some.injEq] at equation
            rw [equation]
            simpa only [encodeInferT] using encodedUpdateRoundtrip s' v (.app xs tc)
        case uvar.app =>
          rename_i v xs tc
          split at equation
          · contradiction
          · simp only [Option.some.injEq] at equation
            rw [equation]
            simpa only [encodeInferT] using encodedUpdateRoundtrip s' v (.app xs tc)
        case uvar.uvar =>
          rename_i v1 v2
          simp only [Option.some.injEq] at equation
          split at equation
          · rw [equation, decodeEncodeSubst]
          · rw [equation]
            simpa only [encodeInferT] using encodedUpdateRoundtrip s' v1 (.uvar v2)
        case app.app =>
          rename_i xs tc1 ys tc2
          have hleft : walk (encodeSubst s') (encodeInferT u1) =
              .pair (.const .tappTag) (.pair (.const (.tcTag tc1)) (encodeInferTs xs)) := by
            rw [ew1, a, encodeInferT]
          have hright : walk (encodeSubst s') (encodeInferT u2) =
              .pair (.const .tappTag) (.pair (.const (.tcTag tc2)) (encodeInferTs ys)) := by
            rw [ew2, b, encodeInferT]
          have head := tunifyAuxSelf (encodeSubst s') (.const .tappTag) hws
          simp only [head, Option.bind] at equation
          have pairResult := equation.symm
          have second := tunifyAuxEquation (encodeSubst s')
            (.pair (.const (.tcTag tc1)) (encodeInferTs xs))
            (.pair (.const (.tcTag tc2)) (encodeInferTs ys)) hws
          rw [second] at equation
          simp only [walk] at equation
          have constEq := tunifyAuxEquation (encodeSubst s') (.const (.tcTag tc1))
            (.const (.tcTag tc2)) hws
          simp only [walk] at constEq
          rw [constEq] at equation
          by_cases same : tc1 = tc2
          · subst tc2
            have tailEq := ih.1 (.const .tappTag)
              (.pair (.const (.tcTag tc1)) (encodeInferTs xs))
              (.const .tappTag) (.pair (.const (.tcTag tc1)) (encodeInferTs ys))
              (encodeSubst s') ⟨hws, hleft, hright, head⟩ s'
              (.app xs tag) (.app ys tag)
              ⟨rfl, Or.inr (Or.inr (Or.inl ⟨.tcTag tc1, xs, ys, rfl, rfl, rfl, rfl⟩)), hw⟩
            rw [appModel s' hw xs ys tag] at tailEq
            rw [pairResult] at tailEq
            simp only [↓reduceIte, Option.bind] at equation
            cases hout : tunifyAux (encodeSubst s') (encodeInferTs xs) (encodeInferTs ys) with
            | none => simp [hout] at equation
            | some result =>
              have resultEq : mid = result := by simpa [hout] using equation
              rw [hout] at tailEq
              simp only [Option.map_some, Option.some.injEq] at tailEq
              rw [resultEq] at tailEq
              rw [resultEq]
              exact tailEq.symm
          · simp [same] at equation
    · rcases constant with ⟨c, rfl, rfl, rfl⟩
      have left := tunifyAuxSelf (encodeSubst s') (.const c) hws
      have right := tunifyAuxSelf (encodeSubst s') (encodeInferT u1) hws
      simp [left, tUnifyModel, specifiedUnifyEqAux _ _ _ hws, right, decodeEncodeSubst]
    · rcases tagged with ⟨c, xs, ys, rfl, rfl, rfl, rfl⟩
      have wh : walk (encodeSubst s') (.pair (.const c) (encodeInferTs xs)) =
          .pair (.const c) (encodeInferTs xs) := by simp [walk]
      have wt : walk (encodeSubst s') (.pair (.const c) (encodeInferTs ys)) =
          .pair (.const c) (encodeInferTs ys) := by simp [walk]
      have head := tunifyAuxSelf (encodeSubst s') (.const c) hws
      have tailEq := ih.1 (.const c) (encodeInferTs xs) (.const c) (encodeInferTs ys)
        (encodeSubst s') ⟨hws, wh, wt, head⟩ s' (.app xs tag) (.app ys tag)
        ⟨rfl, Or.inr (Or.inr (Or.inr ⟨xs, ys, rfl, rfl, rfl, rfl⟩)), hw⟩
      rw [tunifyAuxEquation _ _ _ hws]
      simpa [walk, head] using tailEq
    · rcases lists with ⟨xs, ys, rfl, rfl, rfl, rfl⟩
      rw [appModel s' hw xs ys tag]
      cases xs with
      | nil =>
        cases ys with
        | nil => simp [encodeInferTs, tunifyAuxSelf _ _ hws, decodeEncodeSubst]
        | cons y ys =>
          rw [tunifyAuxEquation _ _ _ hws]
          simp [encodeInferTs, walk]
      | cons x xs =>
        cases ys with
        | nil =>
          rw [tunifyAuxEquation _ _ _ hws]
          simp [encodeInferTs, walk]
        | cons y ys =>
          simp only [encodeInferTs]
          rw [tunifyAuxEquation _ _ _ hws]
          simp only [walk]
          have wh : walk (encodeSubst s') (encodeInferTs (x :: xs)) =
              .pair (encodeInferT x) (encodeInferTs xs) := by simp [encodeInferTs, walk]
          have wt : walk (encodeSubst s') (encodeInferTs (y :: ys)) =
              .pair (encodeInferT y) (encodeInferTs ys) := by simp [encodeInferTs, walk]
          have headEq := ih.2 (encodeInferT x) (encodeInferTs xs)
            (encodeInferT y) (encodeInferTs ys) ⟨hws, wh, wt⟩ s' x y
            ⟨rfl, Or.inl ⟨rfl, rfl⟩, hw⟩
          cases hh : tunifyAux (encodeSubst s') (encodeInferT x) (encodeInferT y) with
          | none => simp
          | some mid =>
            cases hm : tUnifyModel s' x y with
            | none => simp [hh, hm] at headEq
            | some ds =>
              have midEq : mid = encodeSubst ds := by simpa [hh, hm] using headEq
              have hwmid := (tunifyAuxUP _ _ _ _ ⟨hws, hh⟩).1
              have hwds : tWfs ds := by
                change wfs (encodeSubst ds)
                rw [← midEq]
                exact hwmid
              have tailEq := ih.1 (encodeInferT x) (encodeInferTs xs)
                (encodeInferT y) (encodeInferTs ys) mid ⟨hws, wh, wt, hh⟩
                ds (.app xs tag) (.app ys tag)
                ⟨midEq, Or.inr (Or.inr (Or.inr ⟨xs, ys, rfl, rfl, rfl, rfl⟩)), hwds⟩
              cases ht : tunifyAux mid (encodeInferTs xs) (encodeInferTs ys) with
              | none => simp [ht]
              | some result =>
                cases hmt : tUnifyModel ds (.app xs tag) (.app ys tag) with
                | none => simp [ht, hmt] at tailEq
                | some ds2 =>
                  have resultEq : result = encodeSubst ds2 := by simpa [ht, hmt] using tailEq
                  simp [ht, resultEq, decodeEncodeSubst]

end Flapjack.Compiler.Inference.Unify
