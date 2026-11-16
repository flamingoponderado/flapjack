module

public import Flapjack.Compiler.Inference.Unify.Unification.Soundness
public import Flapjack.Compiler.Inference.Unify.Extension

@[expose] public section

/-! The proof-side list and type unification equations. -/

namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

/-- List unification using the proof-side type unifier; HOL correspondence
    and the optional finite-map representation remain to be established. -/
noncomputable def tsUnifyModel (s : HolFiniteMapExact Nat InferT) :
    List InferT → List InferT → Option (HolFiniteMapExact Nat InferT)
  | [], [] => some s
  | x :: xs, y :: ys => (tUnifyModel s x y).bind (fun sx => tsUnifyModel sx xs ys)
  | _, _ => none

/-- Encoding a pair of type lists agrees with sequential inference unification
    on well-formed substitutions. This is proof-model infrastructure for the
    local HOL list correspondence, not yet a tagged port. -/
theorem tsUnifyModelEncoding (xs ys : List InferT) (s : HolFiniteMapExact Nat InferT)
    (hw : tWfs s) :
    (tunifyAux (encodeSubst s) (encodeInferTs xs) (encodeInferTs ys)).map decodeSubst =
      tsUnifyModel s xs ys := by
  induction xs generalizing ys s with
  | nil =>
    have hws : wfs (encodeSubst s) := hw
    cases ys with
    | nil =>
      simp [encodeInferTs, tunifyAuxSelf _ _ hws, decodeEncodeSubst, tsUnifyModel]
    | cons y ys =>
      rw [tunifyAuxEquation _ _ _ hws]
      simp [encodeInferTs, walk, tsUnifyModel]
  | cons x xs ih =>
    have hws : wfs (encodeSubst s) := hw
    cases ys with
    | nil =>
      rw [tunifyAuxEquation _ _ _ hws]
      simp [encodeInferTs, walk, tsUnifyModel]
    | cons y ys =>
      rw [tunifyAuxEquation _ _ _ hws]
      simp only [encodeInferTs, walk, tsUnifyModel]
      have headEq := encodeUnifyModelAll 0 (encodeSubst s) (encodeInferT x) (encodeInferT y)
        s x y ⟨rfl, Or.inl ⟨rfl, rfl⟩, hw⟩
      cases head : tUnifyModel s x y with
      | none =>
        simp [head] at headEq
        simp [headEq]
      | some mid =>
        have headEncoded : tunifyAux (encodeSubst s) (encodeInferT x) (encodeInferT y) =
            some (encodeSubst mid) := by simpa [head] using headEq
        have hmid := (tUnifyModelSound s x y mid ⟨hw, head⟩).1
        simp only [headEncoded, Option.bind]
        exact ih ys mid hmid

/-- The complete type-unification equation for the selected proof model.
    It remains untagged until its first-order unifier is related to HOL's
    specified unifier and its optional finite-map representation is reviewed. -/
theorem tUnifyModelEquation (s : HolFiniteMapExact Nat InferT) (u1 u2 : InferT)
    (hw : tWfs s) : tUnifyModel s u1 u2 = by
      classical
      exact match tWalk s u1, tWalk s u2 with
      | .uvar v1, .uvar v2 => some (if v1 = v2 then s else s.updateEq (v1, .uvar v2))
      | .uvar v, other => tExtSCheck s v other
      | other, .uvar v => tExtSCheck s v other
      | .app xs tc1, .app ys tc2 => if tc1 = tc2 then tsUnifyModel s xs ys else none
      | .varDb x, .varDb y => if x = y then some s else none
      | _, _ => none := by
  classical
  have hws : wfs (encodeSubst s) := hw
  unfold tUnifyModel
  rw [specifiedUnifyEqAux _ _ _ hws]
  rw [tunifyAuxEquation _ _ _ hws]
  have ew1 : walk (encodeSubst s) (encodeInferT u1) = encodeInferT (tWalk s u1) :=
    encodeWalk s hw u1
  have ew2 : walk (encodeSubst s) (encodeInferT u2) = encodeInferT (tWalk s u2) :=
    encodeWalk s hw u2
  rw [ew1, ew2]
  cases a : tWalk s u1 <;> cases b : tWalk s u2 <;>
    simp only [encodeInferT]
  case varDb.varDb =>
    rename_i x y
    simp [Atom.dbTag.injEq, decodeEncodeSubst]
  case varDb.app | app.varDb => rfl
  case varDb.uvar | app.uvar | uvar.varDb | uvar.app =>
    simp only [tExtSCheck, encodeSubst, encodeInferT]
    split <;> simp_all [decodeSubst]
  case uvar.uvar =>
    rename_i v1 v2
    split
    · simp [decodeEncodeSubst]
    · simpa only [Option.map_some, encodeInferT, Option.some.injEq, encodeSubst, decodeSubst] using
        decodeEncodeUpdate s v1 (.uvar v2)
  case app.app =>
    rename_i xs tc1 ys tc2
    simp only [tunifyAuxSelf _ _ hws, Option.bind]
    rw [tunifyAuxEquation _ _ _ hws]
    simp only [walk]
    rw [tunifyAuxEquation _ _ _ hws]
    simp only [walk, Atom.tcTag.injEq]
    split
    · simp only [Option.bind]
      exact tsUnifyModelEncoding xs ys s hw
    · rfl

end Flapjack.Compiler.Inference.Unify
