module

public import Flapjack.Compiler.Inference.TypeDCanon.EnvironmentInverse
public import Flapjack.Compiler.Inference.TypeDCanon.Expression

@[expose] public section

/-! Determinacy of source bindings under canonical renaming. -/
namespace Flapjack.Compiler.Inference.TypeDCanon
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.AstHOL Flapjack.TypeSystemHOL
  Flapjack.Compiler.Inference.InferProps Flapjack.Compiler.Inference.TypeDCanon

/-- Flapjack list infrastructure for the source proof: inverse-renamed bounded
bindings reflect equality using the complete cross-type injectivity theorem. -/
private theorem mapBindingsReflect (g : Nat → Nat) (n : Nat)
    (injective : ∀ a b, a < n → b < n → g a = g b → a = b)
    (xs ys : List (MlString × SemanticT))
    (xbound : ∀ entry ∈ xs, setTidsSubset (fun id => id < n) entry.2)
    (ybound : ∀ entry ∈ ys, setTidsSubset (fun id => id < n) entry.2)
    (eq : xs.map (fun entry => (entry.1, tsTidRename g entry.2)) =
      ys.map (fun entry => (entry.1, tsTidRename g entry.2))) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at eq
    | cons y ys =>
      rcases x with ⟨xn, xt⟩
      rcases y with ⟨yn, yt⟩
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at eq
      have ht : xt = yt := injTsTidRenameEq g xt yt ⟨by
        intro a b cond
        have ha := xbound (xn, xt) (by simp) a cond.1
        have hb := ybound (yn, yt) (by simp) b cond.2.1
        exact injective a b ha hb cond.2.2, eq.1.2⟩
      have rest : xs = ys := ih ys (by
        intro entry member
        exact xbound entry (by simp [member])) (by
        intro entry member
        exact ybound entry (by simp [member])) eq.2
      simp [eq.1.1, ht, rest]

/-- A bounded bijection transports source determinacy to canonical determinacy. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "type_pe_determ_remap"]
theorem typePeDetermRemap (env : TypeEnv) (p : Pat) (e : Flapjack.AstHOL.Exp) (f : Nat → Nat)
    (tids : Set Nat) (n : Nat) :
    typePeDeterm env .empty p e ∧ goodRemap f ∧ primTids true tids ∧
      Set.BijOn f tids (fun id => id < n) ∧ setTidsTenv tids env →
    typePeDetermCanon n (remapTenv f env) .empty p e := by
  rintro ⟨determ, good, prim, bij, envBound⟩
  intro t1 bs1 t2 bs2 ⟨p1, e1, bound1, p2, e2, bound2⟩
  let inv := holLinv f tids
  have goodInv : goodRemap inv := goodRemapBij f tids (fun id => id < n) ⟨good, prim, bij⟩
  have equiv := remapTenvLinv f tids (fun id => id < n) env ⟨bij, envBound⟩
  have p1r := (typePTsTidRename inv goodInv).1 0 (remapTenv f env) p t1 bs1 p1
  have p2r := (typePTsTidRename inv goodInv).1 0 (remapTenv f env) p t2 bs2 p2
  have e1r := (typeETsTidRename inv goodInv).1 (remapTenv f env) .empty e t1 e1
  have e2r := (typeETsTidRename inv goodInv).1 (remapTenv f env) .empty e t2 e2
  simp only [remapTenvE] at e1r e2r
  have p1o := typePTenvEquiv.1 0 _ p _ _ p1r env equiv
  have p2o := typePTenvEquiv.1 0 _ p _ _ p2r env equiv
  have e1o := typeETenvEquiv.1 _ .empty e _ e1r env equiv
  have e2o := typeETenvEquiv.1 _ .empty e _ e2r env equiv
  have mapped := determ (tsTidRename inv t1) (bs1.map (fun entry => (entry.1, tsTidRename inv entry.2)))
    (tsTidRename inv t2) (bs2.map (fun entry => (entry.1, tsTidRename inv entry.2))) ⟨p1o, e1o, p2o, e2o⟩
  have hinj : holInj f tids (fun id => id < n) :=
    ⟨fun _ hx => bij.1 hx, fun _ _ h eq => bij.2.1 h.1 h.2 eq⟩
  have rightInv : ∀ y, y < n → f (inv y) = y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := bij.2.2 hy
    change f (holLinv f tids (f x)) = f x
    rw [holLinvDef f tids (fun id => id < n) hinj x hx]
  have inverseInjective : ∀ a b, a < n → b < n → inv a = inv b → a = b := by
    intro a b ha hb equal
    calc
      a = f (inv a) := (rightInv a ha).symm
      _ = f (inv b) := congrArg f equal
      _ = b := rightInv b hb
  exact mapBindingsReflect inv n inverseInjective bs1 bs2 bound1 bound2 mapped

end Flapjack.Compiler.Inference.TypeDCanon
