module

public import Flapjack.Compiler.Inference.Unify.Walkstar.WorklistWellFounded
public import Flapjack.Compiler.Inference.Unify.ComputationalWalk.Order
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! The normalization worklist step decreases in the source order. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

/-- Source step using the selected total variable walker. It is untagged
    because HOL does not determine the same choice on diverging inputs. -/
noncomputable def starWorklistCodeModel (s : Spt InferT) :
    Bool × List InferT × List KclKont → Sum (Bool × List InferT × List KclKont) (List InferT)
  | (true, items, []) => .inr items
  | (true, items, .db n :: rest) => .inl (true, .varDb n :: items, rest)
  | (true, items, .app args n :: rest) => .inl (true, .app args n :: items, rest)
  | (true, items, .uv n :: rest) => .inl (true, .uvar n :: items, rest)
  | (true, items, .cons args n :: rest) => .inl (false, args, .app items n :: rest)
  | (false, [], kont) => .inl (true, [], kont)
  | (false, .varDb n :: items, kont) => .inl (false, items, .db n :: kont)
  | (false, .app args n :: items, kont) => .inl (false, args, .cons items n :: kont)
  | (false, .uvar v :: items, kont) =>
    match tcvwalkModel s v with
    | .varDb n => .inl (false, items, .db n :: kont)
    | .app args n => .inl (false, args, .cons items n :: kont)
    | .uvar n => .inl (false, items, .uv n :: kont)

@[hol "cakeml/compiler/inference/unifyScript.sml" "kcwalkstarwl_preserves_precond"]
theorem kcwalkstarwlPreservesPrecondModel (s : Spt InferT) : ∀ x y,
    (fun _ : Bool × List InferT × List KclKont => cwfs s) x ∧
      starWorklistCodeModel s x = .inl y →
    (fun _ : Bool × List InferT × List KclKont => cwfs s) y := by
  intro x y h
  exact h.1

private theorem removedHead (subst : HolFiniteMapExact Nat (Term Atom))
    (head : InferT) (tail : List InferT) (kont : List KclKont) :
    Relation.TransGen (bagMultisetStep (fun a b => walkstarR subst (encodeInferT a) (encodeInferT b)))
      (bagUnion (bagOfList tail) (starKwork kont))
      (bagUnion (bagOfList (head :: tail)) (starKwork kont)) := by
  have finite : finiteBag (bagUnion (bagOfList tail) (starKwork kont)) :=
    finiteBagUnion _ (finiteBagOfList tail) _ (finiteStarKwork kont)
  apply Relation.TransGen.single
  rw [show bagOfList (head :: tail) = bagInsert head (bagOfList tail) from rfl,
    (bagUnionInsert head _ _).1]
  exact mlt1BagInsert _ _ _ finite

private theorem expandedHead (subst : HolFiniteMapExact Nat (Term Atom))
    (head : InferT) (args tail : List InferT) (kont : List KclKont)
    (smaller : ∀ a ∈ args, walkstarR subst (encodeInferT a) (encodeInferT head)) :
    Relation.TransGen (bagMultisetStep (fun a b => walkstarR subst (encodeInferT a) (encodeInferT b)))
      (bagUnion (bagOfList args) (bagUnion (bagOfList tail) (starKwork kont)))
      (bagUnion (bagOfList (head :: tail)) (starKwork kont)) := by
  apply Relation.TransGen.single
  have hf : finiteBag (bagUnion (bagOfList tail) (starKwork kont)) :=
    finiteBagUnion _ (finiteBagOfList tail) _ (finiteStarKwork kont)
  refine ⟨finiteBagUnion _ (finiteBagOfList args) _ hf,
    finiteBagUnion _ (finiteBagOfList (head :: tail)) _ (finiteStarKwork kont),
    head, bagOfList args, bagUnion (bagOfList tail) (starKwork kont), rfl, ?_, ?_⟩
  · classical
    funext x
    by_cases hx : x = head <;> simp [bagOfList, bagUnion, bagInsert, emptyBag, hx,
      Nat.add_comm, Nat.add_left_comm]
  · intro a ha
    exact smaller a ((bagInBagOfList a args).mp ha)

/-- Complete source-shaped decrease result for every normalization step.
    The selected walker is used under the original well-formedness guard. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "kcwalkstarwl_ensures_decrease"
  (fmap_as_finite_support_result_observations := [Flapjack.HOL.Transfer.Fmsp.sp2fm])]
theorem kcwalkstarwlEnsuresDecreaseModel (s : Spt InferT) : ∀ x y,
    (fun _ : Bool × List InferT × List KclKont => cwfs s) x ∧
      starWorklistCodeModel s x = .inl y →
    starWorklistOrder ((sp2fm s).map2 (fun p => encodeInferT p.2)) y x := by
  rintro ⟨ready, items, kont⟩ y ⟨hw, step⟩
  cases ready with
  | true =>
    cases kont with
    | nil => simp [starWorklistCodeModel] at step
    | cons frame rest =>
      cases frame with
      | db n =>
        simp [starWorklistCodeModel] at step
        subst y
        simp [starWorklistOrder, starWorkbag, starKwork]
      | app args n =>
        simp [starWorklistCodeModel] at step
        subst y
        simp [starWorklistOrder, starWorkbag, starKwork]
      | uv n =>
        simp [starWorklistCodeModel] at step
        subst y
        simp [starWorklistOrder, starWorkbag, starKwork]
      | cons args n =>
        simp [starWorklistCodeModel] at step
        subst y
        simp [starWorklistOrder, starWorkbag, starKwork, List.filter, isConsK]
  | false =>
    cases items with
    | nil =>
      simp [starWorklistCodeModel] at step
      subst y
      simp [starWorklistOrder, starWorkbag, bagOfList, bagUnion_empty_left]
    | cons head tail =>
      cases head with
      | varDb n =>
        simp [starWorklistCodeModel] at step
        subst y
        exact Or.inl (removedHead _ _ tail kont)
      | app args n =>
        simp [starWorklistCodeModel] at step
        subst y
        apply Or.inl
        apply expandedHead
        intro a ha
        apply subtermWalkstarR
        rw [encodeInferT]
        exact ((memSubtermEncode a args ha).tail (Or.inr ⟨.const (.tcTag n), rfl⟩)).tail
          (Or.inr ⟨.const .tappTag, rfl⟩)
      | uvar v =>
        cases found : tcvwalkModel s v with
        | varDb n =>
          simp [starWorklistCodeModel, found] at step
          subst y
          exact Or.inl (removedHead _ _ tail kont)
        | uvar n =>
          simp [starWorklistCodeModel, found] at step
          subst y
          exact Or.inl (removedHead _ _ tail kont)
        | app args n =>
          simp [starWorklistCodeModel, found] at step
          subst y
          apply Or.inl
          apply expandedHead
          intro a ha
          have hwalk : tcwalkModel s (.uvar v) = .app args n := found
          have h := walkstarOpthModel s (.uvar v) a args n ⟨hw, hwalk, ha⟩
          have hm : sp2fm (sptMap encodeInferT s) =
              (sp2fm s).map2 (fun p => encodeInferT p.2) := by
            apply HolFiniteMapExact.ext_lookup
            intro key
            exact sptLookup_sptMap encodeInferT s key
          simpa [hm] using h

end Flapjack.Compiler.Inference.Unify
