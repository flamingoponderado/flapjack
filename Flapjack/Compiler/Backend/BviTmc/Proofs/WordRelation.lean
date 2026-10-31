import Flapjack.Compiler.Backend.BviTmc.Proofs.ValueRelation
import Flapjack.Compiler.Backend.Semantics.BvlSem.Word

/-! TMC value relations for word operations. -/
namespace Flapjack.Compiler.Backend.BviTmc
open BvlSem

private def maptoBroadlookup (f : HolFiniteMapExact Nat Nat) : Nat → Option Nat := f.lookup
private def mapofBroad (lookup : Nat → Option Nat)
    (support : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact Nat Nat :=
  ⟨lookup, support⟩

theorem holFmapAsFiniteSupportParamWitness_doWordApp_rel_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

private def scalar : Value → Prop
  | .number _ | .word64 _ => True
  | _ => False

private theorem related_scalars_eq (f : HolFiniteMapExact Nat Nat) (values relatedValues : List Value)
    (related : List.Forall₂ (valueRel f) values relatedValues) (all : ∀ v ∈ values, scalar v) :
    relatedValues = values := by
  induction related with
  | nil => rfl
  | @cons a b xs ys head tail ih =>
    have scalarHead := all a (by simp)
    have tailAll : ∀ v ∈ xs, scalar v := by
      intro v member
      exact all v (by simp [member])
    cases head <;> simp_all [scalar]

/-- Successful word operations can only consume scalar values, which the
TMC value relation preserves exactly. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_word_app_v_rel"
  (fmap_as_finite_support_parameters := [f])]
theorem doWordApp_rel (f : HolFiniteMapExact Nat Nat) (op : ClosLang.WordOp)
    (values relatedValues : List Value) (result : Value) (run : doWordApp op values = some result)
    (related : List.Forall₂ (valueRel f) values relatedValues) : relatedValues = values := by
  apply related_scalars_eq f values relatedValues related
  unfold doWordApp at run
  repeat' split at run
  all_goals try (unfold doWordAppIntegral at run; repeat' first | split at run | contradiction)
  all_goals simp_all [scalar]

private theorem boolValue_related (f : HolFiniteMapExact Nat Nat) (b : Bool) :
    valueRel f (boolValue b) (boolValue b) := by
  exact .block _ [] [] .nil

theorem holFmapAsFiniteSupportParamWitness_doWordApp_result_rel_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Successful word-operation results are related to themselves. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_word_app_v_rel_refl"
  (fmap_as_finite_support_parameters := [f])]
theorem doWordApp_result_rel (f : HolFiniteMapExact Nat Nat) (op : ClosLang.WordOp)
    (values : List Value) (result : Value) (run : doWordApp op values = some result) :
    valueRel f result result := by
  unfold doWordApp at run
  repeat' split at run
  all_goals try (simp only [Option.some.injEq] at run; subst result; first | exact .number _ | exact .word64 _ | apply boolValue_related)
  all_goals unfold doWordAppIntegral at run
  all_goals repeat' first | split at run | contradiction
  all_goals try dsimp only [Bind.bind, Option.bind, pure] at run
  all_goals try split at run
  all_goals try contradiction
  all_goals try dsimp only [Bind.bind, Option.bind, pure] at run
  all_goals try split at run
  all_goals try contradiction
  all_goals try dsimp only [pure] at run
  all_goals try simp only [Option.some.injEq] at run
  all_goals subst result
  all_goals first | exact .number _ | exact .word64 _ | apply boolValue_related
