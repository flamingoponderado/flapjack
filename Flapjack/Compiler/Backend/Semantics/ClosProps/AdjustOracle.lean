import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveTotal
import Flapjack.Compiler.Backend.BackendProps.StateCompiler

/-! Closure-state relation for changing the compiler-oracle configuration. -/
namespace Flapjack.Compiler.Backend.ClosProps.AdjustOracle
open ClosSem BackendProps
open Flapjack.SemanticPrimitivesProps

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Two closure states differ only by a mapped compiler configuration and
compatible compilation callbacks. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "adj_orac_rel_def"
  (fmap_as_finite_support := [refs, code])]
def adjOracRel {C D F : Type} (cc : Compiler D) (f : C → D)
    (s : State C F) (t : State D F) : Prop :=
  (∀ n x y, s.compileOracle n = (x, y) →
    (s.compile x y).map (fun (bytes, words, cfg) => (bytes, words, f cfg)) = cc (f x) y) ∧
  t = ⟨s.globals, s.refs, s.ffi, s.clock, cc,
    (fun n => (f (s.compileOracle n).1, (s.compileOracle n).2)), s.code, s.maxApp⟩

private theorem forallEqRefl {A : Type} (xs : List A) : List.Forall₂ Eq xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons rfl ih

private theorem forallEqEqual {A : Type} {xs ys : List A} (h : List.Forall₂ Eq xs ys) : xs = ys := by
  induction h with
  | nil => rfl
  | cons head tail ih => cases head; simp [ih]

/-- Equality is a simple closure-value relation. This helper supports the
source oracle-adjustment simulation. -/
theorem simpleValRelEq : simpleValRel Eq := by
  simp only [simpleValRel]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; trivial
  · intro x p n
    constructor
    · intro h; subst x; exact ⟨p, rfl, forallEqRefl _⟩
    · rintro ⟨xs, rfl, rel⟩
      have same : xs = p := forallEqEqual rel
      subst xs; rfl
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro body arity env args loc x h; subst x; trivial
  · intro index funs env args loc x h; subst x; trivial

/-- The source relation supports all primitive state updates. This is
Lean-side infrastructure for the source oracle-adjustment theorem. -/
theorem adjOracRel_simpleStateRel {C D F : Type} (cc : Compiler D) (f : C → D) :
    simpleStateRel Eq (adjOracRel (F := F) cc f) := by
  simp only [simpleStateRel]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t ptr ⟨missing, rel⟩
    rcases rel with ⟨_, rfl⟩
    exact missing
  · intro bytes t s ptr ⟨found, rel⟩
    rcases rel with ⟨_, rfl⟩
    exact found
  · intro values t s ptr ⟨found, rel⟩
    rcases rel with ⟨_, rfl⟩
    exact ⟨values, found, forallEqRefl _⟩
  · intro mode value t s ptr ⟨found, rel⟩
    rcases rel with ⟨_, rfl⟩
    exact ⟨value, found, rfl⟩
  · intro s t rel
    rcases rel with ⟨_, rfl⟩
    refine ⟨rfl, by simp, ?_⟩
    induction s.globals with
    | nil => exact .nil
    | cons a rest ih =>
      apply List.Forall₂.cons ?_ ih
      cases a <;> simp [optionRel]
  · intro ffi s t rel
    rcases rel with ⟨compiler, rfl⟩
    exact ⟨compiler, rfl⟩
  · intro bytes s t ptr rel
    rcases rel with ⟨compiler, rfl⟩
    exact ⟨compiler, rfl⟩
  · intro s t ptr xs ys ⟨rel, values⟩
    have equal := forallEqEqual values
    subst ys
    rcases rel with ⟨compiler, rfl⟩
    exact ⟨compiler, rfl⟩
  · intro s t ptr mode v w ⟨rel, equal⟩
    subst w
    rcases rel with ⟨compiler, rfl⟩
    exact ⟨compiler, rfl⟩
  · intro s t xs ys ⟨rel, values⟩
    have equal : xs = ys := by
      induction values with
      | nil => rfl
      | @cons x y xs ys h tail ih =>
        cases x <;> cases y <;> simp_all [optionRel]
    subst ys
    rcases rel with ⟨compiler, rfl⟩
    exact ⟨compiler, rfl⟩

/-- A primitive error is unchanged by an oracle adjustment. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "do_app_adj_orac_Rerr"
  (fmap_as_finite_support := [refs, code])]
theorem doAppAdjOracErr {C D F : Type} (cc : Compiler D) (f : C → D)
    (op : ClosLang.Op) (xs : List Value) (s : State C F) (t : State D F)
    (err : Flapjack.SemanticPrimitivesHOL.ErrorResult Value)
    (h : doApp op xs s = .err err ∧ adjOracRel cc f s t) :
    doApp op xs t = .err err := by
  obtain ⟨run, rel⟩ := h
  have sim := PrimitiveTotal.simpleValRelDoApp Eq (adjOracRel cc f) s t xs xs op
    ⟨simpleValRelEq, adjOracRel_simpleStateRel cc f⟩ ⟨rel, forallEqRefl xs⟩
  rw [run] at sim
  obtain ⟨err', result, related⟩ := sim
  have same : err = err' := by cases err <;> cases err' <;> simp_all [excRel]
  simpa [← same] using result

/-- A successful primitive result is unchanged and its final states remain
related after an oracle adjustment. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "do_app_adj_orac_Rval"
  (fmap_as_finite_support := [refs, code])]
theorem doAppAdjOracVal {C D F : Type} (cc : Compiler D) (f : C → D)
    (op : ClosLang.Op) (xs : List Value) (s : State C F) (t : State D F)
    (value : Value) (next : State C F)
    (h : doApp op xs s = .val (value, next) ∧ adjOracRel cc f s t) :
    ∃ target, doApp op xs t = .val (value, target) ∧ adjOracRel cc f next target := by
  obtain ⟨run, rel⟩ := h
  have sim := PrimitiveTotal.simpleValRelDoApp Eq (adjOracRel cc f) s t xs xs op
    ⟨simpleValRelEq, adjOracRel_simpleStateRel cc f⟩ ⟨rel, forallEqRefl xs⟩
  rw [run] at sim
  obtain ⟨y, target, same, related, result⟩ := sim
  subst y
  exact ⟨target, result, related⟩

end Flapjack.Compiler.Backend.ClosProps.AdjustOracle
