import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveBoolean

/-! Numeric cases of the generic closure primitive simulation. -/
namespace Flapjack.Compiler.Backend.ClosProps.PrimitiveNumeric
open ClosSem Flapjack.SemanticPrimitivesProps
open Flapjack.Compiler.Backend.ClosProps.PrimitiveBoolean

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Related arguments produce the same integer primitive observation. This is
Flapjack proof infrastructure. -/
theorem doIntAppRelated (vr : Value → Value → Prop) (simple : simpleValRel vr)
    (op : ClosLang.IntOp) {left right : List Value}
    (related : List.Forall₂ vr left right) : doIntApp op left = doIntApp op right := by
  cases op <;> cases related with
  | nil => rfl
  | @cons a b _ _ head tail =>
    have first := simpleValRel_view vr simple a b head
    cases first <;> cases tail <;> simp_all [doIntApp]
    all_goals
      rename_i head2 tail2
      have second := simpleValRel_view vr simple _ _ head2
      cases second <;> cases tail2 <;> simp_all

/-- A successful integer primitive returns values related to themselves.
This is Flapjack proof infrastructure. -/
theorem doIntAppResultRelated (vr : Value → Value → Prop) (simple : simpleValRel vr)
    (op : ClosLang.IntOp) (args : List Value) (value : Value)
    (run : doIntApp op args = some value) : vr value value := by
  have number : ∀ n, vr (.number n) (.number n) := fun n => (simple.1 _ n).2 rfl
  cases op <;> cases args <;> simp_all [doIntApp]
  all_goals try (subst value; exact number _)
  all_goals
    rename_i head tail
    cases head <;> cases tail <;> try simp_all
    all_goals try (obtain ⟨_, rfl⟩ := run; exact simpleValRel_boolValue vr simple _)
    all_goals
      rename_i head2 tail2
      cases head2 <;> cases tail2 <;> try simp_all
      all_goals try (subst value; exact number _)
      all_goals try (subst value; exact simpleValRel_boolValue vr simple _)
      all_goals try (obtain ⟨_, rfl⟩ := run; exact number _)

/-- Integer-operation case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevInt {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (op : ClosLang.IntOp)
    (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.intOp op) ys t with
    | .err err2 => ∃ err1, doApp (.intOp op) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.intOp op) xs s = .val (x, s1) := by
  obtain ⟨simple, _, states, values⟩ := h
  have same := doIntAppRelated vr simple op values
  cases run : doIntApp op xs with
  | none => simp [doApp, applyNumeric, ← same, run, excRel]
  | some value =>
    have valueRel := doIntAppResultRelated vr simple op xs value run
    simp [doApp, applyNumeric, ← same, run, valueRel, states]

/-- Related arguments produce the same word primitive observation. This is
Flapjack proof infrastructure. -/
theorem doWordAppRelated (vr : Value → Value → Prop) (simple : simpleValRel vr)
    (op : ClosLang.WordOp) {left right : List Value}
    (related : List.Forall₂ vr left right) : doWordApp op left = doWordApp op right := by
  cases op <;> cases related with
  | nil => rfl
  | @cons a b _ _ head tail =>
    have first := simpleValRel_view vr simple a b head
    cases first <;> cases tail <;> simp_all [doWordApp, doWordAppIntegral]
    all_goals
      rename_i head2 tail2
      have second := simpleValRel_view vr simple _ _ head2
      cases second <;> cases tail2 <;> try simp_all
      all_goals
        rename_i head3 tail3
        have third := simpleValRel_view vr simple _ _ head3
        cases third <;> cases tail3 <;> simp_all

/-- A successful word primitive returns values related to themselves.
This is Flapjack proof infrastructure. -/
theorem doWordAppResultRelated (vr : Value → Value → Prop) (simple : simpleValRel vr)
    (op : ClosLang.WordOp) (args : List Value) (value : Value)
    (run : doWordApp op args = some value) : vr value value := by
  have number : ∀ n, vr (.number n) (.number n) := fun n => (simple.1 _ n).2 rfl
  have word : ∀ w, vr (.word64 w) (.word64 w) := fun w => (simple.2.2.1 _ w).2 rfl
  cases op <;> cases args <;> simp_all [doWordApp, doWordAppIntegral]
  all_goals
    rename_i head tail
    cases head <;> cases tail <;> try simp_all
    all_goals try (subst value; exact word _)
    all_goals try (subst value; exact number _)
    all_goals
      repeat
        first
        | split at run
        | simp_all
        | subst value
        | exact number _
        | exact word _
        | exact simpleValRel_boolValue vr simple _
    all_goals try simp_all
    all_goals simp [intToByte] at run
    all_goals split at run <;> simp_all
    all_goals try (split at run <;> simp_all)
    all_goals try (subst value; exact number _)
    all_goals try (subst value; exact word _)

/-- Word-operation cases of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevWord {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (op : ClosLang.WordOp)
    (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.wordOp op) ys t with
    | .err err2 => ∃ err1, doApp (.wordOp op) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.wordOp op) xs s = .val (x, s1) := by
  obtain ⟨simple, _, states, values⟩ := h
  have same := doWordAppRelated vr simple op values
  cases run : doWordApp op xs with
  | none => simp [doApp, applyNumeric, ← same, run, excRel]
  | some value =>
    have valueRel := doWordAppResultRelated vr simple op xs value run
    simp [doApp, applyNumeric, ← same, run, valueRel, states]

end Flapjack.Compiler.Backend.ClosProps.PrimitiveNumeric
