module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.RecClosureRelation
public import Flapjack.Compiler.Backend.ClosCall.Proofs.Environment
public import Flapjack.Compiler.Backend.Semantics.ClosSem

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Value relation for the direct-call simulation. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem

private def toBroad {K V : Type} (code : HolFiniteMapExact K V) : K → Option V := code.lookup
private def ofBroad {K V : Type} (lookup : K → Option V)
    (support : ∃ keys : List K, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact K V :=
  ⟨lookup, support⟩

/-- Canonical finite-map codec for the value relation's code parameter. -/
theorem holFmapAsFiniteSupportParamWitness_valueRel_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code := by
  cases code
  exact ⟨rfl, rfl, rfl⟩

/-- Direct-call conversion relates values recursively. Source lists carry
membership proofs only to justify termination; the source equations below
recover the ordinary list and environment relations. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "v_rel_def"
  (fmap_as_finite_support_parameters := [code])]
def valueRel (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : Value → Value → Prop
  | .number x, v => v = .number x
  | .word64 x, v => v = .word64 x
  | .block tag xs, v => ∃ ys, v = .block tag ys ∧
      List.Forall₂ (fun x y => valueRel g allowed code x.1 y) xs.attach ys
  | .byteVector xs, v => v = .byteVector xs
  | .refPtr b n, v => v = .refPtr b n
  | .closure loco vs env n body, v =>
      ∃ loc vs' env' body', recClosureRel g allowed code loc [(n, body)] [(n, body')] ∧
      v = .closure (some loc) vs' env' n body' ∧ loco = some loc ∧
      List.Forall₂ (fun x y => valueRel g allowed code x.1 y) vs.attach vs' ∧
      envRel (fun x y => valueRel g allowed code x.1 y) env.attach env' 0 [(n, body')]
  | .recclosure loco vs env fns i, v =>
      ∃ loc vs' env' fns', recClosureRel g allowed code loc fns fns' ∧
      v = .recclosure (some loc) vs' env' fns' i ∧ loco = some loc ∧
      List.Forall₂ (fun x y => valueRel g allowed code x.1 y) vs.attach vs' ∧
      envRel (fun x y => valueRel g allowed code x.1 y) env.attach env' fns'.length fns'
termination_by x _ => sizeOf x
decreasing_by
  all_goals simp_wf
  all_goals try have bound := List.sizeOf_lt_of_mem x.property
  all_goals omega

private theorem attachListRel {A B : Type} (R : A → B → Prop) (xs : List A) (ys : List B) :
    List.Forall₂ (fun x y => R x.1 y) xs.attach ys ↔ List.Forall₂ R xs ys := by
  simpa using (List.forall₂_map_left_iff (R := R) (f := Subtype.val) (l := xs.attach) (u := ys)).symm

private theorem attachEnvRel {A B : Type} (R : A → B → Prop) (xs : List A) (ys : List B)
    (offset : Nat) (fns : List (Nat × ClosLang.Exp)) :
    envRel (fun x y => R x.1 y) xs.attach ys offset fns ↔ envRel R xs ys offset fns := by
  unfold envRel
  simp only [List.length_attach]
  split
  · exact attachListRel R xs ys
  · simp

/-- Flapjack infrastructure: these kernel-checked unfolding equations remove
the termination-only list attachments from the three recursive clauses. -/
theorem valueRel_sourceEquations (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) :
    (∀ tag xs v, valueRel g allowed code (.block tag xs) v ↔
      ∃ ys, v = .block tag ys ∧ List.Forall₂ (valueRel g allowed code) xs ys) ∧
    (∀ loco vs env n body v, valueRel g allowed code (.closure loco vs env n body) v ↔
      ∃ loc vs' env' body', recClosureRel g allowed code loc [(n, body)] [(n, body')] ∧
        v = .closure (some loc) vs' env' n body' ∧ loco = some loc ∧
        List.Forall₂ (valueRel g allowed code) vs vs' ∧
        envRel (valueRel g allowed code) env env' 0 [(n, body')]) ∧
    (∀ loco vs env fns i v, valueRel g allowed code (.recclosure loco vs env fns i) v ↔
      ∃ loc vs' env' fns', recClosureRel g allowed code loc fns fns' ∧
        v = .recclosure (some loc) vs' env' fns' i ∧ loco = some loc ∧
        List.Forall₂ (valueRel g allowed code) vs vs' ∧
        envRel (valueRel g allowed code) env env' fns'.length fns') := by
  simp [valueRel, attachListRel, attachEnvRel]

/-- Canonical finite-map codec for value-relation state extension. -/
theorem holFmapAsFiniteSupportParamWitness_valueRel_subg_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_valueRel_code code key

/-- Extending the compiler state and allowed locations preserves the
direct-call value relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "v_rel_subg"
  (fmap_as_finite_support_parameters := [code])]
theorem valueRel_subg (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (left right : Value)
    (gNext : State) (allowedNext : Nat → Prop)
    (h : valueRel g allowed code left right ∧ stateExtends g gNext ∧
      (∀ x, allowed x → allowedNext x)) :
    valueRel gNext allowedNext code left right := by
  cases left with
  | number n => simpa [valueRel] using h.1
  | word64 w => simpa [valueRel] using h.1
  | byteVector bytes => simpa [valueRel] using h.1
  | refPtr b n => simpa [valueRel] using h.1
  | block tag values =>
      obtain ⟨nextValues, eq, related⟩ := (valueRel_sourceEquations g allowed code).1 _ _ _ |>.mp h.1
      apply (valueRel_sourceEquations gNext allowedNext code).1 _ _ _ |>.mpr
      refine ⟨nextValues, eq, ?_⟩
      apply forall₂_mono_members related
      intro x hx y hy rel
      exact valueRel_subg g allowed code x y gNext allowedNext ⟨rel, h.2⟩
  | closure loco values env arity body =>
      obtain ⟨loc, nextValues, nextEnv, nextBody, closure, eq, location, valuesRel, envRelated⟩ :=
        (valueRel_sourceEquations g allowed code).2.1 _ _ _ _ _ _ |>.mp h.1
      apply (valueRel_sourceEquations gNext allowedNext code).2.1 _ _ _ _ _ _ |>.mpr
      refine ⟨loc, nextValues, nextEnv, nextBody, ?_, eq, location, ?_, ?_⟩
      · exact recClosureRel_mono g gNext allowed allowedNext code code loc [(arity, body)]
          [(arity, nextBody)] closure (HolFiniteMapExact.submap_refl _) h.2.1 h.2.2
      · apply forall₂_mono_members valuesRel
        intro x hx y hy rel
        exact valueRel_subg g allowed code x y gNext allowedNext ⟨rel, h.2⟩
      · apply envRel_mono ?_ envRelated
        intro x y ⟨hx, hy, rel⟩
        exact valueRel_subg g allowed code x y gNext allowedNext ⟨rel, h.2⟩
  | recclosure loco values env fns index =>
      obtain ⟨loc, nextValues, nextEnv, nextFns, closure, eq, location, valuesRel, envRelated⟩ :=
        (valueRel_sourceEquations g allowed code).2.2 _ _ _ _ _ _ |>.mp h.1
      apply (valueRel_sourceEquations gNext allowedNext code).2.2 _ _ _ _ _ _ |>.mpr
      refine ⟨loc, nextValues, nextEnv, nextFns, ?_, eq, location, ?_, ?_⟩
      · exact recClosureRel_mono g gNext allowed allowedNext code code loc fns nextFns
          closure (HolFiniteMapExact.submap_refl _) h.2.1 h.2.2
      · apply forall₂_mono_members valuesRel
        intro x hx y hy rel
        exact valueRel_subg g allowed code x y gNext allowedNext ⟨rel, h.2⟩
      · apply envRel_mono ?_ envRelated
        intro x y ⟨hx, hy, rel⟩
        exact valueRel_subg g allowed code x y gNext allowedNext ⟨rel, h.2⟩
termination_by sizeOf left
decreasing_by
  all_goals subst_vars
  all_goals have bound := List.sizeOf_lt_of_mem (show x ∈ _ from ‹x ∈ _›)
  all_goals simp_wf
  all_goals omega

end Flapjack.Compiler.Backend.ClosCall
