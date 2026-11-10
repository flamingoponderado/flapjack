module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.RecClosureRelation
public import Flapjack.Compiler.Backend.ClosCall.Proofs.Environment
public import Flapjack.Compiler.Backend.Semantics.ClosSem
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Install

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

/-- Canonical codec for the source code map in code-extension preservation. -/
theorem holFmapAsFiniteSupportParamWitness_valueRel_submap_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_valueRel_code code key

/-- Canonical codec for the extended code map. -/
theorem holFmapAsFiniteSupportParamWitness_valueRel_submap_codeNext
    (codeNext : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad codeNext) codeNext.finiteSupport).lookup key = codeNext.lookup key ∧
    (ofBroad (toBroad codeNext) codeNext.finiteSupport).finiteSupport = codeNext.finiteSupport ∧
    ofBroad (toBroad codeNext) codeNext.finiteSupport = codeNext :=
  holFmapAsFiniteSupportParamWitness_valueRel_code codeNext key

/-- Adding code bindings preserves the direct-call value relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "v_rel_SUBMAP"
  (fmap_as_finite_support_parameters := [code, codeNext])]
theorem valueRel_submap (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (left right : Value)
    (codeNext : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (h : valueRel g allowed code left right ∧ code.submap codeNext) :
    valueRel g allowed codeNext left right := by
  cases left with
  | number n => simpa [valueRel] using h.1
  | word64 w => simpa [valueRel] using h.1
  | byteVector bytes => simpa [valueRel] using h.1
  | refPtr b n => simpa [valueRel] using h.1
  | block tag values =>
      obtain ⟨nextValues, eq, related⟩ := (valueRel_sourceEquations g allowed code).1 _ _ _ |>.mp h.1
      apply (valueRel_sourceEquations g allowed codeNext).1 _ _ _ |>.mpr
      refine ⟨nextValues, eq, ?_⟩
      apply forall₂_mono_members related
      intro x hx y hy rel
      exact valueRel_submap g allowed code x y codeNext ⟨rel, h.2⟩
  | closure loco values env arity body =>
      obtain ⟨loc, nextValues, nextEnv, nextBody, closure, eq, location, valuesRel, envRelated⟩ :=
        (valueRel_sourceEquations g allowed code).2.1 _ _ _ _ _ _ |>.mp h.1
      apply (valueRel_sourceEquations g allowed codeNext).2.1 _ _ _ _ _ _ |>.mpr
      refine ⟨loc, nextValues, nextEnv, nextBody, ?_, eq, location, ?_, ?_⟩
      · exact recClosureRel_mono g g allowed allowed code codeNext loc [(arity, body)]
          [(arity, nextBody)] closure h.2
          (recClosureRel_stateExtendsSelf g allowed code loc [(arity, body)] [(arity, nextBody)] closure)
          (fun _ member => member)
      · apply forall₂_mono_members valuesRel
        intro x hx y hy rel
        exact valueRel_submap g allowed code x y codeNext ⟨rel, h.2⟩
      · apply envRel_mono ?_ envRelated
        intro x y ⟨hx, hy, rel⟩
        exact valueRel_submap g allowed code x y codeNext ⟨rel, h.2⟩
  | recclosure loco values env fns index =>
      obtain ⟨loc, nextValues, nextEnv, nextFns, closure, eq, location, valuesRel, envRelated⟩ :=
        (valueRel_sourceEquations g allowed code).2.2 _ _ _ _ _ _ |>.mp h.1
      apply (valueRel_sourceEquations g allowed codeNext).2.2 _ _ _ _ _ _ |>.mpr
      refine ⟨loc, nextValues, nextEnv, nextFns, ?_, eq, location, ?_, ?_⟩
      · exact recClosureRel_mono g g allowed allowed code codeNext loc fns nextFns closure h.2
          (recClosureRel_stateExtendsSelf g allowed code loc fns nextFns closure) (fun _ member => member)
      · apply forall₂_mono_members valuesRel
        intro x hx y hy rel
        exact valueRel_submap g allowed code x y codeNext ⟨rel, h.2⟩
      · apply envRel_mono ?_ envRelated
        intro x y ⟨hx, hy, rel⟩
        exact valueRel_submap g allowed code x y codeNext ⟨rel, h.2⟩
termination_by sizeOf left
decreasing_by
  all_goals subst_vars
  all_goals have bound := List.sizeOf_lt_of_mem (show x ∈ _ from ‹x ∈ _›)
  all_goals simp_wf
  all_goals omega

/-- Canonical finite-map codec for code in valueRel_submapSubg. -/
theorem holFmapAsFiniteSupportParamWitness_valueRel_submapSubg_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_valueRel_code code key

/-- Canonical finite-map codec for codeNext in valueRel_submapSubg. -/
theorem holFmapAsFiniteSupportParamWitness_valueRel_submapSubg_codeNext
    (codeNext : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad codeNext) codeNext.finiteSupport).lookup key = codeNext.lookup key ∧
    (ofBroad (toBroad codeNext) codeNext.finiteSupport).finiteSupport = codeNext.finiteSupport ∧
    ofBroad (toBroad codeNext) codeNext.finiteSupport = codeNext :=
  holFmapAsFiniteSupportParamWitness_valueRel_code codeNext key

/-- Canonical finite-map codec for code in listValueRel_subg. -/
theorem holFmapAsFiniteSupportParamWitness_listValueRel_subg_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_valueRel_code code key

/-- Canonical finite-map codec for codeNext in listValueRel_subg. -/
theorem holFmapAsFiniteSupportParamWitness_listValueRel_subg_codeNext
    (codeNext : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad codeNext) codeNext.finiteSupport).lookup key = codeNext.lookup key ∧
    (ofBroad (toBroad codeNext) codeNext.finiteSupport).finiteSupport = codeNext.finiteSupport ∧
    ofBroad (toBroad codeNext) codeNext.finiteSupport = codeNext :=
  holFmapAsFiniteSupportParamWitness_valueRel_code codeNext key

/-- Canonical finite-map codec for code in envValueRel_subg. -/
theorem holFmapAsFiniteSupportParamWitness_envValueRel_subg_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_valueRel_code code key

/-- Canonical finite-map codec for codeNext in envValueRel_subg. -/
theorem holFmapAsFiniteSupportParamWitness_envValueRel_subg_codeNext
    (codeNext : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad codeNext) codeNext.finiteSupport).lookup key = codeNext.lookup key ∧
    (ofBroad (toBroad codeNext) codeNext.finiteSupport).finiteSupport = codeNext.finiteSupport ∧
    ofBroad (toBroad codeNext) codeNext.finiteSupport = codeNext :=
  holFmapAsFiniteSupportParamWitness_valueRel_code codeNext key

/-- Extending code, allowed locations and compiler state preserves related values. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "v_rel_SUBMAP_subg"
  (fmap_as_finite_support_parameters := [code, codeNext])]
theorem valueRel_submapSubg (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (left right : Value)
    (codeNext : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (allowedNext : Nat → Prop) (gNext : State)
    (h : valueRel g allowed code left right ∧ code.submap codeNext ∧
      (∀ x, allowed x → allowedNext x) ∧ stateExtends g gNext) :
    valueRel gNext allowedNext codeNext left right := by
  exact valueRel_subg g allowed codeNext left right gNext allowedNext
    ⟨valueRel_submap g allowed code left right codeNext ⟨h.1, h.2.1⟩, h.2.2.2, h.2.2.1⟩

/-- Extending the compiler state, allowed locations and code preserves related value lists. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "LIST_REL_v_rel_subg"
  (fmap_as_finite_support_parameters := [code, codeNext])]
theorem listValueRel_subg (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (xs ys : List Value)
    (gNext : State) (allowedNext : Nat → Prop) (codeNext : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (h : List.Forall₂ (valueRel g allowed code) xs ys ∧ stateExtends g gNext ∧
      (∀ x, allowed x → allowedNext x) ∧ code.submap codeNext) :
    List.Forall₂ (valueRel gNext allowedNext codeNext) xs ys := by
  apply h.1.imp
  intro x y related
  exact valueRel_submapSubg g allowed code x y codeNext allowedNext gNext
    ⟨related, h.2.2.2, h.2.2.1, h.2.1⟩

/-- Extending the compiler state, allowed locations and code preserves related environments. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "env_rel_subg"
  (fmap_as_finite_support_parameters := [code, codeNext])]
theorem envValueRel_subg (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (env1 env2 : List Value)
    (offset : Nat) (fns : List (Nat × ClosLang.Exp))
    (gNext : State) (allowedNext : Nat → Prop) (codeNext : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (h : envRel (valueRel g allowed code) env1 env2 offset fns ∧ stateExtends g gNext ∧
      (∀ x, allowed x → allowedNext x) ∧ code.submap codeNext) :
    envRel (valueRel gNext allowedNext codeNext) env1 env2 offset fns := by
  apply envRel_mono ?_ h.1
  intro x y ⟨_, _, related⟩
  exact valueRel_submapSubg g allowed code x y codeNext allowedNext gNext
    ⟨related, h.2.2.2, h.2.2.1, h.2.1⟩

/-- Canonical code-map codec for list relation preservation. -/
theorem holFmapAsFiniteSupportParamWitness_listValueRel_submap_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_valueRel_code code key

/-- Canonical extended code-map codec for list relation preservation. -/
theorem holFmapAsFiniteSupportParamWitness_listValueRel_submap_codeNext
    (codeNext : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad codeNext) codeNext.finiteSupport).lookup key = codeNext.lookup key ∧
    (ofBroad (toBroad codeNext) codeNext.finiteSupport).finiteSupport = codeNext.finiteSupport ∧
    ofBroad (toBroad codeNext) codeNext.finiteSupport = codeNext :=
  holFmapAsFiniteSupportParamWitness_valueRel_code codeNext key

/-- Extending the code map preserves related value lists. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "LIST_REL_v_rel_SUBMAP"
  (fmap_as_finite_support_parameters := [code, codeNext])]
theorem listValueRel_submap (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (xs ys : List Value)
    (codeNext : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (h : List.Forall₂ (valueRel g allowed code) xs ys ∧ code.submap codeNext) :
    List.Forall₂ (valueRel g allowed codeNext) xs ys := by
  apply h.1.imp
  intro x y related
  exact valueRel_submap g allowed code x y codeNext ⟨related, h.2⟩

/-- Canonical code-map codec for environment relation preservation. -/
theorem holFmapAsFiniteSupportParamWitness_envValueRel_submap_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_valueRel_code code key

/-- Canonical extended code-map codec for environment relation preservation. -/
theorem holFmapAsFiniteSupportParamWitness_envValueRel_submap_codeNext
    (codeNext : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad codeNext) codeNext.finiteSupport).lookup key = codeNext.lookup key ∧
    (ofBroad (toBroad codeNext) codeNext.finiteSupport).finiteSupport = codeNext.finiteSupport ∧
    ofBroad (toBroad codeNext) codeNext.finiteSupport = codeNext :=
  holFmapAsFiniteSupportParamWitness_valueRel_code codeNext key

/-- Extending the code map preserves related environments. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "env_rel_SUBMAP"
  (fmap_as_finite_support_parameters := [code, codeNext])]
theorem envValueRel_submap (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (codeNext : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (g : State) (allowed : Nat → Prop) (env1 env2 : List Value)
    (offset : Nat) (fns : List (Nat × ClosLang.Exp))
    (h : envRel (valueRel g allowed code) env1 env2 offset fns ∧ code.submap codeNext) :
    envRel (valueRel g allowed codeNext) env1 env2 offset fns := by
  apply envRel_mono ?_ h.1
  intro x y ⟨_, _, related⟩
  exact valueRel_submap g allowed code x y codeNext ⟨related, h.2⟩

/-- Canonical code-map codec for the unit-value relation. -/
theorem holFmapAsFiniteSupportParamWitness_valueRel_unit_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_valueRel_code code key

/-- Unit values are related by direct-call conversion. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "v_rel_Unit"
  (fmap_as_finite_support_parameters := [code])]
theorem valueRel_unit (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) :
    valueRel g allowed code unitValue unitValue := by
  apply (valueRel_sourceEquations g allowed code).1 _ _ _ |>.mpr
  exact ⟨[], rfl, .nil⟩

/-- Canonical code-map codec for list decoding preservation. -/
theorem holFmapAsFiniteSupportParamWitness_valueToList_thm_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_valueRel_code code key

/-- Decoding a related source list yields pointwise related target elements. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "v_to_list_thm"
  (fmap_as_finite_support_parameters := [code])]
theorem valueToList_thm (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (h h' : Value) (x : List Value)
    (assumptions : valueToList h = some x ∧ valueRel g allowed code h h') :
    ∃ x', valueToList h' = some x' ∧ List.Forall₂ (valueRel g allowed code) x x' := by
  cases h with
  | block tag values =>
    obtain ⟨values', eq, related⟩ := (valueRel_sourceEquations g allowed code).1 _ _ _ |>.mp assumptions.2
    subst h'
    cases related with
    | nil =>
      simp only [valueToList] at assumptions ⊢
      split at assumptions <;> simp_all
    | @cons first first' tail tail' firstRel rest =>
      cases rest with
      | nil => simp [valueToList] at assumptions
      | @cons last last' tail tail' lastRel rest =>
        cases rest with
        | cons => simp [valueToList] at assumptions
        | nil =>
          simp only [valueToList] at assumptions ⊢
          split at assumptions <;> simp_all
          cases decoded : valueToList last with
          | none => simp [decoded] at assumptions
          | some xs =>
            simp only [decoded, Option.some.injEq] at assumptions
            obtain ⟨ys, target, elements⟩ := valueToList_thm g allowed code last last' xs ⟨decoded, lastRel⟩
            obtain ⟨⟨_, rfl, rfl⟩, _⟩ := assumptions
            exact ⟨ys, target, .cons firstRel elements⟩
  | number n => simp [valueToList] at assumptions
  | word64 w => simp [valueToList] at assumptions
  | byteVector bytes => simp [valueToList] at assumptions
  | refPtr b n => simp [valueToList] at assumptions
  | closure loco values env arity body => simp [valueToList] at assumptions
  | recclosure loco values env fns index => simp [valueToList] at assumptions
termination_by sizeOf h
decreasing_by
  subst_vars
  simp_wf
  omega

/-- Canonical code-map codec for byte decoding preservation. -/
theorem holFmapAsFiniteSupportParamWitness_valueToBytes_thm_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_valueRel_code code key

/-- Direct-call conversion preserves decoded byte lists. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "v_to_bytes_thm"
  (fmap_as_finite_support_parameters := [code])]
theorem valueToBytes_thm (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (h h' : Value) (x : List (BitVec 8))
    (assumptions : valueToBytes h = some x ∧ valueRel g allowed code h h') :
    valueToBytes h' = some x := by
  have decoded := (valueToBytes_eq_some h x).mp assumptions.1
  obtain ⟨ys, target, related⟩ := valueToList_thm g allowed code h h' _ ⟨decoded, assumptions.2⟩
  have same : ys = x.map (fun b => Value.number b.toNat) := by
    clear assumptions decoded target
    induction x generalizing ys with
    | nil => cases related; rfl
    | cons b bs ih =>
      cases related with
      | cons head tail =>
        simp only [valueRel] at head
        simp [head, ih _ tail]
  exact (valueToBytes_eq_some h' x).mpr (same ▸ target)

/-- Canonical code-map codec for word decoding preservation. -/
theorem holFmapAsFiniteSupportParamWitness_valueToWords_thm_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_valueRel_code code key

/-- Direct-call conversion preserves decoded word lists. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "v_to_words_thm"
  (fmap_as_finite_support_parameters := [code])]
theorem valueToWords_thm (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (h h' : Value) (x : List (BitVec 64))
    (assumptions : valueToWords h = some x ∧ valueRel g allowed code h h') :
    valueToWords h' = some x := by
  have decoded := (valueToWords_eq_some h x).mp assumptions.1
  obtain ⟨ys, target, related⟩ := valueToList_thm g allowed code h h' _ ⟨decoded, assumptions.2⟩
  have same : ys = x.map Value.word64 := by
    clear assumptions decoded target
    induction x generalizing ys with
    | nil => cases related; rfl
    | cons b bs ih =>
      cases related with
      | cons head tail =>
        simp only [valueRel] at head
        simp [head, ih _ tail]
  exact (valueToWords_eq_some h' x).mpr (same ▸ target)

end Flapjack.Compiler.Backend.ClosCall
