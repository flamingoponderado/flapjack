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

end Flapjack.Compiler.Backend.ClosCall
