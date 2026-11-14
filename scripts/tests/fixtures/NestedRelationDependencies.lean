import Flapjack.HolRef

/-! Isolated negative and positive tests of resolved nested-relation dependencies.
Run with `lake lean scripts/tests/fixtures/NestedRelationDependencies.lean`.
The deliberately minimal mock relations must not be imported by production. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate

inductive FunctionsRel : Prop where
  | intro : FunctionsRel

inductive ValueRel : Prop where
  | simple : ValueRel
  | nested : FunctionsRel → ValueRel

inductive EnvOk : Prop where
  | intro : EnvOk

def StateRel : Prop := EnvOk
abbrev HiddenFunctionsRel : Prop := FunctionsRel
structure Packed where
  rel : FunctionsRel

inductive Cycle where
  | next : Cycle → Cycle
  | hidden : FunctionsRel → Cycle

mutual
inductive CycleA where
  | next : CycleB → CycleA
inductive CycleB where
  | next : CycleA → CycleB
  | hidden : FunctionsRel → CycleB
end

mutual
inductive QuietA where
  | next : QuietB → QuietA
inductive QuietB where
  | next : QuietA → QuietB
end

def UsesCycle := Cycle
structure Shared where
  count : Nat
structure WithShared where
  shared : Shared
  hidden : FunctionsRel
structure WithQuietCycle where
  quiet : QuietA
  hidden : FunctionsRel

theorem functionType : FunctionsRel = FunctionsRel := rfl

@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "env_set_default"
  (nested_list_rel_as_mutual := [FunctionsRel])]
theorem validIndirect : StateRel → True := by intro _; trivial

@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "env_set_default"
  (nested_list_rel_as_mutual := [FunctionsRel])]
theorem validDirect : ValueRel → True := by intro _; trivial

@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "env_set_default"
  (nested_list_rel_as_mutual := [FunctionsRel]) (fmap_as_finite_support := [refs, code])]
theorem combinedObserver : EnvOk → True := by intro _; trivial

/-- error: Flapjack.Compiler.Backend.ClosAnnotate.ValueRel: nested-list relation producers cannot combine finite-map qualifiers -/
#guard_msgs in
attribute [hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "v_rel"
  (nested_list_rel_as_mutual := [FunctionsRel]) (fmap_as_finite_support := [refs, code])] ValueRel

/-- error: @[hol]: nested_list_rel_as_mutual cannot combine with other qualifiers -/
#guard_msgs in
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "env_set_default"
  (nested_list_rel_as_mutual := [FunctionsRel]) (words_as_type_indexed_bitvec)]
theorem combinedWords : EnvOk → True := by intro _; trivial

/-- error: @[hol]: nested_list_rel_as_mutual cannot combine with other qualifiers -/
#guard_msgs in
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "env_set_default"
  (nested_list_rel_as_mutual := [FunctionsRel]) (fmap_as_finite_support_relation := [State.refs])]
theorem combinedMapRelation : EnvOk → True := by intro _; trivial

/-- error: Flapjack.Compiler.Backend.ClosAnnotate.badThunkSite: nested relation and finite-map witnesses are restricted to the reviewed thunk update -/
#guard_msgs in
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "rel_update_thunk"
  (nested_list_rel_as_mutual := [FunctionsRel])
  (fmap_as_finite_support_relation := [State.refs, State.code, sourceRefs])
  (fmap_as_finite_support_existentials := [targetRefs])]
theorem badThunkSite : ValueRel → True := by intro _; trivial

/-- error: @[hol]: nested_list_rel_as_mutual cannot combine with other qualifiers -/
#guard_msgs in
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "rel_update_thunk"
  (nested_list_rel_as_mutual := [FunctionsRel])
  (fmap_as_finite_support_relation := [State.code, State.refs, sourceRefs])
  (fmap_as_finite_support_existentials := [targetRefs])]
theorem reorderedThunkMaps : ValueRel → True := by intro _; trivial

/-- error: @[hol]: nested_list_rel_as_mutual cannot combine with other qualifiers -/
#guard_msgs in
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "rel_update_thunk"
  (nested_list_rel_as_mutual := [FunctionsRel])
  (fmap_as_finite_support_relation := [State.refs, State.code, sourceRefs])]
theorem missingThunkWitness : ValueRel → True := by intro _; trivial

/-- error: @[hol]: nested_list_rel_as_mutual cannot combine with other qualifiers -/
#guard_msgs in
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "rel_update_thunk"
  (nested_list_rel_as_mutual := [FunctionsRel])
  (fmap_as_finite_support_relation := [State.refs, State.code, sourceRefs])
  (fmap_as_finite_support_existentials := [targetRefs]) (words_as_type_indexed_bitvec)]
theorem extraThunkQualifier : ValueRel → True := by intro _; trivial

/-- error: @[hol]: nested_list_rel_as_mutual cannot combine with other qualifiers -/
#guard_msgs in
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "rel_update_thunk"
  (nested_list_rel_as_mutual := [FunctionsRel])
  (fmap_as_finite_support_relation := [State.refs, State.code, sourceRefs])
  (fmap_as_finite_support_existentials := [targetRefs])]
theorem wrongThunkSource : ValueRel → True := by intro _; trivial

/-- error: @[hol]: nested_list_rel_as_mutual cannot combine with other qualifiers -/
#guard_msgs in
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "rel_update_thunk"
  (nested_list_rel_as_mutual := [FunctionsRel])
  (fmap_as_finite_support_relation := [State.refs, State.code, sourceRefs])
  (fmap_as_finite_support_existentials := [targetRefs]) (reals_as_rational_cuts)]
theorem realThunkQualifier : ValueRel → True := by intro _; trivial

/-- error: @[hol]: nested_list_rel_as_mutual cannot combine with other qualifiers -/
#guard_msgs in
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "env_set_default"
  (nested_list_rel_as_mutual := [FunctionsRel]) (fmap_as_finite_support := [refs])]
theorem incompleteMapFields : EnvOk → True := by intro _; trivial

/-- error: Flapjack.Compiler.Backend.ClosAnnotate.missing: tagged nested-list observer requires nested_list_rel_as_mutual -/
#guard_msgs in
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "env_set_default"]
theorem missing : StateRel → True := by intro _; trivial

/-- error: Flapjack.Compiler.Backend.ClosAnnotate.hidden: nested-list observer must use ValueRel or EnvOk without exposing FunctionsRel -/
#guard_msgs in
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "env_set_default"
  (nested_list_rel_as_mutual := [FunctionsRel])]
theorem hidden : EnvOk → HiddenFunctionsRel → True := by intro _ _; trivial

/-- error: Flapjack.Compiler.Backend.ClosAnnotate.constructor: nested-list observer must use ValueRel or EnvOk without exposing FunctionsRel -/
#guard_msgs in
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "env_set_default"
  (nested_list_rel_as_mutual := [FunctionsRel])]
theorem constructor : EnvOk → ValueRel.nested FunctionsRel.intro = ValueRel.simple → True := by
  intro _ _; trivial

/-- error: Flapjack.Compiler.Backend.ClosAnnotate.recursor: nested-list observer must use ValueRel or EnvOk without exposing FunctionsRel -/
#guard_msgs in
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "env_set_default"
  (nested_list_rel_as_mutual := [FunctionsRel])]
theorem recursor : EnvOk →
    ValueRel.rec (motive := fun _ => True) trivial (fun _ => trivial) ValueRel.simple = trivial → True := by
  intro _ _; trivial

/-- error: Flapjack.Compiler.Backend.ClosAnnotate.packed: tagged nested-list observer requires nested_list_rel_as_mutual -/
#guard_msgs in
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "env_set_default"]
theorem packed : Packed → True := by intro _; trivial

/-- error: Flapjack.Compiler.Backend.ClosAnnotate.packedQualified: nested-list observer must use ValueRel or EnvOk without exposing FunctionsRel -/
#guard_msgs in
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "env_set_default"
  (nested_list_rel_as_mutual := [FunctionsRel])]
theorem packedQualified : EnvOk → Packed → True := by intro _ _; trivial

/-- error: Flapjack.Compiler.Backend.ClosAnnotate.theoremDependency: tagged nested-list observer requires nested_list_rel_as_mutual -/
#guard_msgs in
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "env_set_default"]
theorem theoremDependency : (0 : Nat) = cast (congrArg (fun _ : Prop => Nat) functionType) 0 → True := by
  intro _; trivial

/-- error: Flapjack.Compiler.Backend.ClosAnnotate.theoremDependencyQualified: nested-list observer must use ValueRel or EnvOk without exposing FunctionsRel -/
#guard_msgs in
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "env_set_default"
  (nested_list_rel_as_mutual := [FunctionsRel])]
theorem theoremDependencyQualified : EnvOk →
    (0 : Nat) = cast (congrArg (fun _ : Prop => Nat) functionType) 0 → True := by
  intro _ _; trivial

/-- error: Flapjack.Compiler.Backend.ClosAnnotate.wrongProducer: v_rel qualifier is restricted to the reviewed relation members -/
#guard_msgs in
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "v_rel"
  (nested_list_rel_as_mutual := [FunctionsRel])]
theorem wrongProducer : EnvOk → True := by intro _; trivial

/-- error: Flapjack.Compiler.Backend.ClosAnnotate.wrongPath: nested-list observer must use ValueRel or EnvOk without exposing FunctionsRel -/
#guard_msgs in
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "env_set_default"
  (nested_list_rel_as_mutual := [FunctionsRel])]
theorem wrongPath : EnvOk → True := by intro _; trivial

end Flapjack.Compiler.Backend.ClosAnnotate

namespace Flapjack.Compiler.Backend.ClosToBvl
inductive ValueRel : Prop where | intro : ValueRel

@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "env_set_default"]
theorem otherRelation : ValueRel → True := by intro _; trivial

/-- error: Flapjack.Compiler.Backend.ClosToBvl.outOfScope: nested-list observer must use ValueRel or EnvOk without exposing FunctionsRel -/
#guard_msgs in
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "env_set_default"
  (nested_list_rel_as_mutual := [FunctionsRel])]
theorem outOfScope : ClosAnnotate.EnvOk → True := by intro _; trivial
end Flapjack.Compiler.Backend.ClosToBvl

open Lean Elab Command Flapjack
run_cmd do
  let env ← getEnv
  let roots := #[
    (``Compiler.Backend.ClosAnnotate.Shared, (false, false)),
    (``Compiler.Backend.ClosAnnotate.WithShared, (false, true)),
    (``Compiler.Backend.ClosAnnotate.WithQuietCycle, (false, true)),
    (``Compiler.Backend.ClosAnnotate.QuietA, (false, false)),
    (``Compiler.Backend.ClosAnnotate.QuietB, (false, false)),
    (``Compiler.Backend.ClosAnnotate.StateRel, (true, false)),
    (``Compiler.Backend.ClosAnnotate.Packed, (false, true)),
    (``Compiler.Backend.ClosAnnotate.Cycle, (false, true)),
    (``Compiler.Backend.ClosAnnotate.Cycle.next, (false, true)),
    (``Compiler.Backend.ClosAnnotate.UsesCycle, (false, true)),
    (``Compiler.Backend.ClosAnnotate.CycleA, (false, true)),
    (``Compiler.Backend.ClosAnnotate.CycleB, (false, true)),
    (``Compiler.Backend.ClosAnnotate.HiddenFunctionsRel, (false, true)),
    (``Compiler.Backend.ClosToBvl.ValueRel, (false, false))]
  for ordered in #[roots, roots.reverse] do
    let mut cache : Std.HashMap Name (Bool × Bool) := {}
    for (name, expected) in ordered do
      let some info := env.find? name | throwError "missing fixture declaration {name}"
      let (actual, next) := nestedListRelationDependenciesCached env info cache
      unless actual == expected && actual == nestedListRelationDependencies env info do
        throwError "incorrect cached nested-list dependency for {name}"
      cache := next
