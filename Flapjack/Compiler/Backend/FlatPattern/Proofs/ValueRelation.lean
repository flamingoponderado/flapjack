module

public import Flapjack.Compiler.Backend.FlatPattern.Proofs.InstallRelation
public import Flapjack.Compiler.Backend.FlatPattern.Proofs.LookupRelation
public import Flapjack.Compiler.Backend.FlatProps.ValueBasics

@[expose] public section

/-! Value and environment relations for the flat pattern compiler. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Compiler.Backend.FlatSem Flapjack.Compiler.Backend.FlatProps

mutual
/-- Source value relation. The mutual environment rule expands option lookups
for positivity; source-shaped induction and case principles are proved in
`ValueRelationInduction`. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "v_rel"]
inductive ValueRel : Value → Value → Prop where
  | basic {left right} (shape : simpleBasicValRel left right)
      (contents : List.Forall₂ ValueRel (valueContainerXs left) (valueContainerXs right)) : ValueRel left right
  | closure {n left name body right cfg}
      (env : EnvRel n left right) (bound : (compileExp cfg body).1 < n) :
      ValueRel (.closure left name body) (.closure right name (compileDec cfg body))
  | recclosure {n left funs name right cfg}
      (env : EnvRel n left right)
      (bounds : ∀ entry ∈ funs, (compileExp cfg entry.2.2).1 < n) :
      ValueRel (.recclosure left funs name)
        (.recclosure right (funs.map fun (f, x, body) => (f, x, compileDec cfg body)) name)

/-- Bounded source environment relation, with equivalent explicit option
lookup cases for positivity. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "v_rel"]
inductive EnvRel : Nat → Environment Value → Environment Value → Prop where
  | intro {n left right}
      (domain : ∀ name, decNameToNum name < n →
        (holALookup left.v name).isSome = (holALookup right.v name).isSome)
      (lookup : ∀ name v v', decNameToNum name < n →
        holALookup left.v name = some v → holALookup right.v name = some v' → ValueRel v v') :
      EnvRel n left right
end

/-- The explicit domain and value premises are equivalent to the original
bounded association-list lookup relation. -/
theorem envRel_iff_lookup (n : Nat) (left right : Environment Value) :
    EnvRel n left right ↔ aLookupRel (fun name => decNameToNum name < n) ValueRel left.v right.v := by
  constructor
  · rintro ⟨domain, lookup⟩ name bound
    cases leftEq : holALookup left.v name with
    | none =>
      cases rightEq : holALookup right.v name with
      | none => trivial
      | some value =>
        have h := domain name bound
        simp [leftEq, rightEq] at h
    | some value =>
      cases rightEq : holALookup right.v name with
      | none =>
        have h := domain name bound
        simp [leftEq, rightEq] at h
      | some value' => exact lookup name value value' bound leftEq rightEq
  · intro related
    constructor
    · intro name bound
      have h := related name bound
      cases leftEq : holALookup left.v name <;> cases rightEq : holALookup right.v name <;>
        simp_all [optionRel]
    · intro name v v' bound leftEq rightEq
      have h := related name bound
      simpa [leftEq, rightEq, optionRel] using h

end Flapjack.Compiler.Backend.FlatPattern
