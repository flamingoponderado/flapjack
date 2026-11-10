module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.RecClosure
public import Flapjack.Compiler.Backend.ClosCall.Proofs.CodeIncludes
public import Flapjack.Compiler.Backend.ClosCall.Compile

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Recursive-closure relation for direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps

private def toBroad {K V : Type} (code : HolFiniteMapExact K V) : K → Option V := code.lookup
private def ofBroad {K V : Type} (lookup : K → Option V)
    (support : ∃ keys : List K, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact K V :=
  ⟨lookup, support⟩

/-- Canonical finite-map codec for the recursive-closure code parameter. -/
theorem holFmapAsFiniteSupportParamWitness_recClosureRel_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code := by
  cases code
  exact ⟨rfl, rfl, rfl⟩

/-- The direct-call pass relates original recursive groups to their generated
functions and records the required compiler state and installed code. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "recclosure_rel_def"
  (fmap_as_finite_support_parameters := [code])]
noncomputable def recClosureRel (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (fns1 fns2 : List (Nat × ClosLang.Exp)) : Prop := by
  classical
  exact ∃ g0 : State,
    recClosureWellFormed loc fns1 ∧ wellFormed g0 ∧
    (∀ label, ¬ (label ∈ Set.image Nat.succ {n | n ∈ codeLocations (fns1.map Prod.snd)} ∧
      label ∈ g0.2.map Prod.fst)) ∧
    (∀ label, ¬ (label ∈ (List.range fns1.length).map (fun i => 2 * i + loc + 1) ∧
      label ∈ g0.2.map Prod.fst)) ∧
    let (es, next) := calls (fns1.map Prod.snd) (insertEachSource loc fns1.length g0)
    if List.Forall₂ (fun fn body => ∀ v, DbVars.hasVar v (free [body]).2 = true → v < fn.1)
        fns1 es then
      (∃ tra n, fns2 = callsListSource tra n loc fns1) ∧
      stateExtends (codeListSource loc ((fns1.map Prod.fst).zip es) next) g ∧
      ({n | n ∈ codeLocations (fns1.map Prod.snd)} \ sptDomain next.1) ⊆ allowed ∧
      codeIncludes (codeListSource loc ((fns1.map Prod.fst).zip es) next).2 code
    else
      let (es, next) := calls (fns1.map Prod.snd) g0
      fns2 = (fns1.map Prod.fst).zip es ∧ stateExtends next g ∧
      ({n | n ∈ codeLocations (fns1.map Prod.snd)} \ sptDomain next.1) ⊆ allowed ∧
      {n | n ∈ (List.range fns1.length).map (fun i => 2 * i + loc)} ⊆ allowed ∧
      codeIncludes next.2 code

end Flapjack.Compiler.Backend.ClosCall
