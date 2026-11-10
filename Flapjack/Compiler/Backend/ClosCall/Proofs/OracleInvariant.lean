module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.MakeState
public import Flapjack.Compiler.Backend.ClosCall.Proofs.StateExtension
public import Flapjack.Compiler.Backend.ClosCall.Compile
public import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLocations
public import Flapjack.Misc.ShiftSeq

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Direct-call compiler oracle invariant. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps

private def toBroad {K V : Type} (code : HolFiniteMapExact K V) : K → Option V := code.lookup
private def ofBroad {K V : Type} (lookup : K → Option V)
    (support : ∃ keys : List K, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact K V :=
  ⟨lookup, support⟩

/-- The oracle invariant's code map uses the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_oracleOk_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code := by
  cases code
  exact ⟨rfl, rfl, rfl⟩

/-- The first k oracle entries can be compiled with consistent state and code. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "co_ok_def"
  (fmap_as_finite_support_parameters := [code])]
noncomputable def oracleOk {A B : Type} (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (co : Nat → (NumSet × A) × List ClosLang.Exp × B) (fullGs : Nat → State) (k : Nat) : Prop :=
  if k = 0 then True else
    let g := (co 0).1.1
    let program := co 0
    let compiled := compileInc g (program.2.1, program.2.2)
    (co 1).1.1 = compiled.1 ∧
    makeState g code = some (fullGs 0) ∧
    (∀ i, stateExtends (fullGs 0) (fullGs i)) ∧
    (∀ x i, x ∈ codeLocations program.2.1 ∧ ¬ sptDomain compiled.1 x →
      ¬ sptDomain (co i).1.1 x) ∧
    (∀ x, ¬ (x ∈ codeLocations program.2.1 ∧ sptDomain g x)) ∧
    (∀ x, ¬ (x ∈ code.domain ∧ x ∈ compiled.2.2.map Prod.fst)) ∧
    (compiled.2.2.map Prod.fst).Nodup ∧
    oracleOk (code.updateListEq compiled.2.2) (holShiftSeq 1 co) (holShiftSeq 1 fullGs) (k - 1)
termination_by k
decreasing_by omega

end Flapjack.Compiler.Backend.ClosCall
