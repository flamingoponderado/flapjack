module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.OracleInvariant
public import Flapjack.Compiler.Backend.ClosCall.Proofs.SyntaxOk
public import Flapjack.Compiler.Backend.BackendProps.StateCompiler
public import Flapjack.Compiler.Backend.BackendProps.OracleMonotonic
public import Flapjack.FiniteMap.AlistExact

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Direct-call code and compiler-oracle invariant. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack BackendProps ClosProps

private def toBroad {K V : Type} (code : HolFiniteMapExact K V) : K → Option V := code.lookup
private def ofBroad {K V : Type} (lookup : K → Option V)
    (support : ∃ keys : List K, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact K V :=
  ⟨lookup, support⟩

/-- Canonical codec for the source code map. -/
theorem holFmapAsFiniteSupportParamWitness_codeInv_sCode
    (sCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad sCode) sCode.finiteSupport).lookup key = sCode.lookup key ∧
    (ofBroad (toBroad sCode) sCode.finiteSupport).finiteSupport = sCode.finiteSupport ∧
    ofBroad (toBroad sCode) sCode.finiteSupport = sCode := by
  cases sCode
  exact ⟨rfl, rfl, rfl⟩

/-- Canonical codec for the target code map. -/
theorem holFmapAsFiniteSupportParamWitness_codeInv_tCode {A : Type}
    (tCode : HolFiniteMapExact Nat A) (key : Nat) :
    (ofBroad (toBroad tCode) tCode.finiteSupport).lookup key = tCode.lookup key ∧
    (ofBroad (toBroad tCode) tCode.finiteSupport).finiteSupport = tCode.finiteSupport ∧
    ofBroad (toBroad tCode) tCode.finiteSupport = tCode := by
  cases tCode
  exact ⟨rfl, rfl, rfl⟩

/-- Relate code, compiler callbacks and oracle entries across direct-call conversion. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "code_inv_def" 2087
  (fmap_as_finite_support_parameters := [sCode, tCode])]
noncomputable def codeInv {A B D E Z H T G : Type}
    (gOpt : Option (NumSet × List (Nat × A))) (allowed : Set Nat)
    (sCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (sCc : NumSet × B → List ClosLang.Exp × G → Option (D × E × NumSet × Z))
    (sCo : Nat → (NumSet × H) × List ClosLang.Exp × List T)
    (tCode : HolFiniteMapExact Nat A)
    (tCc : B → List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp) → Option (D × E × Z))
    (tCo : Nat → H × List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)) : Prop :=
  sCode = HolFiniteMapExact.empty ∧
  sCc = stateCc compileInc tCc ∧
  tCo = stateCo compileInc sCo ∧
  (∃ g aux, wellFormed (g, aux) ∧ (sCo 0).1.1 = g ∧
    oracleMonotonic (fun entry => {x | x ∈ codeLocations entry.2.1}) (· < ·)
      (Set.union (sptDomain g) allowed) sCo ∧
    tCode = HolFiniteMapExact.alistToFmap aux ∧
    (gOpt.isSome → gOpt = some (g, aux))) ∧
  (∀ k, syntaxOk (sCo k).2.1 ∧ (sCo k).2.2 = [])

/-- Canonical codec for the source code map in the oracle-entry theorem. -/
theorem holFmapAsFiniteSupportParamWitness_codeInv_entry_sCode
    (sCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad sCode) sCode.finiteSupport).lookup key = sCode.lookup key ∧
    (ofBroad (toBroad sCode) sCode.finiteSupport).finiteSupport = sCode.finiteSupport ∧
    ofBroad (toBroad sCode) sCode.finiteSupport = sCode :=
  holFmapAsFiniteSupportParamWitness_codeInv_sCode sCode key

/-- Canonical codec for the target code map in the oracle-entry theorem. -/
theorem holFmapAsFiniteSupportParamWitness_codeInv_entry_tCode {A : Type}
    (tCode : HolFiniteMapExact Nat A) (key : Nat) :
    (ofBroad (toBroad tCode) tCode.finiteSupport).lookup key = tCode.lookup key ∧
    (ofBroad (toBroad tCode) tCode.finiteSupport).finiteSupport = tCode.finiteSupport ∧
    ofBroad (toBroad tCode) tCode.finiteSupport = tCode :=
  holFmapAsFiniteSupportParamWitness_codeInv_tCode tCode key

/-- Each source oracle entry has valid syntax and no auxiliary code. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "code_inv_k"
  (fmap_as_finite_support_parameters := [sCode, tCode])]
theorem codeInv_entry {A B D E Z H T G : Type}
    (gOpt : Option (NumSet × List (Nat × A))) (allowed : Set Nat)
    (sCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (sCc : NumSet × B → List ClosLang.Exp × G → Option (D × E × NumSet × Z))
    (sCo : Nat → (NumSet × H) × List ClosLang.Exp × List T)
    (tCode : HolFiniteMapExact Nat A)
    (tCc : B → List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp) → Option (D × E × Z))
    (tCo : Nat → H × List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)) (k : Nat)
    (h : codeInv gOpt allowed sCode sCc sCo tCode tCc tCo) :
    match sCo k with
    | (_, exp, aux) => syntaxOk exp ∧ aux = [] := by
  have entry := h.2.2.2.2 k
  cases found : sCo k with
  | mk config program =>
    cases program with
    | mk exp aux => simpa [found] using entry

end Flapjack.Compiler.Backend.ClosCall
