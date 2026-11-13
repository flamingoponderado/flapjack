import Flapjack.Compiler.Backend.ClosToBvl.Proofs.CommonCompiler
import Flapjack.Compiler.Backend.ClosCall.Proofs.Semantics
import Flapjack.Compiler.Backend.ClosCall.Proofs.LabelDistinct

open Flapjack Flapjack.Compiler.Backend
open BackendProps ClosSem ClosLang ClosProps


/-! Whole-program semantics for conditional direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Conditional direct-call conversion preserves whole-program behavior. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "semantics_cond_call_compile_inc"
  (fmap_as_finite_support_parameter_observations :=
    (map_parameters := [code])
    (map_producers := [Flapjack.HolFiniteMapExact.holEmpty, Flapjack.HolFiniteMapExact.alistToFmap]))]
theorem semanticsCondCallCompileInc {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (co : ClosSem.CompileOracle (NumSet × C)) (cc : ClosSem.Compiler C)
    (es es' : List ClosLang.Exp) (doCall : Bool) (g : NumSet)
    (aux : List (Nat × Nat × ClosLang.Exp))
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (h : ClosSem.semantics ffi maxApp HolFiniteMapExact.holEmpty co
        (closStateCc (ClosCall.condCallCompileInc doCall) cc) es ≠ .fail ∧
      ClosCall.compile doCall es = (es', g, aux) ∧
      code = HolFiniteMapExact.alistToFmap aux ∧
      (doCall = true → ClosCall.syntaxOk es ∧
        isStateOracle ClosCall.compileInc co ∧
        g = (co 0).1.1 ∧
        oracleMonotonic (fun entry => {x | x ∈ codeLocations entry.2.1}) (· < ·)
          {x | x ∈ codeLocations es} co ∧
        ∀ k, ClosCall.syntaxOk (co k).2.1 ∧ (co k).2.2 = [])) :
    ClosSem.semantics ffi maxApp code (stateCo (ClosCall.condCallCompileInc doCall) co) cc es' =
      ClosSem.semantics ffi maxApp HolFiniteMapExact.holEmpty co
        (closStateCc (ClosCall.condCallCompileInc doCall) cc) es := by
  rcases h with ⟨nonFail, compiled, rfl, enabled⟩
  cases doCall with
  | false =>
    simp only [ClosCall.compile, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at compiled
    obtain ⟨rfl, rfl, rfl⟩ := compiled
    change ClosSem.semantics ffi maxApp HolFiniteMapExact.holEmpty co (stateCc (fun s p => (s, p)) cc) es ≠ .fail at nonFail
    change ClosSem.semantics ffi maxApp (HolFiniteMapExact.alistToFmap [])
      (stateCo (fun s p => (s, p)) co) cc es =
      ClosSem.semantics ffi maxApp HolFiniteMapExact.holEmpty co
        (stateCc (fun s p => (s, p)) cc) es
    have emptyMap : HolFiniteMapExact.alistToFmap ([] : List (Nat × Nat × ClosLang.Exp)) =
        HolFiniteMapExact.holEmpty := by
      apply HolFiniteMapExact.ext_lookup
      intro key
      rfl
    rw [emptyMap]
    exact ClosProps.AdjustOracle.semanticsCurryI ffi maxApp HolFiniteMapExact.holEmpty co cc es nonFail
  | true =>
    have syn := (enabled rfl).1
    have run : ClosCall.calls es (.ln, []) = (es', g, aux) := by
      simpa [ClosCall.compile] using compiled
    have wellInit : ClosCall.wellFormed ((.ln : NumSet), ([] : List (Nat × Nat × ClosLang.Exp))) := by
      constructor
      · apply Set.ext
        intro x
        simp only [List.map_nil, List.not_mem_nil, Set.mem_ofPred_eq, false_iff]
        rintro ⟨n, hn, _⟩
        change (sptLookup n (.ln : NumSet)).isSome at hn
        simp [sptLookup] at hn
      · simp
    have well := ClosCall.calls_wellFormed es (.ln, []) es' (g, aux)
      ⟨run, syn.2.2, by simp, syn.1, wellInit⟩
    have mapEq : HolFiniteMapExact.holUpdateList HolFiniteMapExact.holEmpty aux =
        HolFiniteMapExact.alistToFmap aux := by
      rw [ClosCall.updateListCodec]
      exact (ClosCall.alistToFmapDistinct aux well.2).symm
    have bounds := ClosCall.calls_domainLocations es (.ln, []) es' (g, aux) run
    have inv : ClosCall.codeInv none {x | x ∈ codeLocations es} HolFiniteMapExact.holEmpty
        ((stateCc ClosCall.compileInc cc) : ClosSem.Compiler (NumSet × C)) co
        (HolFiniteMapExact.holUpdateList HolFiniteMapExact.holEmpty aux) cc
        (stateCo ClosCall.compileInc co) := by
      refine ⟨rfl, rfl, rfl, ⟨g, aux, well, (enabled rfl).2.2.1.symm, ?_, mapEq, by simp⟩,
        (enabled rfl).2.2.2.2⟩
      apply oracleMonotonic_subset _ _ _ _ _ _ _ ?_ (enabled rfl).2.2.2.1
      constructor
      · intro x hx
        rcases hx with hg | he
        · have hbound := bounds hg
          rcases hbound with empty | present
          · change (sptLookup x (.ln : NumSet)).isSome at empty
            simp [sptLookup] at empty
          · exact present
        · exact he
      · intro n x hx
        exact hx
    change ClosSem.semantics ffi maxApp HolFiniteMapExact.holEmpty co
      (stateCc ClosCall.compileInc cc) es ≠ .fail at nonFail
    change ClosSem.semantics ffi maxApp (HolFiniteMapExact.alistToFmap aux)
      (stateCo ClosCall.compileInc co) cc es' =
      ClosSem.semantics ffi maxApp HolFiniteMapExact.holEmpty co
        (stateCc ClosCall.compileInc cc) es
    have result := ClosCall.semanticsCompile ffi maxApp co (stateCc ClosCall.compileInc cc)
      es es' true g aux cc (stateCo ClosCall.compileInc co)
      ⟨nonFail,
       compiled, by simpa using And.intro syn (And.intro (enabled rfl).2.2.1 inv)⟩
    simpa [mapEq] using result


private def toBroad (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) := code.lookup
private def ofBroad (lookup : Nat → Option (Nat × ClosLang.Exp))
    (support : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact Nat (Nat × ClosLang.Exp) := ⟨lookup, support⟩

/-- The source code-map parameter has the canonical finite-support roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_semanticsCondCallCompileInc_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code := by
  cases code
  exact ⟨rfl, rfl, rfl⟩

end Flapjack.Compiler.Backend.ClosToBvl
