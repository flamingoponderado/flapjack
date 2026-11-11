module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.CallsCorrect
public import Flapjack.FiniteMap.EmptyExact
public import Flapjack.FiniteMap.UpdateListExact
public import Flapjack.Compiler.Backend.ClosCall.Proofs.OracleInvariant
public import Flapjack.Compiler.Backend.Semantics.ClosSem.SemanticsRelated
public import Flapjack.Compiler.Backend.Semantics.ClosProps.AdjustOracleSimulation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Whole-program semantics for direct-call closure conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem ClosLang ClosProps SemanticPrimitivesHOL SemanticPrimitivesProps

/-- HOL uses distinct-key updates to identify the two code-map constructions; this local codec fact packages that calculation. -/
private theorem alistToFmapDistinct {K V : Type} [DecidableEq K] (xs : List (K × V))
    (distinct : (xs.map Prod.fst).Nodup) :
    HolFiniteMapExact.alistToFmap xs = HolFiniteMapExact.empty.updateListEq xs := by
  have decEq : (inferInstance : DecidableEq K) = Classical.typeDecidableEq K := Subsingleton.elim _ _
  cases decEq
  classical
  apply HolFiniteMapExact.ext_lookup
  intro key
  simp only [HolFiniteMapExact.alistToFmap, HolFiniteMapExact.lookup_updateListEq]
  rw [InstallSimulation.updateList_reverse_distinct _ xs distinct]

/-- HOL derives this initialized code invariant inline from the compiled state and its oracle invariant. -/
private theorem initialCodeInvariant {C : Type} (xs : List ClosLang.Exp)
    (known : NumSet) (aux : List (Nat × Nat × ClosLang.Exp))
    (co : ClosSem.CompileOracle (NumSet × C)) (cc : ClosSem.Compiler (NumSet × C))
    (co1 : ClosSem.CompileOracle C) (cc1 : ClosSem.Compiler C)
    (well : wellFormed (known, aux)) (knownEq : (co 0).1.1 = known)
    (inv : codeInv none {x | x ∈ codeLocations xs} HolFiniteMapExact.empty cc co
      (HolFiniteMapExact.empty.updateListEq aux) cc1 co1) :
    codeInv (some (known, aux)) ({x | x ∈ codeLocations xs} \ sptDomain known)
      HolFiniteMapExact.empty cc co (HolFiniteMapExact.empty.updateListEq aux) cc1 co1 := by
  obtain ⟨empty, compiler, oracle, ⟨oldKnown, oldAux, oldWell, first, ordered, code, _⟩, syntaxFacts⟩ := inv
  refine ⟨empty, compiler, oracle, ?_, syntaxFacts⟩
  refine ⟨known, aux, well, knownEq, ?_, ?_, by simp⟩
  · have equalKnown : oldKnown = known := first.symm.trans knownEq
    subst oldKnown
    apply BackendProps.oracleMonotonic_subset _ _ _ _ _ _ _ ?_ ordered
    constructor
    · intro x hx
      rcases hx with left | right
      · exact Or.inl (by simpa [knownEq] using left)
      · exact Or.inr right.1
    · intro n x hx
      exact hx
  · exact (alistToFmapDistinct aux well.2).symm
/-- HOL derives code inclusion inline from distinct auxiliary labels and finite-map lookup. -/
private theorem initialCodeIncludes (aux : List (Nat × Nat × ClosLang.Exp))
    (well : (aux.map Prod.fst).Nodup) :
    codeIncludes aux (HolFiniteMapExact.empty.updateListEq aux) := by
  rw [← alistToFmapDistinct aux well]
  intro key value found
  rw [alistToFmapLookup]
  exact found
/-- Flapjack codec infrastructure equating the two canonical update operations at numeric keys. -/
private theorem updateListCodec {V : Type} (xs : List (Nat × V)) :
    HolFiniteMapExact.holUpdateList HolFiniteMapExact.holEmpty xs = HolFiniteMapExact.empty.updateListEq xs := by
  change @HolFiniteMapExact.updateListEq Nat V (Classical.typeDecidableEq Nat) HolFiniteMapExact.empty xs =
    @HolFiniteMapExact.updateListEq Nat V instDecidableEqNat HolFiniteMapExact.empty xs
  congr 1
  exact Subsingleton.elim _ _

/-- Direct-call conversion preserves whole-program behavior under the HOL hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "semantics_calls"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty, Flapjack.HolFiniteMapExact.holUpdateList])]
theorem semanticsCalls {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (co : ClosSem.CompileOracle (NumSet × C)) (cc : ClosSem.Compiler (NumSet × C))
    (xs ys : List ClosLang.Exp) (known : NumSet) (aux : List (Nat × Nat × ClosLang.Exp))
    (cc1 : ClosSem.Compiler C) (co1 : ClosSem.CompileOracle C)
    (nonFail : ClosSem.semantics ffi maxApp HolFiniteMapExact.holEmpty co cc xs ≠ .fail)
    (h : compile true xs = (ys, known, aux) ∧ everyFnLocationSome xs ∧ everyFnVarsNone xs ∧
      (codeLocations xs).Nodup ∧ (co 0).1.1 = known ∧
      codeInv none {x | x ∈ codeLocations xs} HolFiniteMapExact.holEmpty cc co
        (HolFiniteMapExact.holUpdateList HolFiniteMapExact.holEmpty aux) cc1 co1) :
    ClosSem.semantics ffi maxApp (HolFiniteMapExact.holUpdateList HolFiniteMapExact.holEmpty aux) co1 cc1 ys =
      ClosSem.semantics ffi maxApp HolFiniteMapExact.holEmpty co cc xs := by
  rw [updateListCodec aux, HolFiniteMapExact.holEmpty] at *
  obtain ⟨compiled, annotations, noVars, distinct, knownEq, inv⟩ := h
  have callsRun : calls xs (.ln, []) = (ys, known, aux) := by simpa [compile] using compiled
  have initialWell : wellFormed ((.ln : NumSet), ([] : List (Nat × Nat × ClosLang.Exp))) := by
    constructor
    · apply Set.ext
      intro x
      simp only [List.map_nil, List.not_mem_nil, Set.mem_ofPred_eq, false_iff]
      rintro ⟨n, hn, _⟩
      change (sptLookup n (.ln : NumSet)).isSome at hn
      simp [sptLookup] at hn
    · simp
  have finalWell : wellFormed (known, aux) := calls_wellFormed xs (.ln, []) ys (known, aux)
    ⟨callsRun, distinct, by simp, annotations, initialWell⟩
  let allowed := {x | x ∈ codeLocations xs} \ sptDomain known
  have inv' := initialCodeInvariant xs known aux co cc co1 cc1 finalWell knownEq inv
  have safe := (ClosSem.semantics_ne_fail_iff ffi maxApp HolFiniteMapExact.empty co cc xs).mp nonFail
  symm
  apply ClosSem.semantics_eq_of_related_clocked_simulation ffi maxApp HolFiniteMapExact.empty
    (HolFiniteMapExact.empty.updateListEq aux) co co1 cc cc1 xs ys safe
  intro clock result final run
  let source := ClosSem.initialState ffi maxApp HolFiniteMapExact.empty co cc clock
  let target := ClosSem.initialState ffi maxApp (HolFiniteMapExact.empty.updateListEq aux) co1 cc1 clock
  have invariant : codeInv (some (known, aux)) allowed source.code source.compile source.compileOracle
      target.code target.compile target.compileOracle := by simpa [source, target, allowed, ClosSem.initialState] using inv'
  have stateWell : stateValuesWellFormed (known, aux) allowed target.code source := by
    simp [source, target, stateValuesWellFormed, ClosSem.initialState, HolFiniteMapExact.empty]
  have stateRel' : stateRel (known, aux) allowed source target := by
    simp [source, target, stateRel, ClosSem.initialState, HolFiniteMapExact.empty, optionRel]
  have emptyEnv : envRel (valueRel (known, aux) allowed target.code) [] [] 0 (ys.map (fun e => (0, e))) := by
    simp [envRel]
  have disjoint : Disjoint allowed (sptDomain known) := by
    apply Set.disjoint_left.mpr
    intro n hn hd
    exact hn.2 hd
  have included := initialCodeIncludes aux finalWell.2
  have safeResult : result ≠ .err (.abort .typeError) := by simpa [run] using safe clock
  obtain ⟨extra, targetResult, targetFinal, _, _, _, _, _, _, _, _, _, targetRun, targetStates, related⟩ :=
    callsCorrect.1 (xs, [], source) xs [] source (.ln, []) (known, aux) [] target ys result final allowed allowed
      (known, aux) ⟨rfl, run, safeResult, callsRun, invariant, annotations, noVars, by simp, stateWell,
        initialWell, distinct, by simp, rfl, wfg_subg_refl (known, aux) finalWell,
        Set.Subset.rfl, disjoint, finalWell, emptyEnv, stateRel', included⟩
  have observations := ClosSem.resultRelOutcome _ _ result targetResult related
  refine ⟨extra, targetResult, targetFinal, ?_, observations.1, observations.2, targetStates.1⟩
  simpa [target, ClosSem.initialState, Nat.add_assoc] using targetRun
/-- Direct-call compilation, enabled or disabled, preserves whole-program behavior. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "semantics_compile"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty, Flapjack.HolFiniteMapExact.holUpdateList])]
theorem semanticsCompile {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (co : ClosSem.CompileOracle (NumSet × C)) (cc : ClosSem.Compiler (NumSet × C))
    (xs ys : List ClosLang.Exp) (enabled : Bool) (known : NumSet)
    (aux : List (Nat × Nat × ClosLang.Exp)) (cc1 : ClosSem.Compiler C) (co1 : ClosSem.CompileOracle C)
    (h : ClosSem.semantics ffi maxApp HolFiniteMapExact.holEmpty co cc xs ≠ .fail ∧
      compile enabled xs = (ys, known, aux) ∧
      (if enabled then syntaxOk xs ∧ known = (co 0).1.1 ∧
        codeInv none {x | x ∈ codeLocations xs} HolFiniteMapExact.holEmpty cc co
          (HolFiniteMapExact.holUpdateList HolFiniteMapExact.holEmpty aux) cc1 co1
       else cc = BackendProps.stateCc (fun s p => (s, p)) cc1 ∧
         co1 = BackendProps.stateCo (fun s p => (s, p)) co)) :
    ClosSem.semantics ffi maxApp (HolFiniteMapExact.holUpdateList HolFiniteMapExact.holEmpty aux) co1 cc1 ys =
      ClosSem.semantics ffi maxApp HolFiniteMapExact.holEmpty co cc xs := by
  rw [updateListCodec aux, HolFiniteMapExact.holEmpty] at *
  obtain ⟨nonFail, compiled, condition⟩ := h
  cases enabled with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at condition
    obtain ⟨rfl, rfl⟩ := condition
    simp [compile] at compiled
    obtain ⟨rfl, rfl, rfl⟩ := compiled
    simpa [HolFiniteMapExact.updateListEq] using
      ClosProps.AdjustOracle.semanticsCurryI ffi maxApp HolFiniteMapExact.empty co cc1 xs nonFail
  | true =>
    simp only [↓reduceIte] at condition
    obtain ⟨⟨annotations, noVars, distinct⟩, knownEq, inv⟩ := condition
    have inv' : codeInv none {x | x ∈ codeLocations xs} HolFiniteMapExact.holEmpty cc co
        (HolFiniteMapExact.holUpdateList HolFiniteMapExact.holEmpty aux) cc1 co1 := by
      rw [updateListCodec aux, HolFiniteMapExact.holEmpty]
      exact inv
    have result := semanticsCalls ffi maxApp co cc xs ys known aux cc1 co1 nonFail
      ⟨compiled, annotations, noVars, distinct, knownEq.symm, inv'⟩
    rw [updateListCodec aux, HolFiniteMapExact.holEmpty] at result
    exact result
end Flapjack.Compiler.Backend.ClosCall
