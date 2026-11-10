module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ChainInstalled
public import Flapjack.Compiler.Backend.Semantics.ClosSem.SemanticsRelated
public import Flapjack.Compiler.Backend.Semantics.ClosSem.CodeExtensionEvaluate
public import Flapjack.FiniteMap.UnionExact
public import Flapjack.FiniteMap.AlistExact.Lookup
@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Whole-program semantics of the closure entry-point chain. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack ClosSem ClosProps BackendProps SemanticPrimitivesHOL SemanticPrimitivesProps

private theorem lookup_none_not_mem {V : Type} (entries : List (Nat × V)) (key : Nat)
    (absent : key ∉ entries.map Prod.fst) :
    (HolFiniteMapExact.alistToFmap entries).lookup key = none := by
  induction entries with
  | nil => simp [HolFiniteMapExact.alistToFmap, HolFiniteMapExact.empty]
  | cons entry rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at absent
    rw [HolFiniteMapExact.lookup_alistToFmap_tail entry rest key absent.1]
    exact ih absent.2

private theorem chain_domain_subset (start : Nat) (es : List ClosLang.Exp) (nonempty : es ≠ []) :
    (HolFiniteMapExact.alistToFmap (chainExps start es)).domain ⊆
      (fun i => start + i) '' {i | i < es.length} := by
  intro key member
  by_contra outside
  have notmem : key ∉ (chainExps start es).map Prod.fst := by
    rw [mapFst_chainExps_any]
    intro h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
    apply outside
    refine ⟨i, ?_, rfl⟩
    have len : 1 ≤ es.length := by cases es <;> simp_all
    simpa [Nat.max_eq_right len] using List.mem_range.mp hi
  have none := lookup_none_not_mem _ key notmem
  exact member none

private theorem chain_union_extension (start : Nat) (es : List ClosLang.Exp) (nonempty : es ≠ [])
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (disjoint : Disjoint ((fun i => start + i) '' {i | i < es.length}) code.domain) :
    code.submap ((HolFiniteMapExact.alistToFmap (chainExps start es)).union code) := by
  intro key value found
  have domain : key ∈ code.domain := by simp [HolFiniteMapExact.domain, found]
  have outside : key ∉ (HolFiniteMapExact.alistToFmap (chainExps start es)).domain := by
    intro member
    exact (Set.disjoint_left.mp disjoint) (chain_domain_subset start es nonempty member) domain
  have none : (HolFiniteMapExact.alistToFmap (chainExps start es)).lookup key = none := by
    by_contra ne
    exact outside ne
  simp [HolFiniteMapExact.lookup_union, none, found]

private theorem chain_union_installed (start : Nat) (es : List ClosLang.Exp)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) :
    chainInstalled start es ((HolFiniteMapExact.alistToFmap (chainExps start es)).union code) := by
  apply chainInstalled_submap start es _ _
  constructor
  · exact chainInstalled_chainExps start es
  · intro key value found
    simp [HolFiniteMapExact.lookup_union, found]

private theorem chain_union_domain (start : Nat) (es : List ClosLang.Exp) (nonempty : es ≠ [])
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) :
    ((HolFiniteMapExact.alistToFmap (chainExps start es)).union code).domain ⊆
      ((fun i => start + i) '' {i | i < es.length}) ∪ code.domain := by
  intro key member
  change ((HolFiniteMapExact.alistToFmap (chainExps start es)).union code).lookup key ≠ none at member
  rw [HolFiniteMapExact.union_defined_iff] at member
  rcases member with left | right
  · exact Or.inl (chain_domain_subset start es nonempty left)
  · exact Or.inr right

private theorem chain_initial_extension {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (es : List ClosLang.Exp) (start clock : Nat)
    (nonempty : es ≠ [])
    (disjoint : Disjoint ((fun i => start + i) '' {i | i < es.length}) code.domain)
    (ordered : oracleMonotonic oracleCodeNames (· < ·)
      (((fun i => start + i) '' {i | i < es.length}) ∪ code.domain) oracle) :
    CodeExtension (initialState ffi maxApp code oracle compiler clock)
      (initialState ffi maxApp ((HolFiniteMapExact.alistToFmap (chainExps start es)).union code)
        oracle compiler clock) := by
  refine ⟨rfl, chain_union_extension start es nonempty code disjoint, ?_⟩
  exact oracleMonotonic_subset _ _ _ _ _ _ _
    ⟨chain_union_domain start es nonempty code, fun _ => Set.Subset.rfl⟩ ordered

private theorem chain_semantics_nonempty {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (es : List ClosLang.Exp) (start : Nat)
    (nonempty : es ≠ [])
    (safe : semantics ffi maxApp code oracle compiler es ≠ .fail)
    (disjoint : Disjoint ((fun i => start + i) '' {i | i < es.length}) code.domain)
    (ordered : oracleMonotonic oracleCodeNames (· < ·)
      (((fun i => start + i) '' {i | i < es.length}) ∪ code.domain) oracle) :
    ∃ body, semantics ffi maxApp ((HolFiniteMapExact.alistToFmap (chainExps start es)).union code)
        oracle compiler [body] = semantics ffi maxApp code oracle compiler es ∧
      holALookup (chainExps start es) start = some (0, body) := by
  let targetCode := (HolFiniteMapExact.alistToFmap (chainExps start es)).union code
  obtain ⟨body, chain⟩ := Chain.chainInstalled_thm (C := C) (F := F) (A := Unit) es start
  have installed : chainInstalled start es targetCode := chain_union_installed start es code
  have safeAll := (semantics_ne_fail_iff ffi maxApp code oracle compiler es).mp safe
  have lookup : holALookup (chainExps start es) start = some (0, body) := by
    cases es with
    | nil => exact (nonempty rfl).elim
    | cons first rest =>
      let state := initialState ffi maxApp targetCode oracle compiler 0
      let result := (evaluate (first :: rest) [] state).1
      let final := (evaluate (first :: rest) [] state).2
      have run : evaluate (first :: rest) [] state = (result, final) := by
        exact (Prod.eta _).symm
      obtain ⟨_, _, _, found, _, _, _⟩ := chain state () result final ⟨installed, run, by simp⟩
      have expected := ((chainInstalled_cons start first rest targetCode).mp installed).1
      have same := Option.some.inj (found.symm.trans expected)
      have bodyEq := congrArg Prod.snd same
      simp only at bodyEq
      subst body
      cases rest <;> simp [chainExps, holALookup]
  refine ⟨body, ?_, lookup⟩
  symm
  apply semantics_eq_of_related_clocked_simulation ffi maxApp code targetCode oracle oracle compiler compiler es [body] safeAll
  intro clock result final run
  have noType : result ≠ .err (.abort .typeError) := by
    have h := safeAll clock
    rw [run] at h
    exact h
  have related : CodeExtension (initialState ffi maxApp code oracle compiler clock)
      (initialState ffi maxApp targetCode oracle compiler clock) :=
    chain_initial_extension ffi maxApp code oracle compiler es start clock nonempty disjoint ordered
  obtain ⟨middle, midRun, midRel⟩ :=
    (evaluate_codeExtension (C := C) (F := F)).1 es _ [] _ result final run noType related
  obtain ⟨extra, targetResult, targetFinal, found, targetRun, resultRel, ffiEq⟩ :=
    chain (initialState ffi maxApp targetCode oracle compiler clock) () result middle
      ⟨installed, midRun, by cases es <;> simp_all⟩
  have outcomes := resultRelOutcome (fun _ _ => True) (fun _ _ => True) targetResult result resultRel
  refine ⟨extra, targetResult, targetFinal, ?_, outcomes.1.symm, outcomes.2.symm, ?_⟩
  · simpa [initialState] using targetRun
  · have eqFfi : final.ffi = middle.ffi := by rw [midRel.1]
    exact eqFfi.trans ffiEq

private theorem chain_semantics_empty {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat) :
    ∃ body, semantics ffi maxApp ((HolFiniteMapExact.alistToFmap (chainExps start [])).union code)
        oracle compiler [body] = semantics ffi maxApp code oracle compiler [] ∧
      holALookup (chainExps start []) start = some (0, body) := by
  refine ⟨.op .none (.intOp (.const 0)) [], ?_, by simp [chainExps, holALookup]⟩
  apply semantics_eq_of_related_evaluations
  intro clock
  simp [evaluate, fixClock, doApp, applyNumeric, doIntApp, resultOutcome, initialState]

/-- Executing an installed generated chain has the original program behavior. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "chain_exps_semantics"
  (fmap_as_finite_support_parameter_observations :=
    (map_parameters := [code])
    (map_producers := [Flapjack.HolFiniteMapExact.alistToFmap, Flapjack.HolFiniteMapExact.union]))]
theorem chainExps_semantics {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (es : List ClosLang.Exp) (start : Nat)
    (premises : semantics ffi maxApp code oracle compiler es ≠ .fail ∧
      (∀ x, ¬ (x ∈ ((fun i => start + i) '' {i | i < es.length}) ∧ x ∈ code.domain)) ∧
      oracleMonotonic oracleCodeNames (· < ·)
        (((fun i => start + i) '' {i | i < es.length}) ∪ code.domain) oracle) :
    ∃ body, semantics ffi maxApp (Flapjack.HolFiniteMapExact.union (Flapjack.HolFiniteMapExact.alistToFmap (chainExps start es)) code)
        oracle compiler [body] = semantics ffi maxApp code oracle compiler es ∧
      holALookup (chainExps start es) start = some (0, body) := by
  by_cases nonempty : es ≠ []
  · exact chain_semantics_nonempty ffi maxApp code oracle compiler es start nonempty
      premises.1 (Set.disjoint_left.mpr (fun x hx hy => premises.2.1 x ⟨hx, hy⟩)) premises.2.2
  · have empty : es = [] := by simpa using nonempty
    subst es
    exact chain_semantics_empty ffi maxApp code oracle compiler start

private theorem lookup_alist_eq {V : Type} (entries : List (Nat × V)) (key : Nat) :
    (HolFiniteMapExact.alistToFmap entries).lookup key = holALookup entries key := by
  induction entries with
  | nil => simp [HolFiniteMapExact.alistToFmap, HolFiniteMapExact.empty, holALookup]
  | cons entry rest ih =>
    obtain ⟨k, v⟩ := entry
    by_cases eq : key = k
    · subst key
      rw [HolFiniteMapExact.lookup_alistToFmap_head (k, v) rest]
      simp [holALookup]
    · rw [HolFiniteMapExact.lookup_alistToFmap_tail (k, v) rest key eq]
      simpa [holALookup, eq] using ih

/-- Calling the generated chain entry has the original program behavior. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "chain_exps_semantics_call"
  (fmap_as_finite_support_parameter_observations :=
    (map_parameters := [code])
    (map_producers := [Flapjack.HolFiniteMapExact.alistToFmap, Flapjack.HolFiniteMapExact.union]))]
theorem chainExps_semantics_call {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (es : List ClosLang.Exp) (start : Nat)
    (premises : semantics ffi maxApp code oracle compiler es ≠ .fail ∧
      (∀ x, ¬ (x ∈ ((fun i => start + i) '' {i | i < es.length}) ∧ x ∈ code.domain)) ∧
      oracleMonotonic oracleCodeNames (· < ·)
        (((fun i => start + i) '' {i | i < es.length}) ∪ code.domain) oracle) :
    semantics ffi maxApp (Flapjack.HolFiniteMapExact.union (Flapjack.HolFiniteMapExact.alistToFmap (chainExps start es)) code)
        oracle compiler [.call .none 0 start []] = semantics ffi maxApp code oracle compiler es := by
  obtain ⟨body, semanticsEq, lookup⟩ := chainExps_semantics ffi maxApp code oracle compiler es start premises
  let targetCode := (HolFiniteMapExact.alistToFmap (chainExps start es)).union code
  have entry : targetCode.lookup start = some (0, body) := by
    simp [targetCode, HolFiniteMapExact.lookup_union, lookup_alist_eq, lookup]
  have safe : semantics ffi maxApp targetCode oracle compiler [body] ≠ .fail := by
    rw [semanticsEq]
    exact premises.1
  rw [← semanticsEq]
  symm
  apply semantics_eq_of_related_clocked_simulation ffi maxApp targetCode targetCode oracle oracle compiler compiler
    [body] [.call .none 0 start []] ((semantics_ne_fail_iff ffi maxApp targetCode oracle compiler [body]).mp safe)
  intro clock result final run
  refine ⟨1, result, final, ?_, rfl, Iff.rfl, rfl⟩
  simpa [evaluate, fixClock, findCode, entry, decClock, initialState] using run

private def toBroad (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) := code.lookup

private def ofBroad (lookup : Nat → Option (Nat × ClosLang.Exp))
    (finite : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact Nat (Nat × ClosLang.Exp) := ⟨lookup, finite⟩

/-- Canonical lookup and finite-support codec for the code-map parameter. -/
theorem holFmapAsFiniteSupportParamWitness_chainExps_semantics_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code := by
  cases code
  exact ⟨rfl, rfl, rfl⟩

/-- Canonical lookup and finite-support codec for the call theorem's code map. -/
theorem holFmapAsFiniteSupportParamWitness_chainExps_semantics_call_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_chainExps_semantics_code code key

end Flapjack.Compiler.Backend.ClosToBvl
