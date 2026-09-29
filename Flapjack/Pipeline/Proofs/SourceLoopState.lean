import Flapjack.Pipeline
import Flapjack.Pancake.CrepToLoop.Proofs.LocValueFree
import Flapjack.Pancake.CrepToLoop.StateRel
import Flapjack.Pancake.Semantics.LoopSemStateExact

/-! Proof-only exact/source pipeline bridges. Keeping these state and
`locValue` relations downstream of `Pipeline` preserves executable definitions
and theorem statements without making the CLI import closure load the evaluator
proof stack. -/

namespace Flapjack

/-- Label rebasing changes call labels and `locValue` source identifiers but
does not introduce any `locValue` constructor into recursively free code. -/
theorem rebaseHOLFunctionLabelsExact_preserves_locValueFree {width : Nat} [NeZero width]
    (firstLabel functionCount : Nat) (program : HolLoopProg width)
    (hfree : holLoopProgLocValueFree program) :
    holLoopProgLocValueFree (rebaseHOLFunctionLabelsExact firstLabel functionCount program) := by
  let mProg : HolLoopProg width → Prop := fun p =>
    holLoopProgLocValueFree p →
      holLoopProgLocValueFree (rebaseHOLFunctionLabelsExact firstLabel functionCount p)
  let mPair : HolLoopProg width × NumSet → Prop := fun p => mProg p.1
  let mTriple : HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mProg p.1 ∧ mProg p.2.1
  let mQuad : Nat × HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mTriple p.2
  let mHandler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet) → Prop
    | none => True
    | some entry => mQuad entry
  have hgeneral : mProg program := by
    refine HolLoopProg.rec
        (motive_1 := mProg) (motive_2 := mHandler) (motive_3 := mQuad)
        (motive_4 := mTriple) (motive_5 := mPair)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ program <;>
      simp_all [mProg, mPair, mTriple, mQuad, mHandler,
        holLoopProgLocValueFree, rebaseHOLFunctionLabelsExact]
    case refine_23 =>
      intro returns target arguments handler hHandler hfree
      cases handler with
      | none => simp [holLoopProgLocValueFree, rebaseHOLFunctionLabelsExact]
      | some entry =>
          rcases entry with ⟨exception, first, second, live⟩
          rcases hHandler with ⟨ihFirst, ihSecond⟩
          simp only [holLoopProgLocValueFree] at hfree
          rcases hfree with ⟨hFirst, hSecond⟩
          have hFirst' := ihFirst hFirst
          have hSecond' := ihSecond hSecond
          simp [holLoopProgLocValueFree, rebaseHOLFunctionLabelsExact,
            hFirst', hSecond']
  exact hgeneral hfree

/-- Production label rebasing after canonical projection preserves the same
recursive `locValue`-free fact, by the checked projection/rebase commuting
theorem above. -/
theorem rebaseHOLFunctionLabels_preserves_locValueFree {width : Nat} [NeZero width]
    (firstLabel functionCount : Nat) (program : HolLoopProg width)
    (hfree : holLoopProgLocValueFree program) :
    loopProgLocValueFree
      (rebaseHOLFunctionLabels firstLabel functionCount
        (holLoopProgToExecutableCanonical program)) := by
  rw [rebaseHOLFunctionLabels_projection]
  simpa [holLoopProgToExecutableCanonical] using
    holLoopProgToExecutable_preserves_locValueFree numSetKeys _
      (rebaseHOLFunctionLabelsExact_preserves_locValueFree
        firstLabel functionCount program hfree)

/-- A concrete exact `compile_prog_def` row remains free of the runtime-only
constructor after the same canonical projection and production label rebase
used by `pipelineLoopFunctionsSourceCompileProgExact`. -/
theorem rebaseCompileProgHOLExact_rowLocValueFree {width : Nat} [NeZero width]
    (target : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (firstLabel functionCount : Nat)
    (program : List
      (Flapjack.Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width))
    (row : Nat × List Nat × HolLoopProg width)
    (hrow : row ∈ compileProgHOLExact target program) :
    loopProgLocValueFree
      (rebaseHOLFunctionLabels firstLabel functionCount
        (holLoopProgToExecutableCanonical row.2.2)) := by
  exact rebaseHOLFunctionLabels_preserves_locValueFree firstLabel functionCount
    row.2.2 (compileProgHOLExact_rowLocValueFree target program row hrow)


/-! ### Exact Spt code-table bridge for the non-executed routed alternative

`pipelineLoopFunctionsSourceCompileProgRouted` is a tested alternative, not
the executed CLI route. It emits an association list, while the exact Loop
state uses an `Spt` code field. The declarations here build that Spt table from
the faithful, structurally rebased `compile_prog` rows and prove both lookup
directions needed by `LoopSemStateFiniteExact.prodRel`. They are Flapjack-only
bridges: HOL `compile_prog_def` returns a list and does not state a theorem
about the parser-backed production code carrier. -/

/-- Exact Spt-row view of the caller-label-rebased `compile_prog_def` output
for the parser-backed source route. Flapjack-only carrier infrastructure: HOL
`compile_prog_def` returns triples with the fixed `first_name` base and does
not expose this caller-rebased Spt table. -/
def pipelineLoopFunctionsSourceCompileProgRoutedExactCodeRows
    {width : Nat} [NeZero width] (firstLabel : Nat)
    (functions : List (CompiledFunction (BitVec width))) :
    List (Nat × (List Nat × HolLoopProg width)) :=
  (compileProgHOLExact .riscv (functions.map fun function =>
    (Flapjack.Basis.Pure.MlString.ofString function.name, function.params,
      crepProgToHOL function.body))).map fun entry =>
        (rebaseHOLFunctionLabel firstLabel functions.length entry.1,
          (entry.2.1,
            rebaseHOLFunctionLabelsExact firstLabel functions.length entry.2.2))

/-- Nested code-row view of the non-executed routed alternative's production
list. This preserves its association-list order and row payload suitable for
`LoopMachineState.code`; it does not identify the executed CLI code table or
construct a runtime state. -/
def pipelineLoopFunctionsSourceCompileProgRoutedCodeRows
    {width : Nat} [NeZero width] (architecture : RiscV.Architecture)
    (firstLabel : Nat) (functions : List (CompiledFunction (BitVec width))) :
    List (Nat × (List Nat × LoopProg (BitVec width))) :=
  (pipelineLoopFunctionsSourceCompileProgRouted architecture firstLabel functions).map
    fun entry => (entry.1, (entry.2.1, entry.2.2))

private theorem pipelineLoopFunctionsSourceCompileProgRouted_codeRows_eq
    {width : Nat} [NeZero width] (architecture : RiscV.Architecture)
    (firstLabel : Nat) (functions : List (CompiledFunction (BitVec width)))
    (hFunctionNames : ∀ function ∈ functions, CrepNameRanged function.name)
    (hProgramNames : ∀ function ∈ functions, CrepProgNameRanged function.body) :
    pipelineLoopFunctionsSourceCompileProgRoutedCodeRows architecture firstLabel functions =
      (pipelineLoopFunctionsSourceCompileProgRoutedExactCodeRows firstLabel functions).map
        (fun entry => (entry.1,
          (entry.2.1, holLoopProgToExecutableCanonical entry.2.2))) := by
  unfold pipelineLoopFunctionsSourceCompileProgRoutedCodeRows
  rw [pipelineLoopFunctionsSourceCompileProgRouted_exact architecture firstLabel
    functions hFunctionNames hProgramNames]
  unfold pipelineLoopFunctionsSourceCompileProgRoutedExactCodeRows
  simp only [List.map_map, Function.comp_def]
  congr 1
  funext entry
  cases entry with
  | mk label rest =>
    cases rest with
    | mk parameters body =>
      simp [rebaseHOLFunctionLabels_projection]

private theorem pipelineLoopFunctionsSourceCompileProgRoutedExactCodeRows_length
    {width : Nat} [NeZero width] (firstLabel : Nat)
    (functions : List (CompiledFunction (BitVec width))) :
    (pipelineLoopFunctionsSourceCompileProgRoutedExactCodeRows firstLabel functions).length =
      functions.length := by
  simp [pipelineLoopFunctionsSourceCompileProgRoutedExactCodeRows,
    compileProgHOLExact, List.length_zipWith]

private theorem pipelineLoopFunctionsSourceCompileProgRouted_codeRows_keys
    {width : Nat} [NeZero width] (architecture : RiscV.Architecture)
    (firstLabel : Nat) (functions : List (CompiledFunction (BitVec width)))
    (hFunctionNames : ∀ function ∈ functions, CrepNameRanged function.name)
    (hProgramNames : ∀ function ∈ functions, CrepProgNameRanged function.body) :
    (pipelineLoopFunctionsSourceCompileProgRoutedCodeRows architecture firstLabel
      functions).map Prod.fst =
      (List.range functions.length).map (fun index => firstLabel + index) := by
  have hrouteLength :
      (pipelineLoopFunctionsSourceCompileProgRouted architecture firstLabel functions).length =
        functions.length := by
    rw [pipelineLoopFunctionsSourceCompileProgRouted_exact architecture firstLabel
      functions hFunctionNames hProgramNames]
    simp [compileProgHOLExact, List.length_zipWith]
  apply List.ext_getElem
  · rw [List.length_map, pipelineLoopFunctionsSourceCompileProgRouted_codeRows_eq
      architecture firstLabel functions hFunctionNames hProgramNames]
    simp [pipelineLoopFunctionsSourceCompileProgRoutedExactCodeRows_length]
  · intro index hleft hright
    have hindex : index < functions.length := by
      simpa [pipelineLoopFunctionsSourceCompileProgRoutedCodeRows, List.length_map,
        hrouteLength] using hleft
    have hrow := pipelineLoopFunctionsSourceCompileProgRouted_rowLabel
      architecture firstLabel functions hFunctionNames hProgramNames index hindex
    rw [List.getElem?_eq_getElem (l := pipelineLoopFunctionsSourceCompileProgRouted
      architecture firstLabel functions) (i := index) (by
        rw [hrouteLength]
        exact hindex)] at hrow
    simp only [Option.map_some] at hrow
    simpa [pipelineLoopFunctionsSourceCompileProgRoutedCodeRows,
      List.getElem_map, List.getElem_range] using hrow

private theorem pipelineLoopFunctionsSourceCompileProgRoutedExactCodeRows_keys_nodup
    {width : Nat} [NeZero width] (architecture : RiscV.Architecture)
    (firstLabel : Nat) (functions : List (CompiledFunction (BitVec width)))
    (hFunctionNames : ∀ function ∈ functions, CrepNameRanged function.name)
    (hProgramNames : ∀ function ∈ functions, CrepProgNameRanged function.body) :
    ((pipelineLoopFunctionsSourceCompileProgRoutedExactCodeRows firstLabel functions).map
      Prod.fst).Nodup := by
  have hkeys := pipelineLoopFunctionsSourceCompileProgRouted_codeRows_keys
    architecture firstLabel functions hFunctionNames hProgramNames
  have hsame :
      (pipelineLoopFunctionsSourceCompileProgRoutedExactCodeRows firstLabel functions).map
          Prod.fst =
        (pipelineLoopFunctionsSourceCompileProgRoutedCodeRows architecture firstLabel
          functions).map Prod.fst := by
    rw [pipelineLoopFunctionsSourceCompileProgRouted_codeRows_eq architecture firstLabel
      functions hFunctionNames hProgramNames]
    simp
  rw [hsame, hkeys]
  apply List.nodup_iff_pairwise_ne.mpr
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simp only [List.getElem_map, List.getElem_range] at *
  omega

private theorem sptLookup_sptFromAList_mem_of_nodup {α : Type}
    (entries : List (Nat × α)) (hnodup : (entries.map Prod.fst).Nodup)
    {key : Nat} {value : α}
    (hlookup : sptLookup key (sptFromAList entries) = some value) :
    (key, value) ∈ entries := by
  induction entries with
  | nil => simp [sptFromAList] at hlookup
  | cons entry entries ih =>
      obtain ⟨headKey, headValue⟩ := entry
      rcases List.nodup_cons.mp hnodup with ⟨hheadNot, htailNodup⟩
      by_cases hkey : headKey = key
      · subst key
        have hhead := sptLookup_sptInsert_same headKey headValue (sptFromAList entries)
        rw [sptFromAList, hhead] at hlookup
        injection hlookup with hvalue
        subst value
        exact List.mem_cons_self
      · rw [sptFromAList,
          sptLookup_sptInsert_ne headKey key headValue (sptFromAList entries)
            (Ne.symm hkey)] at hlookup
        exact List.mem_cons_of_mem _ (ih htailNodup hlookup)

private theorem sptFromAList_lookup_mem_of_nodup {α : Type}
    (entries : List (Nat × α)) (hnodup : (entries.map Prod.fst).Nodup)
    {key : Nat} {value : α}
    (hmem : (key, value) ∈ entries) :
    sptLookup key (sptFromAList entries) = some value :=
  memLookupFromAListSomeExact hnodup hmem

/-- The tested, non-executed parser-routed association-list code table relates
    in both directions to the exact Spt table formed from caller-rebased
    `compile_prog_def` rows. Alternative rows point to exact bodies through
    `loopProgExecRel`; exact table lookups are covered by those rows. This is
    only the code-table component of `LoopSemStateFiniteExact.prodRel`, not a
    statement about the executed CLI path or a state/evaluator simulation. -/
theorem pipelineLoopFunctionsSourceCompileProgRouted_codeTableRel
    {width : Nat} [NeZero width] (architecture : RiscV.Architecture)
    (firstLabel : Nat) (functions : List (CompiledFunction (BitVec width)))
    (hFunctionNames : ∀ function ∈ functions, CrepNameRanged function.name)
    (hProgramNames : ∀ function ∈ functions, CrepProgNameRanged function.body) :
    (∀ entry ∈ pipelineLoopFunctionsSourceCompileProgRoutedCodeRows architecture
        firstLabel functions,
      ∃ faithfulBody,
        sptLookup entry.1
            (sptFromAList (pipelineLoopFunctionsSourceCompileProgRoutedExactCodeRows
              firstLabel functions)) = some (entry.2.1, faithfulBody) ∧
          loopProgExecRel entry.2.2 faithfulBody) ∧
    (∀ label parameters faithfulBody,
      sptLookup label
          (sptFromAList (pipelineLoopFunctionsSourceCompileProgRoutedExactCodeRows
            firstLabel functions)) = some (parameters, faithfulBody) →
        ∃ entry ∈ pipelineLoopFunctionsSourceCompileProgRoutedCodeRows architecture
            firstLabel functions,
          entry.1 = label ∧ entry.2.1 = parameters ∧
            loopProgExecRel entry.2.2 faithfulBody) := by
  have hnodup := pipelineLoopFunctionsSourceCompileProgRoutedExactCodeRows_keys_nodup
    architecture firstLabel functions hFunctionNames hProgramNames
  have hrows := pipelineLoopFunctionsSourceCompileProgRouted_codeRows_eq architecture
    firstLabel functions hFunctionNames hProgramNames
  constructor
  · intro entry hentry
    rw [hrows] at hentry
    simp only [List.mem_map] at hentry
    rcases hentry with ⟨faithfulEntry, hfaithfulMem, heq⟩
    cases faithfulEntry with
    | mk label rest =>
      cases rest with
      | mk parameters faithfulBody =>
        cases heq
        refine ⟨faithfulBody, sptFromAList_lookup_mem_of_nodup _ hnodup ?_, ?_⟩
        · exact hfaithfulMem
        · exact holLoopProgToExecutableCanonical_rel faithfulBody
  · intro label parameters faithfulBody hlookup
    have hmem := sptLookup_sptFromAList_mem_of_nodup _ hnodup hlookup
    rw [hrows]
    refine ⟨(label, (parameters, holLoopProgToExecutableCanonical faithfulBody)),
      ?_, rfl, rfl, ?_⟩
    · exact List.mem_map.mpr ⟨(label, (parameters, faithfulBody)), hmem, rfl⟩
    · exact holLoopProgToExecutableCanonical_rel faithfulBody

/-- Build a synthetic pair of exact/production Loop states whose code fields
are the rebased exact `compile_prog_def` table and the non-executed routed
alternative rows. The code-table obligations are derived from
`pipelineLoopFunctionsSourceCompileProgRouted_codeTableRel`; the only supplied
cross-carrier premise is the explicit `FfiStateRel`. This Flapjack-only helper
does not identify the actual CLI state constructor or prove evaluator
simulation. -/
theorem pipelineLoopFunctionsSourceCompileProgRouted_initialState_prodRel
    {width : Nat} [NeZero width] {F : Type}
    (architecture : RiscV.Architecture) (firstLabel : Nat)
    (functions : List (CompiledFunction (BitVec width)))
    (hFunctionNames : ∀ function ∈ functions, CrepNameRanged function.name)
    (hProgramNames : ∀ function ∈ functions, CrepProgNameRanged function.body)
    (state : LoopSemStateFiniteExact width F) (ffi : FfiState F)
    (hFfi : FfiStateRel ffi state.ffi) :
    let exactState : LoopSemStateFiniteExact width F :=
      { state with code := sptFromAList (pipelineLoopFunctionsSourceCompileProgRoutedExactCodeRows
        firstLabel functions) }
    let productionCode : LoopCode (BitVec width) :=
      pipelineLoopFunctionsSourceCompileProgRoutedCodeRows
        architecture firstLabel functions
    exactState.prodRel (exactState.toProductionState productionCode ffi) := by
  let exactState : LoopSemStateFiniteExact width F :=
    { state with code := sptFromAList (pipelineLoopFunctionsSourceCompileProgRoutedExactCodeRows
      firstLabel functions) }
  let productionCode : LoopCode (BitVec width) :=
    pipelineLoopFunctionsSourceCompileProgRoutedCodeRows
      architecture firstLabel functions
  have hCodeTables := pipelineLoopFunctionsSourceCompileProgRouted_codeTableRel
    architecture firstLabel functions hFunctionNames hProgramNames
  have hRows : ∀ entry, entry ∈ productionCode →
      ∃ program, sptLookup entry.1 exactState.code =
        some (entry.2.1, program) ∧ loopProgExecRel entry.2.2 program := by
    intro entry hentry
    simpa [exactState, productionCode] using hCodeTables.1 entry hentry
  have hCoverage : ∀ label parameters program,
      sptLookup label exactState.code = some (parameters, program) →
        ∃ entry ∈ productionCode, entry.1 = label ∧
          entry.2.1 = parameters ∧ loopProgExecRel entry.2.2 program := by
    intro label parameters program hlookup
    simpa [exactState, productionCode] using
      hCodeTables.2 label parameters program hlookup
  change exactState.prodRel (exactState.toProductionState productionCode ffi)
  exact LoopSemStateFiniteExact.toProductionState_prodRel exactState
    productionCode ffi (by simpa [exactState] using hFfi) hRows hCoverage


end Flapjack
