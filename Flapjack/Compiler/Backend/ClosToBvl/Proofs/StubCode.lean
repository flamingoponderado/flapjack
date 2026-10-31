import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ProgramCode
import Flapjack.Compiler.Backend.ClosToBvl.Prepared
import Flapjack.Misc.Sptree.ToAList

/-! Lookup properties of the generated initial closure-application stubs. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

private def insertSequential {α : Type} (entries : List α) (start : Nat) (tree : Spt α) : Nat × Spt α :=
  entries.foldl (fun (acc : Nat × Spt α) entry => (acc.1 + 1, sptInsert acc.1 entry acc.2)) (start, tree)

/-- Inserting a sequence at successive locations preserves all earlier
locations in the target code tree. -/
private theorem insertSequential_before {α : Type} (entries : List α) (start key : Nat) (tree : Spt α)
    (before : key < start) : sptLookup key (insertSequential entries start tree).2 = sptLookup key tree := by
  induction entries generalizing start tree with
  | nil => rfl
  | cons entry rest ih =>
    simp only [insertSequential, List.foldl_cons] at ⊢
    change sptLookup key (insertSequential rest (start + 1) (sptInsert start entry tree)).2 = _
    rw [ih (start + 1) (sptInsert start entry tree) (by omega)]
    exact sptLookup_sptInsert_ne start key entry tree (by omega)

/-- Sequential insertion places each element at its offset from the initial
location. -/
private theorem insertSequential_lookup {α : Type} (entries : List α) (start index : Nat) (tree : Spt α)
    (bound : index < entries.length) :
    sptLookup (start + index) (insertSequential entries start tree).2 = entries[index]? := by
  induction entries generalizing start index tree with
  | nil => simp at bound
  | cons entry rest ih =>
    cases index with
    | zero =>
      simp only [insertSequential, List.foldl_cons, Nat.add_zero, List.getElem?_cons_zero]
      change sptLookup start (insertSequential rest (start + 1) (sptInsert start entry tree)).2 = _
      rw [insertSequential_before rest (start + 1) start (sptInsert start entry tree) (by omega)]
      exact sptLookup_sptInsert_same start entry tree
    | succ index =>
      simp only [insertSequential, List.foldl_cons, List.getElem?_cons_succ]
      change sptLookup (start + (index + 1)) (insertSequential rest (start + 1) (sptInsert start entry tree)).2 = _
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (start + 1) index (sptInsert start entry tree) (by simp at bound; omega)

/-- The generic stubs occupy the initial contiguous segment of the generated
table. This Flapjack helper is stronger than the generic conjunct of HOL's
`init_code_ok`: it omits the redundant positive-`maxApp` premise. The full HOL
conjunction remains to be reviewed and tagged. -/
theorem initCode_generic_lookup (maxApp n : Nat) (bound : n < maxApp) :
    sptLookup (genericAppFnLocation n) (initCode maxApp) =
      some (n + 2, generateGenericApp maxApp n) := by
  let generic := (List.range maxApp).map (fun i => (i + 2, generateGenericApp maxApp i))
  let partialEntries := ((List.range maxApp).map fun total =>
    (List.range total).map fun previous =>
      (total - previous + 1, generatePartialAppClosureFn total previous)).flatten
  have nth : (generic ++ partialEntries)[n]? = some (n + 2, generateGenericApp maxApp n) := by
    simp [generic, List.getElem?_append, bound]
  have lengthBound : n < (generic ++ partialEntries).length := (List.getElem?_eq_some_iff.mp nth).1
  have result := insertSequential_lookup (generic ++ partialEntries) 0 n (.ln) lengthBound
  simpa [initCode, genericAppFnLocation, insertSequential, generic, partialEntries, nth] using result

/-- Rows of generated partial-application stubs, in insertion order. -/
private def partialStubEntries (count : Nat) : List (Nat × Bvl.Exp) :=
  ((List.range count).map fun total => (List.range total).map fun previous =>
    (total - previous + 1, generatePartialAppClosureFn total previous)).flatten

private theorem partialStubEntries_succ (count : Nat) :
    partialStubEntries (count + 1) = partialStubEntries count ++
      (List.range count).map (fun previous => (count - previous + 1, generatePartialAppClosureFn count previous)) := by
  simp [partialStubEntries, List.range_succ]

private theorem partialStubEntries_lookup (count total previous : Nat)
    (inTable : total < count) (inRow : previous < total) :
    (partialStubEntries count)[(partialStubEntries total).length + previous]? =
      some (total - previous + 1, generatePartialAppClosureFn total previous) := by
  induction count with
  | zero => omega
  | succ count ih =>
    rw [partialStubEntries_succ]
    by_cases equal : total = count
    · subst total
      simp [inRow]
    · have smaller : total < count := by omega
      have run := ih smaller
      have bound : (partialStubEntries total).length + previous < (partialStubEntries count).length :=
        (List.getElem?_eq_some_iff.mp run).1
      simp [List.getElem?_append, bound, (List.getElem?_eq_some_iff.mp run).2]

private theorem partialStubEntries_length (count : Nat) :
    (partialStubEntries count).length = count * (count - 1) / 2 := by
  have twice : ∀ n, (partialStubEntries n).length * 2 = n * (n - 1) := by
    intro n
    induction n with
    | zero => simp [partialStubEntries]
    | succ n ih =>
      rw [partialStubEntries_succ]
      simp only [List.length_append, List.length_map, List.length_range]
      cases n with
      | zero => simp [partialStubEntries]
      | succ n =>
        simp only [Nat.add_sub_cancel] at *
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at ih ⊢
        omega
  have h := congrArg (fun n : Nat => n / 2) (twice count)
  simpa using h

/-- Each partial-application stub is installed at its triangularly indexed
location. This Flapjack helper omits the redundant positive-`maxApp` premise
of HOL's `init_code_ok`; the full HOL conjunction remains to be reviewed. -/
theorem initCode_partial_lookup (maxApp total previous : Nat)
    (totalBound : total < maxApp) (previousBound : previous < total) :
    sptLookup (partialAppFnLocation maxApp total previous) (initCode maxApp) =
      some (total - previous + 1, generatePartialAppClosureFn total previous) := by
  let generic := (List.range maxApp).map (fun i => (i + 2, generateGenericApp maxApp i))
  let entries := generic ++ partialStubEntries maxApp
  have partialLookup := partialStubEntries_lookup maxApp total previous totalBound previousBound
  have nth : entries[maxApp + total * (total - 1) / 2 + previous]? =
      some (total - previous + 1, generatePartialAppClosureFn total previous) := by
    have notEarlier : ¬ maxApp + total * (total - 1) / 2 + previous < maxApp := by omega
    have offset : maxApp + total * (total - 1) / 2 + previous - maxApp =
        total * (total - 1) / 2 + previous := by omega
    simpa [entries, generic, List.getElem?_append, partialStubEntries_length, notEarlier, offset] using partialLookup
  have bound : maxApp + total * (total - 1) / 2 + previous < entries.length :=
    (List.getElem?_eq_some_iff.mp nth).1
  have result := insertSequential_lookup entries 0 (maxApp + total * (total - 1) / 2 + previous) (.ln) bound
  rw [nth] at result
  simpa [initCode, partialAppFnLocation, insertSequential, entries, generic, partialStubEntries] using result

/-- Installing the enumerated initialization tree installs every generic and
partial-application stub at the locations required by the state relation. -/
theorem installed_initCode_stubs (maxApp : Nat) (code : Spt (Nat × Bvl.Exp))
    (installed : codeInstalled (sptToAList (initCode maxApp)) code) :
    (∀ n, n < maxApp → sptLookup (genericAppFnLocation n) code =
      some (n + 2, generateGenericApp maxApp n)) ∧
    (∀ total previous, total < maxApp ∧ previous < total →
      sptLookup (partialAppFnLocation maxApp total previous) code =
        some (total - previous + 1, generatePartialAppClosureFn total previous)) := by
  constructor
  · intro n bound
    apply installed (genericAppFnLocation n, n + 2, generateGenericApp maxApp n)
    exact (sptMemToAList _ _ _).2 (initCode_generic_lookup maxApp n bound)
  · intro total previous ⟨totalBound, previousBound⟩
    apply installed (partialAppFnLocation maxApp total previous, total - previous + 1,
      generatePartialAppClosureFn total previous)
    exact (sptMemToAList _ _ _).2 (initCode_partial_lookup maxApp total previous totalBound previousBound)

/-- The code emitted for an annotated source program: application stubs,
force and initialization entries, followed by compiled program entries. -/
noncomputable def initialCompiledEntries (maxApp sourceStart : Nat) (program : List (Nat × Nat × ClosLang.Exp)) :
    List (Nat × Nat × Bvl.Exp) :=
  sptToAList (initCode maxApp) ++
    [(numStubs maxApp - 2, 2, forceThunkCode),
      (numStubs maxApp - 1, 0, initGlobals maxApp (sourceStart + numStubs maxApp))] ++
    compileProgExpsHOL maxApp program

/-- The executable prepared compiler emits the sorted form of the same
initialization and compiled entries used by the proof. -/
theorem compilePrepared_entries (original current : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp)) :
    ∃ names, compilePrepared? original current expressions program =
      some ({ current with start := numStubs current.maxApp - 1 },
        codeSort (initialCompiledEntries current.maxApp current.start program), names) := by
  simp [compilePrepared?, compileProg_checked_eq_original, initialCompiledEntries, Nat.add_comm]

private theorem codeSplit_mem {α : Type} (entries left right : List α) (entry : α) :
    entry ∈ (codeSplit entries left right).1 ∨ entry ∈ (codeSplit entries left right).2 ↔
      entry ∈ entries ∨ entry ∈ left ∨ entry ∈ right := by
  induction entries generalizing left right with
  | nil => simp [codeSplit]
  | cons first rest ih =>
    simp only [codeSplit, ih, List.mem_cons]
    tauto

private theorem codeMerge_mem {α : Type} (left right : List (Nat × α)) (entry : Nat × α) :
    entry ∈ codeMerge left right ↔ entry ∈ left ∨ entry ∈ right := by
  fun_induction codeMerge left right <;> simp_all <;> tauto

/-- Sorting the prepared code preserves membership of each generated entry. -/
theorem codeSort_mem {α : Type} (entries : List (Nat × α)) (entry : Nat × α) :
    entry ∈ codeSort entries ↔ entry ∈ entries := by
  fun_induction codeSort entries <;> simp_all [codeMerge_mem, codeSplit_mem]
  all_goals tauto

/-- Installing the sorted executable output installs the original generated
entries needed by the proof-side state relation. -/
theorem codeInstalled_of_sorted (entries : List (Nat × Nat × Bvl.Exp)) (code : Spt (Nat × Bvl.Exp))
    (installed : codeInstalled (codeSort entries) code) : codeInstalled entries code := by
  intro entry member
  exact installed entry ((codeSort_mem entries entry).2 member)

/-- Once the generated startup and compiled entries are installed, they
supply all code-location premises of the proof-side behavior theorem. The
source annotations and compiler-oracle invariant are still required. -/
theorem initialCompiledEntries_semantics {C F : Type} (ffi : HolFfiState F)
    (maxApp sourceStart : Nat) (program : List (Nat × Nat × ClosLang.Exp))
    (sourceOracle : ClosSem.CompileOracle C) (sourceCompiler : ClosSem.Compiler C)
    (targetCode : Spt (Nat × Bvl.Exp)) (targetOracle : BvlSem.CompileOracle C)
    (targetCompiler : BvlSem.Compiler C)
    (nonfail : ClosSem.semantics ffi maxApp (initialSourceCode program) sourceOracle sourceCompiler
      [.call .none 0 sourceStart []] ≠ .fail)
    (installed : codeInstalled (initialCompiledEntries maxApp sourceStart program) targetCode)
    (locations : ∀ name arity body, (name, arity, body) ∈ program → ClosProps.everyFnLocationSome [body])
    (varsAnnotated : ∀ name arity body, (name, arity, body) ∈ program → ClosProps.everyFnVarsSome [body])
    (oracle : compileOracleInv maxApp (initialSourceCode program) sourceCompiler sourceOracle
      targetCode targetCompiler targetOracle) :
    BvlSem.semantics ffi targetCode targetOracle targetCompiler (numStubs maxApp - 1) =
      ClosSem.semantics ffi maxApp (initialSourceCode program) sourceOracle sourceCompiler [.call .none 0 sourceStart []] := by
  have stubInstalled : codeInstalled (sptToAList (initCode maxApp)) targetCode := by
    intro entry member
    apply installed entry
    simp [initialCompiledEntries, member]
  obtain ⟨generic, partialStubs⟩ := installed_initCode_stubs maxApp targetCode stubInstalled
  have programInstalled : codeInstalled (compileProgExpsHOL maxApp program) targetCode := by
    intro entry member
    apply installed entry
    simp [initialCompiledEntries, member]
  have force : sptLookup (numStubs maxApp - 2) targetCode = some (2, forceThunkCode) := by
    apply installed (numStubs maxApp - 2, 2, forceThunkCode)
    simp [initialCompiledEntries]
  have entry : sptLookup (numStubs maxApp - 1) targetCode =
      some (0, initGlobals maxApp (sourceStart + numStubs maxApp)) := by
    apply installed (numStubs maxApp - 1, 0, initGlobals maxApp (sourceStart + numStubs maxApp))
    simp [initialCompiledEntries]
  exact compiledProgram_entry_semantics ffi maxApp sourceStart (numStubs maxApp - 1) program
    sourceOracle sourceCompiler targetCode targetOracle targetCompiler nonfail programInstalled locations varsAnnotated
    generic partialStubs force oracle entry

/-- Behavior preservation for the executable prepared compiler, conditional
on its emitted code being installed and the source annotation and oracle
invariants. This is a proof-side candidate, pending carrier and preprocessing
correspondence review. -/
theorem compilePrepared_entry_semantics {C F : Type} (ffi : HolFfiState F)
    (original current output : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp)) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (sourceOracle : ClosSem.CompileOracle C) (sourceCompiler : ClosSem.Compiler C)
    (targetCode : Spt (Nat × Bvl.Exp)) (targetOracle : BvlSem.CompileOracle C)
    (targetCompiler : BvlSem.Compiler C)
    (compile : compilePrepared? original current expressions program = some (output, compiled, names))
    (nonfail : ClosSem.semantics ffi current.maxApp (initialSourceCode program) sourceOracle sourceCompiler
      [.call .none 0 current.start []] ≠ .fail)
    (installed : codeInstalled compiled targetCode)
    (locations : ∀ name arity body, (name, arity, body) ∈ program → ClosProps.everyFnLocationSome [body])
    (varsAnnotated : ∀ name arity body, (name, arity, body) ∈ program → ClosProps.everyFnVarsSome [body])
    (oracle : compileOracleInv current.maxApp (initialSourceCode program) sourceCompiler sourceOracle
      targetCode targetCompiler targetOracle) :
    BvlSem.semantics ffi targetCode targetOracle targetCompiler output.start =
      ClosSem.semantics ffi current.maxApp (initialSourceCode program) sourceOracle sourceCompiler
        [.call .none 0 current.start []] := by
  obtain ⟨expectedNames, expected⟩ := compilePrepared_entries original current expressions program
  have equal := Option.some.inj (compile.symm.trans expected)
  cases equal
  apply initialCompiledEntries_semantics ffi current.maxApp current.start program sourceOracle sourceCompiler
    targetCode targetOracle targetCompiler nonfail ?_ locations varsAnnotated oracle
  exact codeInstalled_of_sorted _ _ installed

/-- Distinct output labels make every generated entry installed in the tree
constructed from that output. -/
theorem distinct_entries_installed (entries : List (Nat × Nat × Bvl.Exp))
    (distinct : (entries.map Prod.fst).Nodup) : codeInstalled entries (sptFromAList entries) := by
  have installed := install_codeInstalled (.ln) entries distinct (by simp [sptLookup])
  simpa [sptUnion] using installed

/-- Prepared compiler output with distinct labels preserves the proof-side
behavior when installed using the compiler's target tree construction. -/
theorem compilePrepared_tree_semantics {C F : Type} (ffi : HolFfiState F)
    (original current output : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp)) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (sourceOracle : ClosSem.CompileOracle C) (sourceCompiler : ClosSem.Compiler C)
    (targetOracle : BvlSem.CompileOracle C) (targetCompiler : BvlSem.Compiler C)
    (compile : compilePrepared? original current expressions program = some (output, compiled, names))
    (nonfail : ClosSem.semantics ffi current.maxApp (initialSourceCode program) sourceOracle sourceCompiler
      [.call .none 0 current.start []] ≠ .fail)
    (distinct : (compiled.map Prod.fst).Nodup)
    (locations : ∀ name arity body, (name, arity, body) ∈ program → ClosProps.everyFnLocationSome [body])
    (varsAnnotated : ∀ name arity body, (name, arity, body) ∈ program → ClosProps.everyFnVarsSome [body])
    (oracle : compileOracleInv current.maxApp (initialSourceCode program) sourceCompiler sourceOracle
      (sptFromAList compiled) targetCompiler targetOracle) :
    BvlSem.semantics ffi (sptFromAList compiled) targetOracle targetCompiler output.start =
      ClosSem.semantics ffi current.maxApp (initialSourceCode program) sourceOracle sourceCompiler
        [.call .none 0 current.start []] :=
  compilePrepared_entry_semantics ffi original current output expressions program compiled names sourceOracle sourceCompiler
    (sptFromAList compiled) targetOracle targetCompiler compile nonfail (distinct_entries_installed compiled distinct)
    locations varsAnnotated oracle

end Flapjack.Compiler.Backend.ClosToBvl
