import Flapjack.Compiler.Backend.ClosToBvl.Proofs.SourceChain
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ChainEvaluation
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.SemanticsCorrect

/-! Annotation of installed closure programs and their observable behavior. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps

/-- Annotating every association-list entry preserves its first-match lookup,
including when the source program contains duplicate labels. -/
theorem initialSourceCode_compile (program : List (Nat × Nat × ClosLang.Exp)) :
    initialSourceCode (ClosAnnotate.compile program) =
      (initialSourceCode program).map2 (fun entry => (entry.2.1, ClosAnnotate.annotateSing entry.2.1 entry.2.2)) := by
  apply HolFiniteMapExact.ext_lookup
  intro key
  induction program with
  | nil => simp [ClosAnnotate.compile, initialSourceCode, HolFiniteMapExact.updateListEq, FUPDATE_LIST_HOL]
  | cons first rest ih =>
    obtain ⟨name, arity, body⟩ := first
    simp only [ClosAnnotate.compile, List.map_cons]
    simp only [HolFiniteMapExact.lookup_map2]
    rw [initialSourceCode_cons_lookup, initialSourceCode_cons_lookup]
    by_cases same : key = name
    · simp [same]
    · simp only [same, ↓reduceIte]
      simpa [ClosAnnotate.compile] using ih

/-- A source association-list map and its annotated counterpart satisfy the
annotation state relation at every initial clock. -/
theorem initialState_annotated_code_related {C F : Type} (ffi : HolFfiState F) (maxApp clock : Nat)
    (program : List (Nat × Nat × ClosLang.Exp)) (oracle : CompileOracle C) (compiler : Compiler C) :
    ClosAnnotate.StateRel
      (initialState ffi maxApp (initialSourceCode program) oracle (pureCc ClosAnnotate.compileInc compiler) clock)
      (initialState ffi maxApp (initialSourceCode (ClosAnnotate.compile program))
        (pureCo ClosAnnotate.compileInc ∘ oracle) compiler clock) := by
  simp only [ClosAnnotate.StateRel, initialState, true_and, List.Forall₂.nil]
  constructor
  · intro key
    simp [ClosAnnotate.OptionRel, HolFiniteMapExact.empty]
  · intro key
    rw [initialSourceCode_compile]
    simp only [HolFiniteMapExact.lookup_map2]
    cases h : (initialSourceCode program).lookup key with
    | none => simp [ClosAnnotate.OptionRel]
    | some value =>
      obtain ⟨arity, body⟩ := value
      simp [ClosAnnotate.OptionRel, ClosAnnotate.CodeRel]

/-- Every installed source body is annotation-safe when the association-list
bodies are safe. -/
theorem initialSourceCode_annotationSafe {C F : Type} (ffi : HolFfiState F) (maxApp clock : Nat)
    (program : List (Nat × Nat × ClosLang.Exp)) (oracle : CompileOracle C) (compiler : Compiler C)
    (safe : ∀ name arity body, (name, arity, body) ∈ program → everyFnVarsNone [body]) :
    ClosAnnotate.CodeSafe (initialState ffi maxApp (initialSourceCode program) oracle compiler clock) := by
  intro name arity body lookup
  exact safe name arity body (initialSourceCode_lookup_mem program name arity body lookup)

/-- Annotation preserves observable behavior with an installed source program,
under the evaluator's annotation-safety conditions. -/
theorem annotation_installed_semantics {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : List (Nat × Nat × ClosLang.Exp)) (oracle : CompileOracle C) (compiler : Compiler C)
    (program : List ClosLang.Exp) (safe : everyFnVarsNone program)
    (codeSafe : ∀ name arity body, (name, arity, body) ∈ code → everyFnVarsNone [body])
    (oracleSafe : ∀ n, everyFnVarsNone (oracle n).2.1 ∧
      everyFnVarsNone ((oracle n).2.2.map (fun (_, _, body) => body)))
    (nonfail : semantics ffi maxApp (initialSourceCode code) oracle (pureCc ClosAnnotate.compileInc compiler) program ≠ .fail) :
    semantics ffi maxApp (initialSourceCode code) oracle (pureCc ClosAnnotate.compileInc compiler) program =
      semantics ffi maxApp (initialSourceCode (ClosAnnotate.compile code))
        (pureCo ClosAnnotate.compileInc ∘ oracle) compiler (ClosAnnotate.annotateList 0 program) := by
  apply ClosAnnotate.semantics_eq_of_related
  intro clock
  let source := initialState ffi maxApp (initialSourceCode code) oracle (pureCc ClosAnnotate.compileInc compiler) clock
  let target := initialState ffi maxApp (initialSourceCode (ClosAnnotate.compile code))
    (pureCo ClosAnnotate.compileInc ∘ oracle) compiler clock
  let outcome := evaluate program [] source
  have noType : outcome.1 ≠ .err (.abort .typeError) := by
    exact (semantics_ne_fail_iff ffi maxApp (initialSourceCode code) oracle
      (pureCc ClosAnnotate.compileInc compiler) program).mp nonfail clock
  obtain ⟨targetResult, targetNext, targetRun, results, nextRel⟩ :=
    ClosAnnotate.annotate_correct program source target [] outcome.1 outcome.2 (by exact Prod.eta _) noType safe
      (initialSourceCode_annotationSafe ffi maxApp clock code oracle (pureCc ClosAnnotate.compileInc compiler) codeSafe)
      oracleSafe (initialState_annotated_code_related ffi maxApp clock code oracle compiler)
  rw [targetRun]
  exact ⟨results, nextRel.2.1⟩

end Flapjack.Compiler.Backend.ClosToBvl
