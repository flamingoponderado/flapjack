import Flapjack.Compiler.Backend.ClosToBvl.Proofs.AnnotatedPrepared
import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationInvariants

/-! Location annotations supplied by closure numbering to prepared programs. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Compiler.Backend.BackendProps

/-- Every entry in a chain of numbered expressions retains the locations
assigned by the numbering pass. -/
theorem numberedChain_locations (chainStart numberingStart : Nat) (expressions : List ClosLang.Exp) :
    ∀ name arity body, (name, arity, body) ∈ chainExps chainStart (ClosNumber.renumberList numberingStart expressions).2 →
      ClosProps.everyFnLocationSome [body] := by
  have numbered := ClosNumber.renumberList_locations expressions numberingStart
  have chain := (chainExps_annotations chainStart (ClosNumber.renumberList numberingStart expressions).2).1.mpr numbered
  intro name arity body member
  have inBodies : body ∈ (chainExps chainStart (ClosNumber.renumberList numberingStart expressions).2).map
      (fun (_, _, body) => body) := by
    exact List.mem_map.mpr ⟨(name, arity, body), member, rfl⟩
  exact ClosNumber.locations_member _ body chain inBodies

/-- The no-optimization closure preprocessing path returns a program whose
function bodies have both required annotation kinds. -/
theorem compileCommonNoOpts_annotations (config current : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp))
    (compiled : compileCommonNoOpts? config expressions = some (current, program)) :
    (∀ name arity body, (name, arity, body) ∈ program → ClosProps.everyFnLocationSome [body]) ∧
    (∀ name arity body, (name, arity, body) ∈ program → ClosProps.everyFnVarsSome [body]) := by
  by_cases enabled : config.doMti || config.doCall
  · simp [compileCommonNoOpts?, enabled] at compiled
  · cases known : config.knownConf with
    | some k => simp [compileCommonNoOpts?, enabled, known] at compiled
    | none =>
      let next := config.nextLoc + max 1 expressions.length
      let aligned := if next % 2 = 0 then next else next + 1
      cases numbered : ClosNumber.renumberList aligned expressions with
      | mk nextLoc numberedExpressions =>
        have run : compileCommonNoOpts? config expressions =
            some ({ config with start := config.nextLoc, nextLoc := nextLoc, knownConf := none, callState := (.ln, []) },
              ClosAnnotate.compile (chainExps config.nextLoc numberedExpressions)) := by
          simp [compileCommonNoOpts?, enabled, known, next, aligned, numbered]
        have equal := Option.some.inj (compiled.symm.trans run)
        cases equal
        constructor
        · apply ClosAnnotate.compile_locations
          intro name arity body member
          have source := numberedChain_locations config.nextLoc aligned expressions name arity body
          simp only [numbered] at source
          exact source member
        · exact ClosAnnotate.compile_varsSome _

/-- The executable no-optimization closure compiler satisfies the prepared
entry behavior theorem without separate program-annotation assumptions.
Correctness of preprocessing and the oracle label bounds remain prerequisites
for a theorem about the original source expressions. -/
theorem compileNoOpts_tree_semantics {C F : Type} (ffi : HolFfiState F)
    (config current output : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp)) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (sourceOracle : ClosSem.CompileOracle C) (targetCompiler : BvlSem.Compiler C) (boundary : Nat → Nat)
    (preprocess : compileCommonNoOpts? config expressions = some (current, program))
    (compile : compileNoOpts? config expressions = some (output, compiled, names))
    (nonfail : ClosSem.semantics ffi current.maxApp (initialSourceCode program) sourceOracle
      (pureCc (compileInc current.maxApp) targetCompiler) [.call .none 0 current.start []] ≠ .fail)
    (distinct : (compiled.map Prod.fst).Nodup)
    (monotone : ∀ {i j}, i ≤ j → boundary i ≤ boundary j)
    (initialBelow : ∀ location ∈ compiled.map Prod.fst, location < boundary 0)
    (futureDistinct : ∀ index, ((compileInc current.maxApp (sourceOracle index).2).map Prod.fst).Nodup)
    (ranges : ∀ index location, location ∈ (compileInc current.maxApp (sourceOracle index).2).map Prod.fst →
      boundary index ≤ location ∧ location < boundary (index + 1))
    (futureAnnotations : ∀ index, ClosProps.everyFnLocationSome (sourceOracle index).2.1 ∧
      ClosProps.everyFnVarsSome (sourceOracle index).2.1 ∧
      (∀ entry ∈ (sourceOracle index).2.2, ClosProps.everyFnLocationSome [entry.2.2]) ∧
      (∀ entry ∈ (sourceOracle index).2.2, ClosProps.everyFnVarsSome [entry.2.2])) :
    BvlSem.semantics ffi (sptFromAList compiled) (pureCo (compileInc current.maxApp) ∘ sourceOracle)
        targetCompiler output.start =
      ClosSem.semantics ffi current.maxApp (initialSourceCode program) sourceOracle
        (pureCc (compileInc current.maxApp) targetCompiler) [.call .none 0 current.start []] := by
  have prepared : compilePrepared? config current expressions program = some (output, compiled, names) := by
    simpa [compileNoOpts?, preprocess] using compile
  obtain ⟨locations, varsAnnotated⟩ := compileCommonNoOpts_annotations config current expressions program preprocess
  exact compilePrepared_tree_semantics_of_boundaries ffi config current output expressions program compiled names
    sourceOracle targetCompiler boundary prepared nonfail distinct locations varsAnnotated monotone initialBelow
    futureDistinct ranges futureAnnotations

end Flapjack.Compiler.Backend.ClosToBvl
