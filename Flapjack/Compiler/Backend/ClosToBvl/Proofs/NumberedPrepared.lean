import Flapjack.Compiler.Backend.ClosToBvl.Proofs.AnnotatedPrepared
import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationBounds
import Flapjack.Compiler.Backend.BackendProps.OracleMonotonic
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.CodeLocations

/-! Location annotations supplied by closure numbering to prepared programs. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Compiler.Backend.BackendProps

/-- Chaining top-level expressions adds no closure-code locations. -/
theorem chainExps_codeLocations (start : Nat) (expressions : List ClosLang.Exp) :
    ClosProps.codeLocations ((chainExps start expressions).map (fun (_, _, body) => body)) =
      ClosProps.codeLocations expressions := by
  induction expressions generalizing start with
  | nil => simp [chainExps, ClosProps.codeLocations, ClosProps.codeLocationsExp]
  | cons first rest ih =>
    cases rest with
    | nil => simp [chainExps, ClosProps.codeLocations]
    | cons second tail =>
      simpa [chainExps, ClosProps.codeLocations, ClosProps.codeLocationsExp] using
        congrArg (fun locations => ClosProps.codeLocationsExp first ++ locations) (ih (start + 1))

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

/-- The no-optimization preprocessing path places closure locations in the
interval reserved by the numbering state, even after annotation and chaining. -/
theorem compileCommonNoOpts_location_bounds (config current : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp))
    (compiled : compileCommonNoOpts? config expressions = some (current, program))
    (location : Nat) (member : location ∈ ClosProps.codeLocations (program.map (fun (_, _, body) => body))) :
    config.nextLoc ≤ location ∧ location < current.nextLoc := by
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
        have raw := ClosAnnotate.compile_codeLocations (chainExps config.nextLoc numberedExpressions) member
        rw [chainExps_codeLocations] at raw
        have numberedMember : location ∈ ClosProps.codeLocations (ClosNumber.renumberList aligned expressions).2 := by
          simpa [numbered] using raw
        have bounds := ClosNumber.renumberList_location_bounds expressions aligned location numberedMember
        have lower : config.nextLoc ≤ aligned := by
          dsimp [aligned, next]
          split <;> omega
        simp only [numbered] at bounds
        simp only
        omega

/-- Stateful numbering supplies locations for each incremental main program;
annotation then supplies variables and preserves the supplied auxiliary-code
locations. The auxiliary code is passed through numbering unchanged. -/
theorem numberedAnnotatedOracle_annotations {C : Type}
    (oracle : Nat → (Nat × C) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (auxLocations : ∀ index entry, entry ∈ (oracle index).2.2 →
      ClosProps.everyFnLocationSome [entry.2.2]) :
    ∀ index,
      let program := ((pureCo ClosAnnotate.compileInc ∘
        stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2
      ClosProps.everyFnLocationSome program.1 ∧ ClosProps.everyFnVarsSome program.1 ∧
        (∀ entry ∈ program.2, ClosProps.everyFnLocationSome [entry.2.2]) ∧
        (∀ entry ∈ program.2, ClosProps.everyFnVarsSome [entry.2.2]) := by
  apply annotatedOracle_annotations
  intro index
  constructor
  · simpa [stateCo, ClosNumber.ignoreTable] using
      ClosNumber.compileInc_locations (oracle index).1.1 (oracle index).2.1
  · simpa [stateCo, ClosNumber.ignoreTable] using auxLocations index

/-- The numbering states of a consistent incremental oracle are monotone.
These states can serve as candidate boundaries for future generated code;
the separate proof that emitted labels lie between them is still required. -/
theorem numberingOracle_state_monotone {C : Type}
    (oracle : Nat → (Nat × C) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (state : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) :
    ∀ {i j}, i ≤ j → (oracle i).1.1 ≤ (oracle j).1.1 := by
  have step : ∀ i, (oracle i).1.1 ≤ (oracle (i + 1)).1.1 := by
    intro i
    have increase := ClosNumber.compileInc_start_lt (oracle i).1.1 (oracle i).2.1
    have next := state i
    simp only [ClosNumber.ignoreTable] at next
    omega
  intro i j order
  induction order with
  | refl => exact Nat.le_refl _
  | @step j order ih => exact Nat.le_trans ih (step j)

/-- Main expressions in a consistent numbered oracle use closure locations
between the current and next numbering states. Auxiliary code is unchanged
and therefore requires a separate range argument. -/
theorem numberingOracle_location_bounds {C : Type}
    (oracle : Nat → (Nat × C) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (state : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    (index location : Nat)
    (member : location ∈ ClosProps.codeLocations
      ((stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle index).2.1)) :
    (oracle index).1.1 ≤ location ∧ location < (oracle (index + 1)).1.1 := by
  have numbered : location ∈ ClosProps.codeLocations
      (ClosNumber.compileInc (oracle index).1.1 (oracle index).2.1).2 := by
    simpa [stateCo, ClosNumber.ignoreTable] using member
  have bounds := ClosNumber.compileInc_location_bounds (oracle index).1.1 location (oracle index).2.1 numbered
  have next := state index
  simp only [ClosNumber.ignoreTable] at next
  omega

/-- Numbering followed by variable annotation keeps all main-expression
closure locations inside the oracle entry's numbering interval. -/
theorem numberedAnnotatedOracle_location_bounds {C : Type}
    (oracle : Nat → (Nat × C) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (state : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    (index location : Nat)
    (member : location ∈ ClosProps.codeLocations
      (((pureCo ClosAnnotate.compileInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2.1)) :
    (oracle index).1.1 ≤ location ∧ location < (oracle (index + 1)).1.1 := by
  apply numberingOracle_location_bounds oracle state index location
  apply ClosAnnotate.annotateList_codeLocations 0
  simpa [Function.comp_def, pureCo, ClosAnnotate.compileInc] using member

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

/-- No-optimization compilation with the stateful numbering and annotation
oracle. Only the unchanged auxiliary code still needs input locations;
numbering establishes them for the incremental main expressions. -/
theorem compileNoOpts_numberedOracle_semantics {C F : Type} (ffi : HolFfiState F)
    (config current output : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp)) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : Nat → (Nat × C) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (targetCompiler : BvlSem.Compiler C) (boundary : Nat → Nat)
    (preprocess : compileCommonNoOpts? config expressions = some (current, program))
    (compile : compileNoOpts? config expressions = some (output, compiled, names))
    (nonfail : ClosSem.semantics ffi current.maxApp (initialSourceCode program)
      (pureCo ClosAnnotate.compileInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
      (pureCc (compileInc current.maxApp) targetCompiler) [.call .none 0 current.start []] ≠ .fail)
    (distinct : (compiled.map Prod.fst).Nodup)
    (monotone : ∀ {i j}, i ≤ j → boundary i ≤ boundary j)
    (initialBelow : ∀ location ∈ compiled.map Prod.fst, location < boundary 0)
    (futureDistinct : ∀ index, ((compileInc current.maxApp
      ((pureCo ClosAnnotate.compileInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2).map Prod.fst).Nodup)
    (ranges : ∀ index location, location ∈ (compileInc current.maxApp
      ((pureCo ClosAnnotate.compileInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2).map Prod.fst →
      boundary index ≤ location ∧ location < boundary (index + 1))
    (auxLocations : ∀ index entry, entry ∈ (oracle index).2.2 →
      ClosProps.everyFnLocationSome [entry.2.2]) :
    BvlSem.semantics ffi (sptFromAList compiled)
      (pureCo (compileInc current.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
        stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) targetCompiler output.start =
      ClosSem.semantics ffi current.maxApp (initialSourceCode program)
        (pureCo ClosAnnotate.compileInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
        (pureCc (compileInc current.maxApp) targetCompiler) [.call .none 0 current.start []] := by
  apply compileNoOpts_tree_semantics ffi config current output expressions program compiled names
    (pureCo ClosAnnotate.compileInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    targetCompiler boundary preprocess compile nonfail distinct monotone initialBelow futureDistinct ranges
  exact numberedAnnotatedOracle_annotations oracle auxLocations

end Flapjack.Compiler.Backend.ClosToBvl
