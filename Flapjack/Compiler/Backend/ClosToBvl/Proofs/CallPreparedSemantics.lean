import Flapjack.Compiler.Backend.ClosCall.Proofs.IncrementalInstall
import Flapjack.Compiler.Backend.ClosCall.Proofs.Syntax
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.InstalledSemantics
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.AnnotationInvariants
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.AnnotatedPrepared

/-! Composition of direct-call conversion with the installed closure chain. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps

/-- Direct-call conversion followed by chaining and annotation preserves the
proof-side closure behavior, including the auxiliary code emitted by the pass.
The two oracle-ordering conditions and annotation safety remain explicit. This
is Flapjack-specific composition infrastructure, not a HOL theorem port. -/
theorem call_to_annotatedChain_semantics {C F : Type} (ffi : HolFfiState F)
    (maxApp start passFuel relationFuel : Nat) (compiler : Compiler C)
    (expressions called : List ClosLang.Exp) (callState : ClosCall.State)
    (oracle : CompileOracle (NumSet × C))
    (passRun : ClosCall.compileFuel passFuel true expressions = some (called, callState))
    (syntaxGood : ClosCall.syntaxOk expressions)
    (known : callState.1 = (oracle 0).1.1)
    (callOrdered : oracleMonotonic (fun entry => {loc | loc ∈ codeLocations entry.2.1}) (· < ·)
      {loc | loc ∈ codeLocations expressions} oracle)
    (syntaxOracle : ∀ n, ClosCall.syntaxOk (oracle n).2.1 ∧ (oracle n).2.2 = [])
    (nonempty : called ≠ []) (calledSafe : everyFnVarsNone called)
    (auxSafe : ∀ name arity body, (name, arity, body) ∈ callState.2 → everyFnVarsNone [body])
    (annotationOracleSafe : ∀ n,
      everyFnVarsNone (ClosCall.compileIncFuelOracle passFuel oracle n).2.1 ∧
      everyFnVarsNone ((ClosCall.compileIncFuelOracle passFuel oracle n).2.2.map (fun (_, _, body) => body)))
    (fresh : ∀ key, start ≤ key → key < start + called.length →
      (initialSourceCode callState.2).lookup key = none)
    (chainOrdered : oracleMonotonic oracleCodeNames (· < ·)
      ({key | start ≤ key ∧ key < start + called.length} ∪ codeDomain (initialSourceCode callState.2))
      (ClosCall.compileIncFuelOracle passFuel oracle))
    (sourceSafe : semantics ffi maxApp HolFiniteMapExact.empty oracle
      (ClosCall.compileIncFuelCallback passFuel (pureCc ClosAnnotate.compileInc compiler)) expressions ≠ .fail) :
    semantics ffi maxApp
      (initialSourceCode (ClosAnnotate.compile (chainExps start called ++ callState.2)))
      (pureCo ClosAnnotate.compileInc ∘ ClosCall.compileIncFuelOracle passFuel oracle)
      compiler [.call .none 0 start []] =
    semantics ffi maxApp HolFiniteMapExact.empty oracle
      (ClosCall.compileIncFuelCallback passFuel (pureCc ClosAnnotate.compileInc compiler)) expressions := by
  have callEq := ClosCall.compileFuel_enabled_semantics_of_oracle passFuel relationFuel
    (pureCc ClosAnnotate.compileInc compiler) expressions called callState passRun syntaxGood ffi maxApp oracle
    (ClosCall.compileIncFuelCallback passFuel (pureCc ClosAnnotate.compileInc compiler)) rfl known callOrdered syntaxOracle sourceSafe
  have targetSafe : semantics ffi maxApp (initialSourceCode callState.2)
      (ClosCall.compileIncFuelOracle passFuel oracle) (pureCc ClosAnnotate.compileInc compiler) called ≠ .fail := by
    rw [ClosAnnotate.initialSourceCode_eq_alist, callEq]
    exact sourceSafe
  have chainEq := source_to_annotatedChain_with_aux_semantics ffi maxApp start called callState.2
    (ClosCall.compileIncFuelOracle passFuel oracle) compiler nonempty calledSafe auxSafe annotationOracleSafe
    fresh chainOrdered targetSafe
  rw [chainEq, ClosAnnotate.initialSourceCode_eq_alist, callEq]


/-- The prepared closure-to-BVL compiler preserves the source behavior after
direct-call conversion, chaining, and annotation. The prepared-code and oracle
invariants are explicit premises; this is Flapjack-specific composition, not a
HOL theorem port. -/
theorem call_to_preparedBvl_semantics {C F : Type} (ffi : HolFfiState F)
    (passFuel relationFuel : Nat) (original current output : Config)
    (compiler : Compiler C) (targetCompiler : BvlSem.Compiler C)
    (targetOracle : BvlSem.CompileOracle C)
    (expressions called nameExpressions : List ClosLang.Exp) (callState : ClosCall.State)
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : CompileOracle (NumSet × C))
    (passRun : ClosCall.compileFuel passFuel true expressions = some (called, callState))
    (syntaxGood : ClosCall.syntaxOk expressions) (known : callState.1 = (oracle 0).1.1)
    (callOrdered : oracleMonotonic (fun entry => {loc | loc ∈ codeLocations entry.2.1}) (· < ·)
      {loc | loc ∈ codeLocations expressions} oracle)
    (syntaxOracle : ∀ n, ClosCall.syntaxOk (oracle n).2.1 ∧ (oracle n).2.2 = [])
    (nonempty : called ≠ []) (calledSafe : everyFnVarsNone called)
    (auxSafe : ∀ name arity body, (name, arity, body) ∈ callState.2 → everyFnVarsNone [body])
    (annotationOracleSafe : ∀ n,
      everyFnVarsNone (ClosCall.compileIncFuelOracle passFuel oracle n).2.1 ∧
      everyFnVarsNone ((ClosCall.compileIncFuelOracle passFuel oracle n).2.2.map (fun (_, _, body) => body)))
    (fresh : ∀ key, current.start ≤ key → key < current.start + called.length →
      (initialSourceCode callState.2).lookup key = none)
    (chainOrdered : oracleMonotonic oracleCodeNames (· < ·)
      ({key | current.start ≤ key ∧ key < current.start + called.length} ∪ codeDomain (initialSourceCode callState.2))
      (ClosCall.compileIncFuelOracle passFuel oracle))
    (sourceSafe : semantics ffi current.maxApp HolFiniteMapExact.empty oracle
      (ClosCall.compileIncFuelCallback passFuel (pureCc ClosAnnotate.compileInc compiler)) expressions ≠ .fail)
    (compile : compilePrepared? original current nameExpressions
      (ClosAnnotate.compile (chainExps current.start called ++ callState.2)) = some (output, compiled, names))
    (distinct : (compiled.map Prod.fst).Nodup)
    (locations : ∀ name arity body, (name, arity, body) ∈ ClosAnnotate.compile (chainExps current.start called ++ callState.2) →
      everyFnLocationSome [body])
    (varsAnnotated : ∀ name arity body, (name, arity, body) ∈ ClosAnnotate.compile (chainExps current.start called ++ callState.2) →
      everyFnVarsSome [body])
    (oracleInv : compileOracleInv current.maxApp
      (initialSourceCode (ClosAnnotate.compile (chainExps current.start called ++ callState.2))) compiler
      (pureCo ClosAnnotate.compileInc ∘ ClosCall.compileIncFuelOracle passFuel oracle)
      (sptFromAList compiled) targetCompiler targetOracle) :
    BvlSem.semantics ffi (sptFromAList compiled) targetOracle targetCompiler output.start =
      semantics ffi current.maxApp HolFiniteMapExact.empty oracle
        (ClosCall.compileIncFuelCallback passFuel (pureCc ClosAnnotate.compileInc compiler)) expressions := by
  have closureEq := call_to_annotatedChain_semantics ffi current.maxApp current.start passFuel relationFuel compiler
    expressions called callState oracle passRun syntaxGood known callOrdered syntaxOracle nonempty calledSafe auxSafe
    annotationOracleSafe fresh chainOrdered sourceSafe
  have closureSafe : semantics ffi current.maxApp
      (initialSourceCode (ClosAnnotate.compile (chainExps current.start called ++ callState.2)))
      (pureCo ClosAnnotate.compileInc ∘ ClosCall.compileIncFuelOracle passFuel oracle)
      compiler [.call .none 0 current.start []] ≠ .fail := by
    rw [closureEq]
    exact sourceSafe
  have bvlEq := compilePrepared_tree_semantics ffi original current output nameExpressions
    (ClosAnnotate.compile (chainExps current.start called ++ callState.2)) compiled names
    (pureCo ClosAnnotate.compileInc ∘ ClosCall.compileIncFuelOracle passFuel oracle) compiler
    targetOracle targetCompiler compile closureSafe distinct locations varsAnnotated oracleInv
  exact bvlEq.trans closureEq


/-- The production direct-call pass preserves nonemptiness, and executable
annotation supplies the variable annotations used by the BVL proof. The
remaining code and oracle prerequisites are explicit Flapjack infrastructure. -/
theorem call_to_preparedBvl_semantics_from_source {C F : Type} (ffi : HolFfiState F)
    (passFuel relationFuel : Nat) (original current output : Config)
    (compiler : Compiler C) (targetCompiler : BvlSem.Compiler C)
    (targetOracle : BvlSem.CompileOracle C)
    (expressions called nameExpressions : List ClosLang.Exp) (callState : ClosCall.State)
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : CompileOracle (NumSet × C))
    (passRun : ClosCall.compileFuel passFuel true expressions = some (called, callState))
    (syntaxGood : ClosCall.syntaxOk expressions) (known : callState.1 = (oracle 0).1.1)
    (callOrdered : oracleMonotonic (fun entry => {loc | loc ∈ codeLocations entry.2.1}) (· < ·)
      {loc | loc ∈ codeLocations expressions} oracle)
    (syntaxOracle : ∀ n, ClosCall.syntaxOk (oracle n).2.1 ∧ (oracle n).2.2 = [])
    (sourceNonempty : expressions ≠ []) (calledSafe : everyFnVarsNone called)
    (auxSafe : ∀ name arity body, (name, arity, body) ∈ callState.2 → everyFnVarsNone [body])
    (annotationOracleSafe : ∀ n,
      everyFnVarsNone (ClosCall.compileIncFuelOracle passFuel oracle n).2.1 ∧
      everyFnVarsNone ((ClosCall.compileIncFuelOracle passFuel oracle n).2.2.map (fun (_, _, body) => body)))
    (fresh : ∀ key, current.start ≤ key → key < current.start + called.length →
      (initialSourceCode callState.2).lookup key = none)
    (chainOrdered : oracleMonotonic oracleCodeNames (· < ·)
      ({key | current.start ≤ key ∧ key < current.start + called.length} ∪ codeDomain (initialSourceCode callState.2))
      (ClosCall.compileIncFuelOracle passFuel oracle))
    (sourceSafe : semantics ffi current.maxApp HolFiniteMapExact.empty oracle
      (ClosCall.compileIncFuelCallback passFuel (pureCc ClosAnnotate.compileInc compiler)) expressions ≠ .fail)
    (compile : compilePrepared? original current nameExpressions
      (ClosAnnotate.compile (chainExps current.start called ++ callState.2)) = some (output, compiled, names))
    (distinct : (compiled.map Prod.fst).Nodup)
    (locations : ∀ name arity body, (name, arity, body) ∈ ClosAnnotate.compile (chainExps current.start called ++ callState.2) →
      everyFnLocationSome [body])
    (oracleInv : compileOracleInv current.maxApp
      (initialSourceCode (ClosAnnotate.compile (chainExps current.start called ++ callState.2))) compiler
      (pureCo ClosAnnotate.compileInc ∘ ClosCall.compileIncFuelOracle passFuel oracle)
      (sptFromAList compiled) targetCompiler targetOracle) :
    BvlSem.semantics ffi (sptFromAList compiled) targetOracle targetCompiler output.start =
      semantics ffi current.maxApp HolFiniteMapExact.empty oracle
        (ClosCall.compileIncFuelCallback passFuel (pureCc ClosAnnotate.compileInc compiler)) expressions := by
  have traversal : ClosCall.callsListBounded passFuel expressions (.ln, []) = some (called, callState) := by
    simpa [ClosCall.compileFuel] using passRun
  have lengths := ClosCall.callsListBounded_length passFuel expressions (.ln, []) callState called traversal
  have nonempty : called ≠ [] := by
    intro empty
    apply sourceNonempty
    cases expressions with
    | nil => rfl
    | cons head tail => simp [empty] at lengths
  exact call_to_preparedBvl_semantics ffi passFuel relationFuel original current output compiler targetCompiler targetOracle
    expressions called nameExpressions callState compiled names oracle passRun syntaxGood known callOrdered syntaxOracle
    nonempty calledSafe auxSafe annotationOracleSafe fresh chainOrdered sourceSafe compile distinct locations
    (ClosAnnotate.compile_varsSome _) oracleInv


/-- The prepared BVL compiler after direct-call conversion and annotation
preserves source behavior under explicit raw-code and label-boundary
conditions. Executable annotation supplies the target annotations and the
BVL oracle invariant follows from the boundaries. This is Flapjack-specific
composition infrastructure, not a HOL theorem port. -/
theorem call_to_preparedBvl_semantics_of_boundaries {C F : Type} (ffi : HolFfiState F)
    (passFuel relationFuel : Nat) (original current output : Config)
    (targetCompiler : BvlSem.Compiler C) (boundary : Nat → Nat)
    (expressions called nameExpressions : List ClosLang.Exp) (callState : ClosCall.State)
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : CompileOracle (NumSet × C))
    (passRun : ClosCall.compileFuel passFuel true expressions = some (called, callState))
    (syntaxGood : ClosCall.syntaxOk expressions) (known : callState.1 = (oracle 0).1.1)
    (callOrdered : oracleMonotonic (fun entry => {loc | loc ∈ codeLocations entry.2.1}) (· < ·)
      {loc | loc ∈ codeLocations expressions} oracle)
    (syntaxOracle : ∀ n, ClosCall.syntaxOk (oracle n).2.1 ∧ (oracle n).2.2 = [])
    (sourceNonempty : expressions ≠ []) (calledSafe : everyFnVarsNone called)
    (auxSafe : ∀ name arity body, (name, arity, body) ∈ callState.2 → everyFnVarsNone [body])
    (annotationOracleSafe : ∀ n,
      everyFnVarsNone (ClosCall.compileIncFuelOracle passFuel oracle n).2.1 ∧
      everyFnVarsNone ((ClosCall.compileIncFuelOracle passFuel oracle n).2.2.map (fun (_, _, body) => body)))
    (fresh : ∀ key, current.start ≤ key → key < current.start + called.length →
      (initialSourceCode callState.2).lookup key = none)
    (chainOrdered : oracleMonotonic oracleCodeNames (· < ·)
      ({key | current.start ≤ key ∧ key < current.start + called.length} ∪ codeDomain (initialSourceCode callState.2))
      (ClosCall.compileIncFuelOracle passFuel oracle))
    (sourceSafe : semantics ffi current.maxApp HolFiniteMapExact.empty oracle
      (ClosCall.compileIncFuelCallback passFuel (pureCc ClosAnnotate.compileInc
        (pureCc (compileInc current.maxApp) targetCompiler))) expressions ≠ .fail)
    (compile : compilePrepared? original current nameExpressions
      (ClosAnnotate.compile (chainExps current.start called ++ callState.2)) = some (output, compiled, names))
    (distinct : (compiled.map Prod.fst).Nodup)
    (programLocations : ∀ name arity body, (name, arity, body) ∈ chainExps current.start called ++ callState.2 →
      everyFnLocationSome [body])
    (monotone : ∀ {i j}, i ≤ j → boundary i ≤ boundary j)
    (initialBelow : ∀ location ∈ compiled.map Prod.fst, location < boundary 0)
    (futureDistinct : ∀ index, ((compileInc current.maxApp
      (ClosAnnotate.compileInc (ClosCall.compileIncFuelOracle passFuel oracle index).2)).map Prod.fst).Nodup)
    (ranges : ∀ index location, location ∈ (compileInc current.maxApp
      (ClosAnnotate.compileInc (ClosCall.compileIncFuelOracle passFuel oracle index).2)).map Prod.fst →
      boundary index ≤ location ∧ location < boundary (index + 1))
    (futureLocations : ∀ index, everyFnLocationSome (ClosCall.compileIncFuelOracle passFuel oracle index).2.1 ∧
      ∀ entry ∈ (ClosCall.compileIncFuelOracle passFuel oracle index).2.2, everyFnLocationSome [entry.2.2]) :
    BvlSem.semantics ffi (sptFromAList compiled)
      (pureCo (compileInc current.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘ ClosCall.compileIncFuelOracle passFuel oracle)
      targetCompiler output.start =
    semantics ffi current.maxApp HolFiniteMapExact.empty oracle
      (ClosCall.compileIncFuelCallback passFuel (pureCc ClosAnnotate.compileInc
        (pureCc (compileInc current.maxApp) targetCompiler))) expressions := by
  let compiler := pureCc (compileInc current.maxApp) targetCompiler
  have traversal : ClosCall.callsListBounded passFuel expressions (.ln, []) = some (called, callState) := by
    simpa [ClosCall.compileFuel] using passRun
  have lengths := ClosCall.callsListBounded_length passFuel expressions (.ln, []) callState called traversal
  have nonempty : called ≠ [] := by
    intro empty
    apply sourceNonempty
    cases expressions with
    | nil => rfl
    | cons head tail => simp [empty] at lengths
  have closureEq := call_to_annotatedChain_semantics ffi current.maxApp current.start passFuel relationFuel compiler
    expressions called callState oracle passRun syntaxGood known callOrdered syntaxOracle nonempty calledSafe auxSafe
    annotationOracleSafe fresh chainOrdered sourceSafe
  have closureSafe : semantics ffi current.maxApp
      (initialSourceCode (ClosAnnotate.compile (chainExps current.start called ++ callState.2)))
      (pureCo ClosAnnotate.compileInc ∘ ClosCall.compileIncFuelOracle passFuel oracle)
      compiler [.call .none 0 current.start []] ≠ .fail := by
    rw [closureEq]
    exact sourceSafe
  have bvlEq := compilePrepared_annotated_semantics ffi original current output nameExpressions
    (chainExps current.start called ++ callState.2) compiled names (ClosCall.compileIncFuelOracle passFuel oracle)
    targetCompiler boundary compile closureSafe distinct programLocations monotone initialBelow futureDistinct ranges futureLocations
  exact bvlEq.trans closureEq


/-- The direct-call pass itself supplies all closure syntax safety needed
for annotation and BVL preparation. Label boundaries remain explicit; this
is Flapjack-specific composition infrastructure. -/
theorem call_to_preparedBvl_semantics_of_source_syntax {C F : Type} (ffi : HolFfiState F)
    (passFuel relationFuel : Nat) (original current output : Config)
    (targetCompiler : BvlSem.Compiler C) (boundary : Nat → Nat)
    (expressions called nameExpressions : List ClosLang.Exp) (callState : ClosCall.State)
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : CompileOracle (NumSet × C))
    (passRun : ClosCall.compileFuel passFuel true expressions = some (called, callState))
    (syntaxGood : ClosCall.syntaxOk expressions) (known : callState.1 = (oracle 0).1.1)
    (callOrdered : oracleMonotonic (fun entry => {loc | loc ∈ codeLocations entry.2.1}) (· < ·)
      {loc | loc ∈ codeLocations expressions} oracle)
    (syntaxOracle : ∀ n, ClosCall.syntaxOk (oracle n).2.1 ∧ (oracle n).2.2 = [])
    (sourceNonempty : expressions ≠ [])
    (fresh : ∀ key, current.start ≤ key → key < current.start + called.length →
      (initialSourceCode callState.2).lookup key = none)
    (chainOrdered : oracleMonotonic oracleCodeNames (· < ·)
      ({key | current.start ≤ key ∧ key < current.start + called.length} ∪ codeDomain (initialSourceCode callState.2))
      (ClosCall.compileIncFuelOracle passFuel oracle))
    (sourceSafe : semantics ffi current.maxApp HolFiniteMapExact.empty oracle
      (ClosCall.compileIncFuelCallback passFuel (pureCc ClosAnnotate.compileInc
        (pureCc (compileInc current.maxApp) targetCompiler))) expressions ≠ .fail)
    (compile : compilePrepared? original current nameExpressions
      (ClosAnnotate.compile (chainExps current.start called ++ callState.2)) = some (output, compiled, names))
    (distinct : (compiled.map Prod.fst).Nodup)
    (monotone : ∀ {i j}, i ≤ j → boundary i ≤ boundary j)
    (initialBelow : ∀ location ∈ compiled.map Prod.fst, location < boundary 0)
    (futureDistinct : ∀ index, ((compileInc current.maxApp
      (ClosAnnotate.compileInc (ClosCall.compileIncFuelOracle passFuel oracle index).2)).map Prod.fst).Nodup)
    (ranges : ∀ index location, location ∈ (compileInc current.maxApp
      (ClosAnnotate.compileInc (ClosCall.compileIncFuelOracle passFuel oracle index).2)).map Prod.fst →
      boundary index ≤ location ∧ location < boundary (index + 1))
    :
    BvlSem.semantics ffi (sptFromAList compiled)
      (pureCo (compileInc current.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘ ClosCall.compileIncFuelOracle passFuel oracle)
      targetCompiler output.start =
    semantics ffi current.maxApp HolFiniteMapExact.empty oracle
      (ClosCall.compileIncFuelCallback passFuel (pureCc ClosAnnotate.compileInc
        (pureCc (compileInc current.maxApp) targetCompiler))) expressions := by
  have outputSafe := ClosCall.compileFuel_callSyntax passFuel expressions called callState passRun ⟨syntaxGood.1, syntaxGood.2.1⟩
  have oracleSafe := ClosCall.compileIncFuelOracle_callSyntax passFuel oracle (by
    intro index
    exact ⟨(syntaxOracle index).1.1, (syntaxOracle index).1.2.1⟩)
  have auxSafe : ∀ name arity body, (name, arity, body) ∈ callState.2 → everyFnVarsNone [body] := by
    intro name arity body member
    simpa [everyFnVarsNone] using (outputSafe.2 name arity body member).2
  have annotationOracleSafe : ∀ n,
      everyFnVarsNone (ClosCall.compileIncFuelOracle passFuel oracle n).2.1 ∧
      everyFnVarsNone ((ClosCall.compileIncFuelOracle passFuel oracle n).2.2.map (fun (_, _, body) => body)) := by
    intro n
    exact ⟨(oracleSafe n).1.2, (ClosCall.auxSyntax_bodies _ (oracleSafe n).2).2⟩
  have futureLocations : ∀ index, everyFnLocationSome (ClosCall.compileIncFuelOracle passFuel oracle index).2.1 ∧
      ∀ entry ∈ (ClosCall.compileIncFuelOracle passFuel oracle index).2.2, everyFnLocationSome [entry.2.2] := by
    intro index
    refine ⟨(oracleSafe index).1.1, ?_⟩
    intro entry member
    obtain ⟨name, arity, body⟩ := entry
    simpa [everyFnLocationSome] using ((oracleSafe index).2 name arity body member).1
  have memberLocations : ∀ (bodies : List ClosLang.Exp) (body : ClosLang.Exp),
      everyFnLocationSome bodies → body ∈ bodies → everyFnLocationSome [body] := by
    intro bodies body all member
    induction bodies with
    | nil => simp at member
    | cons head tail ih =>
      simp only [everyFnLocationSome] at all
      rcases List.mem_cons.mp member with rfl | member
      · simpa [everyFnLocationSome] using all.1
      · exact ih all.2 member
  have programLocations : ∀ name arity body, (name, arity, body) ∈ chainExps current.start called ++ callState.2 →
      everyFnLocationSome [body] := by
    intro name arity body member
    rcases List.mem_append.mp member with inChain | inAux
    · apply memberLocations _ body ((chainExps_annotations current.start called).1.mpr outputSafe.1.1)
      exact List.mem_map.mpr ⟨(name, arity, body), inChain, rfl⟩
    · simpa [everyFnLocationSome] using (outputSafe.2 name arity body inAux).1
  exact call_to_preparedBvl_semantics_of_boundaries ffi passFuel relationFuel original current output targetCompiler boundary
    expressions called nameExpressions callState compiled names oracle passRun syntaxGood known callOrdered syntaxOracle
    sourceNonempty outputSafe.1.2 auxSafe annotationOracleSafe fresh chainOrdered sourceSafe compile distinct programLocations
    monotone initialBelow futureDistinct ranges futureLocations


/-- Every auxiliary label emitted by the initial direct-call pass is the
successor of a source closure location. -/
theorem callAux_label_origin (fuel : Nat) (expressions called : List ClosLang.Exp) (state : ClosCall.State)
    (run : ClosCall.compileFuel fuel true expressions = some (called, state)) :
    ∀ label ∈ state.2.map Prod.fst, ∃ loc ∈ codeLocations expressions, label = loc + 1 := by
  have traversal : ClosCall.callsListBounded fuel expressions (.ln, []) = some (called, state) := by
    simpa [ClosCall.compileFuel] using run
  have bounds := ClosCall.callsListBounded_labelsBound fuel expressions (.ln, []) state called traversal
  intro label member
  rcases bounds label member with old | generated
  · simp at old
  · exact generated

/-- Each auxiliary label emitted by an incremental direct-call oracle entry
is the successor of a closure location from that source entry. -/
theorem callOracle_label_origin {C : Type} (fuel : Nat) (oracle : CompileOracle (NumSet × C)) (index : Nat) :
    ∀ label ∈ (ClosCall.compileIncFuelOracle fuel oracle index).2.2.map Prod.fst,
      ∃ loc ∈ codeLocations (oracle index).2.1, label = loc + 1 := by
  obtain ⟨nextKnown, pass, _⟩ := ClosCall.compileIncFuelOracle_entry fuel oracle index
  have traversal := ClosCall.compileIncFuel_traversal fuel (oracle index).1.1 (oracle index).2 nextKnown
    (ClosCall.compileIncFuelOracle fuel oracle index).2 pass
  have bounds := ClosCall.callsListBounded_labelsBound fuel (oracle index).2.1 ((oracle index).1.1, [])
    (nextKnown, (ClosCall.compileIncFuelOracle fuel oracle index).2.2)
    (ClosCall.compileIncFuelOracle fuel oracle index).2.1 traversal
  intro label member
  rcases bounds label member with old | generated
  · simp at old
  · exact generated

/-- Source closure locations above the entry-chain interval and monotone
source oracle locations give the initial auxiliary-code freshness and
transformed-oracle ordering required by the chain simulation. -/
theorem call_chain_fresh_and_ordered {C : Type} (fuel start : Nat)
    (expressions called : List ClosLang.Exp) (state : ClosCall.State)
    (oracle : CompileOracle (NumSet × C))
    (run : ClosCall.compileFuel fuel true expressions = some (called, state))
    (initialLower : ∀ loc ∈ codeLocations expressions, start + expressions.length ≤ loc)
    (futureLower : ∀ index loc, loc ∈ codeLocations (oracle index).2.1 → start + expressions.length ≤ loc)
    (ordered : oracleMonotonic (fun entry => {loc | loc ∈ codeLocations entry.2.1}) (· < ·)
      {loc | loc ∈ codeLocations expressions} oracle) :
    (∀ key, start ≤ key → key < start + called.length → (initialSourceCode state.2).lookup key = none) ∧
    oracleMonotonic oracleCodeNames (· < ·)
      ({key | start ≤ key ∧ key < start + called.length} ∪ codeDomain (initialSourceCode state.2))
      (ClosCall.compileIncFuelOracle fuel oracle) := by
  have traversal : ClosCall.callsListBounded fuel expressions (.ln, []) = some (called, state) := by
    simpa [ClosCall.compileFuel] using run
  have lengths := ClosCall.callsListBounded_length fuel expressions (.ln, []) state called traversal
  have codeOrigin : ∀ key, (initialSourceCode state.2).lookup key ≠ none →
      ∃ loc ∈ codeLocations expressions, key = loc + 1 := by
    intro key found
    cases lookup : (initialSourceCode state.2).lookup key with
    | none => exact (found lookup).elim
    | some entry =>
      obtain ⟨arity, body⟩ := entry
      have member := initialSourceCode_lookup_mem state.2 key arity body lookup
      have label : key ∈ state.2.map Prod.fst := by
        exact List.mem_map.mpr ⟨(key, arity, body), member, rfl⟩
      exact callAux_label_origin fuel expressions called state run key label
  constructor
  · intro key lower upper
    by_contra found
    obtain ⟨loc, member, equal⟩ := codeOrigin key found
    have bound := initialLower loc member
    omega
  · constructor
    · intro i j x y before xMember yMember
      obtain ⟨xLoc, xSource, xEq⟩ := callOracle_label_origin fuel oracle i x xMember
      obtain ⟨yLoc, ySource, yEq⟩ := callOracle_label_origin fuel oracle j y yMember
      have less := ordered.1 i j xLoc yLoc before xSource ySource
      omega
    · intro i x y member yMember
      obtain ⟨yLoc, ySource, yEq⟩ := callOracle_label_origin fuel oracle i y yMember
      rcases member with chain | oldCode
      · change start ≤ x ∧ x < start + called.length at chain
        have bound := futureLower i yLoc ySource
        omega
      · obtain ⟨xLoc, xSource, xEq⟩ := codeOrigin x oldCode
        have less := ordered.2 i xLoc yLoc xSource ySource
        omega


/-- Direct-call to BVL behavior preservation with chain freshness and
oracle ordering derived from source-location bounds. The remaining compiled
label-boundary conditions are explicit Flapjack infrastructure. -/
theorem call_to_preparedBvl_semantics_of_location_bounds {C F : Type} (ffi : HolFfiState F)
    (passFuel relationFuel : Nat) (original current output : Config)
    (targetCompiler : BvlSem.Compiler C) (boundary : Nat → Nat)
    (expressions called nameExpressions : List ClosLang.Exp) (callState : ClosCall.State)
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : CompileOracle (NumSet × C))
    (passRun : ClosCall.compileFuel passFuel true expressions = some (called, callState))
    (syntaxGood : ClosCall.syntaxOk expressions) (known : callState.1 = (oracle 0).1.1)
    (callOrdered : oracleMonotonic (fun entry => {loc | loc ∈ codeLocations entry.2.1}) (· < ·)
      {loc | loc ∈ codeLocations expressions} oracle)
    (syntaxOracle : ∀ n, ClosCall.syntaxOk (oracle n).2.1 ∧ (oracle n).2.2 = [])
    (sourceNonempty : expressions ≠ [])
    (initialLower : ∀ loc ∈ codeLocations expressions, current.start + expressions.length ≤ loc)
    (futureLower : ∀ index loc, loc ∈ codeLocations (oracle index).2.1 → current.start + expressions.length ≤ loc)
    (sourceSafe : semantics ffi current.maxApp HolFiniteMapExact.empty oracle
      (ClosCall.compileIncFuelCallback passFuel (pureCc ClosAnnotate.compileInc
        (pureCc (compileInc current.maxApp) targetCompiler))) expressions ≠ .fail)
    (compile : compilePrepared? original current nameExpressions
      (ClosAnnotate.compile (chainExps current.start called ++ callState.2)) = some (output, compiled, names))
    (distinct : (compiled.map Prod.fst).Nodup)
    (monotone : ∀ {i j}, i ≤ j → boundary i ≤ boundary j)
    (initialBelow : ∀ location ∈ compiled.map Prod.fst, location < boundary 0)
    (futureDistinct : ∀ index, ((compileInc current.maxApp
      (ClosAnnotate.compileInc (ClosCall.compileIncFuelOracle passFuel oracle index).2)).map Prod.fst).Nodup)
    (ranges : ∀ index location, location ∈ (compileInc current.maxApp
      (ClosAnnotate.compileInc (ClosCall.compileIncFuelOracle passFuel oracle index).2)).map Prod.fst →
      boundary index ≤ location ∧ location < boundary (index + 1))
    :
    BvlSem.semantics ffi (sptFromAList compiled)
      (pureCo (compileInc current.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘ ClosCall.compileIncFuelOracle passFuel oracle)
      targetCompiler output.start =
    semantics ffi current.maxApp HolFiniteMapExact.empty oracle
      (ClosCall.compileIncFuelCallback passFuel (pureCc ClosAnnotate.compileInc
        (pureCc (compileInc current.maxApp) targetCompiler))) expressions := by
  obtain ⟨fresh, chainOrdered⟩ := call_chain_fresh_and_ordered passFuel current.start expressions called callState oracle
    passRun initialLower futureLower callOrdered
  exact call_to_preparedBvl_semantics_of_source_syntax ffi passFuel relationFuel original current output targetCompiler boundary
    expressions called nameExpressions callState compiled names oracle passRun syntaxGood known callOrdered syntaxOracle
    sourceNonempty fresh chainOrdered sourceSafe compile distinct monotone initialBelow futureDistinct ranges

end Flapjack.Compiler.Backend.ClosToBvl
