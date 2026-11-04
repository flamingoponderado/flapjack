import Flapjack.Compiler.Backend.ClosCall.Proofs.IncrementalInstall
import Flapjack.Compiler.Backend.ClosCall.Proofs.Syntax
import Flapjack.Compiler.Backend.ClosCall.Proofs.LocationSafety
import Flapjack.Compiler.Backend.ClosCall.Proofs.LocationMultiplicity
import Flapjack.Compiler.Backend.ClosCall.Proofs.LocationAccounting
import Flapjack.Compiler.Backend.ClosCall.Proofs.EntryMarker
import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationParity
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.InstalledSemantics
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.AnnotationInvariants
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.AnnotatedPrepared
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.NumberedPrepared

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


/-- The initial direct-call pass emits distinct auxiliary labels inside the
successor interval of the source closure locations. -/
theorem callAux_distinct_and_range (fuel lower upper : Nat) (expressions called : List ClosLang.Exp)
    (state : ClosCall.State) (run : ClosCall.compileFuel fuel true expressions = some (called, state))
    (distinct : (codeLocations expressions).Nodup)
    (bounds : ∀ loc ∈ codeLocations expressions, lower ≤ loc ∧ loc + 1 < upper) :
    (state.2.map Prod.fst).Nodup ∧
      ∀ label ∈ state.2.map Prod.fst, lower ≤ label ∧ label < upper := by
  have well := ClosCall.compileFuel_enabled_wellFormed fuel expressions called state run distinct
  refine ⟨well.2, ?_⟩
  intro label member
  obtain ⟨loc, sourceMember, equal⟩ := callAux_label_origin fuel expressions called state run label member
  have b := bounds loc sourceMember
  omega

/-- Each transformed oracle entry has distinct auxiliary labels, and those
labels lie in the successor interval of the corresponding source entry. -/
theorem callOracle_aux_distinct_and_range {C : Type} (fuel : Nat)
    (oracle : CompileOracle (NumSet × C)) (lower upper : Nat → Nat)
    (distinct : ∀ index, (codeLocations (oracle index).2.1).Nodup)
    (bounds : ∀ index loc, loc ∈ codeLocations (oracle index).2.1 →
      lower index ≤ loc ∧ loc + 1 < upper index) :
    ∀ index, ((ClosCall.compileIncFuelOracle fuel oracle index).2.2.map Prod.fst).Nodup ∧
      ∀ label ∈ (ClosCall.compileIncFuelOracle fuel oracle index).2.2.map Prod.fst,
        lower index ≤ label ∧ label < upper index := by
  intro index
  obtain ⟨nextKnown, pass, _⟩ := ClosCall.compileIncFuelOracle_entry fuel oracle index
  have generated := ClosCall.compileIncFuel_generated fuel (oracle index).1.1 (oracle index).2 nextKnown
    (ClosCall.compileIncFuelOracle fuel oracle index).2 pass (distinct index)
  refine ⟨generated.1, ?_⟩
  intro label member
  obtain ⟨loc, sourceMember, equal⟩ := generated.2.1 label member
  have b := bounds index loc sourceMember
  omega

/-- Annotation leaves the generated auxiliary labels unchanged, so their
source-derived distinctness and range survive the production annotation
step. -/
theorem annotatedCallOracle_aux_distinct_and_range {C : Type} (fuel : Nat)
    (oracle : CompileOracle (NumSet × C)) (lower upper : Nat → Nat)
    (distinct : ∀ index, (codeLocations (oracle index).2.1).Nodup)
    (bounds : ∀ index loc, loc ∈ codeLocations (oracle index).2.1 →
      lower index ≤ loc ∧ loc + 1 < upper index) :
    ∀ index, ((ClosAnnotate.compile (ClosCall.compileIncFuelOracle fuel oracle index).2.2).map Prod.fst).Nodup ∧
      ∀ label ∈ (ClosAnnotate.compile (ClosCall.compileIncFuelOracle fuel oracle index).2.2).map Prod.fst,
        lower index ≤ label ∧ label < upper index := by
  intro index
  simpa only [annotated_labels] using callOracle_aux_distinct_and_range fuel oracle lower upper distinct bounds index


/-- A consistent numbering oracle reserves the successor of every closure
location before advancing to its next numbering state. -/
theorem numberingOracle_location_successor_bounds {C : Type}
    (oracle : Nat → (Nat × C) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (state : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    (index location : Nat)
    (member : location ∈ codeLocations
      ((stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle index).2.1)) :
    (oracle index).1.1 ≤ location ∧ location + 1 < (oracle (index + 1)).1.1 := by
  have numbered : location ∈ codeLocations (ClosNumber.compileInc (oracle index).1.1 (oracle index).2.1).2 := by
    simpa [stateCo, ClosNumber.ignoreTable] using member
  have bounds := ClosNumber.compileInc_location_successor_bounds (oracle index).1.1 location (oracle index).2.1 numbered
  have next := state index
  simp only [ClosNumber.ignoreTable] at next
  omega

/-- When a direct-call oracle receives numbered programs, its generated
auxiliary labels are distinct and lie strictly inside each numbering interval,
including after closure annotation. -/
theorem numberedCallOracle_aux_distinct_and_range {C : Type} (fuel : Nat)
    (oracle : Nat → (Nat × (NumSet × C)) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (state : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) :
    ∀ index,
      ((ClosAnnotate.compile (ClosCall.compileIncFuelOracle fuel
        (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2.2).map Prod.fst).Nodup ∧
      ∀ label ∈ (ClosAnnotate.compile (ClosCall.compileIncFuelOracle fuel
        (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2.2).map Prod.fst,
        (oracle index).1.1 ≤ label ∧ label < (oracle (index + 1)).1.1 := by
  apply annotatedCallOracle_aux_distinct_and_range fuel
    (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    (fun index => (oracle index).1.1) (fun index => (oracle (index + 1)).1.1)
  · intro index
    simpa [stateCo, ClosNumber.ignoreTable] using
      ClosNumber.compileInc_codeLocations_nodup (oracle index).1.1 (oracle index).2.1
  · intro index loc member
    exact numberingOracle_location_successor_bounds oracle state index loc member

/-- Numbering, direct-call conversion, and annotation preserve distinct
closure locations in each oracle entry's main expressions. -/
theorem numberedCallOracle_main_locations_nodup {C : Type} (fuel : Nat)
    (oracle : Nat → (Nat × (NumSet × C)) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp))) :
    ∀ index, (codeLocations (ClosAnnotate.annotateList 0
      (ClosCall.compileIncFuelOracle fuel
        (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2.1)).Nodup := by
  intro index
  apply ClosAnnotate.annotateList_codeLocations_nodup
  apply ClosCall.compileIncFuelOracle_locations_nodup
  simpa [stateCo, ClosNumber.ignoreTable] using
    ClosNumber.compileInc_codeLocations_nodup (oracle index).1.1 (oracle index).2.1

/-- Main expressions and emitted auxiliary bodies retain distinct locations
together after numbering, direct-call conversion, and annotation. -/
theorem numberedCallOracle_all_locations_nodup {C : Type} (fuel : Nat)
    (oracle : Nat → (Nat × (NumSet × C)) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp))) :
    ∀ index, (codeLocations (ClosAnnotate.annotateList 0
      (ClosCall.compileIncFuelOracle fuel
        (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2.1) ++
      codeLocations ((ClosAnnotate.compile (ClosCall.compileIncFuelOracle fuel
        (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2.2).map
          (fun (_, _, body) => body))).Nodup := by
  intro index
  let numbered := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
  let called := ClosCall.compileIncFuelOracle fuel numbered index
  have sourceDistinct : (codeLocations (numbered index).2.1).Nodup := by
    simpa [numbered, stateCo, ClosNumber.ignoreTable] using
      ClosNumber.compileInc_codeLocations_nodup (oracle index).1.1 (oracle index).2.1
  have distinct := ClosCall.compileIncFuelOracle_all_locations_nodup fuel numbered index sourceDistinct
  exact ((ClosAnnotate.annotateList_codeLocations_sublist 0 called.2.1).append
    (ClosAnnotate.compile_codeLocations_sublist called.2.2)).nodup distinct

/-- Auxiliary entry labels and all nested closure locations are distinct
together after numbering, direct-call conversion, and annotation. -/
theorem numberedCallOracle_entries_and_locations_nodup {C : Type} (fuel : Nat)
    (oracle : Nat → (Nat × (NumSet × C)) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (state : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) :
    ∀ index,
      ((ClosAnnotate.compile (ClosCall.compileIncFuelOracle fuel
        (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2.2).map Prod.fst ++
      (codeLocations (ClosAnnotate.annotateList 0 (ClosCall.compileIncFuelOracle fuel
        (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2.1) ++
       codeLocations ((ClosAnnotate.compile (ClosCall.compileIncFuelOracle fuel
        (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2.2).map
          (fun (_, _, body) => body)))).Nodup := by
  intro index
  let numbered := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
  let called := ClosCall.compileIncFuelOracle fuel numbered index
  have sourceEven : ∀ loc ∈ codeLocations (numbered index).2.1, loc % 2 = 0 := by
    intro loc member
    apply ClosNumber.compileInc_location_even (oracle index).1.1 loc (oracle index).2.1
    simpa [numbered, stateCo, ClosNumber.ignoreTable] using member
  have labelsOdd : ∀ label ∈ (ClosAnnotate.compile called.2.2).map Prod.fst, label % 2 = 1 := by
    intro label member
    have before : label ∈ called.2.2.map Prod.fst := by simpa only [annotated_labels] using member
    obtain ⟨origin, inSource, equal⟩ := callOracle_label_origin fuel numbered index label before
    have even := sourceEven origin inSource
    omega
  have within := ClosCall.compileIncFuelOracle_locationsWithin fuel numbered index
  have locationsEven : ∀ loc ∈ codeLocations (ClosAnnotate.annotateList 0 called.2.1) ++
      codeLocations ((ClosAnnotate.compile called.2.2).map (fun (_, _, body) => body)), loc % 2 = 0 := by
    intro loc member
    rcases List.mem_append.mp member with main | auxiliary
    · exact sourceEven loc (within.1 loc ((ClosAnnotate.annotateList_codeLocations_sublist 0 called.2.1).subset main))
    · have before : loc ∈ codeLocations (called.2.2.map (fun (_, _, body) => body)) :=
        (ClosAnnotate.compile_codeLocations_sublist called.2.2).subset auxiliary
      obtain ⟨body, bodyMember, locMember⟩ := (mem_codeLocations loc _).1 before
      obtain ⟨entry, entryMember, bodyEq⟩ := List.mem_map.mp bodyMember
      obtain ⟨name, arity, sourceBody⟩ := entry
      simp only at bodyEq
      subst body
      exact sourceEven loc (within.2 name arity sourceBody entryMember loc locMember)
  apply List.Nodup.append
  · exact (numberedCallOracle_aux_distinct_and_range fuel oracle state index).1
  · exact numberedCallOracle_all_locations_nodup fuel oracle index
  · intro label inLabels inLocations
    have odd := labelsOdd label inLabels
    have even := locationsEven label inLocations
    omega

/-- Numbering followed by incremental direct-call conversion preserves the
entry marker and one output expression per original source expression. -/
theorem numberedCallOracle_marker {C : Type} (fuel : Nat)
    (oracle : Nat → (Nat × (NumSet × C)) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (index : Nat) :
    ∃ output : List ClosLang.Exp,
      (ClosCall.compileIncFuelOracle fuel
        (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2.1 =
          .op .none (.intOp (.const (Int.ofNat (oracle index).1.1))) [] :: output ∧
      output.length = (oracle index).2.1.length := by
  let start := (oracle index).1.1
  let expressions := (oracle index).2.1
  let next := start + max expressions.length 1
  let aligned := if next % 2 = 0 then next else next + 1
  let numbered := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
  let called := ClosCall.compileIncFuelOracle fuel numbered index
  cases result : ClosNumber.renumberList aligned expressions with
  | mk nextLoc numberedExpressions =>
    have length := ClosNumber.renumberList_length expressions aligned
    rw [result] at length
    have marker : (numbered index).2.1 =
        .op .none (.intOp (.const (Int.ofNat start))) [] :: numberedExpressions := by
      simp [numbered, stateCo, ClosNumber.ignoreTable, ClosNumber.compileInc,
        start, expressions, next, aligned, result]
    obtain ⟨nextKnown, run, _⟩ := ClosCall.compileIncFuelOracle_entry fuel numbered index
    have run' : ClosCall.compileIncFuel? fuel (numbered index).1.1
        (.op .none (.intOp (.const (Int.ofNat start))) [] :: numberedExpressions, (numbered index).2.2) =
        some (nextKnown, called.2) := by
      cases pair : (numbered index).2 with
      | mk es aux =>
        simp only [pair] at marker run ⊢
        subst es
        exact run
    obtain ⟨output, outputMarker, outputLength⟩ := ClosCall.compileIncFuel_entryMarker
      fuel (numbered index).1.1 nextKnown .none start numberedExpressions (numbered index).2.2 called.2 run'
    exact ⟨output, outputMarker, outputLength.trans length⟩

/-- The generated and annotated incremental closure program compiles to
distinct BVL code labels. -/
theorem numberedCallOracle_bvl_labels_nodup {C : Type} (maxApp fuel : Nat)
    (oracle : Nat → (Nat × (NumSet × C)) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (state : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) :
    ∀ index, ((compileInc maxApp (ClosAnnotate.compileInc
      (ClosCall.compileIncFuelOracle fuel
        (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2)).map Prod.fst).Nodup := by
  intro index
  let start := (oracle index).1.1
  let expressions := (oracle index).2.1
  let numbered := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
  let called := ClosCall.compileIncFuelOracle fuel numbered index
  let program := ClosAnnotate.compileInc called.2
  obtain ⟨output, marker, outputLength⟩ := numberedCallOracle_marker fuel oracle index
  have marker' : called.2.1 = .op .none (.intOp (.const (Int.ofNat start))) [] :: output := marker
  have annotatedMarker : program.1 = .op .none (.intOp (.const (Int.ofNat start))) [] ::
      ClosAnnotate.annotateList 0 output := by
    simpa [program, ClosAnnotate.compileInc, marker'] using ClosAnnotate.annotateList_name_marker start output
  let real := (extractName program.1).2
  have shape := extractName_numbered_marker start (ClosAnnotate.annotateList 0 output)
  have startEq : (extractName program.1).1 = start := by simpa [annotatedMarker] using shape.1
  have lengthEq : real.length = max 1 expressions.length := by
    have l : real.length = max 1 output.length := by
      simpa [real, annotatedMarker, ClosAnnotate.annotateList_length] using shape.2.1
    simpa [expressions, outputLength] using l
  have extract : extractName program.1 = (start, real) := by
    cases h : extractName program.1 with
    | mk first second => simp [real, h] at startEq ⊢; exact startEq
  have mainEq : codeLocations real = codeLocations program.1 := by
    rw [show codeLocations real = codeLocations (ClosAnnotate.annotateList 0 output) by
      simpa [real, annotatedMarker] using shape.2.2]
    simp [annotatedMarker, codeLocations, codeLocationsExp]
  have allDistinct : ((program.2.map Prod.fst) ++ (codeLocations real ++
      codeLocations (program.2.map (fun (_, _, body) => body)))).Nodup := by
    rw [mainEq]
    exact numberedCallOracle_entries_and_locations_nodup fuel oracle state index
  have entriesDistinct := allDistinct.of_append_left
  have bodyMainDistinct := allDistinct.of_append_right
  have auxDistinct : ((program.2.map Prod.fst) ++
      codeLocations (program.2.map (fun (_, _, body) => body))).Nodup := by
    apply List.Nodup.append entriesDistinct bodyMainDistinct.of_append_right
    intro label inEntry inBody
    exact allDistinct.disjoint inEntry (List.mem_append_right _ inBody)
  have mainAuxDisjoint : ∀ label ∈ codeLocations real,
      label ∉ (program.2.map Prod.fst) ++ codeLocations (program.2.map (fun (_, _, body) => body)) := by
    intro label inMain inAux
    rcases List.mem_append.mp inAux with entry | body
    · exact allDistinct.disjoint entry (List.mem_append_left _ inMain)
    · exact bodyMainDistinct.disjoint inMain body
  have sourceAbove : ∀ label ∈ codeLocations (numbered index).2.1,
      start + max 1 real.length ≤ label := by
    intro label member
    have bound := ClosNumber.compileInc_location_after_entries start label expressions (by
      simpa [numbered, stateCo, ClosNumber.ignoreTable, start, expressions] using member)
    simpa [lengthEq] using bound
  have within := ClosCall.compileIncFuelOracle_locationsWithin fuel numbered index
  have mainAbove : ∀ label ∈ codeLocations real, start + max 1 real.length ≤ label := by
    intro label member
    rw [mainEq] at member
    exact sourceAbove label (within.1 label ((ClosAnnotate.annotateList_codeLocations_sublist 0 called.2.1).subset member))
  have auxAbove : ∀ label ∈ (program.2.map Prod.fst) ++
      codeLocations (program.2.map (fun (_, _, body) => body)), start + max 1 real.length ≤ label := by
    intro label member
    rcases List.mem_append.mp member with entry | body
    · have before : label ∈ called.2.2.map Prod.fst := by simpa [program, ClosAnnotate.compileInc, annotated_labels] using entry
      obtain ⟨origin, inSource, equal⟩ := callOracle_label_origin fuel numbered index label before
      have bound := sourceAbove origin inSource
      omega
    · have before : label ∈ codeLocations (called.2.2.map (fun (_, _, body) => body)) :=
        (ClosAnnotate.compile_codeLocations_sublist called.2.2).subset body
      obtain ⟨sourceBody, bodyMember, locMember⟩ := (mem_codeLocations label _).1 before
      obtain ⟨entry, entryMember, bodyEq⟩ := List.mem_map.mp bodyMember
      obtain ⟨name, arity, sourceBody'⟩ := entry
      simp only at bodyEq
      subst sourceBody
      exact sourceAbove label (within.2 name arity sourceBody' entryMember label locMember)
  exact compileInc_labels_nodup maxApp start program real extract bodyMainDistinct.of_append_left
    auxDistinct mainAbove auxAbove mainAuxDisjoint


/-- Main expressions and auxiliary bodies produced by the direct-call
oracle retain the numbered source interval, even after annotation. -/
theorem numberedCallOracle_nested_location_bounds {C : Type} (fuel : Nat)
    (oracle : Nat → (Nat × (NumSet × C)) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (state : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) :
    ∀ index,
      (∀ loc ∈ codeLocations (ClosAnnotate.annotateList 0
        (ClosCall.compileIncFuelOracle fuel (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2.1),
        (oracle index).1.1 ≤ loc ∧ loc + 1 < (oracle (index + 1)).1.1) ∧
      (∀ loc ∈ codeLocations ((ClosAnnotate.compile
        (ClosCall.compileIncFuelOracle fuel (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2.2).map
          (fun (_, _, body) => body)),
        (oracle index).1.1 ≤ loc ∧ loc + 1 < (oracle (index + 1)).1.1) := by
  intro index
  let numbered := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
  let called := ClosCall.compileIncFuelOracle fuel numbered index
  have within := ClosCall.compileIncFuelOracle_locationsWithin fuel numbered index
  constructor
  · intro loc member
    have sourceLoc : loc ∈ codeLocations (numbered index).2.1 :=
      within.1 loc ((ClosAnnotate.annotateList_codeLocations_sublist 0 called.2.1).subset member)
    exact numberingOracle_location_successor_bounds oracle state index loc sourceLoc
  · intro loc member
    have before : loc ∈ codeLocations (called.2.2.map (fun (_, _, body) => body)) :=
      (ClosAnnotate.compile_codeLocations_sublist called.2.2).subset member
    obtain ⟨body, bodyMember, locMember⟩ := (mem_codeLocations loc _).1 before
    obtain ⟨entry, entryMember, bodyEq⟩ := List.mem_map.mp bodyMember
    obtain ⟨name, arity, sourceBody⟩ := entry
    simp only at bodyEq
    subst body
    have sourceLoc : loc ∈ codeLocations (numbered index).2.1 :=
      within.2 name arity sourceBody entryMember loc locMember
    exact numberingOracle_location_successor_bounds oracle state index loc sourceLoc

/-- Incremental BVL labels stay within the numbering interval shifted by the
application-stub prefix, including labels generated for auxiliary functions. -/
theorem numberedCallOracle_bvl_labels_range {C : Type} (maxApp fuel : Nat)
    (oracle : Nat → (Nat × (NumSet × C)) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (state : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) :
    ∀ index label, label ∈ (compileInc maxApp (ClosAnnotate.compileInc
      (ClosCall.compileIncFuelOracle fuel
        (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2)).map Prod.fst →
      (oracle index).1.1 + numStubs maxApp ≤ label ∧
        label < (oracle (index + 1)).1.1 + numStubs maxApp := by
  intro index label member
  let start := (oracle index).1.1
  let limit := (oracle (index + 1)).1.1
  let expressions := (oracle index).2.1
  let numbered := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
  let called := ClosCall.compileIncFuelOracle fuel numbered index
  let program := ClosAnnotate.compileInc called.2
  obtain ⟨output, marker, outputLength⟩ := numberedCallOracle_marker fuel oracle index
  have marker' : called.2.1 = .op .none (.intOp (.const (Int.ofNat start))) [] :: output := marker
  have annotatedMarker : program.1 = .op .none (.intOp (.const (Int.ofNat start))) [] ::
      ClosAnnotate.annotateList 0 output := by
    simpa [program, ClosAnnotate.compileInc, marker'] using ClosAnnotate.annotateList_name_marker start output
  let real := (extractName program.1).2
  have shape := extractName_numbered_marker start (ClosAnnotate.annotateList 0 output)
  have startEq : (extractName program.1).1 = start := by simpa [annotatedMarker] using shape.1
  have lengthEq : real.length = max 1 expressions.length := by
    have l : real.length = max 1 output.length := by
      simpa [real, annotatedMarker, ClosAnnotate.annotateList_length] using shape.2.1
    simpa [expressions, outputLength] using l
  have extract : extractName program.1 = (start, real) := by
    cases h : extractName program.1 with
    | mk first second => simp [real, h] at startEq ⊢; exact startEq
  have mainEq : codeLocations real = codeLocations program.1 := by
    rw [show codeLocations real = codeLocations (ClosAnnotate.annotateList 0 output) by
      simpa [real, annotatedMarker] using shape.2.2]
    simp [annotatedMarker, codeLocations, codeLocationsExp]
  have entriesBound : start + max 1 real.length ≤ limit := by
    have reserve := ClosNumber.compileInc_reservation start expressions
    have next := state index
    simp only [ClosNumber.ignoreTable] at next
    simpa [lengthEq, start, expressions, limit, next] using reserve
  have nested := numberedCallOracle_nested_location_bounds fuel oracle state index
  have mainBounds : ∀ loc ∈ codeLocations real, start ≤ loc ∧ loc < limit := by
    intro loc inside
    rw [mainEq] at inside
    have bound := nested.1 loc inside
    omega
  have auxBounds : ∀ entry ∈ program.2, start ≤ entry.1 ∧ entry.1 < limit ∧
      ∀ loc ∈ codeLocationsExp entry.2.2, start ≤ loc ∧ loc < limit := by
    intro entry inside
    have labelIn : entry.1 ∈ program.2.map Prod.fst := List.mem_map.mpr ⟨entry, inside, rfl⟩
    have bound := (numberedCallOracle_aux_distinct_and_range fuel oracle state index).2 entry.1 labelIn
    refine ⟨bound.1, bound.2, ?_⟩
    intro loc locIn
    have bodyIn : entry.2.2 ∈ program.2.map (fun (_, _, body) => body) :=
      List.mem_map.mpr ⟨entry, inside, rfl⟩
    have locs : loc ∈ codeLocations (program.2.map (fun (_, _, body) => body)) :=
      (mem_codeLocations loc _).2 ⟨entry.2.2, bodyIn, locIn⟩
    have locBound := nested.2 loc locs
    omega
  exact compileInc_labels_range maxApp start limit program real extract entriesBound mainBounds auxBounds label member

/-- Numbering intervals order the compiled labels of successive oracle
entries, provided the initial labels precede the first interval. -/
theorem numberedCallOracle_bvl_labels_ordered {C : Type} (maxApp fuel : Nat)
    (oracle : Nat → (Nat × (NumSet × C)) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (state : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    (initial : Set Nat)
    (initialBound : ∀ label ∈ initial, label < (oracle 0).1.1 + numStubs maxApp) :
    oracleMonotonic
      (fun entry => {label | label ∈ (compileInc maxApp (ClosAnnotate.compileInc entry.2)).map Prod.fst})
      (· < ·) initial
      (ClosCall.compileIncFuelOracle fuel (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)) := by
  have step : ∀ i, (oracle i).1.1 ≤ (oracle (i + 1)).1.1 := by
    intro i
    have reserve := ClosNumber.compileInc_reservation (oracle i).1.1 (oracle i).2.1
    have next := state i
    simp only [ClosNumber.ignoreTable] at next
    omega
  have monotone : ∀ i j, i ≤ j → (oracle i).1.1 ≤ (oracle j).1.1 := by
    intro i j le
    induction le with
    | refl => exact Nat.le_refl _
    | @step j le ih => exact Nat.le_trans ih (step j)
  constructor
  · intro i j x y lt xmem ymem
    have xbound := numberedCallOracle_bvl_labels_range maxApp fuel oracle state i x xmem
    have ybound := numberedCallOracle_bvl_labels_range maxApp fuel oracle state j y ymem
    have between := monotone (i + 1) j (by omega)
    omega
  · intro i x y xmem ymem
    have xbound := initialBound x xmem
    have ybound := numberedCallOracle_bvl_labels_range maxApp fuel oracle state i y ymem
    have between := monotone 0 i (Nat.zero_le i)
    omega

end Flapjack.Compiler.Backend.ClosToBvl
