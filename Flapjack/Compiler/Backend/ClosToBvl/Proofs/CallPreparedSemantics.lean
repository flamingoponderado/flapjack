import Flapjack.Compiler.Backend.ClosCall.Proofs.IncrementalInstall
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.InstalledSemantics

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

end Flapjack.Compiler.Backend.ClosToBvl
