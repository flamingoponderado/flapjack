import Flapjack.Compiler.Backend.ClosToBvl.Proofs.InitialState

/-! Connect installed compiled entries to the initial source code map. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- The original association-list code map uses a right fold, represented by
reversing the source entries before the canonical finite-map list update. -/
def initialSourceCode (program : List (Nat × Nat × ClosLang.Exp)) :
    HolFiniteMapExact Nat (Nat × ClosLang.Exp) :=
  HolFiniteMapExact.empty.updateListEq program.reverse

/-- A successful lookup in the initial source code map identifies an entry
of the original program, including when earlier duplicate names shadow later
ones. -/
theorem initialSourceCode_lookup_mem (program : List (Nat × Nat × ClosLang.Exp))
    (name arity : Nat) (body : ClosLang.Exp)
    (found : (initialSourceCode program).lookup name = some (arity, body)) :
    (name, arity, body) ∈ program := by
  have split := install_source_lookup HolFiniteMapExact.empty program.reverse name arity body found
  cases split with
  | inl member => simpa using member
  | inr impossible => simp [HolFiniteMapExact.empty] at impossible

/-- Installing the compiled program supplies the complete source-code
correspondence required by the initial state relation. -/
theorem initialSourceCode_compiled (maxApp : Nat) (program : List (Nat × Nat × ClosLang.Exp))
    (code : Spt (Nat × Bvl.Exp)) (installed : codeInstalled (compileProgExpsHOL maxApp program) code) :
    ∀ name arity body, (initialSourceCode program).lookup name = some (arity, body) →
      ∃ aux targetBody finalAux, compileExpsHOL maxApp [body] aux = ([targetBody], finalAux) ∧
        sptLookup (name + numStubs maxApp) code = some (arity, targetBody) ∧ codeInstalled finalAux code := by
  intro name arity body found
  exact compileProgExps_entry_installed maxApp program code name arity body installed
    (initialSourceCode_lookup_mem program name arity body found)

/-- Annotations on every source program entry give the initial state's code
annotation invariant, including for programs with duplicate names. -/
theorem initialSourceCode_annotations {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (program : List (Nat × Nat × ClosLang.Exp)) (oracle : ClosSem.CompileOracle C)
    (compiler : ClosSem.Compiler C)
    (locations : ∀ name arity body, (name, arity, body) ∈ program → ClosProps.everyFnLocationSome [body])
    (varsAnnotated : ∀ name arity body, (name, arity, body) ∈ program → ClosProps.everyFnVarsSome [body]) :
    codeAnnotations (ClosSem.initialState ffi maxApp (initialSourceCode program) oracle compiler 0) := by
  constructor <;> intro name arity body found
  · exact locations name arity body (initialSourceCode_lookup_mem program name arity body found)
  · exact varsAnnotated name arity body (initialSourceCode_lookup_mem program name arity body found)

/-- A compiled and installed source program supplies the code and annotation
premises of the installed-entry behavior theorem. The application-stub,
entry-point and oracle invariants remain explicit prerequisites. -/
theorem compiledProgram_entry_semantics {C F : Type} (ffi : HolFfiState F)
    (maxApp sourceStart targetStart : Nat) (program : List (Nat × Nat × ClosLang.Exp))
    (sourceOracle : ClosSem.CompileOracle C) (sourceCompiler : ClosSem.Compiler C)
    (targetCode : Spt (Nat × Bvl.Exp)) (targetOracle : BvlSem.CompileOracle C)
    (targetCompiler : BvlSem.Compiler C)
    (nonfail : ClosSem.semantics ffi maxApp (initialSourceCode program) sourceOracle sourceCompiler
      [.call .none 0 sourceStart []] ≠ .fail)
    (installed : codeInstalled (compileProgExpsHOL maxApp program) targetCode)
    (locations : ∀ name arity body, (name, arity, body) ∈ program → ClosProps.everyFnLocationSome [body])
    (varsAnnotated : ∀ name arity body, (name, arity, body) ∈ program → ClosProps.everyFnVarsSome [body])
    (generic : ∀ n, n < maxApp → sptLookup (genericAppFnLocation n) targetCode =
      some (n + 2, generateGenericApp maxApp n))
    (partialStubs : ∀ total n, total < maxApp ∧ n < total →
      sptLookup (partialAppFnLocation maxApp total n) targetCode =
        some (total - n + 1, generatePartialAppClosureFn total n))
    (force : sptLookup (numStubs maxApp - 2) targetCode = some (2, forceThunkCode))
    (oracle : compileOracleInv maxApp (initialSourceCode program) sourceCompiler sourceOracle
      targetCode targetCompiler targetOracle)
    (entry : sptLookup targetStart targetCode = some (0, initGlobals maxApp (sourceStart + numStubs maxApp))) :
    BvlSem.semantics ffi targetCode targetOracle targetCompiler targetStart =
      ClosSem.semantics ffi maxApp (initialSourceCode program) sourceOracle sourceCompiler [.call .none 0 sourceStart []] := by
  exact entry_semantics_eq ffi maxApp sourceStart targetStart (initialSourceCode program) sourceOracle sourceCompiler
    targetCode targetOracle targetCompiler nonfail generic partialStubs force oracle
    (initialSourceCode_compiled maxApp program targetCode installed)
    (initialSourceCode_annotations ffi maxApp program sourceOracle sourceCompiler locations varsAnnotated) entry

end Flapjack.Compiler.Backend.ClosToBvl
