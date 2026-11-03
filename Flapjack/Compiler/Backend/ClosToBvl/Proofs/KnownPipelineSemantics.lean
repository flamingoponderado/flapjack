import Flapjack.Compiler.Backend.ClosToBvl.Proofs.NumberKnownSemantics
import Flapjack.Compiler.Backend.ClosLetop.Proofs.Semantics

/-! Composition of the closure optimization passes used by the compiler. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.ClosKnown
open Flapjack.Compiler.Backend.ClosKnown.OracleGlobals
open Flapjack.Compiler.Backend.ClosKnown.OracleMonotonic
open Flapjack.Compiler.Backend.ClosKnown.StateOracleDisjoint
open Flapjack.Compiler.Backend.ClosKnown.UniqueGlobalsPort
open Flapjack.Compiler.Backend.ClosKnown.Relations.StateRelation.Oracle
open Flapjack.Compiler.Backend.ClosProps.StateGlobalSafety

/-- The incremental program carrier shared by the closure compiler passes. -/
abbrev ClosureProgram := List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)

/-- Specialize the polymorphic cleanup passes to the compiler's program carrier. -/
abbrev fvsInc : ClosureProgram → ClosureProgram := ClosFvs.compileInc
abbrev ticksInc : ClosureProgram → ClosureProgram := ClosTicks.compileInc
abbrev letopInc : ClosureProgram → ClosureProgram := ClosLetop.compileInc

/-- The executable combined tick and let-operation traversal has the same
result as the two source-shaped traversals in sequence. This Lean-side
composition has no standalone HOL declaration. -/
theorem ticks_letop_bounded (fuel : Nat) (program : List ClosLang.Exp) :
    (program.mapM fun e => do
      let e ← ClosTicks.removeBounded fuel e
      ClosLetop.compileBounded fuel e) =
      some (ClosLetop.compileList (ClosTicks.removeList program)) := by
  induction program with
  | nil => rfl
  | cons head tail ih =>
    simp only [ClosTicks.removeBounded_eq_source, ClosLetop.compileBounded_eq_source, bind, Option.bind] at ih
    simp only [List.mapM_cons]
    rw [ClosTicks.removeBounded_eq_source]
    simp only [bind, Option.bind, ClosLetop.compileBounded_eq_source]
    simp only [ClosTicks.removeBounded_eq_source]
    rw [ih]
    rfl

/-- The enabled executable known-function pipeline returns exactly the
source-shaped free-variable, known, tick and let-operation outputs. This
Lean-side production agreement has no standalone HOL declaration. -/
theorem known_compileFuel_eq (fuel : Nat) (config : ClosKnown.Config) (program : List ClosLang.Exp)
    (optimized : List (ClosLang.Exp × ValApprox)) (globals : Spt ValApprox)
    (knownRun : ClosKnown.knownListTotal config (ClosFvs.compile program) [] .ln = (optimized, globals)) :
    ClosKnown.compileFuel fuel (some config) program =
      some (some { config with valApproxSpt := globals },
        ClosLetop.compileList (ClosTicks.removeList (optimized.map Prod.fst))) := by
  simp only [ClosKnown.compileFuel, ClosFvs.compileBounded_eq_source, ClosKnown.knownListBounded,
    knownRun, bind, Option.bind]
  have mapEq : (optimized.mapM fun entry => do
      let e ← ClosTicks.removeBounded fuel entry.1
      ClosLetop.compileBounded fuel e) =
      some (ClosLetop.compileList (ClosTicks.removeList (optimized.map Prod.fst))) := by
    simpa only [List.mapM_map, Function.comp_def] using ticks_letop_bounded fuel (optimized.map Prod.fst)
  simp only [bind, Option.bind] at mapEq
  rw [mapEq]
  rfl

/-- Numbering, free-variable cleanup, known-function optimization, tick
removal, let-operation cleanup and annotation preserve closure observations
under their source invariants. The theorem uses the executed bounded passes;
it is Lean-side composition, not a standalone HOL declaration. -/
theorem number_fvs_known_ticks_letop_annotate_semantics {C F : Type} (ffi : HolFfiState F)
    (fuel maxApp number : Nat) (knownConfig : ClosKnown.Config)
    (oracle : CompileOracle (Nat × (Spt ValApprox × C))) (compiler : Compiler C)
    (program : List ClosLang.Exp) (optimized : List (ClosLang.Exp × ValApprox)) (globals : Spt ValApprox)
    (positive : 1 ≤ maxApp)
    (notFail : semantics ffi maxApp HolFiniteMapExact.holEmpty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCc fvsInc
          (stateCc (ClosKnown.compileInc knownConfig)
            (pureCc ticksInc (pureCc letopInc
              (pureCc ClosAnnotate.compileInc compiler)))))) program ≠ .fail)
    (numberSafe : ¬ containsAppSome maxApp program ∧
      ∀ n, (oracle n).2.2 = [] ∧ ¬ containsAppSome maxApp (oracle n).2.1)
    (knownSafe :
      let numberedCo := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
      let co : CompileOracle (Spt ValApprox × C) := pureCo fvsInc ∘ numberedCo
      let xs := ClosFvs.compile (ClosNumber.renumberList number program).2
      (∀ n, (co n).2.2 = []) ∧ (∀ n, fvMax 0 (co n).2.1) ∧
      (∀ n exps extra, (co n).2 = (exps, extra) → ∀ e ∈ exps, esgcFree e) ∧
      everyFnVarsNone xs ∧ coEveryFnVarsNone co ∧ oracleGapproxSubspt co ∧
      oracleStateSgcFree co ∧ isStateOracle (ClosKnown.compileInc knownConfig) co ∧
      uniqueSetGlobals xs co ∧ (∀ e ∈ xs, esgcFree e) ∧ fvMax 0 xs ∧
      (co 0).1.1 = globals ∧ oracleGapproxDisjoint globals co ∧
      ClosKnown.knownListTotal knownConfig xs [] .ln = (optimized, globals))
    (annotationSafe :
      let knownCo : CompileOracle C := stateCo (ClosKnown.compileInc knownConfig)
        (pureCo fvsInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
      let co : CompileOracle C := pureCo letopInc ∘ pureCo ticksInc ∘ knownCo
      everyFnVarsNone (ClosLetop.compileList (ClosTicks.removeList (optimized.map Prod.fst))) ∧
      ∀ n, everyFnVarsNone (co n).2.1 ∧
        everyFnVarsNone ((co n).2.2.map (fun (_, _, body) => body))) :
    ∃ fvsOutput optimizedOutput,
      (ClosNumber.renumberList number program).2.mapM (ClosFvs.removeBounded fuel 0) = some fvsOutput ∧
      ((optimized.map Prod.fst).mapM fun e => do
        let e ← ClosTicks.removeBounded fuel e
        ClosLetop.compileBounded fuel e) = some optimizedOutput ∧
      ClosKnown.compileFuel fuel (some knownConfig) (ClosNumber.renumberList number program).2 =
        some (some { knownConfig with valApproxSpt := globals }, optimizedOutput) ∧
      semantics ffi maxApp HolFiniteMapExact.holEmpty
        (pureCo ClosAnnotate.compileInc ∘ pureCo letopInc ∘ pureCo ticksInc ∘
          stateCo (ClosKnown.compileInc knownConfig)
            (pureCo fvsInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle))
        compiler (ClosAnnotate.annotateList 0 optimizedOutput) =
      semantics ffi maxApp HolFiniteMapExact.holEmpty oracle
        (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
          (pureCc fvsInc
            (stateCc (ClosKnown.compileInc knownConfig)
              (pureCc ticksInc (pureCc letopInc
                (pureCc ClosAnnotate.compileInc compiler)))))) program := by
  let numberedCo : CompileOracle (Spt ValApprox × C) := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
  let numbered := (ClosNumber.renumberList number program).2
  let co : CompileOracle (Spt ValApprox × C) := pureCo fvsInc ∘ numberedCo
  let transformed := ClosFvs.compile numbered
  let afterKnown := pureCc ticksInc (pureCc letopInc (pureCc ClosAnnotate.compileInc compiler))
  let knownCompiler := stateCc (ClosKnown.compileInc knownConfig) afterKnown
  have numberEq : semantics ffi maxApp HolFiniteMapExact.holEmpty numberedCo
      (pureCc fvsInc knownCompiler) numbered =
      semantics ffi maxApp HolFiniteMapExact.holEmpty oracle
        (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) (pureCc fvsInc knownCompiler)) program :=
    ClosNumber.semanticsNumberHOL ffi maxApp number oracle (pureCc fvsInc knownCompiler)
      program notFail numberSafe
  have numberedNonfail : semantics ffi maxApp HolFiniteMapExact.holEmpty numberedCo
      (pureCc fvsInc knownCompiler) numbered ≠ .fail := by rw [numberEq]; exact notFail
  have numberedAux : ∀ n, (numberedCo n).2.2 = [] := by
    intro n
    simpa [numberedCo, stateCo, ClosNumber.ignoreTable] using (numberSafe.2 n).1
  have fvsEq : semantics ffi maxApp HolFiniteMapExact.holEmpty co knownCompiler transformed =
      semantics ffi maxApp HolFiniteMapExact.holEmpty numberedCo (pureCc fvsInc knownCompiler) numbered :=
    ClosFvs.semantics_compile ffi maxApp numberedCo knownCompiler numbered numberedNonfail ⟨numberedAux, positive⟩
  have fvsNonfail : semantics ffi maxApp HolFiniteMapExact.holEmpty co knownCompiler transformed ≠ .fail := by
    rw [fvsEq, numberEq]; exact notFail
  let knownCo : CompileOracle C := stateCo (ClosKnown.compileInc knownConfig) co
  have knownEq : semantics ffi maxApp HolFiniteMapExact.holEmpty knownCo afterKnown (optimized.map Prod.fst) =
      semantics ffi maxApp HolFiniteMapExact.holEmpty co knownCompiler transformed :=
    ClosKnown.Semantics.semanticsKnownHOL knownConfig ffi maxApp co afterKnown transformed optimized globals
      fvsNonfail knownSafe
  have knownNonfail : semantics ffi maxApp HolFiniteMapExact.holEmpty knownCo afterKnown
      (optimized.map Prod.fst) ≠ .fail := by rw [knownEq, fvsEq, numberEq]; exact notFail
  have knownAux : ∀ n, (knownCo n).2.2 = [] := by
    intro n
    simp [knownCo, stateCo, ClosKnown.compileInc, co, pureCo, fvsInc, ClosFvs.compileInc]
  let ticksCo : CompileOracle C := pureCo ticksInc ∘ knownCo
  let ticksOutput := ClosTicks.removeList (optimized.map Prod.fst)
  have ticksEq := ClosTicks.semantics_remove_ticks ffi maxApp knownCo
    (pureCc letopInc (pureCc ClosAnnotate.compileInc compiler)) (optimized.map Prod.fst)
    knownNonfail ⟨knownAux, positive⟩
  have ticksNonfail : semantics ffi maxApp HolFiniteMapExact.holEmpty ticksCo
      (pureCc letopInc (pureCc ClosAnnotate.compileInc compiler)) ticksOutput ≠ .fail := by
    rw [← ticksEq, knownEq, fvsEq, numberEq]; exact notFail
  have ticksAux : ∀ n, (ticksCo n).2.2 = [] := by simp [ticksCo, pureCo, ticksInc, ClosTicks.compileInc]
  let letopCo : CompileOracle C := pureCo letopInc ∘ ticksCo
  let letopOutput := ClosLetop.compileList ticksOutput
  have letopEq := ClosLetop.semantics_let_op ffi maxApp ticksCo
    (pureCc ClosAnnotate.compileInc compiler) ticksOutput ticksNonfail ⟨ticksAux, positive⟩
  have letopNonfail : semantics ffi maxApp HolFiniteMapExact.holEmpty letopCo
      (pureCc ClosAnnotate.compileInc compiler) letopOutput ≠ .fail := by
    rw [letopEq, ← ticksEq, knownEq, fvsEq, numberEq]; exact notFail
  have annotated := ClosAnnotate.semanticsAnnotate_sourceShape ffi maxApp [] letopCo compiler
    letopOutput (by simpa [HolFiniteMapExact.alistToFmap, HolFiniteMapExact.holEmpty,
      HolFiniteMapExact.updateListEq, FUPDATE_LIST_HOL] using letopNonfail)
    ⟨annotationSafe.1, by simp [everyFnVarsNone], annotationSafe.2⟩
  have annotationEq : semantics ffi maxApp HolFiniteMapExact.holEmpty
      (pureCo ClosAnnotate.compileInc ∘ letopCo) compiler (ClosAnnotate.annotateList 0 letopOutput) =
      semantics ffi maxApp HolFiniteMapExact.holEmpty letopCo
        (pureCc ClosAnnotate.compileInc compiler) letopOutput := by
    simpa [HolFiniteMapExact.alistToFmap, HolFiniteMapExact.holEmpty,
      HolFiniteMapExact.updateListEq, FUPDATE_LIST_HOL, ClosAnnotate.compile] using annotated
  have knownRun : ClosKnown.knownListTotal knownConfig (ClosFvs.compile numbered) [] .ln = (optimized, globals) := by
    rcases knownSafe with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, run⟩
    exact run
  exact ⟨transformed, letopOutput, ClosFvs.compileBounded_eq_source fuel numbered,
    ticks_letop_bounded fuel (optimized.map Prod.fst),
    known_compileFuel_eq fuel knownConfig numbered optimized globals knownRun,
    annotationEq.trans (letopEq.trans (ticksEq.symm.trans (knownEq.trans (fvsEq.trans numberEq))))⟩

end Flapjack.Compiler.Backend.ClosToBvl
