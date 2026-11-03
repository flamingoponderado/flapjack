import Flapjack.Compiler.Backend.ClosNumber.Proofs.Semantics
import Flapjack.Compiler.Backend.ClosKnown.Proofs.Semantics
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.InstalledSemantics
import Flapjack.Compiler.Backend.ClosFvs.Proofs.Semantics
import Flapjack.Compiler.Backend.ClosTicks.Proofs.Semantics

/-! Observational composition of numbering and known-function optimization. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.ClosKnown
open Flapjack.Compiler.Backend.ClosKnown.OracleGlobals
open Flapjack.Compiler.Backend.ClosKnown.OracleMonotonic
open Flapjack.Compiler.Backend.ClosKnown.StateOracleDisjoint
open Flapjack.Compiler.Backend.ClosKnown.UniqueGlobalsPort
open Flapjack.Compiler.Backend.ClosKnown.Relations.StateRelation.Oracle
open Flapjack.Compiler.Backend.ClosProps.StateGlobalSafety

/-- Numbering followed by known-function optimization preserves closure
observations when the two passes' source conditions hold. This composition
is Flapjack infrastructure and has no separate HOL declaration. -/
theorem number_known_semantics {C F : Type} (ffi : HolFfiState F) (maxApp number : Nat)
    (knownConfig : ClosKnown.Config) (oracle : CompileOracle (Nat × (Spt ValApprox × C)))
    (compiler : Compiler C) (program : List ClosLang.Exp)
    (optimized : List (ClosLang.Exp × ValApprox)) (globals : Spt ValApprox)
    (notFail : semantics ffi maxApp HolFiniteMapExact.holEmpty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (stateCc (ClosKnown.compileInc knownConfig) compiler)) program ≠ .fail)
    (numberSafe : ¬ containsAppSome maxApp program ∧
      ∀ n, (oracle n).2.2 = [] ∧ ¬ containsAppSome maxApp (oracle n).2.1)
    (knownSafe :
      let co := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
      let xs := (ClosNumber.renumberList number program).2
      (∀ n, (co n).2.2 = []) ∧ (∀ n, fvMax 0 (co n).2.1) ∧
      (∀ n exps extra, (co n).2 = (exps, extra) → ∀ e ∈ exps, esgcFree e) ∧
      everyFnVarsNone xs ∧ coEveryFnVarsNone co ∧ oracleGapproxSubspt co ∧
      oracleStateSgcFree co ∧ isStateOracle (ClosKnown.compileInc knownConfig) co ∧
      uniqueSetGlobals xs co ∧ (∀ e ∈ xs, esgcFree e) ∧ fvMax 0 xs ∧
      (co 0).1.1 = globals ∧ oracleGapproxDisjoint globals co ∧
      ClosKnown.knownListTotal knownConfig xs [] .ln = (optimized, globals)) :
    semantics ffi maxApp HolFiniteMapExact.holEmpty
      (stateCo (ClosKnown.compileInc knownConfig)
        (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)) compiler (optimized.map Prod.fst) =
    semantics ffi maxApp HolFiniteMapExact.holEmpty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (stateCc (ClosKnown.compileInc knownConfig) compiler)) program := by
  let co := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
  let xs := (ClosNumber.renumberList number program).2
  have numberEq : semantics ffi maxApp HolFiniteMapExact.holEmpty co
      (stateCc (ClosKnown.compileInc knownConfig) compiler) xs =
      semantics ffi maxApp HolFiniteMapExact.holEmpty oracle
        (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
          (stateCc (ClosKnown.compileInc knownConfig) compiler)) program :=
    ClosNumber.semanticsNumberHOL ffi maxApp number oracle
      (stateCc (ClosKnown.compileInc knownConfig) compiler) program notFail numberSafe
  have numberedNonfail : semantics ffi maxApp HolFiniteMapExact.holEmpty co
      (stateCc (ClosKnown.compileInc knownConfig) compiler) xs ≠ .fail := by
    rw [numberEq]
    exact notFail
  exact (ClosKnown.Semantics.semanticsKnownHOL knownConfig ffi maxApp co compiler xs optimized globals
    numberedNonfail knownSafe).trans numberEq

/-- Numbering, known-function optimization and closure annotation preserve
observations when their source invariants hold. This composition has no
separate HOL declaration; it does not yet cover the surrounding driver. -/
theorem number_known_annotate_semantics {C F : Type} (ffi : HolFfiState F) (maxApp number : Nat)
    (knownConfig : ClosKnown.Config) (oracle : CompileOracle (Nat × (Spt ValApprox × C)))
    (compiler : Compiler C) (program : List ClosLang.Exp)
    (optimized : List (ClosLang.Exp × ValApprox)) (globals : Spt ValApprox)
    (notFail : semantics ffi maxApp HolFiniteMapExact.holEmpty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (stateCc (ClosKnown.compileInc knownConfig) (pureCc ClosAnnotate.compileInc compiler))) program ≠ .fail)
    (numberSafe : ¬ containsAppSome maxApp program ∧
      ∀ n, (oracle n).2.2 = [] ∧ ¬ containsAppSome maxApp (oracle n).2.1)
    (knownSafe :
      let co := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
      let xs := (ClosNumber.renumberList number program).2
      (∀ n, (co n).2.2 = []) ∧ (∀ n, fvMax 0 (co n).2.1) ∧
      (∀ n exps extra, (co n).2 = (exps, extra) → ∀ e ∈ exps, esgcFree e) ∧
      everyFnVarsNone xs ∧ coEveryFnVarsNone co ∧ oracleGapproxSubspt co ∧
      oracleStateSgcFree co ∧ isStateOracle (ClosKnown.compileInc knownConfig) co ∧
      uniqueSetGlobals xs co ∧ (∀ e ∈ xs, esgcFree e) ∧ fvMax 0 xs ∧
      (co 0).1.1 = globals ∧ oracleGapproxDisjoint globals co ∧
      ClosKnown.knownListTotal knownConfig xs [] .ln = (optimized, globals))
    (annotationSafe :
      let co := stateCo (ClosKnown.compileInc knownConfig)
        (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
      everyFnVarsNone (optimized.map Prod.fst) ∧
      ∀ n, everyFnVarsNone (co n).2.1 ∧
        everyFnVarsNone ((co n).2.2.map (fun (_, _, body) => body))) :
    semantics ffi maxApp HolFiniteMapExact.holEmpty
      (pureCo ClosAnnotate.compileInc ∘
        stateCo (ClosKnown.compileInc knownConfig)
          (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle))
      compiler (ClosAnnotate.annotateList 0 (optimized.map Prod.fst)) =
    semantics ffi maxApp HolFiniteMapExact.holEmpty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (stateCc (ClosKnown.compileInc knownConfig) (pureCc ClosAnnotate.compileInc compiler))) program := by
  let co := stateCo (ClosKnown.compileInc knownConfig)
    (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
  have knownEq := number_known_semantics ffi maxApp number knownConfig oracle
    (pureCc ClosAnnotate.compileInc compiler) program optimized globals notFail numberSafe knownSafe
  have knownNonfail : semantics ffi maxApp HolFiniteMapExact.holEmpty co
      (pureCc ClosAnnotate.compileInc compiler) (optimized.map Prod.fst) ≠ .fail := by
    rw [knownEq]
    exact notFail
  have annotated := ClosAnnotate.semanticsAnnotate_sourceShape ffi maxApp [] co compiler
    (optimized.map Prod.fst) (by
      simpa [HolFiniteMapExact.alistToFmap, HolFiniteMapExact.holEmpty,
        HolFiniteMapExact.updateListEq, FUPDATE_LIST_HOL] using knownNonfail)
    ⟨annotationSafe.1, by simp [everyFnVarsNone], annotationSafe.2⟩
  have annotationEq : semantics ffi maxApp HolFiniteMapExact.holEmpty
      (pureCo ClosAnnotate.compileInc ∘ co) compiler
      (ClosAnnotate.annotateList 0 (optimized.map Prod.fst)) =
      semantics ffi maxApp HolFiniteMapExact.holEmpty co
        (pureCc ClosAnnotate.compileInc compiler) (optimized.map Prod.fst) := by
    simpa [HolFiniteMapExact.alistToFmap, HolFiniteMapExact.holEmpty,
      HolFiniteMapExact.updateListEq, FUPDATE_LIST_HOL, ClosAnnotate.compile] using annotated
  exact annotationEq.trans knownEq

/-- Tick removal followed by annotation preserves observations under the
original pass invariants. This is Flapjack composition infrastructure and
does not yet include let-operation cleanup. -/
theorem ticks_annotate_semantics {C F : Type} (ffi : HolFfiState F) (fuel maxApp : Nat)
    (oracle : CompileOracle C) (compiler : Compiler C) (program : List ClosLang.Exp)
    (notFail : semantics ffi maxApp HolFiniteMapExact.holEmpty oracle
      (pureCc ClosTicks.compileInc (pureCc ClosAnnotate.compileInc compiler)) program ≠ .fail)
    (tickSafe : (∀ n, (oracle n).2.2 = []) ∧ 1 ≤ maxApp)
    (annotationSafe :
      let co : CompileOracle C := pureCo ClosTicks.compileInc ∘ oracle
      everyFnVarsNone (ClosTicks.removeList program) ∧
      ∀ n, everyFnVarsNone (co n).2.1 ∧
        everyFnVarsNone ((co n).2.2.map (fun (_, _, body) => body))) :
    ∃ transformed, program.mapM (ClosTicks.removeBounded fuel) = some transformed ∧
      semantics ffi maxApp HolFiniteMapExact.holEmpty
        (pureCo ClosAnnotate.compileInc ∘ pureCo ClosTicks.compileInc ∘ oracle)
        compiler (ClosAnnotate.annotateList 0 transformed) =
      semantics ffi maxApp HolFiniteMapExact.holEmpty oracle
        (pureCc ClosTicks.compileInc (pureCc ClosAnnotate.compileInc compiler)) program := by
  let co : CompileOracle C := pureCo ClosTicks.compileInc ∘ oracle
  have ticksEq := ClosTicks.semantics_remove_ticks ffi maxApp oracle
    (pureCc ClosAnnotate.compileInc compiler) program notFail tickSafe
  have ticksNonfail : semantics ffi maxApp HolFiniteMapExact.holEmpty co
      (pureCc ClosAnnotate.compileInc compiler) (ClosTicks.removeList program) ≠ .fail := by
    rw [← ticksEq]
    exact notFail
  have annotated := ClosAnnotate.semanticsAnnotate_sourceShape ffi maxApp [] co compiler
    (ClosTicks.removeList program) (by
      simpa [HolFiniteMapExact.alistToFmap, HolFiniteMapExact.holEmpty,
        HolFiniteMapExact.updateListEq, FUPDATE_LIST_HOL] using ticksNonfail)
    ⟨annotationSafe.1, by simp [everyFnVarsNone], annotationSafe.2⟩
  have annotationEq : semantics ffi maxApp HolFiniteMapExact.holEmpty
      (pureCo ClosAnnotate.compileInc ∘ co) compiler
      (ClosAnnotate.annotateList 0 (ClosTicks.removeList program)) =
      semantics ffi maxApp HolFiniteMapExact.holEmpty co
        (pureCc ClosAnnotate.compileInc compiler) (ClosTicks.removeList program) := by
    simpa [HolFiniteMapExact.alistToFmap, HolFiniteMapExact.holEmpty,
      HolFiniteMapExact.updateListEq, FUPDATE_LIST_HOL, ClosAnnotate.compile] using annotated
  exact ⟨ClosTicks.removeList program, ClosTicks.removeBounded_list_eq_source fuel program,
    annotationEq.trans ticksEq.symm⟩

/-- Numbering, executable free-variable removal, known-function optimization
and annotation preserve observations when the original pass invariants hold.
The remaining tick-removal and let-operation passes are not included. This is
Flapjack composition infrastructure, not a separate HOL theorem. -/
theorem number_fvs_known_annotate_semantics {C F : Type} (ffi : HolFfiState F)
    (fuel maxApp number : Nat) (knownConfig : ClosKnown.Config)
    (oracle : CompileOracle (Nat × (Spt ValApprox × C))) (compiler : Compiler C)
    (program : List ClosLang.Exp) (optimized : List (ClosLang.Exp × ValApprox)) (globals : Spt ValApprox)
    (positive : 1 ≤ maxApp)
    (notFail : semantics ffi maxApp HolFiniteMapExact.holEmpty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCc ClosFvs.compileInc
          (stateCc (ClosKnown.compileInc knownConfig) (pureCc ClosAnnotate.compileInc compiler)))) program ≠ .fail)
    (numberSafe : ¬ containsAppSome maxApp program ∧
      ∀ n, (oracle n).2.2 = [] ∧ ¬ containsAppSome maxApp (oracle n).2.1)
    (knownSafe :
      let numberedCo := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
      let co : CompileOracle (Spt ValApprox × C) := pureCo ClosFvs.compileInc ∘ numberedCo
      let xs := ClosFvs.compile (ClosNumber.renumberList number program).2
      (∀ n, (co n).2.2 = []) ∧ (∀ n, fvMax 0 (co n).2.1) ∧
      (∀ n exps extra, (co n).2 = (exps, extra) → ∀ e ∈ exps, esgcFree e) ∧
      everyFnVarsNone xs ∧ coEveryFnVarsNone co ∧ oracleGapproxSubspt co ∧
      oracleStateSgcFree co ∧ isStateOracle (ClosKnown.compileInc knownConfig) co ∧
      uniqueSetGlobals xs co ∧ (∀ e ∈ xs, esgcFree e) ∧ fvMax 0 xs ∧
      (co 0).1.1 = globals ∧ oracleGapproxDisjoint globals co ∧
      ClosKnown.knownListTotal knownConfig xs [] .ln = (optimized, globals))
    (annotationSafe :
      let fvsCo : CompileOracle (Spt ValApprox × C) :=
        pureCo ClosFvs.compileInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
      let co : CompileOracle C := stateCo (ClosKnown.compileInc knownConfig) fvsCo
      everyFnVarsNone (optimized.map Prod.fst) ∧
      ∀ n, everyFnVarsNone (co n).2.1 ∧
        everyFnVarsNone ((co n).2.2.map (fun (_, _, body) => body))) :
    ∃ transformed, (ClosNumber.renumberList number program).2.mapM (ClosFvs.removeBounded fuel 0) = some transformed ∧
      semantics ffi maxApp HolFiniteMapExact.holEmpty
        (pureCo ClosAnnotate.compileInc ∘ stateCo (ClosKnown.compileInc knownConfig)
          (pureCo ClosFvs.compileInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle))
        compiler (ClosAnnotate.annotateList 0 (optimized.map Prod.fst)) =
      semantics ffi maxApp HolFiniteMapExact.holEmpty oracle
        (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
          (pureCc ClosFvs.compileInc
            (stateCc (ClosKnown.compileInc knownConfig) (pureCc ClosAnnotate.compileInc compiler)))) program := by
  let numberedCo : CompileOracle (Spt ValApprox × C) := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
  let numbered := (ClosNumber.renumberList number program).2
  let co : CompileOracle (Spt ValApprox × C) := pureCo ClosFvs.compileInc ∘ numberedCo
  let transformed := ClosFvs.compile numbered
  let knownCompiler := stateCc (ClosKnown.compileInc knownConfig) (pureCc ClosAnnotate.compileInc compiler)
  have numberEq : semantics ffi maxApp HolFiniteMapExact.holEmpty numberedCo
      (pureCc ClosFvs.compileInc knownCompiler) numbered =
      semantics ffi maxApp HolFiniteMapExact.holEmpty oracle
        (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) (pureCc ClosFvs.compileInc knownCompiler)) program :=
    ClosNumber.semanticsNumberHOL ffi maxApp number oracle (pureCc ClosFvs.compileInc knownCompiler)
      program notFail numberSafe
  have numberedNonfail : semantics ffi maxApp HolFiniteMapExact.holEmpty numberedCo
      (pureCc ClosFvs.compileInc knownCompiler) numbered ≠ .fail := by rw [numberEq]; exact notFail
  have numberedAux : ∀ n, (numberedCo n).2.2 = [] := by
    intro n
    simpa [numberedCo, stateCo, ClosNumber.ignoreTable] using (numberSafe.2 n).1
  have fvsEq : semantics ffi maxApp HolFiniteMapExact.holEmpty co knownCompiler transformed =
      semantics ffi maxApp HolFiniteMapExact.holEmpty numberedCo (pureCc ClosFvs.compileInc knownCompiler) numbered :=
    ClosFvs.semantics_compile ffi maxApp numberedCo knownCompiler numbered numberedNonfail ⟨numberedAux, positive⟩
  have fvsNonfail : semantics ffi maxApp HolFiniteMapExact.holEmpty co knownCompiler transformed ≠ .fail := by
    rw [fvsEq, numberEq]
    exact notFail
  have knownEq := ClosKnown.Semantics.semanticsKnownHOL knownConfig ffi maxApp co
    (pureCc ClosAnnotate.compileInc compiler) transformed optimized globals fvsNonfail knownSafe
  let annotatedCo : CompileOracle C := stateCo (ClosKnown.compileInc knownConfig) co
  have knownNonfail : semantics ffi maxApp HolFiniteMapExact.holEmpty annotatedCo
      (pureCc ClosAnnotate.compileInc compiler) (optimized.map Prod.fst) ≠ .fail := by
    rw [knownEq, fvsEq, numberEq]
    exact notFail
  have annotated := ClosAnnotate.semanticsAnnotate_sourceShape ffi maxApp [] annotatedCo compiler
    (optimized.map Prod.fst) (by
      simpa [HolFiniteMapExact.alistToFmap, HolFiniteMapExact.holEmpty,
        HolFiniteMapExact.updateListEq, FUPDATE_LIST_HOL] using knownNonfail)
    ⟨annotationSafe.1, by simp [everyFnVarsNone], annotationSafe.2⟩
  have annotationEq : semantics ffi maxApp HolFiniteMapExact.holEmpty
      (pureCo ClosAnnotate.compileInc ∘ annotatedCo) compiler
      (ClosAnnotate.annotateList 0 (optimized.map Prod.fst)) =
      semantics ffi maxApp HolFiniteMapExact.holEmpty annotatedCo
        (pureCc ClosAnnotate.compileInc compiler) (optimized.map Prod.fst) := by
    simpa [HolFiniteMapExact.alistToFmap, HolFiniteMapExact.holEmpty,
      HolFiniteMapExact.updateListEq, FUPDATE_LIST_HOL, ClosAnnotate.compile] using annotated
  exact ⟨transformed, ClosFvs.compileBounded_eq_source fuel numbered,
    annotationEq.trans (knownEq.trans (fvsEq.trans numberEq))⟩

end Flapjack.Compiler.Backend.ClosToBvl
