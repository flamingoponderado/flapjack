import Flapjack.Compiler.Backend.ClosNumber.Proofs.Semantics
import Flapjack.Compiler.Backend.ClosKnown.Proofs.Semantics

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

end Flapjack.Compiler.Backend.ClosToBvl
