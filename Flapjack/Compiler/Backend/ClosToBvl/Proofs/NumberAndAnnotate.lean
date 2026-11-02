import Flapjack.Compiler.Backend.ClosNumber.Proofs.Semantics
import Flapjack.Compiler.Backend.ClosNumber.Proofs.VarsNone
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.SemanticsCorrect
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.CodeLocations
import Flapjack.Compiler.Backend.ClosToBvl.Incremental

/-! Observable composition of closure numbering and annotation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.ClosProps

/-- Numbering followed by annotation preserves proof-side observable
behavior. This combines the actual pass definitions but is not yet a
whole-compiler theorem or a reviewed HOL correspondence result. -/
theorem number_annotate_semantics {C F : Type} (ffi : HolFfiState F) (maxApp number : Nat)
    (oracle : CompileOracle (Nat × C)) (compiler : Compiler C) (program : List ClosLang.Exp)
    (notFail : semantics ffi maxApp HolFiniteMapExact.empty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) (pureCc ClosAnnotate.compileInc compiler)) program ≠ .fail)
    (numberSafe : ¬ containsAppSome maxApp program) (varsSafe : everyFnVarsNone program)
    (oracleSafe : ∀ index, (oracle index).2.2 = [] ∧
      ¬ containsAppSome maxApp (oracle index).2.1 ∧ everyFnVarsNone (oracle index).2.1) :
    semantics ffi maxApp HolFiniteMapExact.empty
      (pureCo ClosAnnotate.compileInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) compiler
      (ClosAnnotate.annotateList 0 (ClosNumber.renumberList number program).2) =
    semantics ffi maxApp HolFiniteMapExact.empty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) (pureCc ClosAnnotate.compileInc compiler)) program := by
  let numberedOracle := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
  let numbered := (ClosNumber.renumberList number program).2
  have numberEq : semantics ffi maxApp HolFiniteMapExact.empty numberedOracle
      (pureCc ClosAnnotate.compileInc compiler) numbered =
      semantics ffi maxApp HolFiniteMapExact.empty oracle
        (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) (pureCc ClosAnnotate.compileInc compiler)) program := by
    apply ClosNumber.semantics_number ffi maxApp number oracle (pureCc ClosAnnotate.compileInc compiler) program
      notFail numberSafe
    intro index
    exact ⟨(oracleSafe index).1, (oracleSafe index).2.1⟩
  have numberedSafe : everyFnVarsNone numbered := (ClosNumber.renumberList_varsNone program number).mpr varsSafe
  have numberedOracleSafe : ∀ index, everyFnVarsNone (numberedOracle index).2.1 ∧
      everyFnVarsNone ((numberedOracle index).2.2.map (fun (_, _, body) => body)) := by
    intro index
    have safe := oracleSafe index
    constructor
    · simpa [numberedOracle, stateCo, ClosNumber.ignoreTable, ClosNumber.compileInc_varsNone] using safe.2.2
    · simp [numberedOracle, stateCo, ClosNumber.ignoreTable, safe.1, everyFnVarsNone]
  have numberedNonfail : semantics ffi maxApp HolFiniteMapExact.empty numberedOracle
      (pureCc ClosAnnotate.compileInc compiler) numbered ≠ .fail := by
    rw [numberEq]
    exact notFail
  have annotateEq := ClosAnnotate.annotate_semantics_correct ffi maxApp numberedOracle compiler numbered
    numberedSafe numberedOracleSafe numberedNonfail
  exact annotateEq.symm.trans numberEq

/-- Multi-argument introduction, numbering and annotation preserve the current
Lean observations for unary input and dynamic compiler results. This is not a
reviewed HOL correspondence or a whole-compiler theorem. -/
theorem mti_number_annotate_semantics {C F : Type} (ffi : HolFfiState F) (maxApp number : Nat)
    (oracle : CompileOracle (Nat × C)) (compiler : Compiler C) (program : List ClosLang.Exp)
    (positive : 1 ≤ maxApp)
    (unary : ∀ e ∈ program, noMti e)
    (oracleUnary : ∀ index, (oracle index).2.2 = [] ∧
      ∀ e ∈ (oracle index).2.1, noMti e)
    (notFail : semantics ffi maxApp HolFiniteMapExact.empty oracle
      (pureCc (ClosMti.compileInc maxApp)
        (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) (pureCc ClosAnnotate.compileInc compiler)))
      program ≠ .fail) :
    semantics ffi maxApp HolFiniteMapExact.empty
      (pureCo ClosAnnotate.compileInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCo (ClosMti.compileInc maxApp) ∘ oracle)) compiler
      (ClosAnnotate.annotateList 0 (ClosNumber.renumberList number (ClosMti.introList maxApp program)).2) =
    semantics ffi maxApp HolFiniteMapExact.empty oracle
      (pureCc (ClosMti.compileInc maxApp)
        (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) (pureCc ClosAnnotate.compileInc compiler)))
      program := by
  let transformedOracle : CompileOracle (Nat × C) := pureCo (ClosMti.compileInc maxApp) ∘ oracle
  let transformed := ClosMti.introList maxApp program
  have mtiEq := ClosMti.semantics_introMulti_candidate ffi maxApp oracle
    (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) (pureCc ClosAnnotate.compileInc compiler))
    program positive oracleUnary unary
  have safe := noMtiList_syntactic maxApp positive program unary
  have transformedSafe : ¬ containsAppSome maxApp transformed :=
    ClosMti.introList_numberingSafe maxApp program positive unary
  have transformedVars : everyFnVarsNone transformed :=
    (ClosMti.introList_varsNone maxApp program).mp safe.1
  have transformedOracleSafe : ∀ index, (transformedOracle index).2.2 = [] ∧
      ¬ containsAppSome maxApp (transformedOracle index).2.1 ∧
      everyFnVarsNone (transformedOracle index).2.1 := by
    intro index
    change (ClosMti.compileInc maxApp (oracle index).2).2 = [] ∧
      ¬ containsAppSome maxApp (ClosMti.compileInc maxApp (oracle index).2).1 ∧
      everyFnVarsNone (ClosMti.compileInc maxApp (oracle index).2).1
    exact ⟨rfl, ClosMti.introList_numberingSafe maxApp _ positive (oracleUnary index).2,
      (ClosMti.introList_varsNone maxApp _).mp
        (noMtiList_syntactic maxApp positive _ (oracleUnary index).2).1⟩
  have transformedNotFail : semantics ffi maxApp HolFiniteMapExact.empty transformedOracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) (pureCc ClosAnnotate.compileInc compiler))
      transformed ≠ .fail := by
    simpa [transformedOracle, transformed, ← mtiEq] using notFail
  have combined := number_annotate_semantics ffi maxApp number transformedOracle compiler transformed
    transformedNotFail transformedSafe transformedVars transformedOracleSafe
  exact combined.trans mtiEq.symm

/-- Observation preservation for the actual fuelled multi-argument pass
followed by numbering and annotation. -/
theorem compileFuel_number_annotate_semantics {C F : Type} (ffi : HolFfiState F)
    (fuel maxApp number : Nat) (oracle : CompileOracle (Nat × C))
    (compiler : Compiler C) (program : List ClosLang.Exp)
    (positive : 1 ≤ maxApp)
    (unary : ∀ e ∈ program, noMti e)
    (oracleUnary : ∀ index, (oracle index).2.2 = [] ∧
      ∀ e ∈ (oracle index).2.1, noMti e)
    (notFail : semantics ffi maxApp HolFiniteMapExact.empty oracle
      (pureCc (ClosMti.compileInc maxApp)
        (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) (pureCc ClosAnnotate.compileInc compiler)))
      program ≠ .fail) :
    ∃ transformed, ClosMti.compileFuel fuel true maxApp program = some transformed ∧
      semantics ffi maxApp HolFiniteMapExact.empty
        (pureCo ClosAnnotate.compileInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc)
          (pureCo (ClosMti.compileInc maxApp) ∘ oracle)) compiler
        (ClosAnnotate.annotateList 0 (ClosNumber.renumberList number transformed).2) =
      semantics ffi maxApp HolFiniteMapExact.empty oracle
        (pureCc (ClosMti.compileInc maxApp)
          (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) (pureCc ClosAnnotate.compileInc compiler)))
        program := by
  exact ⟨ClosMti.introList maxApp program, ClosMti.compileFuel_introList fuel maxApp program,
    mti_number_annotate_semantics ffi maxApp number oracle compiler program positive unary oracleUnary notFail⟩

/-- The executed incremental marker survives annotation and determines the
entry label. A singleton marker is retained when the source batch is empty. -/
theorem extract_numbered_annotated (number : Nat) (program : List ClosLang.Exp) :
    let next := number + max program.length 1
    let aligned := if next % 2 = 0 then next else next + 1
    let annotated := ClosAnnotate.annotateList 0 (ClosNumber.renumberList aligned program).2
    extractName (ClosAnnotate.compileInc ((ClosNumber.compileInc number program).2, [])).1 =
      (number, if program.isEmpty then [.op .none (.intOp (.const (Int.ofNat number))) []] else annotated) := by
  dsimp only [ClosAnnotate.compileInc, ClosNumber.compileInc]
  rw [ClosAnnotate.annotateList_name_marker]
  by_cases empty : program = []
  · subst program
    simp [ClosNumber.renumberList, ClosAnnotate.annotateList, ClosAnnotate.altFreeList,
      ClosAnnotate.shiftList, extractName]
  · have nonempty : ∀ start, ClosAnnotate.annotateList 0 (ClosNumber.renumberList start program).2 ≠ [] := by
      intro start h
      have len := ClosAnnotate.annotateList_length 0 (ClosNumber.renumberList start program).2
      rw [h] at len
      have z : program.length = 0 := by simpa [ClosNumber.renumberList_length] using len.symm
      exact empty (List.eq_nil_of_length_eq_zero z)
    simp [extractName, nonempty, List.isEmpty_iff, empty]

/-- For a nonempty batch, the expressions actually passed to incremental
closure conversion have the behavior of the original source batch. -/
theorem incremental_number_annotate_semantics {C F : Type} (ffi : HolFfiState F) (maxApp number : Nat)
    (oracle : CompileOracle (Nat × C)) (compiler : Compiler C) (program : List ClosLang.Exp)
    (nonempty : program ≠ [])
    (notFail : semantics ffi maxApp HolFiniteMapExact.empty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) (pureCc ClosAnnotate.compileInc compiler)) program ≠ .fail)
    (numberSafe : ¬ containsAppSome maxApp program) (varsSafe : everyFnVarsNone program)
    (oracleSafe : ∀ index, (oracle index).2.2 = [] ∧
      ¬ containsAppSome maxApp (oracle index).2.1 ∧ everyFnVarsNone (oracle index).2.1) :
    semantics ffi maxApp HolFiniteMapExact.empty
      (pureCo ClosAnnotate.compileInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) compiler
      (extractName (ClosAnnotate.compileInc ((ClosNumber.compileInc number program).2, [])).1).2 =
    semantics ffi maxApp HolFiniteMapExact.empty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) (pureCc ClosAnnotate.compileInc compiler)) program := by
  rw [extract_numbered_annotated]
  simp only [List.isEmpty_iff, nonempty, ↓reduceIte]
  exact number_annotate_semantics ffi maxApp _ oracle compiler program notFail numberSafe varsSafe oracleSafe

end Flapjack.Compiler.Backend.ClosToBvl
