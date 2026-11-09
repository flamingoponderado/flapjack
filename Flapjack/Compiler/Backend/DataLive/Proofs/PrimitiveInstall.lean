module

public import Flapjack.Compiler.Backend.DataLive.Proofs.PrimitiveFfi

@[expose] public section

/-! Code installation simulation for the liveness pass. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Installation on related states produces matching errors or values and
updates their code and future compiler oracle consistently. This theorem is
untagged pending source evaluator and carrier review. -/
theorem stateRel_doInstall {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doInstall args source) (doInstall args target) := by
  have code := related.1
  have compiler := related.2.2.2.2.2.2.2.2.1
  have oracle := related.2.2.2.2.2.2.2.2.2.1
  cases args with
  | nil => simp [doInstall, appRel]
  | cons v1 tail =>
    cases tail with
    | nil => simp [doInstall, appRel]
    | cons v2 tail =>
      cases tail with
      | nil => simp [doInstall, appRel]
      | cons len1 tail =>
        cases tail with
        | nil => simp [doInstall, appRel]
        | cons len2 tail =>
          cases tail with
          | cons extra tail => simp [doInstall, appRel]
          | nil =>
            cases bytesFound : valueToBytes v1 with
            | none => simp [doInstall, appRel, bytesFound]
            | some bytes =>
              cases wordsFound : valueToWords v2 with
              | none => simp [doInstall, appRel, bytesFound, wordsFound]
              | some words =>
                by_cases lengths : len1 ≠ .number (bytes.length : Int) ∨ len2 ≠ .number (words.length : Int)
                · simp [doInstall, appRel, bytesFound, wordsFound, lengths]
                · cases oracleFound : source.compileOracle 0 with
                  | mk config programs =>
                    cases compileFound : source.compile config programs with
                    | none => simp [doInstall, appRel, bytesFound, wordsFound, lengths, ← compiler, ← oracle, oracleFound, compileFound]
                    | some compiled =>
                      obtain ⟨outputBytes, outputWords, configNext⟩ := compiled
                      cases programs with
                      | nil => simp [doInstall, appRel, bytesFound, wordsFound, lengths, ← compiler, ← oracle, oracleFound, compileFound]
                      | cons entry rest =>
                        obtain ⟨label, arity, body⟩ := entry
                        by_cases matchOutput : bytes = outputBytes ∧ words = outputWords ∧ (source.compileOracle 1).1 = configNext
                        · have outputLengths : ¬(len1 ≠ .number (outputBytes.length : Int) ∨ len2 ≠ .number (outputWords.length : Int)) := by
                            simpa [matchOutput.1, matchOutput.2.1] using lengths
                          have updated : stateRel
                            { source with safeForSpace := false, code := sptUnion source.code (sptFromAList ((label, arity, body) :: rest)), compileOracle := fun n => source.compileOracle (n + 1) }
                            { target with safeForSpace := false, code := sptUnion target.code (sptFromAList ((label, arity, body) :: rest)), compileOracle := fun n => target.compileOracle (n + 1) } live := by
                              simpa [stateRel, code, oracle] using related
                          simpa [doInstall, appRel, bytesFound, wordsFound, lengths, outputLengths, ← compiler, ← oracle, oracleFound, compileFound, matchOutput] using updated
                        · simp [doInstall, appRel, bytesFound, wordsFound, lengths, ← compiler, ← oracle, oracleFound, compileFound, matchOutput]

/-- Related states produce matching results through the full installation
primitive, including the frame-size reset. -/
theorem stateRel_doApp_install {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doApp .install args source) (doApp .install args target) := by
  have resetRel : stateRel { source with stackMax := none, stackFrameSizes := .ln }
      { target with stackMax := none, stackFrameSizes := .ln } live := by
    rcases related with ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, _, locals⟩
    exact ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, rfl, locals⟩
  exact stateRel_doInstall _ _ live args resetRel

/-- Code-installation assignments satisfy the liveness simulation with or
without an annotation. Unannotated installations fail with a type error. -/
theorem simulationFor_assign_install_all {C F : Type} (dest : Nat) (args : List Nat)
    (names : Option NumSet) (live : NumSet) :
    simulationFor (C := C) (F := F) (.assign dest .install args names) live := by
  cases names with
  | none => exact simulationFor_removed_requiresNames dest .install args live rfl
  | some names =>
    apply simulationFor_annotated_of_appRel dest .install args names live
    intro source target values related
    exact stateRel_doApp_install source target _ values related

end Flapjack.Compiler.Backend.DataLive
