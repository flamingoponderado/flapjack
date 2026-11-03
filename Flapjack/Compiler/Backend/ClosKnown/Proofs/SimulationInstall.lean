import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationDecode
import Flapjack.Compiler.Backend.ClosKnown.Proofs.StateRelation
import Flapjack.Compiler.Backend.Semantics.ClosSem.Install

/-! Installation prerequisites for the known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.Install
open ClosSem ClosProps Relations Relations.StateRelation BackendProps
open Flapjack.SemanticPrimitivesHOL

/-- A non-type-error installation and related arguments have identical
decoded byte and word payloads on the target side. This is Flapjack proof
infrastructure for the installation case. -/
theorem relatedInstallPayload {C F : Type} (c : Config) (g : Spt ValApprox)
    (sourceValues targetValues : List ClosSem.Value) (s s1 : State C F)
    (result : Result (List ClosLang.Exp) ClosSem.Value)
    (related : List.Forall₂ (ValueRel c g) sourceValues targetValues)
    (run : doInstall sourceValues s = (result, s1)) (noType : result ≠ .err (.abort .typeError)) :
    ∃ sourceBytes sourceWords targetBytes targetWords bytes words,
      sourceValues = [sourceBytes, sourceWords] ∧ targetValues = [targetBytes, targetWords] ∧
      valueToBytes sourceBytes = some bytes ∧ valueToBytes targetBytes = some bytes ∧
      valueToWords sourceWords = some words ∧ valueToWords targetWords = some words := by
  obtain ⟨sourceBytes, sourceWords, bytes, words, _, _, _, _, shape, bytesRun, wordsRun, _⟩ :=
    doInstall_nonType_parts sourceValues s s1 result run noType
  subst sourceValues
  cases related with
  | cons first tail =>
    cases tail with
    | cons second tail =>
      cases tail
      rename_i targetBytes targetWords
      have bytesSame := valueRelImpValueToBytes c g sourceBytes targetBytes first
      have wordsSame := valueRelImpValueToWords c g sourceWords targetWords second
      exact ⟨sourceBytes, sourceWords, targetBytes, targetWords, bytes, words,
        rfl, rfl, bytesRun, bytesSame.trans bytesRun, wordsRun, wordsSame.trans wordsRun⟩

/-- Each target compiler-oracle entry is obtained by running the known pass
on the source entry, preserving the empty auxiliary-code component. This is
Flapjack proof infrastructure for installation. -/
theorem relatedOracleEntry {C F : Type} (c : Config) (g : Spt ValApprox)
    (s : State (Spt ValApprox × C) F) (t : State C F) (n : Nat)
    (related : StateRel c g s t) :
    ∃ tree config program eas next,
      s.compileOracle n = ((tree, config), program, []) ∧
      knownListTotal (resetInlineFactor c) program [] tree = (eas, next) ∧
      t.compileOracle n = (config, eas.map Prod.fst, []) := by
  obtain ⟨auxEmpty, _, _, _, _, _, _, _, _, _, oracle⟩ := related
  cases entry : s.compileOracle n with
  | mk config program =>
    rcases config with ⟨tree, config⟩
    rcases program with ⟨program, auxiliary⟩
    have aux : auxiliary = [] := by simpa [entry] using auxEmpty n
    subst auxiliary
    cases known : knownListTotal (resetInlineFactor c) program [] tree with
    | mk eas next =>
      refine ⟨tree, config, program, eas, next, rfl, known, ?_⟩
      rw [oracle]
      simp [stateCo, entry, compileInc, known]

/-- A successful source callback yields the identical code and data from the
target callback and threads exactly the known pass's next approximation tree.
This is Flapjack proof infrastructure for installation. -/
theorem relatedCompilerCallback {C F : Type} (c : Config) (g : Spt ValApprox)
    (s : State (Spt ValApprox × C) F) (t : State C F) (related : StateRel c g s t)
    (tree : Spt ValApprox) (config : C) (program : List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp))
    (bytes : List (BitVec 8)) (words : List (BitVec 64)) (nextTree : Spt ValApprox) (nextConfig : C)
    (run : s.compile (tree, config) program = some (bytes, words, (nextTree, nextConfig))) :
    t.compile config (compileInc c tree program).2 = some (bytes, words, nextConfig) ∧
      (compileInc c tree program).1 = nextTree := by
  have compiler := related.2.2.2.2.2.2.2.2.2.1
  rw [compiler] at run
  unfold stateCc at run
  cases compiled : compileInc c tree program with
  | mk computedTree computedProgram =>
    simp only [compiled] at run ⊢
    cases callback : t.compile config computedProgram with
    | none => simp [callback] at run
    | some output =>
      rcases output with ⟨code, data, configNext⟩
      simp [callback] at run
      rcases run with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, rfl⟩

end Flapjack.Compiler.Backend.ClosKnown.Simulation.Install
