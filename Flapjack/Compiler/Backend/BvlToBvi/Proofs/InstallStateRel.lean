import Flapjack.Compiler.Backend.BvlToBvi.Proofs.InstallEntries

/-! State relation after BVL-to-BVI code installation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs

/-- Installing the current oracle program on both sides preserves the state
relation when the next oracle entry carries the incremental compiler's new
counter. -/
theorem stateRel_install {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (related : stateRel relocate source target)
    (available : ∀ entry ∈ (source.compileOracle 0).2, sptLookup entry.1 source.code = none)
    (distinct : ((source.compileOracle 0).2.map Prod.fst).Nodup)
    (advance : (source.compileOracle 1).1.1 =
      (compileIncSource (source.compileOracle 0).1.1 (source.compileOracle 0).2).1) :
    stateRel relocate
      { source with
        code := sptUnion source.code (sptFromAList (source.compileOracle 0).2)
        compileOracle := fun n => source.compileOracle (n + 1) }
      { target with
        code := sptUnion target.code (sptFromAList (compileIncSource (source.compileOracle 0).1.1 (source.compileOracle 0).2).2)
        compileOracle := fun n => target.compileOracle (n + 1) } := by
  have names := namesOk_install source.code target.code source.compileOracle related.2.2.2.2.2.2.2.2.2.2.2.2.2.1 advance
  have entries := installed_code_correspondence relocate source target related available distinct
  rcases related with ⟨refs, ffi, globals, clock, oracle, compiler, alloc, copy, length, fromByte, toByte, sum, concat, _, _⟩
  refine ⟨refs, ffi, globals, clock, ?_, compiler, ?_, ?_, ?_, ?_, ?_, ?_, ?_, names, entries⟩
  · funext n
    have atIndex := congrFun oracle (n + 1)
    simpa [BackendProps.stateCo] using atIndex
  · simp [sptLookup_sptUnion, alloc]
  · simp [sptLookup_sptUnion, copy]
  · simp [sptLookup_sptUnion, length]
  · simp [sptLookup_sptUnion, fromByte]
  · simp [sptLookup_sptUnion, toByte]
  · simp [sptLookup_sptUnion, sum]
  · simp [sptLookup_sptUnion, concat]

/-- A successful source installation advances the fresh-name counter to the
one returned by incremental compilation. -/
theorem install_counter_advance {C F : Type} (relocate : Nat → Nat)
    (source next : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (byteValue wordValue result : BvlSem.Value) (related : stateRel relocate source target)
    (run : BvlSem.doInstall (R := BvlSem.Value) [byteValue, wordValue] source = .val (result, next)) :
    (source.compileOracle 1).1.1 = (compileIncSource (source.compileOracle 0).1.1 (source.compileOracle 0).2).1 := by
  obtain ⟨_, _, ⟨counter, config⟩, ⟨nextCounter, nextConfig⟩, key, arity, body, rest,
    _, _, oracle, _, _, callback, nextOracle, _, _⟩ :=
      install_success_shape byteValue wordValue source next result run
  rcases compiled : compileIncSource counter ((key, arity, body) :: rest) with ⟨actualCounter, targetCode⟩
  have sourceCallback := callback
  rw [related.2.2.2.2.2.1] at sourceCallback
  simp [BackendProps.stateCc, compiled] at sourceCallback
  cases targetRun : target.compile config targetCode with
  | none => simp [targetRun] at sourceCallback
  | some output =>
    rcases output with ⟨outBytes, outWords, outConfig⟩
    simp [targetRun] at sourceCallback
    have counters : actualCounter = nextCounter := sourceCallback.2.2.1
    simp [nextOracle, oracle, compiled, counters]

/-- Successful installation preserves the complete BVL-to-BVI state
relation. Untagged pending evaluator and dispatcher correspondence review. -/
theorem stateRel_install_success {C F : Type} (relocate : Nat → Nat)
    (source next : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (byteValue wordValue result : BvlSem.Value) (related : stateRel relocate source target)
    (run : BvlSem.doInstall (R := BvlSem.Value) [byteValue, wordValue] source = .val (result, next)) :
    stateRel relocate next
      { target with
        code := sptUnion target.code (sptFromAList (compileIncSource (source.compileOracle 0).1.1 (source.compileOracle 0).2).2)
        compileOracle := fun n => target.compileOracle (n + 1) } := by
  obtain ⟨_, _, config, _, key, arity, body, rest, _, _, oracle, available, distinct, _, _, _, nextEq⟩ :=
    install_success_shape byteValue wordValue source next result run
  have available' : ∀ entry ∈ (source.compileOracle 0).2, sptLookup entry.1 source.code = none := by
    simpa [oracle] using available
  have distinct' : ((source.compileOracle 0).2.map Prod.fst).Nodup := by simpa [oracle] using distinct
  have advance := install_counter_advance relocate source next target byteValue wordValue result related run
  subst next
  simpa [oracle] using stateRel_install relocate source target related available' distinct' advance

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
