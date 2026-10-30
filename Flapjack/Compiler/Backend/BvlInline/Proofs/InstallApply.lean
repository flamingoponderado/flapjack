import Flapjack.Compiler.Backend.BvlInline.Proofs.InstallCode
import Flapjack.Compiler.Backend.BvlInline.Proofs.InlineApply
import Flapjack.Compiler.Backend.Semantics.BvlSem.Apply

/-! Relating actual dynamic installation runs. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open BvlSem Flapjack.SemanticPrimitivesHOL

namespace InlineApplicationCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end InlineApplicationCarrier

/-- A successful installation exposes the exact checks, callback result,
entry label and state update used by the BVL evaluator. This helper has no
standalone HOL declaration. -/
theorem doInstall_success_details {C F R : Type} (args : List BvlSem.Value)
    (state next : State C F) (value : BvlSem.Value)
    (run : doInstall (R := R) args state = .val (value, next)) :
    ∃ first second bytes words code data cfg key arity body tail,
      args = [first, second] ∧ valueToBytes first = some bytes ∧
      valueToWords second = some words ∧
      (state.compileOracle 0).2 = (key, arity, body) :: tail ∧
      (∀ entry ∈ (state.compileOracle 0).2, sptLookup entry.1 state.code = none) ∧
      ((state.compileOracle 0).2.map Prod.fst).Nodup ∧
      state.compile (state.compileOracle 0).1 (state.compileOracle 0).2 = some (code, data, cfg) ∧
      bytes = code ∧ words = data ∧ (state.compileOracle 1).1 = cfg ∧
      value = .codePtr key ∧
      next = { state with
        code := sptUnion state.code (sptFromAList (state.compileOracle 0).2)
        compileOracle := fun n => state.compileOracle (n + 1) } := by
  unfold doInstall at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop

/-- A successful source installation has a matching target installation and
preserves the inlining state relation. This is the successful Install case of
the local primitive simulation, not the whole HOL theorem. -/
theorem inDoInstall_success {C F : Type} (limit : Nat)
    (source : State (Spt (Nat × Bvl.Exp) × C) F) (target : State C F)
    (related : inStateRel limit source target) (args : List BvlSem.Value)
    (value : BvlSem.Value) (next : State (Spt (Nat × Bvl.Exp) × C) F)
    (success : doInstall (R := BvlSem.Value) args source = .val (value, next)) :
    ∃ targetNext, inStateRel limit next targetNext ∧
      doInstall (R := BvlSem.Value) args target = .val (value, targetNext) := by
  classical
  obtain ⟨first, second, bytes, words, code, data, cfg, key, arity, body, tail,
    argsEq, bytesEq, wordsEq, programEq, free, distinct, compiled,
    bytesCode, wordsData, cfgEq, valueEq, nextEq⟩ := doInstall_success_details args source next value success
  cases compileRun : tickCompileProg limit (source.compileOracle 0).1.1 (source.compileOracle 0).2 with
  | mk cache output =>
    have names : output.map Prod.fst = (source.compileOracle 0).2.map Prod.fst := by
      have h := mapFstTickInlineAll limit (source.compileOracle 0).1.1 (source.compileOracle 0).2
      change (tickCompileProg limit (source.compileOracle 0).1.1 (source.compileOracle 0).2).2.map Prod.fst = _ at h
      simpa [compileRun] using h
    have targetFree : ∀ entry ∈ output, sptLookup entry.1 target.code = none :=
      (installFresh_iff source.code target.code (source.compileOracle 0).2 output
        related.2.2.2.2.2.2.2.1 names).2 free
    have targetDistinct : (output.map Prod.fst).Nodup := by simpa [names] using distinct
    have fresh : ∀ name, sptDomain source.code name → name ∉ (source.compileOracle 0).2.map Prod.fst := by
      intro name present member
      obtain ⟨entry, entryMem, entryName⟩ := List.mem_map.mp member
      have absent := free entry entryMem
      rw [entryName] at absent
      simp [sptDomain, absent] at present
    have targetOracle : target.compileOracle 0 = ((source.compileOracle 0).1.2, output) := by
      have h := congrFun related.2.2.2.2.1 0
      simpa [compileRun] using h
    have targetOracle1 : (target.compileOracle 1).1 = (source.compileOracle 1).1.2 := by
      have h := congrArg Prod.fst (congrFun related.2.2.2.2.1 1)
      simpa using h
    have compiled' := compiled
    rw [related.2.2.2.2.2.2.1] at compiled'
    have compiledParts : target.compile (source.compileOracle 0).1.2 output =
        some (code, data, cfg.2) ∧ cfg.1 = cache := by
      cases result : target.compile (source.compileOracle 0).1.2 output with
      | none => simp [inCc, compileRun, result] at compiled'
      | some triple =>
        obtain ⟨bs, ds, config⟩ := triple
        simp [inCc, compileRun, result] at compiled'
        rcases compiled' with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨rfl, rfl⟩
    have targetCompile := compiledParts.1
    have cacheNext : (source.compileOracle 1).1.1 = cache := by
      rw [cfgEq]
      exact compiledParts.2
    have targetNextConfig : (target.compileOracle 1).1 = cfg.2 := by
      rw [targetOracle1, cfgEq]
    have stateRel := inStateRel_after_install limit source target related cache output compileRun distinct fresh cacheNext
    cases output with
    | nil => simp [programEq] at names
    | cons entry rest =>
      obtain ⟨targetKey, targetArity, targetBody⟩ := entry
      have targetKeyEq : targetKey = key := by
        simpa [programEq] using congrArg List.head? names
      subst targetKey
      subst args
      subst value
      subst next
      refine ⟨_, stateRel, ?_⟩
      have valid := And.intro targetFree targetDistinct
      simp only [doInstall, bytesEq, wordsEq, targetOracle]
      rw [if_pos valid]
      simp [targetCompile, bytesCode, wordsData, targetNextConfig]

/-- Installation can only fail with the BVL type error. This helper has no
standalone HOL declaration. -/
theorem doInstall_error_is_typeError {C F R : Type} (args : List BvlSem.Value)
    (state : State C F) (error : ErrorResult R)
    (run : doInstall (R := R) args state = .err error) :
    error = .abort .typeError := by
  unfold doInstall at run
  repeat' split at run
  all_goals simp_all
  all_goals split at run <;> simp_all

/-- Primitive simulation for BVL inlining, including dynamic installation.
The original local theorem and its inferred types are replayed in the probe. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "in_do_app_lemma"
  (fmap_as_finite_support := [refs])]
theorem inDoApp {C F : Type} (limit : Nat)
    (source : Flapjack.Compiler.Backend.BvlSem.State (Spt (Nat × Bvl.Exp) × C) F)
    (target : Flapjack.Compiler.Backend.BvlSem.State C F)
    (related : inStateRel limit source target) (op : ClosLang.Op) (args : List BvlSem.Value) :
    match doApp op args source with
    | .err error => error ≠ .abort .typeError → doApp op args target = .err error
    | .val (value, next) => ∃ targetNext, inStateRel limit next targetNext ∧
        doApp op args target = .val (value, targetNext) := by
  by_cases install : op = .install
  · subst op
    simp only [doApp]
    cases run : doInstall (R := BvlSem.Value) args source with
    | err error =>
      intro notType
      exact False.elim (notType (doInstall_error_is_typeError args source error run))
    | val pair =>
      obtain ⟨value, next⟩ := pair
      exact inDoInstall_success limit source target related args value next run
  · have h := inDoApp_nonInstall limit source target related op args install
    cases run : doApp op args source with
    | err error =>
      rw [run] at h
      intro _
      exact h
    | val pair =>
      rw [run] at h
      exact h

end Flapjack.Compiler.Backend.BvlInline.Proofs
