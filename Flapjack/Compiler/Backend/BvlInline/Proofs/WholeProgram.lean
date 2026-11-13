module

public import Flapjack.Compiler.Backend.BvlInline.Proofs.FullSemantics
public import Flapjack.Compiler.Backend.BackendProps.StateCompiler

@[expose] public section

/-! Source-shaped stateful callback and whole-program correctness properties. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.BvlSem

/-- Sparse-tree mapping commutes with construction from association lists. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "map_fromAList"]
theorem map_fromAList {α β : Type} (xs : List (Nat × α)) (f : α → β) :
    sptMap f (sptFromAList xs) = sptFromAList (xs.map fun (key, value) => (key, f value)) := by
  exact sptMap_sptFromAList f xs

/-- The stateful callback for inlining is the composition of the source passes. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "state_cc_compile_inc_eq"]
theorem stateCc_compileInc {C A B D : Type} (limit : Nat) (splitSeq : Bool) (cutSize : Nat)
    (compiler : C → List (Nat × Nat × Bvl.Exp) → Option (A × B × D)) :
    stateCc (compileInc limit splitSeq cutSize) compiler =
      inCc limit (removeTicksCc (letOpCompiler splitSeq cutSize compiler)) := by
  funext config program
  obtain ⟨cache, cfg⟩ := config
  simp only [stateCc, inCc, removeTicksCc, letOpCompiler, compileInc]
  cases run : tickCompileProg limit cache program with
  | mk cache' program' =>
    have optEq : (fun x : Nat × Nat × Bvl.Exp =>
        (x.1, letOptRemove splitSeq cutSize x.2)) = optimise splitSeq cutSize := by
      funext entry
      obtain ⟨name, arity, body⟩ := entry
      rfl
    have optEqUnfolded : (fun x : Nat × Nat × Bvl.Exp =>
        (x.1, letOpt splitSeq cutSize (x.2.1, removeTicksSing x.2.2))) =
        optimise splitSeq cutSize := by
      simpa only [letOptRemove] using optEq
    simp only [List.map_map, Function.comp_def, optEqUnfolded]
    cases answer : compiler cfg (program'.map (optimise splitSeq cutSize)) with
    | none => rfl
    | some result =>
      obtain ⟨code, data, config⟩ := result
      rfl

/-- The stateful oracle for inlining is the composition of the source passes. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "state_co_compile_inc_eq"]
theorem stateCo_compileInc {I C : Type} (limit : Nat) (splitSeq : Bool) (cutSize : Nat)
    (oracle : I → (Spt (Nat × Bvl.Exp) × C) × List (Nat × Nat × Bvl.Exp)) :
    stateCo (compileInc limit splitSeq cutSize) oracle =
      (fun entry : C × List (Nat × Nat × Bvl.Exp) =>
        (entry.1, entry.2.map fun (name, arity, body) =>
          (name, arity, letOpTransform splitSeq cutSize arity body))) ∘
        removeTicksCo ∘ inCo limit oracle := by
  funext index
  simp [stateCo, compileInc, inCo, removeTicksCo, optimise, letOpTransform,
    List.map_map, Function.comp_def]


/-- Whole-program inlining preserves the source behavior. Its semantics inherit
the real-model assumption documented in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "compile_prog_semantics"]
theorem compileProg_semantics {C F : Type} (limit : Nat) (splitSeq : Bool) (cutSize : Nat)
    (program : List (Nat × Nat × Bvl.Exp)) (cache : Spt (Nat × Bvl.Exp))
    (output : List (Nat × Nat × Bvl.Exp))
    (oracle : CompileOracle (Spt (Nat × Bvl.Exp) × C)) (ffi : HolFfiState F)
    (compiler : Compiler C) (start : Nat)
    (assumptions : compileProg limit splitSeq cutSize program = (cache, output) ∧
      (oracle 0).1.1 = cache ∧ (program.map Prod.fst).Nodup)
    (nonFail : BvlSem.semantics ffi (sptFromAList program) oracle
      (stateCc (compileInc limit splitSeq cutSize) compiler) start ≠ .fail) :
    BvlSem.semantics ffi (sptFromAList output)
      (stateCo (compileInc limit splitSeq cutSize) oracle) compiler start =
    BvlSem.semantics ffi (sptFromAList program) oracle
      (stateCc (compileInc limit splitSeq cutSize) compiler) start := by
  obtain ⟨run, cacheEq, distinct⟩ := assumptions
  rw [stateCc_compileInc] at nonFail ⊢
  rw [stateCo_compileInc]
  have compiled : compileProgFuel 0 limit cutSize splitSeq program = some (cache, output) := by
    rw [compileProgFuel_eq_compileProg, run]
  have oracleEq : letOpOracle splitSeq cutSize (removeTicksCo ∘ inCo limit oracle) =
      (fun entry : C × List (Nat × Nat × Bvl.Exp) =>
        (entry.1, entry.2.map fun (name, arity, body) =>
          (name, arity, letOpTransform splitSeq cutSize arity body))) ∘
        removeTicksCo ∘ inCo limit oracle := by
    funext index
    rfl
  rw [← oracleEq]
  let inlined := (tickCompileProg limit .ln program).2
  let unticked := inlined.map fun (name, arity, body) => (name, arity, removeTicksSing body)
  have exactRun := compileProgFuel_eq 0 limit cutSize splitSeq program
  rw [compiled] at exactRun
  have pairEq := Option.some.inj exactRun
  have cacheRun : cache = (tickCompileProg limit .ln program).1 := congrArg Prod.fst pairEq
  have outputRun : output = unticked.map (fun (name, arity, body) =>
      (name, arity, letOpTransform splitSeq cutSize arity body)) := congrArg Prod.snd pairEq
  have inlinedSame := inline_semantics ffi program oracle (removeTicksCc (letOpCompiler splitSeq cutSize compiler))
    start limit (cacheEq.trans cacheRun) distinct nonFail
  have untickedSame := removeTicks_semantics ffi (sptFromAList inlined) (inCo limit oracle)
    (letOpCompiler splitSeq cutSize compiler) start
  have middleSame : BvlSem.semantics ffi (sptFromAList unticked) (removeTicksCo ∘ inCo limit oracle)
      (letOpCompiler splitSeq cutSize compiler) start =
      BvlSem.semantics ffi (sptFromAList program) oracle
        (inCc limit (removeTicksCc (letOpCompiler splitSeq cutSize compiler))) start := by
    simpa [unticked, inlined, sptMap_sptFromAList] using untickedSame.trans inlinedSame
  have middleNonFail : BvlSem.semantics ffi (sptFromAList unticked) (removeTicksCo ∘ inCo limit oracle)
      (letOpCompiler splitSeq cutSize compiler) start ≠ .fail := by
    rw [middleSame]
    exact nonFail
  have finalSame := letOp_semantics splitSeq cutSize start ffi (sptFromAList unticked)
    (removeTicksCo ∘ inCo limit oracle) compiler middleNonFail
  simpa [outputRun, sptMap_sptFromAList, bvlInlineCc, bvlInlineCo] using finalSame.trans middleSame

end Flapjack.Compiler.Backend.BvlInline.Proofs
