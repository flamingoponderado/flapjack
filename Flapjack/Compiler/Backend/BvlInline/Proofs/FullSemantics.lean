module

public import Flapjack.Compiler.Backend.BvlInline.Proofs.LetOpSemantics
public import Flapjack.Compiler.Backend.BvlInline.Proofs.ProductionSemantics
public import Flapjack.Compiler.Backend.BvlInline.SourceCompile

@[expose] public section


/-! Production correspondence and behavior for the complete BVL optimizer. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem

/-- The executed program optimizer returns the total inlining, tick-removal,
let-operation, and handler transformations. -/
theorem compileProgFuel_eq (fuel inlineLimit cutSize : Nat) (splitSeq : Bool)
    (program : List (Nat × Nat × Bvl.Exp)) :
    compileProgFuel fuel inlineLimit cutSize splitSeq program =
      let inlined := tickCompileProg inlineLimit .ln program
      let unticked := inlined.2.map fun (name, arity, body) => (name, arity, removeTicksSing body)
      some (inlined.1, unticked.map fun (name, arity, body) =>
        (name, arity, letOpTransform splitSeq cutSize arity body)) := by
  rw [compileProgFuel, compileIncFuel_eq_compileInc]
  simp [compileInc, optimise, letOpTransform, List.map_map,
    Function.comp_def]

/-- The production optimizer preserves the ordered list of program labels. -/
theorem compileProgFuel_names (fuel inlineLimit cutSize : Nat) (splitSeq : Bool)
    (program : List (Nat × Nat × Bvl.Exp)) (cache : Spt (Nat × Bvl.Exp))
    (output : List (Nat × Nat × Bvl.Exp))
    (compiled : compileProgFuel fuel inlineLimit cutSize splitSeq program = some (cache, output)) :
    output.map Prod.fst = program.map Prod.fst := by
  rw [compileProgFuel_eq] at compiled
  have pair := Option.some.inj compiled
  have outputEq := congrArg Prod.snd pair
  simp only [List.map_map, Function.comp_def] at outputEq
  rw [← outputEq]
  simpa [tickCompileProg, List.map_map, Function.comp_def] using mapFstTickInlineAll inlineLimit .ln program

/-- Mapping the combined transformation over program entries establishes the
handler invariant for every generated body. -/
theorem letOpTransform_program_handleOk (splitSeq : Bool) (limit : Nat)
    (program : List (Nat × Nat × Bvl.Exp)) :
    BvlHandle.Proofs.handleOk
      ((program.map fun (name, arity, body) => (name, arity, letOpTransform splitSeq limit arity body)).map
        (fun (_, _, body) => body)) := by
  rw [BvlHandle.Proofs.handleOk_every]
  rw [List.forall_iff_forall_mem]
  intro body member
  simp only [List.mem_map] at member
  obtain ⟨entry, ⟨original, _, rfl⟩, rfl⟩ := member
  obtain ⟨name, arity, originalBody⟩ := original
  exact (letOpTransform_wellFormed splitSeq limit arity originalBody).2

/-- Every body emitted by the actual BVL optimizer has legal handler shape. -/
theorem compileProgFuel_handleOk (fuel inlineLimit cutSize : Nat) (splitSeq : Bool)
    (program : List (Nat × Nat × Bvl.Exp)) (cache : Spt (Nat × Bvl.Exp))
    (output : List (Nat × Nat × Bvl.Exp))
    (compiled : compileProgFuel fuel inlineLimit cutSize splitSeq program = some (cache, output)) :
    BvlHandle.Proofs.handleOk (output.map (fun (_, _, body) => body)) := by
  rw [compileProgFuel_eq] at compiled
  have outputEq := congrArg Prod.snd (Option.some.inj compiled)
  dsimp only at outputEq
  rw [← outputEq]
  exact letOpTransform_program_handleOk splitSeq cutSize _

/-- The full executed BVL optimizer preserves whole-program behavior for a
non-failing source program, including its divergent I/O trace. This remains
untagged pending HOL review of the underlying evaluator and state carriers. -/
theorem compileProgFuel_semantics {C F : Type} (fuel inlineLimit cutSize start : Nat) (splitSeq : Bool)
    (ffi : HolFfiState F) (program : List (Nat × Nat × Bvl.Exp))
    (oracle : CompileOracle (Spt (Nat × Bvl.Exp) × C)) (compiler : Compiler C)
    (cache : Spt (Nat × Bvl.Exp)) (output : List (Nat × Nat × Bvl.Exp))
    (compiled : compileProgFuel fuel inlineLimit cutSize splitSeq program = some (cache, output))
    (cacheEq : (oracle 0).1.1 = cache)
    (distinct : (program.map Prod.fst).Nodup)
    (nonFail : BvlSem.semantics ffi (sptFromAList program) oracle
      (inCc inlineLimit (removeTicksCc (letOpCompiler splitSeq cutSize compiler))) start ≠ .fail) :
    BvlSem.semantics ffi (sptFromAList output)
      (letOpOracle splitSeq cutSize (removeTicksCo ∘ inCo inlineLimit oracle)) compiler start =
    BvlSem.semantics ffi (sptFromAList program) oracle
      (inCc inlineLimit (removeTicksCc (letOpCompiler splitSeq cutSize compiler))) start := by
  let inlined := (tickCompileProg inlineLimit .ln program).2
  let unticked := inlined.map fun (name, arity, body) => (name, arity, removeTicksSing body)
  have exactRun := compileProgFuel_eq fuel inlineLimit cutSize splitSeq program
  rw [compiled] at exactRun
  have pairEq := Option.some.inj exactRun
  have cacheRun : cache = (tickCompileProg inlineLimit .ln program).1 := congrArg Prod.fst pairEq
  have outputRun : output = unticked.map (fun (name, arity, body) =>
      (name, arity, letOpTransform splitSeq cutSize arity body)) := congrArg Prod.snd pairEq
  have inlinedSame := inline_semantics ffi program oracle (removeTicksCc (letOpCompiler splitSeq cutSize compiler))
    start inlineLimit (cacheEq.trans cacheRun) distinct nonFail
  have untickedSame := removeTicks_semantics ffi (sptFromAList inlined) (inCo inlineLimit oracle)
    (letOpCompiler splitSeq cutSize compiler) start
  have middleSame : BvlSem.semantics ffi (sptFromAList unticked) (removeTicksCo ∘ inCo inlineLimit oracle)
      (letOpCompiler splitSeq cutSize compiler) start =
      BvlSem.semantics ffi (sptFromAList program) oracle
        (inCc inlineLimit (removeTicksCc (letOpCompiler splitSeq cutSize compiler))) start := by
    simpa [unticked, inlined, sptMap_sptFromAList] using untickedSame.trans inlinedSame
  have middleNonFail : BvlSem.semantics ffi (sptFromAList unticked) (removeTicksCo ∘ inCo inlineLimit oracle)
      (letOpCompiler splitSeq cutSize compiler) start ≠ .fail := by
    rw [middleSame]
    exact nonFail
  have finalSame := letOp_semantics splitSeq cutSize start ffi (sptFromAList unticked)
    (removeTicksCo ∘ inCo inlineLimit oracle) compiler middleNonFail
  simpa [outputRun, sptMap_sptFromAList] using finalSame.trans middleSame

end Flapjack.Compiler.Backend.BvlInline.Proofs
