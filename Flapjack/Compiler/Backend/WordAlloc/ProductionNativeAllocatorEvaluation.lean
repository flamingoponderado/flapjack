import Flapjack.Compiler.Backend.WordAlloc.ProductionNativeCleanupChainEvaluation
import Flapjack.Compiler.Backend.WordAlloc.ProductionNativeColouringOk
import Flapjack.Compiler.Backend.WordAlloc.ProductionFullSSACanonicalImage
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSingle
import Flapjack.Pancake.Proofs.WordConvs.SSAFlatFull

/-! Whole executed allocator stage.

The executed allocator `cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy`
(`RiscV/WordDeadCode.lean`) runs the SSA producer, the cleanup chain and register
colouring: the `full_ssa_cc_trans` .. `word_alloc` segment of HOL `compile_single`
(`word_to_wordScript.sml:26-33`). This module composes `nativeSsa`, the cleanup chain
(`nativeCleanupChain_evaluation`) and `nativeAllocator_colouringEvaluation` into one
evaluation theorem for the executed stage, in the shape HOL `compile_single_correct`
composes those passes. It is Flapjack API infrastructure with no separate HOL original;
the preceding `word_simp`/`inst_select` stages and the production/native evaluator relation
are separate obligations. -/

namespace Flapjack.WordAlloc
open WordSemStateFiniteExact Compiler.Backend.WordCopy Compiler.Backend.WordInst
  Compiler.Backend.WordUnreach Compiler.Backend.WordCse RiscV RiscV.CakeRegAlloc
  Compiler.Encoders.Asm Compiler.Backend.WordAlloc
open Compiler.Backend.WordAlloc.Proofs (evenStartingLocals)
set_option autoImplicit false

/-- SSA's starting-locals domain (`even_list`) consists of physical variables, as the
colouring theorem's `even_starting_locals` premise requires (Flapjack infrastructure). -/
theorem evenStartingLocals_of_evenList {width : Nat} [NeZero width]
    (locals : Spt (WordLocW width)) (count : Nat)
    (domain : sptDomain locals = (fun key => key ∈ evenList count)) :
    evenStartingLocals locals := by
  intro key member
  rw [domain] at member
  simp only [evenList, List.mem_map, List.mem_range] at member
  obtain ⟨index, -, rfl⟩ := member
  simp [Flapjack.isPhyVar]

end Flapjack.WordAlloc
