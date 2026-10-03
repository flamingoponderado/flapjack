import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions
import Flapjack.Pancake.WordConvs.FullInstOkLess

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Encoders.Asm

/-- Original unconditional fake-sequence instruction validity, with arbitrary
assembler configuration and source list. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "fake_seq_full_inst_ok_less" (words_as_type_indexed_bitvec)]
theorem fakeSeq_fullInstOkLess {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (names : List Nat) :
    fullInstOkLessExact config
      ((names.map (fakeMove : Nat → WordLangProgHOL (BitVec width))).foldr .seq .skip) = true := by
  induction names with
  | nil => simp [fullInstOkLessExact, fullInstOkLessWith]
  | cons name names ih =>
      simpa [fullInstOkLessExact, fullInstOkLessWith, fakeMove,
        HolInst.ofWordLangInst, instOkLessExact] using ih

/-- Original loop setup validity with the actual producer equation as sole
premise; no SSA map or register-bound assumptions are added. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "loop_setup_full_inst_ok_less" (words_as_type_indexed_bitvec)]
theorem loopSetup_fullInstOkLess {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (names exitNames : Spt Unit) (ssa : Spt Nat) (na : Nat)
    (setupProg : WordLangProgHOL (BitVec width)) (ssaRefreshed : Spt Nat)
    (naRefreshed : Nat)
    (setup : loopSetup names exitNames ssa na = (setupProg, ssaRefreshed, naRefreshed)) :
    fullInstOkLessExact config setupProg = true := by
  unfold loopSetup at setup
  generalize hr : listNextVarRename
    (((sptToAList (sptUnion names exitNames)).map Prod.fst).filter
      fun v => (sptLookup v ssa).isNone) ssa na = renamed at setup
  rcases renamed with ⟨fresh, extended, next⟩
  generalize hm : listNextVarRenameMove (width := width) extended next
    (((sptToAList (sptUnion names exitNames)).map Prod.fst).filter
      fun v => (sptLookup v ssa).isSome) = moved at setup
  rcases moved with ⟨moves, refreshed, nextOut⟩
  simp only [hr, hm] at setup
  have fake := fakeSeq_fullInstOkLess config fresh
  have moveConvention : fullInstOkLessExact config moves = true := by
    unfold listNextVarRenameMove at hm
    have projected := congrArg Prod.fst hm
    simp only at projected
    rw [← projected]
    simp [fullInstOkLessExact, fullInstOkLessWith]
  have output := congrArg Prod.fst setup
  simp only at output
  rw [← output]
  rw [fullInstOkLessExactSeq, fake, moveConvention]
  rfl

end Flapjack.WordAlloc
