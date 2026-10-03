import Flapjack.Compiler.Backend.WordAlloc.ProductionHeuristicCountMap
import Flapjack.Compiler.Backend.WordAlloc.HeuInst
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip

namespace Flapjack.WordAlloc
open RiscV

/-! Complete actual instruction and move-list heuristic producers on the
accepted source encoder. These implementation correspondences are untagged:
the original getHeuInst definition is already reviewed, and this file connects
the real accelerator to it without supplied output equations. -/

theorem heuristicArith_production {width : Nat} [NeZero width]
    (operation : WordArith (BitVec width)) (native : WordLangArith (BitVec width))
    (encoded : wordLangArithToHOL operation = some native)
    (counts : WordHeuristicCountMap) :
    heuristicCountMapToNative (wordHeuristicInstFast (.arith operation) counts) =
      getHeuInst (.arith native) (heuristicCountMapToNative counts) := by
  cases operation <;> simp only [wordLangArithToHOL, Option.some.injEq] at encoded
  all_goals try contradiction
  all_goals subst native
  all_goals try simp only [wordHeuristicInstFast, getHeuInst,
    heuristicCountMap_addLhsReg, heuristicCountMap_addRhsReg]
  all_goals split <;> simp only [heuristicCountMap_addRhsReg]

theorem heuristicInst_production {width : Nat} [NeZero width]
    (instruction : WordInst (BitVec width)) (native : WordLangInst (BitVec width))
    (encoded : wordLangInstToHOL instruction = some native)
    (counts : WordHeuristicCountMap) :
    heuristicCountMapToNative (wordHeuristicInstFast instruction counts) =
      getHeuInst native (heuristicCountMapToNative counts) := by
  cases instruction with
  | const name value =>
      simp only [wordLangInstToHOL, Option.some.injEq] at encoded
      subst native
      exact heuristicCountMap_addLhsConst counts name
  | arith operation =>
      cases found : wordLangArithToHOL operation with
      | none => simp [wordLangInstToHOL, found] at encoded
      | some arithmetic =>
          simp only [wordLangInstToHOL, found, Option.map_some, Option.some.injEq] at encoded
          subst native
          exact heuristicArith_production operation arithmetic found counts
  | mem operator name address =>
      simp only [wordLangInstToHOL, Option.some.injEq] at encoded
      subst native
      cases operator <;> simp only [wordHeuristicInstFast, getHeuInst,
        heuristicCountMap_addLhsMem, heuristicCountMap_addRhsMem]
  | memOffset operator name address offset =>
      simp only [wordLangInstToHOL, Option.some.injEq] at encoded
      subst native
      cases operator <;> simp only [wordHeuristicInstFast, getHeuInst,
        heuristicCountMap_addLhsMem, heuristicCountMap_addRhsMem]

theorem heuristicLhsRegs_production (names : List Nat) (counts : WordHeuristicCountMap) :
    heuristicCountMapToNative (wordHeuristicAddLhsRegsFast names counts) =
      names.foldr add1LhsReg (heuristicCountMapToNative counts) := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
      simp only [wordHeuristicAddLhsRegsFast, heuristicCountMap_addLhsReg,
        ih, List.foldr_cons]

theorem heuristicRhsRegs_production (names : List Nat) (counts : WordHeuristicCountMap) :
    heuristicCountMapToNative (wordHeuristicAddRhsRegsFast names counts) =
      names.foldr add1RhsReg (heuristicCountMapToNative counts) := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
      simp only [wordHeuristicAddRhsRegsFast, heuristicCountMap_addRhsReg,
        ih, List.foldr_cons]

theorem heuristicMoves_production (moves : List (Nat × Nat)) (counts : WordHeuristicCountMap) :
    heuristicCountMapToNative (wordHeuristicMovesFast moves counts) =
      (moves.map Prod.fst).foldr add1LhsReg
        ((moves.map Prod.snd).foldr add1RhsReg (heuristicCountMapToNative counts)) := by
  rw [wordHeuristicMovesFast, heuristicLhsRegs_production, heuristicRhsRegs_production]

end Flapjack.WordAlloc
