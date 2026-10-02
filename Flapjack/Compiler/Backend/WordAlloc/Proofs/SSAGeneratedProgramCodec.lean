import Flapjack.Compiler.Backend.WordAlloc.SSAHelpers
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec

namespace Flapjack.Compiler.Backend.WordAlloc

/-! These are Flapjack carrier-boundary lemmas, without independent HOL originals.
They prove decoder availability for complete native SSA helper outputs; they do
not establish the full pass simulation or switch its production caller. -/

theorem ssaGeneratedSeq_decoderClosure {width : Nat}
    (left right : WordLangProgHOL (BitVec width))
    (hl : (wordLangProgFromHOL left).isSome = true)
    (hr : (wordLangProgFromHOL right).isSome = true) :
    (wordLangProgFromHOL (.seq left right)).isSome = true := by
  cases hleft : wordLangProgFromHOL left <;> simp [hleft] at hl
  cases hright : wordLangProgFromHOL right <;> simp [hright] at hr
  simp [wordLangProgFromHOL, hleft, hright]

theorem fakeMove_decoderClosure {width : Nat} [NeZero width] (register : Nat) :
    (wordLangProgFromHOL (fakeMove (width := width) register)).isSome = true := by
  simp [fakeMove, wordLangProgFromHOL, wordLangInstFromHOL]

theorem fakeMoves_decoderClosure {width : Nat} [NeZero width]
    (prio : Option (Unit ⊕ Unit)) (names : List Nat) (left right : Spt Nat) (next : Nat) :
    (wordLangProgFromHOL (fakeMoves (width := width) prio names left right next).1).isSome = true ∧
    (wordLangProgFromHOL (fakeMoves (width := width) prio names left right next).2.1).isSome = true := by
  induction names generalizing left right next with
  | nil => simp [fakeMoves, wordLangProgFromHOL]
  | cons name names ih =>
    have tail := ih left right next
    generalize h : fakeMoves (width := width) prio names left right next = result at tail ⊢
    rcases result with ⟨lp, rp, n, lm, rm⟩
    simp only [fakeMoves, h]
    cases sptLookup name lm <;> cases sptLookup name rm <;> simp only
    · exact tail
    · exact ⟨ssaGeneratedSeq_decoderClosure _ _ tail.1 (fakeMove_decoderClosure _),
        ssaGeneratedSeq_decoderClosure _ _ tail.2 (by simp [wordLangProgFromHOL])⟩
    · exact ⟨ssaGeneratedSeq_decoderClosure _ _ tail.1 (by simp [wordLangProgFromHOL]),
        ssaGeneratedSeq_decoderClosure _ _ tail.2 (fakeMove_decoderClosure _)⟩
    · exact tail

theorem fixInconsistencies_decoderClosure {width : Nat} [NeZero width]
    (prio : Option (Unit ⊕ Unit)) (left right : Spt Nat) (next : Nat) :
    (wordLangProgFromHOL (fixInconsistencies (width := width) prio left right next).1).isSome = true ∧
    (wordLangProgFromHOL (fixInconsistencies (width := width) prio left right next).2.1).isSome = true := by
  unfold fixInconsistencies
  dsimp only
  generalize hmerge : mergeMoves ((sptToAList (sptUnion left right)).map Prod.fst) left right next = merged
  rcases merged with ⟨movesL, movesR, n, lm, rm⟩
  have accepted := fakeMoves_decoderClosure (width := width) prio
    ((sptToAList (sptUnion left right)).map Prod.fst) lm rm n
  generalize h : fakeMoves (width := width) prio
    ((sptToAList (sptUnion left right)).map Prod.fst) lm rm n = result at accepted ⊢
  rcases result with ⟨lp, rp, n2, lm2, rm2⟩
  exact ⟨ssaGeneratedSeq_decoderClosure _ _ (by simp [wordLangProgFromHOL]) accepted.1,
    ssaGeneratedSeq_decoderClosure _ _ (by simp [wordLangProgFromHOL]) accepted.2⟩

theorem listNextVarRenameMove_decoderClosure {width : Nat} [NeZero width]
    (ssa : Spt Nat) (next : Nat) (names : List Nat) :
    (wordLangProgFromHOL (listNextVarRenameMove (width := width) ssa next names).1).isSome = true := by
  unfold listNextVarRenameMove
  split
  simp [wordLangProgFromHOL]

theorem fakeMoveFold_decoderClosure {width : Nat} [NeZero width] (registers : List Nat) :
    (wordLangProgFromHOL ((registers.map (fakeMove (width := width))).foldr .seq .skip)).isSome = true := by
  induction registers with
  | nil => simp [wordLangProgFromHOL]
  | cons register registers ih =>
    exact ssaGeneratedSeq_decoderClosure _ _ (fakeMove_decoderClosure register) ih

theorem loopSetup_decoderClosure {width : Nat} [NeZero width]
    (names exits : Spt Unit) (ssa : Spt Nat) (next : Nat) :
    (wordLangProgFromHOL (loopSetup (width := width) names exits ssa next).1).isSome = true := by
  unfold loopSetup
  dsimp only
  generalize hrename : listNextVarRename
    (((sptToAList (sptUnion names exits)).map Prod.fst).filter fun v => (sptLookup v ssa).isNone) ssa next = renamed
  rcases renamed with ⟨registers, extended, n⟩
  have accepted := listNextVarRenameMove_decoderClosure (width := width) extended n
    (((sptToAList (sptUnion names exits)).map Prod.fst).filter fun v => (sptLookup v ssa).isSome)
  generalize h : listNextVarRenameMove (width := width) extended n
    (((sptToAList (sptUnion names exits)).map Prod.fst).filter fun v => (sptLookup v ssa).isSome) = result at accepted ⊢
  rcases result with ⟨program, finalMap, finalNext⟩
  exact ssaGeneratedSeq_decoderClosure _ _ (fakeMoveFold_decoderClosure registers) accepted

end Flapjack.Compiler.Backend.WordAlloc
