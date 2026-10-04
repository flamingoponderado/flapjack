import Flapjack.Pancake.Proofs.LoopToWord.EveryInstOkLess
import Flapjack.Pancake.LoopCall
import Flapjack.Pancake.LoopLive

/-!
# `pan_to_wordProof`: `loop_inst_ok` preservation through the loop optimisations

Counterparts of `cakeml/pancake/proofs/pan_to_wordProofScript.sml` 738-801:
`every_inst_ok_loop_call`, `every_inst_ok_loop_live` and
`every_inst_ok_less_optimise`. HOL `every_prog (loop_inst_ok c)` is the reviewed
`everyProgHOL (LoopToWord.loopInstOk c)`.
-/

namespace Flapjack.PanToWord

open Flapjack Flapjack.LoopToWord Flapjack.Compiler.Encoders.Asm

/-- Full original every_inst_ok_loop_call (`pan_to_wordProofScript.sml:738-752`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_loop_call"
  (words_as_type_indexed_bitvec)]
theorem everyInstOkLoopCall {width : Nat} [NeZero width] {cWidth : Nat} [NeZero cWidth] (c : AsmConfigExact cWidth) :
    ∀ (l : Spt Nat) (prog : HolLoopProg width),
      everyProgHOL (loopInstOk c) prog →
      everyProgHOL (loopInstOk c) (loopCallCompHOL l prog).1 := by
  intro l prog
  fun_induction loopCallCompHOL l prog
  case case2 returns target arguments handler compiled =>
    intro h
    have hc : ∀ r t a, everyProgHOL (loopInstOk c) (.call r t a handler) := by
      intro r t a; unfold everyProgHOL at h ⊢; exact ⟨by simp [loopInstOk], h.2⟩
    simp only [compiled]
    split
    · exact hc _ _ _
    · split
      · simp [everyProgHOL, loopInstOk]
      · split <;> exact hc _ _ _
  all_goals intro h; simp_all [everyProgHOL, loopInstOk]

/-- `loop_inst_ok` is preserved by `shrink`, and by every `fixedpoint` success
(Flapjack infrastructure: the first conjunct-pair of the HOL proof of
`every_inst_ok_loop_live`, proved by the mutual `shrink_ind`). -/
theorem shrinkHOL_everyProg_loopInstOk {width : Nat} [NeZero width] {cWidth : Nat} [NeZero cWidth] (c : AsmConfigExact cWidth) :
    ∀ (lt : List (NumSet × NumSet)) (p : HolLoopProg width) (l : NumSet),
      everyProgHOL (loopInstOk c) p → everyProgHOL (loopInstOk c) (shrinkHOL lt p l).1 := by
  intro lt p l
  apply shrinkHOL.induct
    (motive1 := fun lt liveIn l1 l2 body => everyProgHOL (loopInstOk c) body →
      ∀ b l0, fixedpointHOL lt liveIn l1 l2 body = some (b, l0) →
        everyProgHOL (loopInstOk c) b)
    (motive2 := fun lt p l => everyProgHOL (loopInstOk c) p →
      everyProgHOL (loopInstOk c) (shrinkHOL lt p l).1)
  all_goals intros
  all_goals (try (rw [shrinkHOL]; simp_all [everyProgHOL, loopInstOk]; done))
  case case1 hx ih hb b l0 hf =>
    rw [fixedpointHOL, hx] at hf
    simp only [if_true, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    have := ih hb
    rwa [hx] at this
  case case2 hx hne hle _ hb b l0 hf =>
    rw [fixedpointHOL, hx] at hf
    simp [hne, hle] at hf
  case case3 hx hne hnle _ _ _ ih hb b l0 hf =>
    rw [fixedpointHOL, hx] at hf
    simp only [hne, hnle, if_false, dite_false] at hf
    exact ih hb b l0 hf
  case case5 body' l0 hx ih hp =>
    rw [shrinkHOL]
    simp (config := { zetaDelta := true }) only [] at hx
    simp only [hx]
    unfold everyProgHOL at hp ⊢
    exact ⟨by simp [loopInstOk], ih hp.2 _ _ hx⟩
  case case6 hn b l0 hx _ ih hp =>
    rw [shrinkHOL]
    simp (config := { zetaDelta := true }) only [] at hn hx ih
    simp only [hn, hx]
    unfold everyProgHOL at hp ⊢
    have := ih hp.2
    rw [hx] at this
    exact ⟨by simp [loopInstOk], this⟩
  case case7 b1 l1 hx1 b2 l2 hx2 ih2 ih1 hp =>
    unfold shrinkHOL
    simp (config := { zetaDelta := true }) only [] at hx1 hx2 ih1 ih2
    simp only [hx1, hx2]
    unfold everyProgHOL at hp ⊢
    have e1 := ih2 hp.2.1; rw [hx1] at e1
    have e2 := ih1 hp.2.2; rw [hx2] at e2
    exact ⟨by simp [loopInstOk], e1, e2⟩

/-- `loop_inst_ok` is preserved by `mark_all` (Flapjack infrastructure: the
`mark_all_ind` step of the HOL proof of `every_inst_ok_loop_live`). -/
theorem markAllHOL_everyProg_loopInstOk {width : Nat} [NeZero width] {cWidth : Nat} [NeZero cWidth] (c : AsmConfigExact cWidth) :
    ∀ (p : HolLoopProg width),
      everyProgHOL (loopInstOk c) p → everyProgHOL (loopInstOk c) (markAllHOL p).1 := by
  intro p
  fun_induction markAllHOL p
  case case1 f s f' _ hx1 s' _ hx2 marked ih2 ih1 =>
    intro hp
    unfold everyProgHOL at hp
    have e1 := ih2 hp.2.1; rw [hx1] at e1
    have e2 := ih1 hp.2.2; rw [hx2] at e2
    have hseq : everyProgHOL (loopInstOk c) (.seq f' s') := by
      unfold everyProgHOL; exact ⟨by simp [loopInstOk], e1, e2⟩
    by_cases hm : marked = true
    · simp only [hm, if_true]; unfold everyProgHOL; exact ⟨by simp [loopInstOk], hseq⟩
    · simp only [hm]; exact hseq
  case case2 _ hx ih =>
    intro hp
    unfold everyProgHOL at hp
    have e := ih hp.2; rw [hx] at e
    unfold everyProgHOL; exact ⟨by simp [loopInstOk], e⟩
  case case3 _ _ hx1 _ _ hx2 marked program ih2 ih1 =>
    intro hp
    unfold everyProgHOL at hp
    have e1 := ih2 hp.2.1; rw [hx1] at e1
    have e2 := ih1 hp.2.2; rw [hx2] at e2
    have hprog : everyProgHOL (loopInstOk c) program := by
      simp only [program]; unfold everyProgHOL; exact ⟨by simp [loopInstOk], e1, e2⟩
    by_cases hm : marked = true
    · simp only [hm, if_true]; unfold everyProgHOL; exact ⟨by simp [loopInstOk], hprog⟩
    · simp only [hm]; exact hprog
  case case4 ih =>
    intro hp
    unfold everyProgHOL at hp
    exact ih hp.2
  case case5 =>
    intro hp
    unfold everyProgHOL; exact ⟨by simp [loopInstOk], hp⟩
  case case6 _ _ hx1 _ _ hx2 marked program ih2 ih1 =>
    intro hp
    unfold everyProgHOL at hp
    have e1 := ih2 hp.2.1; rw [hx1] at e1
    have e2 := ih1 hp.2.2; rw [hx2] at e2
    have hprog : everyProgHOL (loopInstOk c) program := by
      simp only [program]; unfold everyProgHOL; exact ⟨by simp [loopInstOk], e1, e2⟩
    by_cases hm : marked = true
    · simp only [hm, if_true]; unfold everyProgHOL; exact ⟨by simp [loopInstOk], hprog⟩
    · simp only [hm]; exact hprog
  case case7 =>
    intro hp
    unfold everyProgHOL; exact ⟨by simp [loopInstOk], hp⟩

/-- Full original every_inst_ok_loop_live (`pan_to_wordProofScript.sml:756-793`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_loop_live"
  (words_as_type_indexed_bitvec)]
theorem everyInstOkLoopLive {width : Nat} [NeZero width] {cWidth : Nat} [NeZero cWidth] (c : AsmConfigExact cWidth) :
    ∀ (prog : HolLoopProg width),
      everyProgHOL (loopInstOk c) prog → everyProgHOL (loopInstOk c) (Flapjack.compHOL prog) := by
  intro prog h
  exact markAllHOL_everyProg_loopInstOk c _ (shrinkHOL_everyProg_loopInstOk c [] prog .ln h)

/-- Full original every_inst_ok_less_optimise (`pan_to_wordProofScript.sml:795-801`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_optimise"
  (words_as_type_indexed_bitvec)]
theorem everyInstOkLessOptimise {width : Nat} [NeZero width] {cWidth : Nat} [NeZero cWidth] (c : AsmConfigExact cWidth)
    (prog : HolLoopProg width) :
    everyProgHOL (loopInstOk c) prog → everyProgHOL (loopInstOk c) (optimiseHOL prog) := by
  intro h
  exact everyInstOkLoopLive c _ (everyInstOkLoopCall c .ln prog h)

end Flapjack.PanToWord
