import Flapjack.Pancake.LoopLive

/-!
# loop_live `fixedpoint_thm`

Exact port of `cakeml/pancake/loop_liveScript.sml`'s `fixedpoint_thm` (167) over
the tagged `shrinkHOL` / its mutual `fixedpointHOL` half
(bead `flapjack-pxn.18.5.8.1.10`).
-/

namespace Flapjack

/-- Flapjack sptree helper (HOL `inter_assoc` + `inter` idempotence, used inline
    by HOL's `fixedpoint_thm` proof): intersecting twice with the same left tree
    is structurally the same as once. -/
private theorem sptInter_idem_left {α β : Type} :
    ∀ (a : Spt α) (X : Spt β), sptInter a (sptInter a X) = sptInter a X
  | .ln, _ => by simp [sptInter]
  | .ls v, X => by cases X <;> simp [sptInter]
  | .bn l r, X => by
      cases X with
      | ln => simp [sptInter]
      | ls _ => simp [sptInter]
      | bn X1 X2 =>
        simp only [sptInter]
        have hIL := sptInter_idem_left l X1
        have hIR := sptInter_idem_left r X2
        generalize sptInter l X1 = L at hIL ⊢
        generalize sptInter r X2 = R at hIR ⊢
        cases L <;> cases R <;> simp_all [sptMkBN, sptInter]
      | bs X1 _ X2 =>
        simp only [sptInter]
        have hIL := sptInter_idem_left l X1
        have hIR := sptInter_idem_left r X2
        generalize sptInter l X1 = L at hIL ⊢
        generalize sptInter r X2 = R at hIR ⊢
        cases L <;> cases R <;> simp_all [sptMkBN, sptInter]
  | .bs l v r, X => by
      cases X with
      | ln => simp [sptInter]
      | ls _ => simp [sptInter]
      | bn X1 X2 =>
        simp only [sptInter]
        have hIL := sptInter_idem_left l X1
        have hIR := sptInter_idem_left r X2
        generalize sptInter l X1 = L at hIL ⊢
        generalize sptInter r X2 = R at hIR ⊢
        cases L <;> cases R <;> simp_all [sptMkBN, sptInter]
      | bs X1 _ X2 =>
        simp only [sptInter]
        have hIL := sptInter_idem_left l X1
        have hIR := sptInter_idem_left r X2
        generalize sptInter l X1 = L at hIL ⊢
        generalize sptInter r X2 = R at hIR ⊢
        cases L <;> cases R <;> simp_all [sptMkBS, sptInter]

/-- Exact HOL `fixedpoint_thm` (`loop_liveScript.sml:167-170`):
    `∀lt live_in l1 l2 (body:'a loopLang$prog) l0 b.
      fixedpoint lt live_in l1 l2 body = SOME (b, l0) ⇒
      shrink ((inter live_in l0, l2)::lt) body l2 = (b, l0)`. -/
@[hol "cakeml/pancake/loop_liveScript.sml" "fixedpoint_thm" (words_as_type_indexed_bitvec)]
theorem fixedpoint_thm {width : Nat} [NeZero width] :
    ∀ (lt : List (NumSet × NumSet)) (live_in l1 l2 : NumSet) (body : HolLoopProg width)
      (l0 : NumSet) (b : HolLoopProg width),
      fixedpointHOL lt live_in l1 l2 body = some (b, l0) →
      shrinkHOL ((sptInter live_in l0, l2) :: lt) body l2 = (b, l0) := by
  intro lt live_in l1 l2 body
  induction hn : sptSize live_in - sptSize l1 using Nat.strongRecOn generalizing l1 with
  | ind n ih =>
    intro l0 b h
    rw [fixedpointHOL] at h
    rcases hs : shrinkHOL ((sptInter live_in l1, l2) :: lt) body l2 with ⟨b', l0'⟩
    rw [hs] at h
    simp only at h
    by_cases heq : sptInter live_in l0' = l1
    · rw [if_pos heq, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hidem : sptInter live_in l1 = l1 := by
        rw [← heq]; exact sptInter_idem_left live_in l0'
      rw [heq, ← hidem, hs]
    · rw [if_neg heq] at h
      by_cases hle : sptSize (sptInter live_in l0') ≤ sptSize l1
      · rw [dif_pos hle] at h; cases h
      · rw [dif_neg hle] at h
        have hb := sptSize_inter_le live_in l0'
        exact ih (sptSize live_in - sptSize (sptInter live_in l0')) (by omega) _ rfl l0 b h

end Flapjack
