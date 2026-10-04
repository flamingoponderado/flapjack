import Flapjack.Pancake.Proofs.LoopToWord.EveryInstOkLess
import Flapjack.Pancake.LoopCall
import Flapjack.Pancake.LoopLive
import Flapjack.Pancake.CrepToLoop.ContextExact
import Flapjack.Pancake.Semantics.CrepProps.EveryExpHOL
import Flapjack.Pancake.CrepArith

/-!
# `pan_to_wordProof`: `loop_inst_ok` preservation through the loop optimisations

Counterparts of `cakeml/pancake/proofs/pan_to_wordProofScript.sml` 738-801:
`every_inst_ok_loop_call`, `every_inst_ok_loop_live` and
`every_inst_ok_less_optimise`. HOL `every_prog (loop_inst_ok c)` is the reviewed
`everyProgHOL (LoopToWord.loopInstOk c)`.
-/

namespace Flapjack.PanToWord

open Flapjack Flapjack.LoopToWord Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Full original every_inst_ok_loop_call (`pan_to_wordProofScript.sml:738-752`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
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
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem everyInstOkLoopLive {width : Nat} [NeZero width] {cWidth : Nat} [NeZero cWidth] (c : AsmConfigExact cWidth) :
    ∀ (prog : HolLoopProg width),
      everyProgHOL (loopInstOk c) prog → everyProgHOL (loopInstOk c) (Flapjack.compHOL prog) := by
  intro prog h
  exact markAllHOL_everyProg_loopInstOk c _ (shrinkHOL_everyProg_loopInstOk c [] prog .ln h)

/-- Full original every_inst_ok_less_optimise (`pan_to_wordProofScript.sml:795-801`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem everyInstOkLessOptimise {width : Nat} [NeZero width] {cWidth : Nat} [NeZero cWidth] (c : AsmConfigExact cWidth)
    (prog : HolLoopProg width) :
    everyProgHOL (loopInstOk c) prog → everyProgHOL (loopInstOk c) (optimiseHOL prog) := by
  intro h
  exact everyInstOkLoopLive c _ (everyInstOkLoopCall c .ln prog h)

/-- `compile_exps` returns one value per argument (Flapjack infrastructure). -/
theorem compileExpsHOLExact_values_length {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) :
    ∀ (n : Nat) (ns : NumSet) (es : List (CrepExpHOL width)),
      (compileExpsHOLExact ctxt n ns es).2.1.length = es.length := by
  intro n ns es
  induction es generalizing n ns with
  | nil => simp [compileExpsHOLExact]
  | cons e es ih =>
    rw [compileExpsHOLExact]
    simp only [List.length_cons, ih]

/-- Full original every_inst_ok_less_crep_to_loop_compile_exp
(`pan_to_wordProofScript.sml:803-838`), both conjuncts: for `compile_exp` and for
the mutual `compile_exps`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem everyInstOkLessCrepToLoopCompileExp {width : Nat} [NeZero width]
    {cWidth : Nat} [NeZero cWidth] (c : AsmConfigExact cWidth) :
    (∀ (ctxt : CrepToLoopContextExact) (n : Nat) (ns : NumSet) (e : CrepExpHOL width),
      ctxt.target = c.isa ∧
        crepEveryExpHOL (fun x => ∀ op es, x = .crepOp op es → es.length = 2) e →
      ∀ p ∈ (compileExpHOLExact ctxt n ns e).1, everyProgHOL (loopInstOk c) p) ∧
    (∀ (ctxt : CrepToLoopContextExact) (n : Nat) (ns : NumSet) (es : List (CrepExpHOL width)),
      ctxt.target = c.isa ∧
        (∀ e ∈ es, crepEveryExpHOL (fun x => ∀ op es, x = .crepOp op es → es.length = 2) e) →
      ∀ p ∈ (compileExpsHOLExact ctxt n ns es).1, everyProgHOL (loopInstOk c) p) := by
  have key : ∀ (ctxt : CrepToLoopContextExact), ctxt.target = c.isa →
      (∀ n ns (e : CrepExpHOL width),
        crepEveryExpHOL (fun x => ∀ op es, x = .crepOp op es → es.length = 2) e →
        ∀ p ∈ (compileExpHOLExact ctxt n ns e).1, everyProgHOL (loopInstOk c) p) ∧
      (∀ n ns (es : List (CrepExpHOL width)),
        (∀ e ∈ es, crepEveryExpHOL (fun x => ∀ op es, x = .crepOp op es → es.length = 2) e) →
        ∀ p ∈ (compileExpsHOLExact ctxt n ns es).1, everyProgHOL (loopInstOk c) p) := by
    intro ctxt ht
    apply compileExpHOLExact.mutual_induct ctxt
    all_goals intros
    case case1 | case2 | case3 | case4 | case8 =>
      rename_i hp; rw [compileExpHOLExact] at hp; simp at hp
    case case13 =>
      rename_i hp; rw [compileExpsHOLExact] at hp; simp at hp
    case case5 hx ih he p hp =>
      rw [compileExpHOLExact] at hp; simp only [hx] at hp
      unfold crepEveryExpHOL at he
      have := ih he.2; rw [hx] at this; exact this p hp
    case case6 hx ih he p hp =>
      rw [compileExpHOLExact] at hp; simp only [hx] at hp
      unfold crepEveryExpHOL at he
      have := ih he.2; rw [hx] at this
      rcases List.mem_append.mp hp with hp | hp
      · exact this p hp
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> (unfold everyProgHOL; simp [loopInstOk])
    case case7 hx ih he p hp =>
      rw [compileExpHOLExact] at hp; simp only [hx] at hp
      unfold crepEveryExpHOL at he
      have := ih he.2; rw [hx] at this
      rcases List.mem_append.mp hp with hp | hp
      · exact this p hp
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> (unfold everyProgHOL; simp [loopInstOk])
    case case9 hx ih he p hp =>
      rw [compileExpHOLExact] at hp; simp only [hx] at hp
      unfold crepEveryExpHOL at he
      have := ih ((crepEveryExpListHOL_iff _ _).mp he.2); rw [hx] at this; exact this p hp
    case case12 hx1 _ _ _ _ hx2 ih2 ih1 he p hp =>
      rw [compileExpHOLExact] at hp; simp only [hx1, hx2] at hp
      unfold crepEveryExpHOL at he
      have e1 := ih2 he.2.1; rw [hx1] at e1
      have e2 := ih1 he.2.2; rw [hx2] at e2
      rcases List.mem_append.mp hp with hp | hp
      · exact e1 p hp
      · exact e2 p hp
    case case14 hx1 _ _ _ _ hx2 ih2 ih1 he p hp =>
      rw [compileExpsHOLExact] at hp; simp only [hx1, hx2] at hp
      have e1 := ih2 (he _ List.mem_cons_self); rw [hx1] at e1
      have e2 := ih1 (fun e h => he e (List.mem_cons_of_mem _ h)); rw [hx2] at e2
      rcases List.mem_append.mp hp with hp | hp
      · exact e1 p hp
      · exact e2 p hp
    case case11 hx1 _ _ _ _ hx2 ih2 ih1 he p hp =>
      rw [compileExpHOLExact] at hp; simp only [hx1, hx2, progIfHOLExact] at hp
      unfold crepEveryExpHOL at he
      have e1 := ih2 he.2.1; rw [hx1] at e1
      have e2 := ih1 he.2.2; rw [hx2] at e2
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with (hp | hp) | hp | hp | hp
      · exact e1 p hp
      · exact e2 p hp
      all_goals (subst hp; unfold everyProgHOL; simp only [loopInstOk, true_and])
      all_goals (try trivial)
      exact ⟨by unfold everyProgHOL; trivial, by unfold everyProgHOL; trivial⟩
    case case10 tmp live op es _ vals nxt _ hx1 opc dst hx2 ih he p hp =>
      rw [compileExpHOLExact] at hp; simp only [hx1, hx2] at hp
      unfold crepEveryExpHOL at he
      have hlen : es.length = 2 := he.1 op es rfl
      have hvl := compileExpsHOLExact_values_length ctxt tmp live es
      rw [hx1] at hvl; simp only at hvl
      have e1 := ih ((crepEveryExpListHOL_iff _ _).mp he.2); rw [hx1] at e1
      rcases List.mem_append.mp hp with hp | hp
      · rcases List.mem_append.mp hp with hp | hp
        · exact e1 p hp
        · have hz : ∀ (l : List Nat) (vs : List (HolLoopExp width)),
              p ∈ List.zipWith (fun o v => HolLoopProg.assign (nxt + o) v) l vs →
              ∃ a b, p = HolLoopProg.assign a b := by
            intro l
            induction l with
            | nil => intro vs h; simp at h
            | cons x xs ihl =>
              intro vs h
              cases vs with
              | nil => simp at h
              | cons v vs =>
                simp only [List.zipWith_cons_cons, List.mem_cons] at h
                rcases h with rfl | h
                · exact ⟨_, _, rfl⟩
                · exact ihl vs h
          obtain ⟨a, b, rfl⟩ := hz _ _ hp
          unfold everyProgHOL; simp [loopInstOk]
      · cases op
        rw [hvl, hlen] at hx2
        unfold compileCrepopHOLExact at hx2
        by_cases h7 : ctxt.target = .armv7
        · simp only [h7, if_true, Prod.mk.injEq] at hx2
          obtain ⟨rfl, -⟩ := hx2
          simp only [List.mem_singleton] at hp; subst hp
          unfold everyProgHOL
          simp only [loopInstOk]
          exact ⟨fun _ => by omega, fun _ => ⟨by omega, by omega⟩⟩
        · simp only [h7, if_false, Prod.mk.injEq] at hx2
          obtain ⟨rfl, -⟩ := hx2
          simp only [List.mem_singleton] at hp; subst hp
          unfold everyProgHOL
          simp only [loopInstOk]
          exact ⟨fun h => absurd (ht.trans h) h7, fun _ => ⟨by omega, by omega⟩⟩
  exact ⟨fun ctxt n ns e h => (key ctxt h.1).1 n ns e h.2,
    fun ctxt n ns es h => (key ctxt h.1).2 n ns es h.2⟩

/-- Full original every_prog_loop_inst_ok_nested_seq
(`pan_to_wordProofScript.sml:840-847`); HOL's Boolean equation is `↔`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem everyProgLoopInstOkNestedSeq {cWidth : Nat} [NeZero cWidth] {width : Nat} [NeZero width] :
    ∀ (c : AsmConfigExact cWidth) (ps : List (HolLoopProg width)),
      everyProgHOL (loopInstOk c) (loopNestedSeqHOL ps) ↔ ∀ p ∈ ps, everyProgHOL (loopInstOk c) p := by
  intro c ps
  induction ps with
  | nil => simp [loopNestedSeqHOL, everyProgHOL, loopInstOk]
  | cons p ps ih =>
    simp [loopNestedSeqHOL, everyProgHOL, loopInstOk, ih]

/-- Every assignment produced by zipping registers with values satisfies
`every_prog (loop_inst_ok c)` (Flapjack infrastructure). -/
theorem everyProg_zipWith_assign {width : Nat} [NeZero width] {cWidth : Nat} [NeZero cWidth]
    (c : AsmConfigExact cWidth) :
    ∀ (ns : List Nat) (vs : List (HolLoopExp width)),
      ∀ p ∈ List.zipWith HolLoopProg.assign ns vs, everyProgHOL (loopInstOk c) p := by
  intro ns
  induction ns with
  | nil => intro vs p h; simp at h
  | cons n ns ih =>
    intro vs p h
    cases vs with
    | nil => simp at h
    | cons v vs =>
      simp only [List.zipWith_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · simp [everyProgHOL, loopInstOk]
      · exact ih vs p h

namespace CrepToLoopContextWitness

/-- Same-module witness for the `fmap_as_finite_support := [vars, funcs]`
qualifier of `every_inst_ok_less_crep_to_loop_compile`, re-exporting the
reviewed `CrepToLoopContextExact` roundtrip. -/
theorem holFmapAsFiniteSupportWitness (context : CrepToLoopContextExact) :
    CrepToLoopContextExact.ofBroad (CrepToLoopContextExact.toBroad context) = context :=
  CrepToLoopContextExact.holFmapAsFiniteSupportWitness context

end CrepToLoopContextWitness

/-- Full original every_inst_ok_less_crep_to_loop_compile
(`pan_to_wordProofScript.sml:849-884`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem everyInstOkLessCrepToLoopCompile {width : Nat} [NeZero width]
    {cWidth : Nat} [NeZero cWidth] (c : AsmConfigExact cWidth) :
    ∀ (ctxt : CrepToLoopContextExact) (ns : NumSet) (body : CrepProgHOL width),
      ctxt.target = c.isa ∧
        (∀ e ∈ crepExpsOfHOL body,
          crepEveryExpHOL (fun x => ∀ op es, x = .crepOp op es → es.length = 2) e) →
      everyProgHOL (loopInstOk c) (compileHOLExact ctxt ns body) := by
  intro ctxt ns body
  induction hs : sizeOf body using Nat.strongRecOn generalizing ctxt ns body with
  | _ k ih =>
  rintro ⟨ht, he⟩
  have hexp := fun n ns e h => (everyInstOkLessCrepToLoopCompileExp (width := width) c).1 ctxt n ns e ⟨ht, h⟩
  have hexps := fun n ns es h => (everyInstOkLessCrepToLoopCompileExp (width := width) c).2 ctxt n ns es ⟨ht, h⟩
  cases body
  case skip | «break» | «continue» | tick | raise =>
    rw [compileHOLExact.eq_def]; simp [everyProgHOL, loopInstOk]
  case primitive =>
    rw [compileHOLExact.eq_def]; dsimp only; split <;> simp [everyProgHOL, loopInstOk]
  case extCall =>
    rw [compileHOLExact.eq_def]; dsimp only; split <;> simp [everyProgHOL, loopInstOk]
  case assign name value =>
    have hv := he value (by rw [crepExpsOfHOL]; simp)
    rw [compileHOLExact.eq_def]; dsimp only
    split
    · simp [everyProgHOL, loopInstOk]
    · rw [everyProgLoopInstOkNestedSeq]
      simp only [List.forall_mem_append, List.forall_mem_cons]
      exact ⟨hexp _ _ _ hv, by simp [everyProgHOL, loopInstOk], by simp⟩
  case store a v =>
    have ha := he a (by rw [crepExpsOfHOL]; simp)
    have hv := he v (by rw [crepExpsOfHOL]; simp)
    rw [compileHOLExact.eq_def]; dsimp only
    rw [everyProgLoopInstOkNestedSeq]
    simp only [List.forall_mem_append, List.forall_mem_cons]
    exact ⟨⟨hexp _ _ _ ha, hexp _ _ _ hv⟩, by simp [everyProgHOL, loopInstOk],
      by simp [everyProgHOL, loopInstOk], by simp⟩
  case store32 a v | storeByte a v =>
    have ha := he a (by rw [crepExpsOfHOL]; simp)
    have hv := he v (by rw [crepExpsOfHOL]; simp)
    rw [compileHOLExact.eq_def]; dsimp only
    rw [everyProgLoopInstOkNestedSeq]
    simp only [List.forall_mem_append, List.forall_mem_cons]
    exact ⟨⟨hexp _ _ _ ha, hexp _ _ _ hv⟩, by simp [everyProgHOL, loopInstOk],
      by simp [everyProgHOL, loopInstOk], by simp [everyProgHOL, loopInstOk], by simp⟩
  case storeGlob a v =>
    have hv := he v (by rw [crepExpsOfHOL]; simp)
    rw [compileHOLExact.eq_def]; dsimp only
    rw [everyProgLoopInstOkNestedSeq]
    simp only [List.forall_mem_append, List.forall_mem_cons]
    exact ⟨hexp _ _ _ hv, by simp [everyProgHOL, loopInstOk], by simp⟩
  case shMem op n a =>
    have ha := he a (by rw [crepExpsOfHOL]; simp)
    rw [compileHOLExact.eq_def]; dsimp only
    split
    · simp [everyProgHOL, loopInstOk]
    · rw [everyProgLoopInstOkNestedSeq]
      simp only [List.forall_mem_append, List.forall_mem_cons]
      exact ⟨hexp _ _ _ ha, by simp [everyProgHOL, loopInstOk], by simp⟩
  case «return» vs =>
    have hvs : ∀ e ∈ vs, _ := fun e h => he e (by rw [crepExpsOfHOL]; exact h)
    rw [compileHOLExact.eq_def]; dsimp only
    rw [everyProgLoopInstOkNestedSeq]
    simp only [List.forall_mem_append, List.forall_mem_cons]
    exact ⟨⟨hexps _ _ _ hvs, everyProg_zipWith_assign c _ _⟩,
      by simp [everyProgHOL, loopInstOk], by simp⟩
  case seq f g =>
    have hf := ih (sizeOf f) (by rw [← hs]; simp; omega) ctxt ns f rfl
      ⟨ht, fun e h => he e (by rw [crepExpsOfHOL]; simp [h])⟩
    have hg := ih (sizeOf g) (by rw [← hs]; simp; omega) ctxt ns g rfl
      ⟨ht, fun e h => he e (by rw [crepExpsOfHOL]; simp [h])⟩
    rw [compileHOLExact.eq_def]; dsimp only
    unfold everyProgHOL
    exact ⟨by simp [loopInstOk], hf, hg⟩
  case dec n v b =>
    have hv := he v (by rw [crepExpsOfHOL]; simp)
    rw [compileHOLExact.eq_def]; dsimp only
    have hb := ih (sizeOf b) (by rw [← hs]; simp; omega)
      { ctxt with vars := ctxt.vars.updateEq (n, (compileExpHOLExact ctxt (ctxt.vmax + 1) ns v).2.2.1),
                  vmax := (compileExpHOLExact ctxt (ctxt.vmax + 1) ns v).2.2.1 }
      (sptInsert (compileExpHOLExact ctxt (ctxt.vmax + 1) ns v).2.2.1 () ns) b rfl
      ⟨ht, fun e h => he e (by rw [crepExpsOfHOL]; simp [h])⟩
    unfold everyProgHOL
    refine ⟨by simp [loopInstOk], (everyProgLoopInstOkNestedSeq c _).mpr (hexp _ _ _ hv), ?_⟩
    unfold everyProgHOL
    exact ⟨by simp [loopInstOk], by simp [everyProgHOL, loopInstOk], hb⟩
  case ite cond t f =>
    have hc := he cond (by rw [crepExpsOfHOL]; simp)
    have hT := ih (sizeOf t) (by rw [← hs]; simp; omega) ctxt ns t rfl
      ⟨ht, fun e h => he e (by rw [crepExpsOfHOL]; simp [h])⟩
    have hF := ih (sizeOf f) (by rw [← hs]; simp; omega) ctxt ns f rfl
      ⟨ht, fun e h => he e (by rw [crepExpsOfHOL]; simp [h])⟩
    rw [compileHOLExact.eq_def]; dsimp only
    rw [everyProgLoopInstOkNestedSeq]
    simp only [List.forall_mem_append, List.forall_mem_cons]
    refine ⟨hexp _ _ _ hc, by simp [everyProgHOL, loopInstOk], ?_, by simp⟩
    unfold everyProgHOL
    exact ⟨by simp [loopInstOk], hT, hF⟩
  case «while» cond b =>
    have hc := he cond (by rw [crepExpsOfHOL]; simp)
    have hb := ih (sizeOf b) (by rw [← hs]; simp; omega) ctxt ns b rfl
      ⟨ht, fun e h => he e (by rw [crepExpsOfHOL]; simp [h])⟩
    rw [compileHOLExact.eq_def]; dsimp only
    unfold everyProgHOL
    refine ⟨by simp [loopInstOk], ?_⟩
    rw [everyProgLoopInstOkNestedSeq]
    simp only [List.forall_mem_append, List.forall_mem_cons]
    refine ⟨hexp _ _ _ hc, by simp [everyProgHOL, loopInstOk], ?_, by simp⟩
    unfold everyProgHOL
    refine ⟨by simp [loopInstOk], ?_, by simp [everyProgHOL, loopInstOk]⟩
    unfold everyProgHOL
    exact ⟨by simp [loopInstOk], hb, by simp [everyProgHOL, loopInstOk]⟩
  case call ri name args =>
    have hargs : ∀ e ∈ args, _ := fun e h => he e (by
      rcases ri with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rw [crepExpsOfHOL] <;> simp [h])
    rw [compileHOLExact.eq_def]; dsimp only
    rw [everyProgLoopInstOkNestedSeq]
    simp only [List.forall_mem_append, List.forall_mem_cons]
    refine ⟨⟨hexps _ _ _ hargs, everyProg_zipWith_assign c _ _⟩, ?_, by simp⟩
    rcases ri with _ | ⟨rv, _ | ⟨exn, hp⟩⟩
    · simp [everyProgHOL, loopInstOk]
    · simp [everyProgHOL, loopInstOk]
    · have hh := ih (sizeOf hp) (by rw [← hs]; simp; omega) ctxt ns hp rfl
        ⟨ht, fun e h => he e (by rw [crepExpsOfHOL]; simp [h])⟩
      dsimp only
      unfold everyProgHOL
      refine ⟨by simp [loopInstOk], ?_, by simp [everyProgHOL, loopInstOk]⟩
      unfold everyProgHOL
      refine ⟨by simp [loopInstOk], by simp [everyProgHOL, loopInstOk], ?_⟩
      unfold everyProgHOL
      exact ⟨by simp [loopInstOk], by simp [everyProgHOL, loopInstOk], hh⟩

/-- Full original every_inst_ok_less_comp_func (`pan_to_wordProofScript.sml:886-893`):
`comp_func c.ISA (make_funcs prog) params body`, with `make_funcs` the reviewed
generic `crepToLoopMakeFuncsExactHOL` over the independent `γ`, `δ` of HOL's
`prog : (mlstring # γ list # δ) list`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem everyInstOkLessCompFunc {width : Nat} [NeZero width] {cWidth : Nat} [NeZero cWidth]
    {γ δ : Type} (c : AsmConfigExact cWidth) (prog : List (MlString × List γ × δ))
    (params : List Nat) (body : CrepProgHOL width) :
    (∀ e ∈ crepExpsOfHOL body,
      crepEveryExpHOL (fun x => ∀ op es, x = .crepOp op es → es.length = 2) e) →
    everyProgHOL (loopInstOk c)
      (compFuncHOLExact c.isa (crepToLoopMakeFuncsExactHOL prog) params body) := by
  intro h
  unfold compFuncHOLExact
  exact everyInstOkLessCrepToLoopCompile c _ _ body ⟨rfl, h⟩

/-- `mul_const` preserves the two-argument `Crepop` condition (Flapjack
infrastructure for `every_inst_ok_arith_simp_exp`'s `mul_const_def` case split). -/
theorem crepEveryExpHOL_mulConst {width : Nat} [NeZero width] (e : CrepExpHOL width)
    (k : BitVec width)
    (he : crepEveryExpHOL (fun x => ∀ op es, x = .crepOp op es → es.length = 2) e) :
    crepEveryExpHOL (fun x => ∀ op es, x = .crepOp op es → es.length = 2)
      (crepMulConstHOL e k) := by
  unfold crepMulConstHOL
  split
  · simp [crepEveryExpHOL]
  · split
    · exact he
    · split
      · simp only [crepEveryExpHOL, crepEveryExpListHOL]
        exact ⟨(by intro op es h; cases h; rfl), he, (by simp), trivial⟩
      · simp only [crepEveryExpHOL]
        exact ⟨(by intro op es h; cases h), he, (by simp)⟩

/-- Both simplified arguments of a two-argument `Crepop` satisfy the condition
(Flapjack infrastructure). -/
theorem crepEveryExpHOL_simp_pair {width : Nat} [NeZero width]
    (es : List (CrepExpHOL width)) (first second : CrepExpHOL width)
    (hmap : es.map crepSimpExpHOL = [first, second])
    (ih : ∀ x ∈ es,
      crepEveryExpHOL (fun x => ∀ op es, x = .crepOp op es → es.length = 2) x →
      crepEveryExpHOL (fun x => ∀ op es, x = .crepOp op es → es.length = 2) (crepSimpExpHOL x))
    (hes : ∀ x ∈ es, crepEveryExpHOL (fun x => ∀ op es, x = .crepOp op es → es.length = 2) x) :
    crepEveryExpHOL (fun x => ∀ op es, x = .crepOp op es → es.length = 2) first ∧
      crepEveryExpHOL (fun x => ∀ op es, x = .crepOp op es → es.length = 2) second := by
  rcases es with _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, es⟩⟩⟩ <;> simp at hmap
  obtain ⟨rfl, rfl⟩ := hmap
  exact ⟨ih e1 (by simp) (hes e1 (by simp)), ih e2 (by simp) (hes e2 (by simp))⟩

/-- Full original every_inst_ok_arith_simp_exp (`pan_to_wordProofScript.sml:895-908`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_arith_simp_exp"
  (words_as_type_indexed_bitvec)]
theorem everyInstOkArithSimpExp {width : Nat} [NeZero width] :
    ∀ (exp : CrepExpHOL width),
      crepEveryExpHOL (fun x => ∀ op es, x = .crepOp op es → es.length = 2) exp →
      crepEveryExpHOL (fun x => ∀ op es, x = .crepOp op es → es.length = 2)
        (crepSimpExpHOL exp) := by
  intro exp
  fun_induction crepSimpExpHOL exp
  case case1 es1 exs first second hx _ _ h2 h1 ih =>
    intro he
    have hmap : es1.map crepSimpExpHOL = [first, second] := by simpa [exs] using hx
    unfold crepEveryExpHOL at he
    have hes := (crepEveryExpListHOL_iff _ _).mp he.2
    obtain ⟨hf, hs⟩ := crepEveryExpHOL_simp_pair es1 first second hmap ih hes
    simp only [hmap, h1, h2]
    simp [crepEveryExpHOL]
  case case2 es1 exs first second hx _ h2 h1 ih =>
    intro he
    have hmap : es1.map crepSimpExpHOL = [first, second] := by simpa [exs] using hx
    unfold crepEveryExpHOL at he
    have hes := (crepEveryExpListHOL_iff _ _).mp he.2
    obtain ⟨hf, hs⟩ := crepEveryExpHOL_simp_pair es1 first second hmap ih hes
    simp only [hmap, h1, h2]
    exact crepEveryExpHOL_mulConst _ _ hs
  case case3 es1 exs first second hx _ h2 h1 ih =>
    intro he
    have hmap : es1.map crepSimpExpHOL = [first, second] := by simpa [exs] using hx
    unfold crepEveryExpHOL at he
    have hes := (crepEveryExpListHOL_iff _ _).mp he.2
    obtain ⟨hf, hs⟩ := crepEveryExpHOL_simp_pair es1 first second hmap ih hes
    simp only [hmap, h1, h2]
    exact crepEveryExpHOL_mulConst _ _ hf
  case case4 es1 exs first second hx h2 h1 ih =>
    intro he
    have hmap : es1.map crepSimpExpHOL = [first, second] := by simpa [exs] using hx
    unfold crepEveryExpHOL at he
    have hes := (crepEveryExpListHOL_iff _ _).mp he.2
    obtain ⟨hf, hs⟩ := crepEveryExpHOL_simp_pair es1 first second hmap ih hes
    simp only [hmap, h1, h2]
    simp only [crepEveryExpHOL, crepEveryExpListHOL]
    exact ⟨(by intro op es h; cases h; rfl), hf, hs, trivial⟩
  case case5 op es1 exs hno ih =>
    intro he
    unfold crepEveryExpHOL at he
    have hes := (crepEveryExpListHOL_iff _ _).mp he.2
    have hlen : es1.length = 2 := he.1 op es1 rfl
    have hall : ∀ x ∈ es1.map crepSimpExpHOL,
        crepEveryExpHOL (fun x => ∀ op es, x = .crepOp op es → es.length = 2) x := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact ih y hy (hes y hy)
    dsimp only
    split
    · rename_i first second hm
      exact absurd (by simpa [exs] using hm) (hno first second rfl)
    · unfold crepEveryExpHOL
      exact ⟨(fun op' es h => by cases h; simp [hlen]),
        (crepEveryExpListHOL_iff _ _).mpr hall⟩
  case case6 | case7 | case8 =>
    rename_i ih
    intro he
    unfold crepEveryExpHOL at he ⊢
    exact ⟨(fun op es h => by cases h), ih he.2⟩
  case case9 op es1 ih =>
    intro he
    unfold crepEveryExpHOL at he ⊢
    have hes := (crepEveryExpListHOL_iff _ _).mp he.2
    refine ⟨(fun op es h => by cases h), (crepEveryExpListHOL_iff _ _).mpr ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact ih y hy (hes y hy)
  case case10 | case11 =>
    rename_i ih2 ih1
    intro he
    unfold crepEveryExpHOL at he ⊢
    exact ⟨(fun op es h => by cases h), ih2 he.2.1, ih1 he.2.2⟩
  case case12 => exact id

/-- Full original every_inst_ok_arith_simp_prog (`pan_to_wordProofScript.sml:910-925`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_arith_simp_prog"
  (words_as_type_indexed_bitvec)]
theorem everyInstOkArithSimpProg {width : Nat} [NeZero width] :
    ∀ (prog : CrepProgHOL width),
      (∀ e ∈ crepExpsOfHOL prog,
        crepEveryExpHOL (fun x => ∀ op es, x = .crepOp op es → es.length = 2) e) →
      ∀ e ∈ crepExpsOfHOL (crepSimpProgHOL prog),
        crepEveryExpHOL (fun x => ∀ op es, x = .crepOp op es → es.length = 2) e := by
  intro prog
  induction hs : sizeOf prog using Nat.strongRecOn generalizing prog with
  | _ k ih =>
  intro h e he
  have hx := fun (x : CrepExpHOL width) hx => everyInstOkArithSimpExp x (h x hx)
  have sub : ∀ (q : CrepProgHOL width), sizeOf q < k →
      (∀ x ∈ crepExpsOfHOL q, crepEveryExpHOL
        (fun x => ∀ op es, x = .crepOp op es → es.length = 2) x) →
      ∀ x ∈ crepExpsOfHOL (crepSimpProgHOL q), crepEveryExpHOL
        (fun x => ∀ op es, x = .crepOp op es → es.length = 2) x :=
    fun q hq hqe => ih (sizeOf q) hq q rfl hqe
  cases prog
  all_goals unfold crepSimpProgHOL at he
  case skip | primitive | «break» | «continue» | extCall | raise | tick =>
    unfold crepExpsOfHOL at he; simp at he
  case assign | storeGlob | shMem =>
    rw [crepExpsOfHOL] at he; simp only [List.mem_singleton] at he; subst he
    exact hx _ (by rw [crepExpsOfHOL]; simp)
  case store | store32 | storeByte =>
    rw [crepExpsOfHOL] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> exact hx _ (by rw [crepExpsOfHOL]; simp)
  case «return» vs =>
    rw [crepExpsOfHOL] at he
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp he
    exact hx y (by rw [crepExpsOfHOL]; exact hy)
  case dec n v b =>
    rw [crepExpsOfHOL] at he
    rcases List.mem_cons.mp he with rfl | hb
    · exact hx v (by rw [crepExpsOfHOL]; simp)
    · exact sub b (by rw [← hs]; simp; omega)
        (fun x hx' => h x (by rw [crepExpsOfHOL]; simp [hx'])) e hb
  case seq f g =>
    rw [crepExpsOfHOL] at he
    rcases List.mem_append.mp he with hf | hg
    · exact sub f (by rw [← hs]; simp; omega)
        (fun x hx' => h x (by rw [crepExpsOfHOL]; simp [hx'])) e hf
    · exact sub g (by rw [← hs]; simp; omega)
        (fun x hx' => h x (by rw [crepExpsOfHOL]; simp [hx'])) e hg
  case ite c t f =>
    rw [crepExpsOfHOL] at he
    rcases List.mem_cons.mp he with rfl | he
    · exact hx c (by rw [crepExpsOfHOL]; simp)
    rcases List.mem_append.mp he with ht | hf
    · exact sub t (by rw [← hs]; simp; omega)
        (fun x hx' => h x (by rw [crepExpsOfHOL]; simp [hx'])) e ht
    · exact sub f (by rw [← hs]; simp; omega)
        (fun x hx' => h x (by rw [crepExpsOfHOL]; simp [hx'])) e hf
  case «while» c b =>
    rw [crepExpsOfHOL] at he
    rcases List.mem_cons.mp he with rfl | hb
    · exact hx c (by rw [crepExpsOfHOL]; simp)
    · exact sub b (by rw [← hs]; simp; omega)
        (fun x hx' => h x (by rw [crepExpsOfHOL]; simp [hx'])) e hb
  case call ri name args =>
    rcases ri with _ | ⟨rv, _ | ⟨exn, hb⟩⟩
    all_goals dsimp only at he
    all_goals rw [crepExpsOfHOL] at he
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp he
      exact hx y (by rw [crepExpsOfHOL]; exact hy)
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp he
      exact hx y (by rw [crepExpsOfHOL]; exact hy)
    · rcases List.mem_append.mp he with ha | hh
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
        exact hx y (by rw [crepExpsOfHOL]; simp [hy])
      · exact sub hb (by rw [← hs]; simp; omega)
          (fun x hx' => h x (by rw [crepExpsOfHOL]; simp [hx'])) e hh

/-- Membership in a `zipWith` (Flapjack infrastructure). -/
theorem mem_zipWith_exists {α β γ : Type} (g : α → β → γ) :
    ∀ (l1 : List α) (l2 : List β) (x : γ), x ∈ List.zipWith g l1 l2 →
      ∃ a ∈ l1, ∃ b ∈ l2, x = g a b := by
  intro l1
  induction l1 with
  | nil => intro l2 x h; simp at h
  | cons a l1 ih =>
    intro l2 x h
    cases l2 with
    | nil => simp at h
    | cons b l2 =>
      simp only [List.zipWith_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨a, by simp, b, by simp, rfl⟩
      · obtain ⟨a', ha', b', hb', rfl⟩ := ih l2 x h
        exact ⟨a', by simp [ha'], b', by simp [hb'], rfl⟩

/-- Full original every_inst_ok_less_crep_to_loop_compile_prog
(`pan_to_wordProofScript.sml:1209-1223`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem everyInstOkLessCrepToLoopCompileProg {width : Nat} [NeZero width]
    {cWidth : Nat} [NeZero cWidth] (c : AsmConfigExact cWidth)
    (crepCode : List (MlString × List Nat × CrepProgHOL width)) :
    (∀ f ∈ crepCode, ∀ e ∈ crepExpsOfHOL f.2.2,
      crepEveryExpHOL (fun x => ∀ op es, x = .crepOp op es → es.length = 2) e) →
    ∀ f ∈ compileProgHOLExact c.isa crepCode, everyProgHOL (loopInstOk c) f.2.2 := by
  intro h f hf
  unfold compileProgHOLExact at hf
  obtain ⟨n, -, entry, hentry, rfl⟩ := mem_zipWith_exists _ _ _ _ hf
  apply everyInstOkLessOptimise
  unfold compFuncHOLExact
  exact everyInstOkLessCrepToLoopCompile c _ _ _
    ⟨rfl, everyInstOkArithSimpProg entry.2.2 (h entry hentry)⟩

end Flapjack.PanToWord
