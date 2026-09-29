import Flapjack.Pancake.LoopCall
import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate
import Flapjack.Pancake.Semantics.LoopProps.EvalExact
import Flapjack.Pancake.Semantics.LoopProps.NestedSeqExact
import Flapjack.Pancake.Semantics.LoopProps.NestedSeqSyntaxExact
import Flapjack.Misc.SptreeLookup
import Flapjack.Pancake.LoopCall.IsLoad

/-!
# loop_call `compile_correct`

Port of `cakeml/pancake/proofs/loop_callProofScript.sml`: `labels_in_def` (11)
and `compile_correct` (16) over the exact `LoopSemStateFiniteExact.evaluate`
(`evaluate_def`) and the tagged `loopCallCompHOL` (`loop_call$comp_def`)
(bead `flapjack-pxn.18.5.7`).  HOL proves `compile_correct` by
`recInduct loopSemTheory.evaluate_ind` with one `Resume` block per constructor.
The per-constructor lemmas below are Flapjack-only auxiliary lemmas of that
proof, not ports of HOL declarations and not case pieces in the `AGENTS.md`
sense: their sub-program hypotheses are the ones the Lean lexicographic
`(clock, program size)` assembly supplies, not `evaluate_ind`'s.  They carry no
`@[hol]` tag; the tag is on the assembled `loopCall_compile_correct`, whose
statement is HOL's.
-/

namespace Flapjack

open LoopSemStateFiniteExact

namespace LoopCallCompileCorrectWitnesses

/-- Same-module re-export of the canonical `loopSem$state` witness for the
    `fmap_as_finite_support := [globals]` qualifier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopSemStateFiniteExact.LoopEvaluateFiniteSupport.holFmapAsFiniteSupportWitness

end LoopCallCompileCorrectWitnesses

/-- Exact HOL `labels_in_def` (`loop_callProofScript.sml:11-14`):
    `labels_in l locals = !n x. lookup n l = SOME x ==> lookup n locals = SOME (Loc x 0)`. -/
@[hol "cakeml/pancake/proofs/loop_callProofScript.sml" "labels_in_def"
  (words_as_type_indexed_bitvec)]
def labelsInHOL {width : Nat} [NeZero width] (l : Spt Nat) (locals : Spt (WordLocW width)) : Prop :=
  ∀ n x, sptLookup n l = some x → sptLookup n locals = some (.loc x 0)

private theorem labelsIn_ln {width : Nat} [NeZero width] (locals : Spt (WordLocW width)) :
    labelsInHOL .ln locals := fun n x h => by simp [sptLookup] at h

/-- Flapjack-only abbreviation (no HOL declaration) of the `compile_correct`
    statement at a fixed program `v` and state `v1`, used for the auxiliary lemmas'
    induction hypotheses. -/
def loopCallCompileCorrectAt {width : Nat} [NeZero width] {F : Type}
    (v : HolLoopProg width) (v1 : LoopSemStateFiniteExact width F) : Prop :=
  ∀ (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
    (l : Spt Nat) (p : HolLoopProg width) (nl : Spt Nat),
    evaluate v v1 = (res, s1) ∧ res ≠ some .error ∧ loopCallCompHOL l v = (p, nl) ∧
      labelsInHOL l v1.locals →
    evaluate p v1 = (res, s1) ∧ labelsInHOL nl s1.locals

/-- Flapjack-only auxiliary lemma (no HOL declaration) for a leaf case of the proof of the
    tagged `loopCall_compile_correct` (HOL `compile_correct`, `loop_callProofScript.sml:16-20`). -/
theorem loopCall_compile_correct_skip {width : Nat} [NeZero width] {F : Type} :
    ∀ (v1 : LoopSemStateFiniteExact width F), loopCallCompileCorrectAt (.skip : HolLoopProg width) v1 := by
  intro v1 res s1 l p nl ⟨he, hne, hc, hl⟩
  simp only [loopCallCompHOL, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [evaluate, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨by simp [evaluate], hl⟩

/-- Flapjack-only auxiliary lemma (no HOL declaration) for a leaf case of the proof of the
    tagged `loopCall_compile_correct` (HOL `compile_correct`, `loop_callProofScript.sml:16-20`). -/
theorem loopCall_compile_correct_fail {width : Nat} [NeZero width] {F : Type} :
    ∀ (v1 : LoopSemStateFiniteExact width F), loopCallCompileCorrectAt (.fail : HolLoopProg width) v1 := by
  intro v1 res s1 l p nl ⟨he, hne, hc, hl⟩
  simp only [evaluate, Prod.mk.injEq] at he
  exact absurd he.1.symm hne

/-- Flapjack-only auxiliary lemma (no HOL declaration) for a leaf case of the proof of the
    tagged `loopCall_compile_correct` (HOL `compile_correct`, `loop_callProofScript.sml:16-20`). -/
theorem loopCall_compile_correct_tick {width : Nat} [NeZero width] {F : Type} :
    ∀ (v1 : LoopSemStateFiniteExact width F), loopCallCompileCorrectAt (.tick : HolLoopProg width) v1 := by
  intro v1 res s1 l p nl ⟨he, hne, hc, hl⟩
  simp only [loopCallCompHOL, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  exact ⟨he, labelsIn_ln _⟩

/-- Flapjack-only auxiliary lemma (no HOL declaration) for a leaf case of the proof of the
    tagged `loopCall_compile_correct` (HOL `compile_correct`, `loop_callProofScript.sml:16-20`). -/
theorem loopCall_compile_correct_break {width : Nat} [NeZero width] {F : Type} :
    ∀ (k : Nat) (v1 : LoopSemStateFiniteExact width F), loopCallCompileCorrectAt (.break k : HolLoopProg width) v1 := by
  intro k v1 res s1 l p nl ⟨he, hne, hc, hl⟩
  simp only [loopCallCompHOL, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [evaluate, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨by simp [evaluate], hl⟩

/-- Flapjack-only auxiliary lemma (no HOL declaration) for a leaf case of the proof of the
    tagged `loopCall_compile_correct` (HOL `compile_correct`, `loop_callProofScript.sml:16-20`). -/
theorem loopCall_compile_correct_continue {width : Nat} [NeZero width] {F : Type} :
    ∀ (k : Nat) (v1 : LoopSemStateFiniteExact width F), loopCallCompileCorrectAt (.continue k : HolLoopProg width) v1 := by
  intro k v1 res s1 l p nl ⟨he, hne, hc, hl⟩
  simp only [loopCallCompHOL, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [evaluate, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨by simp [evaluate], hl⟩

/-- Flapjack-only auxiliary lemma (no HOL declaration) for a leaf case of the proof of the
    tagged `loopCall_compile_correct` (HOL `compile_correct`, `loop_callProofScript.sml:16-20`). -/
theorem loopCall_compile_correct_return {width : Nat} [NeZero width] {F : Type} :
    ∀ (ns : List Nat) (v1 : LoopSemStateFiniteExact width F), loopCallCompileCorrectAt (.return ns : HolLoopProg width) v1 := by
  intro ns v1 res s1 l p nl ⟨he, hne, hc, hl⟩
  simp only [loopCallCompHOL, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  exact ⟨he, labelsIn_ln _⟩

/-- Flapjack-only auxiliary lemma (no HOL declaration) for a leaf case of the proof of the
    tagged `loopCall_compile_correct` (HOL `compile_correct`, `loop_callProofScript.sml:16-20`). -/
theorem loopCall_compile_correct_raise {width : Nat} [NeZero width] {F : Type} :
    ∀ (x : Nat) (v1 : LoopSemStateFiniteExact width F), loopCallCompileCorrectAt (.raise x : HolLoopProg width) v1 := by
  intro x v1 res s1 l p nl ⟨he, hne, hc, hl⟩
  simp only [loopCallCompHOL, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  exact ⟨he, labelsIn_ln _⟩

/-- Flapjack-only auxiliary lemma (no HOL declaration) for a leaf case of the proof of the
    tagged `loopCall_compile_correct` (HOL `compile_correct`, `loop_callProofScript.sml:16-20`). -/
theorem loopCall_compile_correct_setGlobal {width : Nat} [NeZero width] {F : Type} :
    ∀ (g : BitVec 5) (x : HolLoopExp width) (v1 : LoopSemStateFiniteExact width F), loopCallCompileCorrectAt (.setGlobal g x : HolLoopProg width) v1 := by
  intro g x v1 res s1 l p nl ⟨he, hne, hc, hl⟩
  simp only [loopCallCompHOL, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  refine ⟨he, ?_⟩
  cases hx : eval v1 x with
  | none => simp [evaluate, hx] at he; exact absurd he.1.symm hne
  | some w =>
    simp only [evaluate, hx, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact hl

/-- Flapjack-only auxiliary lemma (no HOL declaration) for the `Seq` case of the proof of the
    tagged `loopCall_compile_correct`, following `Resume compile_correct[Seq]` (`loop_callProofScript.sml:50-76`). -/
theorem loopCall_compile_correct_seq {width : Nat} [NeZero width] {F : Type} :
    ∀ (c1 c2 : HolLoopProg width) (v1 : LoopSemStateFiniteExact width F),
      loopCallCompileCorrectAt c1 v1 →
      (∀ s1', fixClock v1 (evaluate c1 v1) = (none, s1') → loopCallCompileCorrectAt c2 s1') →
      loopCallCompileCorrectAt (.seq c1 c2) v1 := by
  intro c1 c2 v1 ih1 ih2 res s1 l p nl ⟨he, hne, hc, hl⟩
  rcases h1c : loopCallCompHOL l c1 with ⟨np, nl1⟩
  rcases h2c : loopCallCompHOL nl1 c2 with ⟨nq, nl2⟩
  rw [loopCallCompHOL, h1c] at hc
  simp only [h2c, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  refine ⟨?_, labelsIn_ln _⟩
  rw [evaluate_seq] at he
  rw [evaluate_seq]
  rcases hr1 : evaluate c1 v1 with ⟨r, sm⟩
  rw [hr1] at he
  have hrne : r ≠ some .error := fun e => by
    subst e; simp at he; exact hne he.1.symm
  obtain ⟨hn1, hl1⟩ := ih1 r sm l np nl1 ⟨hr1, hrne, h1c, hl⟩
  rw [hn1]
  cases r with
  | none =>
    simp only at he ⊢
    have hfix : fixClock v1 (evaluate c1 v1) = (none, sm) := by rw [fix_clock_evaluate, hr1]
    exact (ih2 sm hfix res s1 nl1 nq nl2 ⟨he, hne, h2c, hl1⟩).1
  | some _ => exact he

/-- Flapjack-only auxiliary lemma (no HOL declaration) for the `Mark` case of the proof of the
    tagged `loopCall_compile_correct`, following `Resume compile_correct[Mark]` (`loop_callProofScript.sml:164-175`). -/
theorem loopCall_compile_correct_mark {width : Nat} [NeZero width] {F : Type} :
    ∀ (body : HolLoopProg width) (v1 : LoopSemStateFiniteExact width F),
      loopCallCompileCorrectAt body v1 → loopCallCompileCorrectAt (.mark body) v1 := by
  intro body v1 ih res s1 l p nl ⟨he, hne, hc, hl⟩
  rcases hbc : loopCallCompHOL l body with ⟨np, nl1⟩
  rw [loopCallCompHOL, hbc] at hc
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  rw [evaluate] at he
  obtain ⟨h1, h2⟩ := ih res s1 l np nl1 ⟨he, hne, hbc, hl⟩
  exact ⟨by rw [evaluate]; exact h1, h2⟩

/-- Flapjack-only auxiliary lemma (no HOL declaration) for the `If` case of the proof of the
    tagged `loopCall_compile_correct`, following `Resume compile_correct[If]` (`loop_callProofScript.sml:192-235`). -/
theorem loopCall_compile_correct_if {width : Nat} [NeZero width] {F : Type} :
    ∀ (cmp : Cmp) (r1 : Nat) (ri : RegImm (BitVec width)) (c1 c2 : HolLoopProg width)
      (live : NumSet) (v1 : LoopSemStateFiniteExact width F),
      (∀ x y, sptLookup r1 v1.locals = some (.word x) →
        LoopSemStateFiniteExact.getVarImm ri v1 = some (.word y) →
        loopCallCompileCorrectAt (if Compiler.Encoders.Asm.wordCmpHOL cmp x y then c1 else c2) v1) →
      loopCallCompileCorrectAt (.ite cmp r1 ri c1 c2 live) v1 := by
  intro cmp r1 ri c1 c2 live v1 ih res s1 l p nl ⟨he, hne, hc, hl⟩
  rcases h1c : loopCallCompHOL l c1 with ⟨np, n1⟩
  rcases h2c : loopCallCompHOL l c2 with ⟨nq, n2⟩
  rw [loopCallCompHOL, h1c] at hc
  simp only [h2c, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  refine ⟨?_, labelsIn_ln _⟩
  cases hx : sptLookup r1 v1.locals with
  | none => simp [evaluate, hx] at he; exact absurd he.1.symm hne
  | some a =>
  cases a with
  | loc _ _ => simp [evaluate, hx] at he; exact absurd he.1.symm hne
  | word x =>
  cases hy : LoopSemStateFiniteExact.getVarImm ri v1 with
  | none => simp [evaluate, hx, hy] at he; exact absurd he.1.symm hne
  | some b =>
  cases b with
  | loc _ _ => simp [evaluate, hx, hy] at he; exact absurd he.1.symm hne
  | word y =>
  have ih' := ih x y hx hy
  simp only [evaluate, hx, hy] at he ⊢
  by_cases hb : Compiler.Encoders.Asm.wordCmpHOL cmp x y = true
  · simp only [hb, if_true] at he ih' ⊢
    rcases hr : evaluate c1 v1 with ⟨rr, sr⟩
    rw [hr] at he
    have hrne : rr ≠ some .error := fun e => by subst e; simp [cutRes] at he; exact hne he.1.symm
    rw [(ih' rr sr l np n1 ⟨hr, hrne, h1c, hl⟩).1]; exact he
  · simp only [hb, if_false, Bool.false_eq_true] at he ih' ⊢
    rcases hr : evaluate c2 v1 with ⟨rr, sr⟩
    rw [hr] at he
    have hrne : rr ≠ some .error := fun e => by subst e; simp [cutRes] at he; exact hne he.1.symm
    rw [(ih' rr sr l nq n2 ⟨hr, hrne, h2c, hl⟩).1]; exact he

/-- Flapjack-only auxiliary lemma (no HOL declaration) for the `Loop` case of the proof of the
    tagged `loopCall_compile_correct`, following `Resume compile_correct[Loop]` (`loop_callProofScript.sml:371-401`). -/
theorem loopCall_compile_correct_loop {width : Nat} [NeZero width] {F : Type} :
    ∀ (liveIn : NumSet) (body : HolLoopProg width) (liveOut : NumSet)
      (v1 : LoopSemStateFiniteExact width F),
      (∀ st : LoopSemStateFiniteExact width F, st.clock < v1.clock →
        loopCallCompileCorrectAt body st ∧ loopCallCompileCorrectAt (.loop liveIn body liveOut) st) →
      loopCallCompileCorrectAt (.loop liveIn body liveOut) v1 := by
  intro liveIn body liveOut v1 ih res s1 l p nl ⟨he, hne, hc, hl⟩
  rcases hbc : loopCallCompHOL .ln body with ⟨np, nb⟩
  rw [loopCallCompHOL, hbc] at hc
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  refine ⟨?_, labelsIn_ln _⟩
  rw [evaluate] at he
  rw [evaluate]
  rcases hcr : cutRes liveIn (none, v1) with ⟨r0, s1c⟩
  rw [hcr] at he
  cases r0 with
  | some _ => exact he
  | none =>
    simp only at he ⊢
    have hs1 := cutRes_none_clock hcr
    rw [fix_clock_evaluate] at he
    rw [fix_clock_evaluate]
    rcases hb : evaluate body s1c with ⟨rb, s2⟩
    rw [hb] at he
    have hrb : rb ≠ some .error := fun e => by
      subst e; simp [LoopSemStateFiniteExact.exitLoop] at he; exact hne he.1.symm
    rw [((ih s1c hs1).1 rb s2 .ln np nb ⟨hb, hrb, hbc, labelsIn_ln _⟩).1]
    have hs2 : s2.clock < v1.clock := by
      have := evaluate_clock_snd body s1c
      rw [hb] at this; simp only at this; omega
    have hL : evaluate (.loop liveIn body liveOut) s2 = (res, s1) →
        evaluate (.loop liveIn np liveOut) s2 = (res, s1) := fun h =>
      ((ih s2 hs2).2 res s1 .ln (.loop liveIn np liveOut) .ln ⟨h, hne, by
        rw [loopCallCompHOL, hbc], labelsIn_ln _⟩).1
    rcases rb with _ | r
    · exact hL he
    · cases r with
      | «continue» n => cases n with
        | zero => exact hL he
        | succ n => exact he
      | «break» n => cases n <;> exact he
      | _ => exact he

/-! ## Statement cases (the compiled program is the source program) -/

private theorem labelsIn_mono {width : Nat} [NeZero width] {l L : Spt Nat}
    {loc loc' : Spt (WordLocW width)} (h : labelsInHOL l loc)
    (hk : ∀ n x, sptLookup n L = some x → sptLookup n l = some x ∧ sptLookup n loc' = sptLookup n loc) :
    labelsInHOL L loc' := fun n x hn => by
  obtain ⟨h1, h2⟩ := hk n x hn
  rw [h2]; exact h n x h1

/-- The `set_var k` / `delete k` (or unchanged when `k` is not a label) step
    shared by HOL's `Assign`/`Load32`/`LoadByte`/`Arith` resumes. -/
private theorem labelsIn_set_del {width : Nat} [NeZero width] (l : Spt Nat)
    (loc : Spt (WordLocW width)) (k : Nat) (w : WordLocW width) (h : labelsInHOL l loc) :
    labelsInHOL (match sptLookup k l with | none => l | some _ => sptDelete k l) (sptInsert k w loc) := by
  cases hk : sptLookup k l with
  | none =>
    refine labelsIn_mono h fun n x hn => ⟨hn, ?_⟩
    have : n ≠ k := fun e => by subst e; rw [hk] at hn; cases hn
    rw [sptLookup_sptInsert, if_neg this]
  | some _ =>
    refine labelsIn_mono h fun n x hn => ?_
    rw [sptLookup_sptDelete] at hn
    by_cases hnk : n = k
    · rw [if_pos hnk] at hn; cases hn
    · rw [if_neg hnk] at hn
      exact ⟨hn, by rw [sptLookup_sptInsert, if_neg hnk]⟩

/-- Flapjack-only auxiliary lemma (no HOL declaration) for the `LocValue` case of the proof of the
    tagged `loopCall_compile_correct`, following `Resume compile_correct[LocValue]` (`loop_callProofScript.sml:79-92`). -/
theorem loopCall_compile_correct_locValue {width : Nat} [NeZero width] {F : Type} :
    ∀ (r m : Nat) (v1 : LoopSemStateFiniteExact width F),
      loopCallCompileCorrectAt (.locValue r m : HolLoopProg width) v1 := by
  intro r m v1 res s1 l p nl ⟨he, hne, hc, hl⟩
  simp only [loopCallCompHOL, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  refine ⟨he, ?_⟩
  by_cases hcd : (sptLookup m v1.code).isSome = true
  · simp only [evaluate, hcd, if_true, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    intro n x hn
    simp only [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert] at hn ⊢
    by_cases hnr : n = r
    · rw [if_pos hnr] at hn ⊢; cases hn; rfl
    · rw [if_neg hnr] at hn ⊢; exact hl n x hn
  · simp [evaluate, hcd] at he; exact absurd he.1.symm hne

/-- Flapjack-only auxiliary lemma (no HOL declaration) for the `Assign` case of the proof of the
    tagged `loopCall_compile_correct`, following `Resume compile_correct[Assign]` (`loop_callProofScript.sml:95-129`). -/
theorem loopCall_compile_correct_assign {width : Nat} [NeZero width] {F : Type} :
    ∀ (n : Nat) (e : HolLoopExp width) (v1 : LoopSemStateFiniteExact width F),
      loopCallCompileCorrectAt (.assign n e) v1 := by
  intro n e v1 res s1 l p nl ⟨he, hne, hc, hl⟩
  cases hx : eval v1 e with
  | none => simp [evaluate, hx] at he; exact absurd he.1.symm hne
  | some w =>
  simp only [evaluate, hx, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  cases e with
  | var m =>
    simp only [loopCallCompHOL, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    refine ⟨by simp [evaluate, hx], ?_⟩
    simp only [LoopSemStateFiniteExact.setVar]
    cases hm : sptLookup m l with
    | none =>
      cases hn : sptLookup n l with
      | none => simpa [hn] using labelsIn_set_del l v1.locals n w hl
      | some _ => simpa [hn] using labelsIn_set_del l v1.locals n w hl
    | some locv =>
      have hw : w = .loc locv 0 := by
        have := hl m locv hm
        simp only [eval] at hx
        rw [hx] at this; cases this; rfl
      subst hw
      cases hn : sptLookup n l <;> simp only <;>
      · intro k x hk
        rw [sptLookup_sptInsert] at hk ⊢
        by_cases hkn : k = n
        · rw [if_pos hkn] at hk ⊢; cases hk; rfl
        · rw [if_neg hkn] at hk ⊢; exact hl k x hk
  | _ =>
    simp only [loopCallCompHOL, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨by simp [evaluate, hx], labelsIn_set_del l v1.locals n w hl⟩

/-- Flapjack-only auxiliary lemma (no HOL declaration) for the `Load32` case of the proof of the
    tagged `loopCall_compile_correct`, following `Resume compile_correct[Load32]` (`loop_callProofScript.sml:131-145`). -/
theorem loopCall_compile_correct_load32 {width : Nat} [NeZero width] {F : Type} :
    ∀ (a dst : Nat) (v1 : LoopSemStateFiniteExact width F),
      loopCallCompileCorrectAt (.load32 a dst : HolLoopProg width) v1 := by
  intro a dst v1 res s1 l p nl ⟨he, hne, hc, hl⟩
  simp only [loopCallCompHOL, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  refine ⟨he, ?_⟩
  cases ha : sptLookup a v1.locals with
  | none => simp [evaluate, ha] at he; exact absurd he.1.symm hne
  | some av =>
  cases av with
  | loc _ _ => simp [evaluate, ha] at he; exact absurd he.1.symm hne
  | word w =>
  cases hm : memLoad32Exact v1.memory v1.mdomain v1.be w with
  | none => simp [evaluate, ha, hm] at he; exact absurd he.1.symm hne
  | some b =>
  simp only [evaluate, ha, hm, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact labelsIn_set_del l v1.locals dst _ hl

/-- Flapjack-only auxiliary lemma (no HOL declaration) for the `LoadByte` case of the proof of the
    tagged `loopCall_compile_correct`, following `Resume compile_correct[LoadByte]` (`loop_callProofScript.sml:147-161`). -/
theorem loopCall_compile_correct_loadByte {width : Nat} [NeZero width] {F : Type} :
    ∀ (a dst : Nat) (v1 : LoopSemStateFiniteExact width F),
      loopCallCompileCorrectAt (.loadByte a dst : HolLoopProg width) v1 := by
  intro a dst v1 res s1 l p nl ⟨he, hne, hc, hl⟩
  simp only [loopCallCompHOL, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  refine ⟨he, ?_⟩
  cases ha : sptLookup a v1.locals with
  | none => simp [evaluate, ha] at he; exact absurd he.1.symm hne
  | some av =>
  cases av with
  | loc _ _ => simp [evaluate, ha] at he; exact absurd he.1.symm hne
  | word w =>
  cases hm : memLoadByteAuxExact v1.memory v1.mdomain v1.be w with
  | none => simp [evaluate, ha, hm] at he; exact absurd he.1.symm hne
  | some b =>
  simp only [evaluate, ha, hm, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact labelsIn_set_del l v1.locals dst _ hl

/-- Flapjack-only auxiliary lemma (no HOL declaration) for the `Store` case of the proof of the
    tagged `loopCall_compile_correct`, following `Resume compile_correct[Store]` (`loop_callProofScript.sml:261-271`). -/
theorem loopCall_compile_correct_store {width : Nat} [NeZero width] {F : Type} :
    ∀ (e : HolLoopExp width) (n : Nat) (v1 : LoopSemStateFiniteExact width F),
      loopCallCompileCorrectAt (.store e n) v1 := by
  intro e n v1 res s1 l p nl ⟨he, hne, hc, hl⟩
  simp only [loopCallCompHOL, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  refine ⟨he, ?_⟩
  cases hx : eval v1 e with
  | none => simp [evaluate, hx] at he; exact absurd he.1.symm hne
  | some a =>
  cases a with
  | loc _ _ => simp [evaluate, hx] at he; exact absurd he.1.symm hne
  | word adr =>
  cases hn : sptLookup n v1.locals with
  | none => simp [evaluate, hx, hn] at he; exact absurd he.1.symm hne
  | some w =>
  by_cases hd : v1.mdomain adr = true
  · simp only [evaluate, hx, hn, memStore, hd, if_true, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact hl
  · simp [evaluate, hx, hn, memStore, hd] at he; exact absurd he.1.symm hne

/-- Flapjack-only auxiliary lemma (no HOL declaration) for the `Store32` case of the proof of the
    tagged `loopCall_compile_correct`, following `Resume compile_correct[Store32]` (`loop_callProofScript.sml:237-247`). -/
theorem loopCall_compile_correct_store32 {width : Nat} [NeZero width] {F : Type} :
    ∀ (a w : Nat) (v1 : LoopSemStateFiniteExact width F),
      loopCallCompileCorrectAt (.store32 a w : HolLoopProg width) v1 := by
  intro a w v1 res s1 l p nl ⟨he, hne, hc, hl⟩
  simp only [loopCallCompHOL, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  refine ⟨he, ?_⟩
  cases ha : sptLookup a v1.locals with
  | none => simp [evaluate, ha] at he; exact absurd he.1.symm hne
  | some av =>
  cases hw : sptLookup w v1.locals with
  | none => cases av <;> simp [evaluate, ha, hw] at he <;> exact absurd he.1.symm hne
  | some wv =>
  cases av with
  | loc _ _ => simp [evaluate, ha, hw] at he; exact absurd he.1.symm hne
  | word x =>
  cases wv with
  | loc _ _ => simp [evaluate, ha, hw] at he; exact absurd he.1.symm hne
  | word y =>
  cases hm : memStore32Exact v1.memory v1.mdomain v1.be x (y.setWidth 32) with
  | none => simp [evaluate, ha, hw, hm] at he; exact absurd he.1.symm hne
  | some m =>
  simp only [evaluate, ha, hw, hm, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact hl

/-- Flapjack-only auxiliary lemma (no HOL declaration) for the `StoreByte` case of the proof of the
    tagged `loopCall_compile_correct`, following `Resume compile_correct[StoreByte]` (`loop_callProofScript.sml:249-259`). -/
theorem loopCall_compile_correct_storeByte {width : Nat} [NeZero width] {F : Type} :
    ∀ (a w : Nat) (v1 : LoopSemStateFiniteExact width F),
      loopCallCompileCorrectAt (.storeByte a w : HolLoopProg width) v1 := by
  intro a w v1 res s1 l p nl ⟨he, hne, hc, hl⟩
  simp only [loopCallCompHOL, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  refine ⟨he, ?_⟩
  cases ha : sptLookup a v1.locals with
  | none => simp [evaluate, ha] at he; exact absurd he.1.symm hne
  | some av =>
  cases hw : sptLookup w v1.locals with
  | none => cases av <;> simp [evaluate, ha, hw] at he <;> exact absurd he.1.symm hne
  | some wv =>
  cases av with
  | loc _ _ => simp [evaluate, ha, hw] at he; exact absurd he.1.symm hne
  | word x =>
  cases wv with
  | loc _ _ => simp [evaluate, ha, hw] at he; exact absurd he.1.symm hne
  | word y =>
  cases hm : memStoreByteAuxExact v1.memory v1.mdomain v1.be x (y.setWidth 8) with
  | none => simp [evaluate, ha, hw, hm] at he; exact absurd he.1.symm hne
  | some m =>
  simp only [evaluate, ha, hw, hm, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact hl

/-- Flapjack-only auxiliary lemma (no HOL declaration) for the `FFI` case of the proof of the
    tagged `loopCall_compile_correct`, following `Resume compile_correct[FFI]` (`loop_callProofScript.sml:178-189`). -/
theorem loopCall_compile_correct_ffi {width : Nat} [NeZero width] {F : Type} :
    ∀ (idx : Basis.Pure.MlString.MlString) (p1 n1 p2 n2 : Nat) (cs : NumSet)
      (v1 : LoopSemStateFiniteExact width F),
      loopCallCompileCorrectAt (.ffi idx p1 n1 p2 n2 cs : HolLoopProg width) v1 := by
  intro idx p1 n1 p2 n2 cs v1 res s1 l p nl ⟨he, _, hc, _⟩
  simp only [loopCallCompHOL, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  exact ⟨he, labelsIn_ln _⟩

/-- Flapjack-only auxiliary lemma (no HOL declaration) for the `ShMem` case of the proof of the
    tagged `loopCall_compile_correct`, following `Resume compile_correct[ShMem]` (`loop_callProofScript.sml:436-443`). -/
theorem loopCall_compile_correct_shMem {width : Nat} [NeZero width] {F : Type} :
    ∀ (op : WordMemOp) (r : Nat) (ad : HolLoopExp width) (v1 : LoopSemStateFiniteExact width F),
      loopCallCompileCorrectAt (.shMem op r ad) v1 := by
  intro op r ad v1 res s1 l p nl ⟨he, _, hc, _⟩
  simp only [loopCallCompHOL, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  exact ⟨he, labelsIn_ln _⟩

private theorem holAlookup_zip_not_mem {β : Type} :
    ∀ (xs : List Nat) (ys : List β) (k : Nat), k ∉ xs → holAlookup (xs.zip ys) k = none
  | [], _, _, _ => by simp [holAlookup]
  | _ :: _, [], _, _ => by simp [holAlookup]
  | x :: xs, y :: ys, k, h => by
      simp only [List.zip_cons_cons, holAlookup]
      rw [if_neg (fun (e : x = k) => h (e ▸ List.mem_cons_self))]
      exact holAlookup_zip_not_mem xs ys k (fun hk => h (List.mem_cons_of_mem _ hk))

/-- Flapjack-only auxiliary lemma (no HOL declaration) for the `Primitive` case of the proof of the
    tagged `loopCall_compile_correct`, following `Resume compile_correct[Primitive]` (`loop_callProofScript.sml:445-451`). -/
theorem loopCall_compile_correct_primitive {width : Nat} [NeZero width] {F : Type} :
    ∀ (lhss : List Nat) (pop : PrimOp) (rhss : List Nat) (v1 : LoopSemStateFiniteExact width F),
      loopCallCompileCorrectAt (.primitive lhss pop rhss : HolLoopProg width) v1 := by
  intro lhss pop rhss v1 res s1 l p nl ⟨he, hne, hc, hl⟩
  simp only [loopCallCompHOL, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  refine ⟨he, ?_⟩
  cases hg : LoopSemStateFiniteExact.getVars rhss v1 with
  | none => simp [evaluate, hg] at he; exact absurd he.1.symm hne
  | some ws =>
  cases hp : loopPrimop pop ws with
  | none => simp [evaluate, hg, hp] at he; exact absurd he.1.symm hne
  | some rws =>
  by_cases hlen : lhss.length = rws.length
  · simp only [evaluate, hg, hp, hlen, if_true, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine labelsIn_mono hl fun n x hn => ?_
    rw [sptLookup_sptListDelete] at hn
    by_cases hnl : n ∈ lhss
    · rw [if_pos hnl] at hn; cases hn
    · rw [if_neg hnl] at hn
      refine ⟨hn, ?_⟩
      simp only [LoopSemStateFiniteExact.setVars]
      rw [lookup_alist_insert_any, holAlookup_zip_not_mem lhss rws n hnl]
  · simp [evaluate, hg, hp, hlen] at he; exact absurd he.1.symm hne

/-- The LongMul/LongDiv two-destination deletion of `loop_call$comp`: every
    surviving label is a label of `l` distinct from both destinations. -/
private theorem comp_two_dests (l : Spt Nat) (d1 d2 : Nat) :
    ∀ n x, sptLookup n (match sptLookup d1 l, sptLookup d2 l with
        | none, none => l
        | some _, none => sptDelete d1 l
        | none, some _ => sptDelete d2 l
        | _, _ => sptDelete d1 (sptDelete d2 l)) = some x →
      sptLookup n l = some x ∧ n ≠ d1 ∧ n ≠ d2 := by
  intro n x hn
  have nd : ∀ {d : Nat}, sptLookup d l = none → sptLookup n l = some x → n ≠ d :=
    fun hd hnl e => by subst e; rw [hd] at hnl; cases hnl
  cases h1 : sptLookup d1 l with
  | none =>
    cases h2 : sptLookup d2 l with
    | none =>
      simp only [h1, h2] at hn
      exact ⟨hn, nd h1 hn, nd h2 hn⟩
    | some _ =>
      simp only [h1, h2] at hn
      rw [sptLookup_sptDelete] at hn
      by_cases e2 : n = d2
      · rw [if_pos e2] at hn; cases hn
      · rw [if_neg e2] at hn; exact ⟨hn, nd h1 hn, e2⟩
  | some _ =>
    cases h2 : sptLookup d2 l with
    | none =>
      simp only [h1, h2] at hn
      rw [sptLookup_sptDelete] at hn
      by_cases e1 : n = d1
      · rw [if_pos e1] at hn; cases hn
      · rw [if_neg e1] at hn; exact ⟨hn, e1, nd h2 hn⟩
    | some _ =>
      simp only [h1, h2] at hn
      rw [sptLookup_sptDelete, sptLookup_sptDelete] at hn
      by_cases e1 : n = d1
      · rw [if_pos e1] at hn; cases hn
      · rw [if_neg e1] at hn
        by_cases e2 : n = d2
        · rw [if_pos e2] at hn; cases hn
        · rw [if_neg e2] at hn; exact ⟨hn, e1, e2⟩

/-- Flapjack-only auxiliary lemma (no HOL declaration) for the `Arith` case of the proof of the
    tagged `loopCall_compile_correct`, following `Resume compile_correct[Arith]` (`loop_callProofScript.sml:403-410`). -/
theorem loopCall_compile_correct_arith {width : Nat} [NeZero width] {F : Type} :
    ∀ (a : LoopArith) (v1 : LoopSemStateFiniteExact width F),
      loopCallCompileCorrectAt (.arith a : HolLoopProg width) v1 := by
  intro a
  cases a with
  | div r1 r2 r3 =>
    intro v1 res s1 l p nl ⟨he, hne, hc, hl⟩
    cases hA : LoopSemStateFiniteExact.loopArith v1 (.div r1 r2 r3) with
    | none => simp [evaluate, hA] at he; exact absurd he.1.symm hne
    | some s' =>
    simp only [evaluate, hA, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [loopCallCompHOL, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    refine ⟨by simp [evaluate, hA], ?_⟩
    unfold LoopSemStateFiniteExact.loopArith at hA
    simp only at hA
    split at hA
    · split at hA
      · cases hA; exact labelsIn_set_del l v1.locals r1 _ hl
      · cases hA
    · cases hA
  | longMul r1 r2 r3 r4 =>
    intro v1 res s1 l p nl ⟨he, hne, hc, hl⟩
    cases hA : LoopSemStateFiniteExact.loopArith v1 (.longMul r1 r2 r3 r4) with
    | none => simp [evaluate, hA] at he; exact absurd he.1.symm hne
    | some s' =>
    simp only [evaluate, hA, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [loopCallCompHOL, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    refine ⟨by simp [evaluate, hA], ?_⟩
    unfold LoopSemStateFiniteExact.loopArith at hA
    simp only at hA
    split at hA
    · cases hA
      refine labelsIn_mono hl fun n x hn => ?_
      obtain ⟨h1, h2, h3⟩ := comp_two_dests l r1 r2 n x hn
      refine ⟨h1, ?_⟩
      simp only [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert, h2, h3, if_false]
    · cases hA
  | longDiv r1 r2 r3 r4 r5 =>
    intro v1 res s1 l p nl ⟨he, hne, hc, hl⟩
    cases hA : LoopSemStateFiniteExact.loopArith v1 (.longDiv r1 r2 r3 r4 r5) with
    | none => simp [evaluate, hA] at he; exact absurd he.1.symm hne
    | some s' =>
    simp only [evaluate, hA, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [loopCallCompHOL, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    refine ⟨by simp [evaluate, hA], ?_⟩
    unfold LoopSemStateFiniteExact.loopArith at hA
    simp only at hA
    split at hA
    · split at hA
      · cases hA
        refine labelsIn_mono hl fun n x hn => ?_
        obtain ⟨h1, h2, h3⟩ := comp_two_dests l r1 r2 n x hn
        refine ⟨h1, ?_⟩
        simp only [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert, h2, h3, if_false]
      · cases hA
    · cases hA

private theorem shMemOp_locals {width : Nat} [NeZero width] {F : Type}
    (op : WordMemOp) (v : Nat) (addr : BitVec width) (s : LoopSemStateFiniteExact width F) :
    (∃ e, (shMemOp op v addr s).1 = some (.finalFfi e)) ∨
      (shMemOp op v addr s).2.locals = s.locals ∨
      (Compiler.Encoders.Asm.asmIsLoad op = true ∧ ∃ w, (shMemOp op v addr s).2.locals = sptInsert v w s.locals) := by
  cases op <;> simp only [shMemOp, Compiler.Encoders.Asm.asmIsLoad] <;>
    (first | unfold shMemLoad | unfold shMemStore) <;>
    (repeat' split) <;>
    simp_all [LoopSemStateFiniteExact.setVar, LoopSemStateFiniteExact.callEnv] <;>
    exact Or.inr ⟨_, rfl⟩

private theorem evaluate_shMem_cases {width : Nat} [NeZero width] {F : Type}
    (op : WordMemOp) (v : Nat) (ad : HolLoopExp width) (s : LoopSemStateFiniteExact width F)
    (res : Option (LoopResultExact width)) (s' : LoopSemStateFiniteExact width F)
    (he : evaluate (.shMem op v ad) s = (res, s')) :
    s' = s ∨ ∃ addr, shMemOp op v addr s = (res, s') := by
  simp only [evaluate] at he
  split at he
  · rename_i addr _
    split at he
    · split at he
      · exact Or.inr ⟨addr, he⟩
      · simp only [Prod.mk.injEq] at he; exact Or.inl he.2.symm
    · split at he
      · exact Or.inr ⟨addr, he⟩
      · simp only [Prod.mk.injEq] at he; exact Or.inl he.2.symm
  · simp only [Prod.mk.injEq] at he; exact Or.inl he.2.symm

/-- Exact HOL `evaluate_ShMem_neq_locals` (`loop_callProofScript.sml:412-415`):
    `evaluate (ShMem op v ad, s) = (res, s') ∧ v ≠ n ∧ ¬ (∃x. res = SOME (FinalFFI x)) ∧
      lookup n s.locals = x ⇒ lookup n s'.locals = x`, its free variables
    quantified in order of occurrence. -/
@[hol "cakeml/pancake/proofs/loop_callProofScript.sml" "evaluate_ShMem_neq_locals"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem evaluate_ShMem_neq_locals {width : Nat} [NeZero width] {F : Type} :
    ∀ (op : WordMemOp) (v : Nat) (ad : HolLoopExp width) (s : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)) (s' : LoopSemStateFiniteExact width F) (n : Nat)
      (x : Option (WordLocW width)),
      evaluate (.shMem op v ad) s = (res, s') ∧ v ≠ n ∧ ¬ (∃ e, res = some (.finalFfi e)) ∧
        sptLookup n s.locals = x →
      sptLookup n s'.locals = x := by
  intro op v ad s res s' n x ⟨he, hvn, hnf, hx⟩
  rcases evaluate_shMem_cases op v ad s res s' he with rfl | ⟨addr, hop⟩
  · exact hx
  · rcases shMemOp_locals op v addr s with ⟨e, he'⟩ | hl | ⟨_, w, hl⟩
    · rw [hop] at he'; exact absurd ⟨e, he'⟩ hnf
    · rw [hop] at hl; simp only at hl; rw [hl, hx]
    · rw [hop] at hl; simp only at hl
      rw [hl, sptLookup_sptInsert, if_neg (fun e => hvn e.symm), hx]

/-- Exact HOL `evaluate_ShMem_not_load_locals` (`loop_callProofScript.sml:424-427`):
    `evaluate (ShMem op v ad, s) = (res, s') ∧ ¬is_load op ∧
      ¬ (∃x. res = SOME (FinalFFI x)) ⇒ s.locals = s'.locals`; HOL `loop_call$is_load`
    is the tagged `loopCallIsLoadHOL` (`is_load_def`). -/
@[hol "cakeml/pancake/proofs/loop_callProofScript.sml" "evaluate_ShMem_not_load_locals"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem evaluate_ShMem_not_load_locals {width : Nat} [NeZero width] {F : Type} :
    ∀ (op : WordMemOp) (v : Nat) (ad : HolLoopExp width) (s : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)) (s' : LoopSemStateFiniteExact width F),
      evaluate (.shMem op v ad) s = (res, s') ∧ ¬ loopCallIsLoadHOL op = true ∧
        ¬ (∃ e, res = some (.finalFfi e)) →
      s.locals = s'.locals := by
  intro op v ad s res s' ⟨he, hnl, hnf⟩
  rw [loopCallIsLoadHOL_eq_crepIsLoadMemOp, crepIsLoadMemOp_eq_asmIsLoad] at hnl
  rcases evaluate_shMem_cases op v ad s res s' he with rfl | ⟨addr, hop⟩
  · rfl
  · rcases shMemOp_locals op v addr s with ⟨e, he'⟩ | hl | ⟨hld, _, _⟩
    · rw [hop] at he'; exact absurd ⟨e, he'⟩ hnf
    · rw [hop] at hl; exact hl.symm
    · exact absurd hld hnl

/-! ## Call case -/

private theorem getVars_eq_mapM {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) :
    ∀ xs : List Nat, LoopSemStateFiniteExact.getVars xs s = xs.mapM (fun n => sptLookup n s.locals)
  | [] => rfl
  | x :: xs => by
      simp only [LoopSemStateFiniteExact.getVars, List.mapM_cons, getVars_eq_mapM s xs]
      cases sptLookup x s.locals <;> cases xs.mapM (fun n => sptLookup n s.locals) <;> rfl

private theorem mapM_dropLast {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → xs.dropLast.mapM f = some ys.dropLast
  | [], ys, h => by simp at h; subst h; rfl
  | [x], ys, h => by
      simp only [List.mapM_cons, List.mapM_nil] at h
      cases hx : f x <;> simp [hx] at h
      subst h; rfl
  | x :: y :: rest, ys, h => by
      rw [List.mapM_cons] at h
      cases hx : f x with
      | none => rw [hx] at h; simp at h
      | some w =>
        cases hr : (y :: rest).mapM f with
        | none => rw [hx, hr] at h; simp at h
        | some ws =>
          have hr' : (y :: rest).mapM f = some ws := hr
          rw [hx, hr] at h
          simp at h
          subst h
          rw [List.mapM_cons] at hr
          have ih := mapM_dropLast f (y :: rest) ws hr'
          have hne : ws ≠ [] := by
            intro e; subst e
            cases hy : f y <;> cases hrr : rest.mapM f <;> simp [hy, hrr] at hr
          obtain ⟨w', ws', rfl⟩ : ∃ w' ws', ws = w' :: ws' := by
            cases ws with | nil => exact absurd rfl hne | cons a b => exact ⟨a, b, rfl⟩
          rw [List.dropLast_cons_cons, List.dropLast_cons_cons, List.mapM_cons, ih]
          simp [hx]

private theorem mapM_getLast {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β) (hxs : xs ≠ []), xs.mapM f = some ys →
      f (xs.getLast hxs) = ys.getLast?
  | [], _, h, _ => absurd rfl h
  | [x], ys, _, h => by
      simp only [List.mapM_cons, List.mapM_nil] at h
      cases hx : f x <;> simp [hx] at h
      subst h; simpa using hx
  | x :: y :: rest, ys, _, h => by
      rw [List.mapM_cons] at h
      cases hx : f x with
      | none => rw [hx] at h; simp at h
      | some w =>
        cases hr : (y :: rest).mapM f with
        | none => rw [hx, hr] at h; simp at h
        | some ws =>
          have hr' : (y :: rest).mapM f = some ws := hr
          rw [hx, hr] at h
          simp at h
          subst h
          rw [List.mapM_cons] at hr
          have ih := mapM_getLast f (y :: rest) ws (by simp) hr'
          have hne : ws ≠ [] := by
            intro e; subst e
            cases hy : f y <;> cases hrr : rest.mapM f <;> simp [hy, hrr] at hr
          rw [List.getLast_cons (by simp), ih]
          obtain ⟨w', ws', rfl⟩ : ∃ w' ws', ws = w' :: ws' := by
            cases ws with | nil => exact absurd rfl hne | cons a b => exact ⟨a, b, rfl⟩
          simp [List.getLast?_cons_cons]

/-- Exact HOL `get_vars_front` (`loop_callProofScript.sml:273-275`):
    `!xs ys s. get_vars xs s = SOME ys /\ xs <> [] ==> get_vars (FRONT xs) s = SOME (FRONT ys)`.
    HOL `FRONT` on these non-empty lists is `List.dropLast`. -/
@[hol "cakeml/pancake/proofs/loop_callProofScript.sml" "get_vars_front"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem get_vars_front {width : Nat} [NeZero width] {F : Type} :
    ∀ (xs : List Nat) (ys : List (WordLocW width)) (s : LoopSemStateFiniteExact width F),
      LoopSemStateFiniteExact.getVars xs s = some ys ∧ xs ≠ [] →
      LoopSemStateFiniteExact.getVars xs.dropLast s = some ys.dropLast := by
  intro xs ys s ⟨h, _⟩
  rw [getVars_eq_mapM] at h ⊢
  exact mapM_dropLast _ xs ys h

/-- A successful `get_vars` on a non-empty name list returns a non-empty list. -/
theorem getVars_ne_nil {width : Nat} [NeZero width] {F : Type}
    {xs : List Nat} {ys : List (WordLocW width)} {s : LoopSemStateFiniteExact width F}
    (h : LoopSemStateFiniteExact.getVars xs s = some ys) (hxs : xs ≠ []) : ys ≠ [] := by
  intro e; subst e
  cases xs with
  | nil => exact hxs rfl
  | cons x rest =>
    simp only [LoopSemStateFiniteExact.getVars] at h
    cases hx : sptLookup x s.locals <;> cases hr : LoopSemStateFiniteExact.getVars rest s <;>
      simp [hx, hr] at h

/-- Exact HOL `get_vars_last` (`loop_callProofScript.sml:300-302`):
    `!xs ys s. get_vars xs s = SOME ys /\ xs <> [] ==> lookup (LAST xs) s.locals = SOME (LAST ys)`.
    HOL `LAST xs` and `LAST ys` are `List.getLast` at the premise's `xs ≠ []` and at the
    derived `ys ≠ []` (`getVars_ne_nil`). -/
@[hol "cakeml/pancake/proofs/loop_callProofScript.sml" "get_vars_last"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem get_vars_last {width : Nat} [NeZero width] {F : Type} :
    ∀ (xs : List Nat) (ys : List (WordLocW width)) (s : LoopSemStateFiniteExact width F)
      (h : LoopSemStateFiniteExact.getVars xs s = some ys ∧ xs ≠ []),
      sptLookup (xs.getLast h.2) s.locals = some (ys.getLast (getVars_ne_nil h.1 h.2)) := by
  intro xs ys s ⟨h, hxs⟩
  have h' := h
  rw [getVars_eq_mapM] at h'
  rw [mapM_getLast _ xs ys hxs h', List.getLast?_eq_some_getLast]

private theorem findCode_front {width : Nat} [NeZero width]
    (av : List (WordLocW width)) (n : Nat) (code : Spt (List Nat × HolLoopProg width))
    (hlast : av.getLast? = some (.loc n 0)) :
    LoopSemStateFiniteExact.findCode (some n) av.dropLast code =
      LoopSemStateFiniteExact.findCode none av code := by
  obtain ⟨a, rest, rfl⟩ : ∃ a rest, av = a :: rest := by
    cases av with | nil => simp at hlast | cons a b => exact ⟨a, b, rfl⟩
  have hgl : (a :: rest).getLast (by simp) = .loc n 0 := by
    rw [List.getLast?_eq_some_getLast (by simp)] at hlast; exact Option.some.inj hlast
  simp only [LoopSemStateFiniteExact.findCode, hgl]
  cases sptLookup n code with
  | none => rfl
  | some pb =>
    obtain ⟨params, body⟩ := pb
    simp only [List.length_dropLast, List.length_cons, Nat.add_sub_cancel, Nat.add_right_cancel_iff]

/-- Flapjack-only auxiliary lemma (no HOL declaration) for the `Call` case of the proof of the
    tagged `loopCall_compile_correct`, following `Resume compile_correct[Call]` (`loop_callProofScript.sml:326-368`).
    `comp` only rewrites `Call` targets, never the callee or handler programs, so the
    compiled call evaluates identically and no sub-program hypothesis is needed. -/
theorem loopCall_compile_correct_call {width : Nat} [NeZero width] {F : Type} :
    ∀ (ret : Option (List Nat × NumSet)) (dest : Option Nat) (args : List Nat)
      (handler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet))
      (v1 : LoopSemStateFiniteExact width F),
      loopCallCompileCorrectAt (.call ret dest args handler) v1 := by
  intro ret dest args handler v1 res s1 l p nl ⟨he, hne, hc, hl⟩
  cases dest with
  | some d =>
    simp only [loopCallCompHOL, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨he, labelsIn_ln _⟩
  | none =>
  cases hlast : args.getLast? with
  | none =>
    have : args = [] := List.getLast?_eq_none_iff.mp hlast
    subst this
    simp [evaluate, LoopSemStateFiniteExact.getVars, LoopSemStateFiniteExact.findCode] at he
    exact absurd he.1.symm hne
  | some last =>
  cases hn : sptLookup last l with
  | none =>
    simp only [loopCallCompHOL, hlast, hn, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨he, labelsIn_ln _⟩
  | some n =>
  simp only [loopCallCompHOL, hlast, hn, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  refine ⟨?_, labelsIn_ln _⟩
  have hargs : args ≠ [] := fun e => by subst e; simp at hlast
  cases hg : LoopSemStateFiniteExact.getVars args v1 with
  | none => simp [evaluate, hg] at he; exact absurd he.1.symm hne
  | some av =>
  have hg' := get_vars_front args av v1 ⟨hg, hargs⟩
  have hL := get_vars_last args av v1 ⟨hg, hargs⟩
  have hla : args.getLast hargs = last := by
    rw [List.getLast?_eq_some_getLast hargs] at hlast; exact Option.some.inj hlast
  rw [hla, hl last n hn] at hL
  have hL' : av.getLast? = some (.loc n 0) := by
    rw [List.getLast?_eq_some_getLast (getVars_ne_nil hg hargs)]; exact hL.symm
  have key := findCode_front av n v1.code hL'
  rw [evaluate] at he ⊢
  rw [hg] at he
  rw [hg']
  simp only at he ⊢
  rw [key]
  exact he

/-! ## Assembly -/

private theorem loopCall_compile_correct_at {width : Nat} [NeZero width] {F : Type} :
    ∀ (v : HolLoopProg width) (v1 : LoopSemStateFiniteExact width F),
      loopCallCompileCorrectAt v v1 := by
  have key : ∀ (x : Nat × Nat) (v : HolLoopProg width) (v1 : LoopSemStateFiniteExact width F),
      (v1.clock, sizeOf v) = x → loopCallCompileCorrectAt v v1 := by
    intro x
    induction x using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction with
    | h x ih0 =>
      intro v v1 hx
      have ih : ∀ (p' : HolLoopProg width) (t' : LoopSemStateFiniteExact width F),
          Prod.Lex (· < ·) (· < ·) (t'.clock, sizeOf p') (v1.clock, sizeOf v) →
          loopCallCompileCorrectAt p' t' :=
        fun p' t' hlt => ih0 _ (hx ▸ hlt) p' t' rfl
      clear ih0 hx
      have ihc : ∀ (p' : HolLoopProg width) (t' : LoopSemStateFiniteExact width F),
          t'.clock < v1.clock → loopCallCompileCorrectAt p' t' :=
        fun p' t' h => ih p' t' (Prod.Lex.left _ _ h)
      have ihs : ∀ (p' : HolLoopProg width), sizeOf p' < sizeOf v →
          loopCallCompileCorrectAt p' v1 :=
        fun p' h => ih p' v1 (Prod.Lex.right _ h)
      cases v with
      | skip => exact loopCall_compile_correct_skip v1
      | fail => exact loopCall_compile_correct_fail v1
      | tick => exact loopCall_compile_correct_tick v1
      | «continue» k => exact loopCall_compile_correct_continue k v1
      | «break» k => exact loopCall_compile_correct_break k v1
      | «return» ns => exact loopCall_compile_correct_return ns v1
      | raise x => exact loopCall_compile_correct_raise x v1
      | mark p => exact loopCall_compile_correct_mark p v1 (ihs p (by simp <;> omega))
      | seq c1 c2 =>
        refine loopCall_compile_correct_seq c1 c2 v1 (ihs c1 (by simp <;> omega)) fun s1' hs1' => ?_
        have hle : s1'.clock ≤ v1.clock := by
          have := evaluate_clock_snd c1 v1
          rw [fix_clock_evaluate] at hs1'
          rw [hs1'] at this; exact this
        rcases Nat.lt_or_eq_of_le hle with hlt | heq
        · exact ihc c2 s1' hlt
        · exact ih c2 s1' (by rw [heq]; exact Prod.Lex.right _ (by simp <;> omega))
      | loop liveIn body liveOut =>
        exact loopCall_compile_correct_loop liveIn body liveOut v1
          fun st hst => ⟨ihc body st hst, ihc _ st hst⟩
      | assign n x => exact loopCall_compile_correct_assign n x v1
      | setGlobal g x => exact loopCall_compile_correct_setGlobal g x v1
      | locValue r m => exact loopCall_compile_correct_locValue r m v1
      | store e n => exact loopCall_compile_correct_store e n v1
      | store32 a w => exact loopCall_compile_correct_store32 a w v1
      | storeByte a w => exact loopCall_compile_correct_storeByte a w v1
      | load32 a y => exact loopCall_compile_correct_load32 a y v1
      | loadByte a y => exact loopCall_compile_correct_loadByte a y v1
      | arith a => exact loopCall_compile_correct_arith a v1
      | primitive lhss pop rhss => exact loopCall_compile_correct_primitive lhss pop rhss v1
      | shMem op r ad => exact loopCall_compile_correct_shMem op r ad v1
      | ffi idx p1 n1 p2 n2 cs => exact loopCall_compile_correct_ffi idx p1 n1 p2 n2 cs v1
      | ite cmp r1 ri c1 c2 live =>
        refine loopCall_compile_correct_if cmp r1 ri c1 c2 live v1 fun x y _ _ => ?_
        by_cases hb : Compiler.Encoders.Asm.wordCmpHOL cmp x y = true
        · simp only [hb, if_true]; exact ihs c1 (by simp <;> omega)
        · simp only [hb, if_false, Bool.false_eq_true]; exact ihs c2 (by simp <;> omega)
      | call ret dest args handler => exact loopCall_compile_correct_call ret dest args handler v1
  exact fun v v1 => key _ v v1 rfl

/-- Exact HOL `compile_correct` (`loop_callProofScript.sml:16-20`), assembled from the
    auxiliary per-constructor lemmas above by the lexicographic `(clock, program size)` induction that
    mirrors `loopSemTheory.evaluate_ind`:
    `∀v v1 res s1 l p nl. evaluate (v,v1) = (res,s1) ∧ res ≠ SOME Error ∧
      comp l v = (p,nl) ∧ labels_in l v1.locals ⇒
      evaluate (p,v1) = (res,s1) ∧ labels_in nl s1.locals`. -/
@[hol "cakeml/pancake/proofs/loop_callProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopCall_compile_correct {width : Nat} [NeZero width] {F : Type} :
    ∀ (v : HolLoopProg width) (v1 : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
      (l : Spt Nat) (p : HolLoopProg width) (nl : Spt Nat),
      evaluate v v1 = (res, s1) ∧ res ≠ some .error ∧ loopCallCompHOL l v = (p, nl) ∧
        labelsInHOL l v1.locals →
      evaluate p v1 = (res, s1) ∧ labelsInHOL nl s1.locals :=
  fun v v1 => loopCall_compile_correct_at v v1

end Flapjack
