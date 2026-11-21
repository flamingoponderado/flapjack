module

public import Flapjack.Compiler.Backend.WordBignum.Proofs.Relations
public import Flapjack.Compiler.Backend.WordBignum.Proofs.MiniStateOps

@[expose] public section

/-! Flapjack-only support for the generated `*_corr_thm` ports of
`cakeml/compiler/backend/proofs/word_bignumProofScript.sml`. HOL derives each
such theorem by `derive_corr_thm`, composing the `Corr_*` rules symbolically
and closing the remaining state equalities by rewriting. The Lean proofs run
the deep program symbolically with the continuation-style `Eval` lemmas below
and close state equalities extensionally; loops use the generic
`SHORT_TAILREC` simulation `evalLoopBody_of_step`. These lemmas have no
separate HOL names. -/

namespace Flapjack.Compiler.Backend.WordBignum.CorrSupport

open Flapjack
open Flapjack.Misc.Multiword
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordBignum

variable {width : Nat} [NeZero width]

theorem ev_seq_assign {r : Option (Mini (BitVec width))} {s : MiniState width} {n : Nat}
    {x : WordLangExpHOL (BitVec width)} {p : Mini (BitVec width)}
    {t : Sum (MiniState width) (MiniState width)}
    (hp : evalExpPre s x) (h : Eval r (regWrite n (some (evalExp s x)) s) p t) :
    Eval r s (.seq (.assign n x) p) t :=
  Eval.seq r s _ t _ p (Eval.assign r s x n hp) h

theorem ev_seq_delete {r : Option (Mini (BitVec width))} {s : MiniState width} {vs : List Nat}
    {p : Mini (BitVec width)} {t : Sum (MiniState width) (MiniState width)}
    (h : Eval r (deleteVars vs s) p t) : Eval r s (.seq (.delete vs) p) t :=
  Eval.seq r s _ t _ p (Eval.delete r vs s) h

theorem ev_seq_swap {r : Option (Mini (BitVec width))} {s : MiniState width}
    {p : Mini (BitVec width)} {t : Sum (MiniState width) (MiniState width)}
    (h : Eval r (arrayWrite .in1 (s.arrays .in2) (arrayWrite .in2 (s.arrays .in1) s)) p t) :
    Eval r s (.seq .swap p) t :=
  Eval.seq r s _ t _ p (Eval.swap r s) h

theorem ev_seq_load {r : Option (Mini (BitVec width))} {s : MiniState width} {n i : Nat}
    {a : Address} {p : Mini (BitVec width)} {t : Sum (MiniState width) (MiniState width)}
    (hi : i ∈ s.regs.dom) (hb : (holFapply s.regs i).toNat < (s.arrays a).length)
    (h : Eval r (regWrite n (some (holEl (holFapply s.regs i).toNat (s.arrays a))) s) p t) :
    Eval r s (.seq (.load n i a) p) t := by
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hi
  rw [holFapply_of_lookup hw] at hb h
  exact Eval.seq r s _ t _ p (Eval.load r s n i a w ⟨hw, hb⟩) h

theorem ev_seq_store {r : Option (Mini (BitVec width))} {s : MiniState width} {n i : Nat}
    {p : Mini (BitVec width)} {t : Sum (MiniState width) (MiniState width)}
    (hn : n ∈ s.regs.dom) (hi : i ∈ s.regs.dom)
    (hb : (holFapply s.regs i).toNat < (s.arrays .out).length)
    (h : Eval r (arrayWrite .out ((s.arrays .out).set (holFapply s.regs i).toNat
      (holFapply s.regs n)) s) p t) :
    Eval r s (.seq (.store n i) p) t := by
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hi
  obtain ⟨wr, hwr⟩ := Option.ne_none_iff_exists'.mp hn
  rw [holFapply_of_lookup hw, holFapply_of_lookup hwr] at h
  rw [holFapply_of_lookup hw] at hb
  exact Eval.seq r s _ t _ p (Eval.store r s n i w wr ⟨hw, hwr, hb⟩) h

theorem ev_seq_add {r : Option (Mini (BitVec width))} {s : MiniState width} {n1 n2 n3 : Nat}
    {n4 n5 : WordRegImm (BitVec width)} {p : Mini (BitVec width)}
    {t : Sum (MiniState width) (MiniState width)}
    (h3 : n3 ∈ s.regs.dom) (h4 : evalRiPre s n4) (h5 : evalRiPre s n5)
    (hc : evalRi s n5 ≠ 0 → evalRi s n5 = 1) (h12 : n1 ≠ n2)
    (h : Eval r (regWrite n1 (some (singleAddWord (holFapply s.regs n3) (evalRi s n4)
        (evalRi s n5)).1)
      (regWrite n2 (some (singleAddWord (holFapply s.regs n3) (evalRi s n4)
        (evalRi s n5)).2) s)) p t) :
    Eval r s (.seq (.add n1 n2 n3 n4 n5) p) t :=
  Eval.seq r s _ t _ p (Eval.add n1 n2 n3 n4 n5 r s _ _ ⟨h3, h4, h5, hc, h12, rfl⟩) h

theorem ev_seq_sub {r : Option (Mini (BitVec width))} {s : MiniState width} {n1 n2 n3 : Nat}
    {n4 n5 : WordRegImm (BitVec width)} {p : Mini (BitVec width)}
    {t : Sum (MiniState width) (MiniState width)}
    (h3 : n3 ∈ s.regs.dom) (h4 : evalRiPre s n4) (h5 : evalRiPre s n5)
    (hc : evalRi s n5 ≠ 0 → evalRi s n5 = 1) (h12 : n1 ≠ n2)
    (h : Eval r (regWrite n1 (some (singleSubWord (holFapply s.regs n3) (evalRi s n4)
        (evalRi s n5)).1)
      (regWrite n2 (some (singleSubWord (holFapply s.regs n3) (evalRi s n4)
        (evalRi s n5)).2) s)) p t) :
    Eval r s (.seq (.sub n1 n2 n3 n4 n5) p) t :=
  Eval.seq r s _ t _ p (Eval.sub r s n1 n2 n3 n4 n5 _ _ ⟨h3, h4, h5, hc, h12, rfl⟩) h

theorem ev_seq_mul {r : Option (Mini (BitVec width))} {s : MiniState width} {n1 n2 n3 n4 : Nat}
    {p : Mini (BitVec width)} {t : Sum (MiniState width) (MiniState width)}
    (h3 : n3 ∈ s.regs.dom) (h4 : n4 ∈ s.regs.dom) (h12 : n1 ≠ n2)
    (h : Eval r (regWrite n1 (some (singleMul (holFapply s.regs n3) (holFapply s.regs n4) 0).1)
      (regWrite n2 (some (singleMul (holFapply s.regs n3) (holFapply s.regs n4) 0).2) s)) p t) :
    Eval r s (.seq (.mul n1 n2 n3 n4) p) t :=
  Eval.seq r s _ t _ p (Eval.mul r s n1 n2 n3 n4 ⟨h3, h4, h12⟩) h

theorem ev_seq_div {r : Option (Mini (BitVec width))} {s : MiniState width}
    {n1 n2 n3 n4 n5 : Nat} {p : Mini (BitVec width)} {t : Sum (MiniState width) (MiniState width)}
    (h3 : n3 ∈ s.regs.dom) (h4 : n4 ∈ s.regs.dom) (h5 : n5 ∈ s.regs.dom) (h12 : n1 ≠ n2)
    (hpre : singleDivPre (holFapply s.regs n3) (holFapply s.regs n4) (holFapply s.regs n5))
    (h : Eval r (regWrite n1 (some (singleDiv (holFapply s.regs n3) (holFapply s.regs n4)
        (holFapply s.regs n5)).1)
      (regWrite n2 (some (singleDiv (holFapply s.regs n3) (holFapply s.regs n4)
        (holFapply s.regs n5)).2) s)) p t) :
    Eval r s (.seq (.div n1 n2 n3 n4 n5) p) t :=
  Eval.seq r s _ t _ p (Eval.div r s n1 n2 n3 n4 n5 ⟨h3, h4, h5, h12, hpre⟩) h

/-- Reassociate a nested sequence. -/
theorem ev_seq_seq {r : Option (Mini (BitVec width))} {s : MiniState width}
    {a b c : Mini (BitVec width)} {t : Sum (MiniState width) (MiniState width)}
    (h : Eval r s (.seq a (.seq b c)) t) : Eval r s (.seq (.seq a b) c) t := by
  cases h with
  | seq _ _ s2 _ _ _ ha hbc =>
    cases hbc with
    | seq _ _ s3 _ _ _ hb hc => exact Eval.seq r s s3 t _ c (Eval.seq r s s2 _ a b ha hb) hc

/-- A generated sub-program whose correctness theorem is known. -/
theorem ev_seq_corr {r : Option (Mini (BitVec width))} {s s' : MiniState width}
    {c p : Mini (BitVec width)} {q : Prop} {t : Sum (MiniState width) (MiniState width)}
    (hc : Corr c s (.inr s') q) (hq : q) (h : Eval r s' p t) : Eval r s (.seq c p) t := by
  have h1 := hc hq
  cases r with
  | none => exact Eval.seq none s s' t c p h1 h
  | some body => exact Eval.seq _ s s' t c p (Eval_NONE_IMP s c _ body h1) h

/-- A generated sub-program in final position. -/
theorem ev_corr {r : Option (Mini (BitVec width))} {s s' b : MiniState width}
    {c : Mini (BitVec width)} {q : Prop}
    (hc : Corr c s (.inr s') q) (hq : q) (hb : s' = b) : Eval r s c (.inr b) := by
  subst hb
  have h1 := hc hq
  cases r with
  | none => exact h1
  | some body => exact Eval_NONE_IMP s c _ body h1

theorem ev_skip {r : Option (Mini (BitVec width))} {s b : MiniState width}
    (h : s = b) : Eval r s .skip (.inr b) := h ▸ Eval.skip r s

theorem ev_continue {r : Option (Mini (BitVec width))} {s b : MiniState width}
    (h : s = b) : Eval r s .continue (.inl b) := h ▸ Eval.continue r s

theorem ev_ite {rec : Option (Mini (BitVec width))} {s : MiniState width} {c : Cmp} {r : Nat}
    {ri : WordRegImm (BitVec width)} {p1 p2 : Mini (BitVec width)}
    {t : Sum (MiniState width) (MiniState width)}
    (hreg : r ∈ s.regs.dom) (hri : evalRiPre s ri)
    (h : Eval rec s (if wordCmpHOL c (evalExp s (.var r)) (evalRi s ri) then p1 else p2) t) :
    Eval rec s (.ite c r ri p1 p2) t :=
  Eval.ite rec s c r ri p1 p2 t hreg hri h

theorem decide_true_any {p : Prop} {inst : Decidable p} : (@decide p inst = true) = p := by
  cases inst <;> simp_all

theorem decide_false_any {p : Prop} {inst : Decidable p} : (@decide p inst = false) = ¬ p := by
  cases inst <;> simp_all

/-- HOL's signed word order on the assembler side is `BitVec.slt`. -/
theorem holAsmSignedLess_eq_slt {width : Nat} [NeZero width] (a b : BitVec width) :
    Compiler.Encoders.Asm.holAsmSignedLess a b = a.slt b := by
  have hw : width ≠ 0 := NeZero.ne width
  have hpow : 2 ^ width = 2 * 2 ^ (width - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hz : (2 : Int) ^ width = 2 * ((2 ^ (width - 1) : Nat) : Int) := by
    exact_mod_cast hpow
  have bl := a.isLt
  have br := b.isLt
  simp only [Compiler.Encoders.Asm.holAsmSignedLess, BitVec.slt_eq_decide, BitVec.toInt_eq_msb_cond,
    BitVec.msb_eq_decide]
  rw [hpow] at bl br ⊢
  generalize 2 ^ (width - 1) = P at *
  clear hpow hz
  repeat (any_goals first | split)
  all_goals simp_all only [decide_eq_true_eq]
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals simp_all [decide_eq_true_eq]
  all_goals omega

/-- A conditional, split on the outcome of its comparison. -/
theorem ev_ite2 {rec : Option (Mini (BitVec width))} {s : MiniState width} {c : Cmp} {r : Nat}
    {ri : WordRegImm (BitVec width)} {p1 p2 : Mini (BitVec width)}
    {t : Sum (MiniState width) (MiniState width)}
    (hreg : r ∈ s.regs.dom) (hri : evalRiPre s ri)
    (h1 : wordCmpHOL c (evalExp s (.var r)) (evalRi s ri) = true → Eval rec s p1 t)
    (h2 : wordCmpHOL c (evalExp s (.var r)) (evalRi s ri) = false → Eval rec s p2 t) :
    Eval rec s (.ite c r ri p1 p2) t := by
  refine Eval.ite rec s c r ri p1 p2 t hreg hri ?_
  cases h : wordCmpHOL c (evalExp s (.var r)) (evalRi s ri)
  · simpa [h] using h2 h
  · simpa [h] using h1 h

theorem lookup_regWrite (n k : Nat) (v : BitVec width) (s : MiniState width) :
    (regWrite n (some v) s).regs.lookup k = if k = n then some v else s.regs.lookup k := rfl

theorem lookup_regDelete (n k : Nat) (s : MiniState width) :
    (regWrite n none s).regs.lookup k = if k = n then none else s.regs.lookup k := rfl

theorem holFapply_regWrite (n k : Nat) (v : BitVec width) (s : MiniState width) :
    holFapply (regWrite n (some v) s).regs k = if k = n then v else holFapply s.regs k := by
  by_cases h : k = n
  · subst h; rw [if_pos rfl]; exact holFapply_of_lookup (by rw [lookup_regWrite, if_pos rfl])
  · rw [if_neg h]
    exact holFapply_congr (by rw [lookup_regWrite, if_neg h])

theorem mem_dom_iff (s : MiniState width) (k : Nat) :
    k ∈ s.regs.dom ↔ s.regs.lookup k ≠ none := Iff.rfl

theorem MiniState.ext' {a b : MiniState width} (hr : ∀ k, a.regs.lookup k = b.regs.lookup k)
    (ha : a.arrays = b.arrays) (hc : a.clock = b.clock) : a = b := by
  obtain ⟨ra, aa, ca⟩ := a
  obtain ⟨rb, ab, cb⟩ := b
  have : ra = rb := HolFiniteMapExact.ext_of_lookup hr
  simp_all

theorem regWrite_arrays (n : Nat) (v : Option (BitVec width)) (s : MiniState width) :
    (regWrite n v s).arrays = s.arrays := by cases v <;> rfl
theorem regWrite_clock (n : Nat) (v : Option (BitVec width)) (s : MiniState width) :
    (regWrite n v s).clock = s.clock := by cases v <;> rfl
theorem arrayWrite_regs (a : Address) (v : List (BitVec width)) (s : MiniState width) :
    (arrayWrite a v s).regs = s.regs := rfl
theorem arrayWrite_clock (a : Address) (v : List (BitVec width)) (s : MiniState width) :
    (arrayWrite a v s).clock = s.clock := rfl
theorem arrayWrite_arrays (a b : Address) (v : List (BitVec width)) (s : MiniState width) :
    (arrayWrite a v s).arrays b = if b = a then v else s.arrays b := by
  simp [arrayWrite, Function.update]
theorem clockWrite_regs (l : Nat) (s : MiniState width) : (clockWrite l s).regs = s.regs := rfl
theorem clockWrite_arrays (l : Nat) (s : MiniState width) :
    (clockWrite l s).arrays = s.arrays := rfl
theorem clockWrite_clock (l : Nat) (s : MiniState width) : (clockWrite l s).clock = l := rfl
theorem decClock_regs (s : MiniState width) : (decClock s).regs = s.regs := rfl
theorem decClock_arrays (s : MiniState width) : (decClock s).arrays = s.arrays := rfl
theorem decClock_clock (s : MiniState width) : (decClock s).clock = s.clock - 1 := rfl
theorem deleteVars_arrays (vs : List Nat) (s : MiniState width) :
    (deleteVars vs s).arrays = s.arrays := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [deleteVars, regWrite_arrays, ih]
theorem deleteVars_clock (vs : List Nat) (s : MiniState width) :
    (deleteVars vs s).clock = s.clock := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [deleteVars, regWrite_clock, ih]
theorem deleteVars_lookup (vs : List Nat) (s : MiniState width) (k : Nat) :
    (deleteVars vs s).regs.lookup k = if k ∈ vs then none else s.regs.lookup k := by
  induction vs with
  | nil => simp [deleteVars]
  | cons v vs ih =>
    simp only [deleteVars, lookup_regDelete, ih, List.mem_cons]
    by_cases h : k = v <;> simp [h]
theorem holFapply_eq_of_regs {a b : MiniState width} (h : a.regs = b.regs) (k : Nat) :
    holFapply a.regs k = holFapply b.regs k := by rw [h]

theorem lookup_of_dom {s : MiniState width} {k : Nat} (h : k ∈ s.regs.dom) :
    s.regs.lookup k = some (holFapply s.regs k) := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h
  rw [hv, holFapply_of_lookup hv]

/-- Increment the clock: the state a `Continue` leaves before `loop_app`
decrements it. -/
def incClock (s : MiniState width) : MiniState width := { s with clock := s.clock + 1 }

theorem incClock_regs (s : MiniState width) : (incClock s).regs = s.regs := rfl
theorem incClock_arrays (s : MiniState width) : (incClock s).arrays = s.arrays := rfl
theorem incClock_clock (s : MiniState width) : (incClock s).clock = s.clock + 1 := rfl

/-- HOL's `SHORT_TAILREC` simulation of a loop body by its step function: if the
body, started from the encoding of a step input, ends with `Continue` in the
(clock-incremented) encoding of the next input, or finishes in the encoding of
the result, then the loop body runs the whole tail recursion. -/
theorem evalLoopBody_of_step {T U : Type} [Nonempty T] [Nonempty U]
    (B : Mini (BitVec width)) (step : T → (T ⊕ U) × Prop) (enc : T → MiniState width)
    (out : U → MiniState width)
    (hbody : ∀ x, (step x).2 → Eval none (enc x) B
      (match (step x).1 with
       | .inl x' => .inl (incClock (enc x'))
       | .inr y => .inr (out y))) :
    ∀ x, holShortTailrecPre step x →
      Eval none (enc x) (.loopBody B) (.inr (out (holShortTailrec step x))) := by
  intro x hpre
  refine holShortTailrecPre_induct (f := step)
    (fun x => Eval none (enc x) (.loopBody B) (.inr (out (holShortTailrec step x)))) ?_ x hpre
  rintro x ⟨_, hguard, ih⟩
  have hb := hbody x hguard
  rcases hs : step x with ⟨q, c⟩
  rw [hs] at hb ih
  cases q with
  | inl x' =>
    rw [holShortTailrec_inl hs]
    exact Eval.loopBodyContinue none (enc x) _ _ B hb (by simp [incClock])
      (by simpa [incClock, decClock] using ih x' rfl)
  | inr y =>
    rw [holShortTailrec_inr hs]
    exact Eval.loopBodyReturn none (enc x) B _ hb

/-- A non-recursive loop whose body simulates a tail recursion. -/
theorem corr_loop_of_step {T U : Type} [Nonempty T] [Nonempty U]
    (B : Mini (BitVec width)) (vs : List Nat) (s : MiniState width)
    (step : T → (T ⊕ U) × Prop) (enc : T → MiniState width) (out : U → MiniState width)
    (hbody : ∀ x, (step x).2 → Eval none (enc x) B
      (match (step x).1 with
       | .inl x' => .inl (incClock (enc x'))
       | .inr y => .inr (out y)))
    (x0 : T) (target : MiniState width)
    (ht : out (holShortTailrec step x0) = target) (G : Prop)
    (hG : G → holShortTailrecPre step x0 ∧ s.clock ≠ 0 ∧ enc x0 = deleteVars vs (decClock s)) :
    Corr (.loop false vs B) s (.inr target) G := by
  intro hg
  obtain ⟨hpre, hclock, hx0⟩ := hG hg
  have h := evalLoopBody_of_step B step enc out hbody x0 hpre
  rw [hx0, ht] at h
  exact Eval.loop none s B vs target false h hclock

end Flapjack.Compiler.Backend.WordBignum.CorrSupport
