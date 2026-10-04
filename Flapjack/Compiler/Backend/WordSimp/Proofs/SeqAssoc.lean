import Flapjack.Compiler.Backend.WordSimp
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateConsts

/-!
# `word_simpProof`: verification of `Seq_assoc`

Counterpart of `cakeml/compiler/backend/proofs/word_simpProofScript.sml:12-128`
(bead `flapjack-pxn.18.5.15.2.41`): `evaluate_SmartSeq`, `evaluate_Seq_Skip`,
`evaluate_Skip_Seq`, `evaluate_Loop_body_cong(_gc)`, `evaluate_Seq_assoc_lemma`,
`evaluate_Seq_assoc`, the `dest_*` characterisations, `dest_Seq_IMP` and
`dest_Seq_Assign_Const_IMP`, over the native exact `evaluate` and the tagged
`word_simp` definitions.

The untagged `evalEq_*` lemmas are Flapjack proof infrastructure: each says a
program constructor's semantics depends on its sub-programs only through their
semantics.  HOL obtains them by unfolding `evaluate_def` inside each case of the
`Seq_assoc_ind` proof.

Inherited assumption: theorems mentioning `evaluate` reach the
`reals_as_rational_cuts`-qualified `inst`; the theorem map records the
`docs/SOUNDNESS.md` item 8 assumption.
-/

namespace Flapjack

namespace WordSimpSeqAssocSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSimpSeqAssocSupport

namespace WordSemStateFiniteExact

open Flapjack.Compiler.Backend.WordSimp

section Congruence

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

theorem evaluate_skip_eq (s : WordSemStateFiniteExact width C F) :
    evaluate (.skip : WordLangProgHOL (BitVec width)) s = (none, s) :=
  (evaluate_def_rebound (width := width) (C := C) (F := F)).1 s

theorem evaluate_seq_eq (a b : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) :
    evaluate (.seq a b) s =
      match evaluate a s with
      | (none, s1) => evaluate b s1
      | (res, s1) => (res, s1) := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [ht]
  rcases evaluate a s with ⟨_ | r, s1⟩ <;> rfl

theorem evalEq_seq {a a' b b' : WordLangProgHOL (BitVec width)}
    (ha : ∀ v : WordSemStateFiniteExact width C F, evaluate a v = evaluate a' v)
    (hb : ∀ v : WordSemStateFiniteExact width C F, evaluate b v = evaluate b' v)
    (s : WordSemStateFiniteExact width C F) :
    evaluate (.seq a b) s = evaluate (.seq a' b') s := by
  rw [evaluate_seq_eq, evaluate_seq_eq, ha]
  rcases evaluate a' s with ⟨_ | r, s1⟩
  · exact hb s1
  · rfl

theorem evalEq_seq_assoc (a b c : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) :
    evaluate (.seq (.seq a b) c) s = evaluate (.seq a (.seq b c)) s := by
  rw [evaluate_seq_eq, evaluate_seq_eq, evaluate_seq_eq]
  rcases evaluate a s with ⟨_ | r, s1⟩
  · simp only
    rw [evaluate_seq_eq]
  · rfl

theorem evalEq_ite {c1 c1' c2 c2' : WordLangProgHOL (BitVec width)}
    (h1 : ∀ v : WordSemStateFiniteExact width C F, evaluate c1 v = evaluate c1' v)
    (h2 : ∀ v : WordSemStateFiniteExact width C F, evaluate c2 v = evaluate c2' v)
    (cmp : Cmp) (r : Nat) (ri : WordRegImm (BitVec width))
    (s : WordSemStateFiniteExact width C F) :
    evaluate (.ite cmp r ri c1 c2) s = evaluate (.ite cmp r ri c1' c2') s := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [ht, ht, h1, h2]

theorem evalEq_mustTerminate {c c' : WordLangProgHOL (BitVec width)}
    (h : ∀ v : WordSemStateFiniteExact width C F, evaluate c v = evaluate c' v)
    (s : WordSemStateFiniteExact width C F) :
    evaluate (.mustTerminate c) s = evaluate (.mustTerminate c') s := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
  rw [ht, ht, h]

theorem evalEq_call_ret {h1 h2 : WordLangProgHOL (BitVec width)}
    (h : ∀ v : WordSemStateFiniteExact width C F, evaluate h1 v = evaluate h2 v)
    (n : List Nat) (names : WordLangCutsetsHOL) (l1 l2 : Nat) (dest : Option Nat)
    (args : List Nat) (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) :
    evaluate (.call (some (n, names, h1, l1, l2)) dest args handler) s =
      evaluate (.call (some (n, names, h2, l1, l2)) dest args handler) s := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [ht, ht]
  simp only [wordSemAddRetLoc, h]

theorem evalEq_call_handler {e1 e2 : WordLangProgHOL (BitVec width)}
    (h : ∀ v : WordSemStateFiniteExact width C F, evaluate e1 v = evaluate e2 v)
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (dest : Option Nat) (args : List Nat) (n l1 l2 : Nat)
    (s : WordSemStateFiniteExact width C F) :
    evaluate (.call ret dest args (some (n, e1, l1, l2))) s =
      evaluate (.call ret dest args (some (n, e2, l1, l2))) s := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hp : ∀ (envs : Spt (WordLocW width) × Spt (WordLocW width))
      (t : WordSemStateFiniteExact width C F),
      pushEnv envs (some (n, e1, l1, l2)) t = pushEnv envs (some (n, e2, l1, l2)) t :=
    fun _ _ => rfl
  rw [ht, ht]
  simp only [hp, h]

end Congruence

/-- Exact HOL `evaluate_SmartSeq` (`word_simpProofScript.sml:14-18`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluate_SmartSeq {width : Nat} [NeZero width] {C : Type} {F : Type}
    (p1 p2 : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    evaluate (Compiler.Backend.WordSimp.smartSeqHOL p1 p2) s = evaluate (.seq p1 p2) s := by
  cases p1 <;> simp only [Compiler.Backend.WordSimp.smartSeqHOL]
  rw [evaluate_seq_eq, evaluate_skip_eq]

/-- Exact HOL `evaluate_Seq_Skip` (`word_simpProofScript.sml:20-25`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluate_Seq_Skip {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (p1 : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      evaluate (.seq p1 .skip) s = evaluate p1 s := by
  intro p1 s
  rw [evaluate_seq_eq]
  rcases evaluate p1 s with ⟨_ | r, s1⟩
  · exact evaluate_skip_eq s1
  · rfl

/-- Exact HOL `evaluate_Skip_Seq` (`word_simpProofScript.sml:27-31`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluate_Skip_Seq {width : Nat} [NeZero width] {C : Type} {F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    evaluate (.seq .skip p) s = evaluate p s := by
  rw [evaluate_seq_eq, evaluate_skip_eq]

/-- Exact HOL `evaluate_Loop_body_cong_gc` (`word_simpProofScript.sml:49-67`):
    HOL's free predicate `R` on the GC function is the outermost binder. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluate_Loop_body_cong_gc {width : Nat} [NeZero width] {C : Type} {F : Type}
    (R : WordSemGcFun width → Prop) :
    ∀ (s : WordSemStateFiniteExact width C F) (names : WordLangNumSetHOL)
      (c c' : WordLangProgHOL (BitVec width)) (exitNames : WordLangNumSetHOL),
      (∀ v : WordSemStateFiniteExact width C F, R v.gcFun → evaluate c' v = evaluate c v) →
      R s.gcFun →
      evaluate (.loop names c' exitNames) s = evaluate (.loop names c exitNames) s := by
  intro s names c c' exitNames h
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  suffices ∀ n (s : WordSemStateFiniteExact width C F), s.clock = n → R s.gcFun →
      evaluate (.loop names c' exitNames) s = evaluate (.loop names c exitNames) s from
    this _ s rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs hR
    rw [ht, ht]
    rcases hcs : cutState (names, .ln) s with _ | v
    · rfl
    simp only
    obtain ⟨l, rfl⟩ := cutStateConst _ _ _ hcs
    have hc2 := cutState_clock_termdep _ _ _ hcs
    have hRv : R ({ s with locals := l } : WordSemStateFiniteExact width C F).gcFun := hR
    rw [h _ hRv]
    rcases hb : evaluate c { s with locals := l } with ⟨rb, s1⟩
    have hcl := evaluate_clock c _ rb s1 hb
    have hcon := evaluate_consts c _ rb s1 hb
    simp only
    by_cases hcont : wordSemContLoop rb = true
    · simp only [hcont, if_true]
      by_cases hz : s1.clock = 0
      · simp only [hz, if_true]
      · simp only [hz, if_false, wordSemSTOP]
        refine ih (decClock s1).clock ?_ (decClock s1) rfl ?_
        · simp only [decClock] at *; omega
        · show R s1.gcFun
          rw [← hcon.1]; exact hR
    · simp only [hcont, Bool.false_eq_true, if_false]

/-- Exact HOL `evaluate_Loop_body_cong` (`word_simpProofScript.sml:33-47`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluate_Loop_body_cong {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (s : WordSemStateFiniteExact width C F) (names : WordLangNumSetHOL)
      (c c' : WordLangProgHOL (BitVec width)) (exitNames : WordLangNumSetHOL),
      (∀ v : WordSemStateFiniteExact width C F, evaluate c' v = evaluate c v) →
      evaluate (.loop names c' exitNames) s = evaluate (.loop names c exitNames) s :=
  fun s names c c' exitNames h =>
    evaluate_Loop_body_cong_gc (fun _ => True) s names c c' exitNames (fun v _ => h v) trivial

/-- Exact HOL `evaluate_Seq_assoc_lemma` (`word_simpProofScript.sml:69-88`), by
    recursion on `Seq_assoc`'s second argument as HOL's `Seq_assoc_ind`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluate_Seq_assoc_lemma {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (p1 p2 : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      evaluate (Compiler.Backend.WordSimp.seqAssoc p1 p2) s = evaluate (.seq p1 p2) s
  | p1, .skip, s => by
      simp only [Compiler.Backend.WordSimp.seqAssoc]; exact (evaluate_Seq_Skip p1 s).symm
  | p1, .seq q1 q2, s => by
      simp only [Compiler.Backend.WordSimp.seqAssoc]
      rw [evaluate_Seq_assoc_lemma _ q2 s,
        evalEq_seq (fun v => evaluate_Seq_assoc_lemma p1 q1 v) (fun _ => rfl), evalEq_seq_assoc]
  | p1, .ite v n r q1 q2, s => by
      simp only [Compiler.Backend.WordSimp.seqAssoc]
      rw [evaluate_SmartSeq]
      refine evalEq_seq (fun _ => rfl) (fun w => ?_) s
      refine evalEq_ite (fun u => ?_) (fun u => ?_) v n r w
      · rw [evaluate_Seq_assoc_lemma, evaluate_Skip_Seq]
      · rw [evaluate_Seq_assoc_lemma, evaluate_Skip_Seq]
  | p1, .mustTerminate q, s => by
      simp only [Compiler.Backend.WordSimp.seqAssoc]
      rw [evaluate_SmartSeq]
      refine evalEq_seq (fun _ => rfl) (fun w => evalEq_mustTerminate (fun u => ?_) w) s
      rw [evaluate_Seq_assoc_lemma, evaluate_Skip_Seq]
  | p1, .call ret dest args handler, s => by
      unfold Compiler.Backend.WordSimp.seqAssoc
      rw [evaluate_SmartSeq]
      refine evalEq_seq (fun _ => rfl) (fun w => ?_) s
      have hh : ∀ w : WordSemStateFiniteExact width C F,
          evaluate (.call ret dest args (match handler with
            | none => none
            | some (y1, q2, y2, y3) =>
                some (y1, Compiler.Backend.WordSimp.seqAssoc .skip q2, y2, y3))) w =
          evaluate (.call ret dest args handler) w := by
        intro w
        rcases handler with _ | ⟨y1, q2, y2, y3⟩
        · rfl
        · exact evalEq_call_handler (fun u => by
            rw [evaluate_Seq_assoc_lemma, evaluate_Skip_Seq]) ret dest args y1 y2 y3 w
      rcases ret with _ | ⟨x1, x2, q1, x3, x4⟩
      · exact hh w
      · rw [evalEq_call_ret (h1 := Compiler.Backend.WordSimp.seqAssoc .skip q1) (h2 := q1)
          (fun u => by rw [evaluate_Seq_assoc_lemma, evaluate_Skip_Seq])]
        exact hh w
  | p1, .loop names body exitNames, s => by
      simp only [Compiler.Backend.WordSimp.seqAssoc]
      rw [evaluate_SmartSeq]
      refine evalEq_seq (fun _ => rfl) (fun w => ?_) s
      refine evaluate_Loop_body_cong w names body _ exitNames (fun u => ?_)
      rw [evaluate_Seq_assoc_lemma, evaluate_Skip_Seq]
  | p1, .move _ _, s | p1, .inst _, s | p1, .assign _ _, s | p1, .get _ _, s
  | p1, .set _ _, s | p1, .store _ _, s | p1, .alloc _ _, s | p1, .storeConsts _ _ _ _ _, s
  | p1, .raise _, s | p1, .return _ _, s | p1, .break _, s | p1, .continue _, s
  | p1, .tick, s | p1, .opCurrHeap _ _ _, s | p1, .locValue _ _, s
  | p1, .install _ _ _ _ _, s | p1, .codeBufferWrite _ _, s | p1, .dataBufferWrite _ _, s
  | p1, .ffi _ _ _ _ _ _, s | p1, .shareInst _ _ _, s => by
      simp only [Compiler.Backend.WordSimp.seqAssoc]; exact evaluate_SmartSeq _ _ s

/-- Exact HOL `evaluate_Seq_assoc` (`word_simpProofScript.sml:90-94`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluate_Seq_assoc {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      evaluate (Compiler.Backend.WordSimp.seqAssoc .skip p) s = evaluate p s := by
  intro p s
  rw [evaluate_Seq_assoc_lemma, evaluate_Skip_Seq]

/-- Exact HOL `dest_If_Eq_Imm_thm` (`word_simpProofScript.sml:96-102`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem dest_If_Eq_Imm_thm {width : Nat} [NeZero width] (x2 : WordLangProgHOL (BitVec width))
    (n : Nat) (w : BitVec width) (p1 p2 : WordLangProgHOL (BitVec width)) :
    Compiler.Backend.WordSimp.destIfEqImm x2 = some (n, w, p1, p2) ↔
      x2 = .ite .equal n (.imm w) p1 p2 := by
  cases x2 <;> simp [Compiler.Backend.WordSimp.destIfEqImm, Compiler.Backend.WordSimp.destIf]
  rename_i cmp r ri c1 c2
  cases cmp <;> cases ri <;> simp

/-- Exact HOL `dest_If_thm` (`word_simpProofScript.sml:104-108`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem dest_If_thm {width : Nat} [NeZero width] (x2 : WordLangProgHOL (BitVec width))
    (g1 : Cmp) (g2 : Nat) (g3 : WordRegImm (BitVec width)) (g4 g5 : WordLangProgHOL (BitVec width)) :
    Compiler.Backend.WordSimp.destIf x2 = some (g1, g2, g3, g4, g5) ↔
      x2 = .ite g1 g2 g3 g4 g5 := by
  cases x2 <;> simp [Compiler.Backend.WordSimp.destIf]

/-- Exact HOL `dest_Seq_IMP` (`word_simpProofScript.sml:110-115`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem dest_Seq_IMP {width : Nat} [NeZero width] {C : Type} {F : Type}
    (p1 x1 x2 : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    Compiler.Backend.WordSimp.destSeq p1 = (x1, x2) →
      evaluate p1 s = evaluate (.seq x1 x2) s := by
  intro h
  cases p1 <;> simp only [Compiler.Backend.WordSimp.destSeq, Prod.mk.injEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> first | rfl | exact (evaluate_Skip_Seq _ s).symm

/-- Exact HOL `dest_Seq_Assign_Const_IMP` (`word_simpProofScript.sml:117-124`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem dest_Seq_Assign_Const_IMP {width : Nat} [NeZero width] {C : Type} {F : Type}
    (v : Nat) (p q : WordLangProgHOL (BitVec width)) (w : BitVec width)
    (s : WordSemStateFiniteExact width C F) :
    Compiler.Backend.WordSimp.destSeqAssignConst v p = some (q, w) →
      evaluate p s = evaluate (.seq q (.assign v (.const w))) s := by
  intro h
  unfold Compiler.Backend.WordSimp.destSeqAssignConst at h
  rcases hd : Compiler.Backend.WordSimp.destSeq p with ⟨a, b⟩
  rw [hd] at h
  simp only at h
  rw [dest_Seq_IMP p a b s hd]
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rename_i hm
      rw [hm]
    · cases h
  · cases h

end WordSemStateFiniteExact

end Flapjack
