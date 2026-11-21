module

public import Flapjack.Compiler.Backend.WordBignum.Proofs.CompileThmSupport

@[expose] public section

/-! Flapjack-only case lemmas for the `compile_thm` port of
`cakeml/compiler/backend/proofs/word_bignumProofScript.sml`. `CompileGoal`
is the conclusion of HOL's `compile_thm` for one `Eval` judgement (everything
after `Eval rec s1 prog s2 ==>`); each lemma below proves it for one `Eval`
rule, following HOL's `ho_match_mp_tac eval_ind` case split. -/

namespace Flapjack.Compiler.Backend.WordBignum.CompileThmSupport

open Flapjack
open Flapjack.WordSemStateFiniteExact.BignumClauses
open Flapjack.Compiler.Backend.WordBignum
open Flapjack.Compiler.Encoders.Asm

variable {width : Nat} [NeZero width] {β C F : Type}

/-- The conclusion of HOL `compile_thm` for one evaluation judgement. -/
def CompileGoal (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (cs2Ty : Type) (rec : Option (Mini (BitVec width))) (s1 : MiniState width)
    (prog : Mini (BitVec width)) (s2 : Sum (MiniState width) (MiniState width)) : Prop :=
  ∀ (n l i : Nat) (cs : CodeAcc width) (p1 : WordLangProgHOL (BitVec width)) (l1 i1 : Nat)
    (cs1 : CodeAcc width) (cs2 : cs2Ty × List (CodeEntry width))
    (t1 : WordSemStateFiniteExact width C F) (retVal : WordLocW width)
    (p9 : WordLangProgHOL (BitVec width)),
    compile n l i cs prog = (p1, l1, i1, cs1) ∧ stateRel s1 t1 cs2 t0 frame ∧ 0 < i ∧
      syntaxOk prog ∧ codeSubset cs1 cs2 ∧
      (∀ body, rec = some body →
        ∃ (l i : Nat) (cs : CodeAcc width) (p1 : WordLangProgHOL (BitVec width)) (l1 i1 : Nat)
          (cs1 : CodeAcc width),
          compile n l i cs body = (p1, l1, i1, cs1) ∧ 0 < i ∧ syntaxOkAux body ∧
            codeSubset cs1 cs2 ∧ sptLookup n t1.code = some (1, .seq p1 (.return 0 [0]))) ∧
      (∀ body, prog = .loopBody body →
        p9 = .return 0 [0] ∧ sptLookup n t1.code = some (1, .seq p1 (.return 0 [0]))) ∧
      WordSemStateFiniteExact.getVar 0 t1 = some retVal ∧ goodDimindex width →
    ∃ (t2 : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width) × WordSemStateFiniteExact width C F),
      WordSemStateFiniteExact.evaluate (.seq p1 p9) t1 = res ∧
        match s2 with
        | .inl s =>
            res = WordSemStateFiniteExact.evaluate (.call none (some n) [0] none) t2 ∧ 0 < i1 ∧
              t2.stack = t1.stack ∧ WordSemStateFiniteExact.getVar 0 t2 = some retVal ∧
              stateRel s t2 cs2 t0 frame ∧ t2.code = t1.code
        | .inr s =>
            res = WordSemStateFiniteExact.evaluate p9 t2 ∧ 0 < i1 ∧
              t2.stack = t1.stack ∧ WordSemStateFiniteExact.getVar 0 t2 = some retVal ∧
              stateRel s t2 cs2 t0 frame ∧ t2.code = t1.code

/-- A straight-line compiled program finishing normally discharges the
`INR` conclusion. -/
theorem goal_of_none {t0 t1 t2 : WordSemStateFiniteExact width C F}
    {frame : ((BitVec width × WordLocW width) → Prop) → Prop} {cs2 : β × List (CodeEntry width)}
    {s : MiniState width} {p1 p9 : WordLangProgHOL (BitVec width)} {i1 : Nat}
    {retVal : WordLocW width}
    (hev : WordSemStateFiniteExact.evaluate p1 t1 = (none, t2)) (hi : 0 < i1)
    (hstack : t2.stack = t1.stack) (hret : WordSemStateFiniteExact.getVar 0 t2 = some retVal)
    (hrel : stateRel s t2 cs2 t0 frame) (hcode : t2.code = t1.code) :
    ∃ (t2 : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width) × WordSemStateFiniteExact width C F),
      WordSemStateFiniteExact.evaluate (.seq p1 p9) t1 = res ∧
        res = WordSemStateFiniteExact.evaluate p9 t2 ∧ 0 < i1 ∧
          t2.stack = t1.stack ∧ WordSemStateFiniteExact.getVar 0 t2 = some retVal ∧
          stateRel s t2 cs2 t0 frame ∧ t2.code = t1.code :=
  ⟨t2, _, rfl, evaluate_seq_of_none _ _ _ _ hev, hi, hstack, hret, hrel, hcode⟩

/-- `Skip` case. -/
theorem case_skip (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (r : Option (Mini (BitVec width))) (s : MiniState width) :
    CompileGoal t0 frame β r s .skip (.inr s) := by
  rintro n l i cs p1 l1 i1 cs1 cs2 t1 retVal p9 ⟨hc, hrel, hi, -, -, -, -, hret, -⟩
  rw [compile_skip] at hc
  cases hc
  exact goal_of_none (evaluate_skip t1) hi rfl hret hrel rfl

/-- `Delete` case: the compiled code is `Skip`, and deleting registers
preserves `state_rel`. -/
theorem case_delete (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (r : Option (Mini (BitVec width))) (vs : List Nat) (s : MiniState width) :
    CompileGoal t0 frame β r s (.delete vs) (.inr (deleteVars vs s)) := by
  rintro n l i cs p1 l1 i1 cs1 cs2 t1 retVal p9 ⟨hc, hrel, hi, -, -, -, -, hret, -⟩
  rw [compile_delete] at hc
  cases hc
  exact goal_of_none (evaluate_skip t1) hi rfl hret
    (stateRel_delete_vars vs s t1 cs2 t0 frame hrel) rfl

/-- A tail call never finishes normally: a normal callee result is a bad
function return and becomes an error. -/
theorem evaluate_tailCall_ne_none (t : WordSemStateFiniteExact width C F) (n : Nat) :
    (WordSemStateFiniteExact.evaluate (.call none (some n) [0] none) t).1 ≠ none := by
  rw [evaluate_call]
  cases hv : WordSemStateFiniteExact.getVars [0] t with
  | none => simp
  | some xs =>
    simp only [wordSemBadDestArgs, Bool.false_eq_true, if_false]
    cases hf : wordSemFindCode (some n) (wordSemAddRetLoc none xs) t.code t.stackSize with
    | none => simp
    | some tri =>
      obtain ⟨args1, prog, ss⟩ := tri
      simp only
      split
      · simp
      · rcases WordSemStateFiniteExact.evaluate prog
            (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock t))
          with ⟨res, s'⟩
        simp only
        split
        · simp
        · rename_i hbad
          cases res with
          | none => simp [wordSemBadFunReturn] at hbad
          | some r => simp

/-- `Continue` case: the compiled code is the tail call itself. -/
theorem case_continue (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (r : Option (Mini (BitVec width))) (s : MiniState width) :
    CompileGoal t0 frame β r s .continue (.inl s) := by
  rintro n l i cs p1 l1 i1 cs1 cs2 t1 retVal p9 ⟨hc, hrel, hi, -, -, -, -, hret, -⟩
  rw [compile_continue] at hc
  cases hc
  refine ⟨t1, _, rfl, ?_, hi, rfl, hret, hrel, rfl⟩
  rw [evaluate_seq]
  have hne := evaluate_tailCall_ne_none t1 n
  rcases h : WordSemStateFiniteExact.evaluate (.call none (some n) [0] none) t1 with ⟨res, s'⟩
  rw [h] at hne
  cases res with
  | none => exact absurd rfl hne
  | some r => rfl

/-- Reading local `0` past a `set_var` of a positive name. -/
theorem getVar_zero_setVar {t : WordSemStateFiniteExact width C F} {k : Nat} (hk : 0 < k)
    (v : WordLocW width) :
    WordSemStateFiniteExact.getVar 0 (WordSemStateFiniteExact.setVar k v t) =
      WordSemStateFiniteExact.getVar 0 t := by
  simp only [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar]
  exact sptLookup_sptInsert_ne k 0 v t.locals (by omega)

/-- `Assign` case. -/
theorem case_assign (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (r : Option (Mini (BitVec width))) (s : MiniState width)
    (x : WordLangExpHOL (BitVec width)) (j : Nat) (hpre : evalExpPre s x) :
    CompileGoal t0 frame β r s (.assign j x) (.inr (regWrite j (some (evalExp s x)) s)) := by
  rintro n l i cs p1 l1 i1 cs1 cs2 t1 retVal p9 ⟨hc, hrel, hi, hsyn, -, -, -, hret, hgood⟩
  rw [compile_assign] at hc
  cases hc
  have hj : j < 25 := by simpa [syntaxOk, syntaxOkAux] using hsyn.1
  have hexp := compileExp_thm s t1 cs2 t0 frame x ⟨hrel, hpre, hgood⟩
  have hev : WordSemStateFiniteExact.evaluate
      (.seq (.assign i (compileExp x)) (.set (.temp (BitVec.ofNat 5 j)) (.var i))) t1 =
      (none, WordSemStateFiniteExact.setStore (.temp (BitVec.ofNat 5 j)) (.word (evalExp s x))
        (WordSemStateFiniteExact.setVar i (.word (evalExp s x)) t1)) := by
    rw [evaluate_seq, evaluate_assign, hexp]
    simp only
    rw [evaluate_set]
    simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
  refine goal_of_none hev (by omega) rfl ?_ ?_ rfl
  · simp only [WordSemStateFiniteExact.setStore]
    exact (getVar_zero_setVar hi _).trans hret
  · exact stateRel_write j _ hj (stateRel_setVar i _ hrel)

/-- A well-formed non-`LoopBody` program is well formed at the top level. -/
theorem syntaxOk_of_aux {p : Mini (BitVec width)} (h : syntaxOkAux p) :
    syntaxOk p ∧ ∀ b, p ≠ .loopBody b := by
  cases p with
  | loopBody b => exact absurd h (by simp [syntaxOkAux])
  | _ => exact ⟨by simpa [syntaxOk] using h, fun _ h => by cases h⟩

/-- `Seq` case. -/
theorem case_seq (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (r : Option (Mini (BitVec width))) (s1 s2 : MiniState width)
    (s3 : Sum (MiniState width) (MiniState width)) (a b : Mini (BitVec width))
    (iha : CompileGoal t0 frame β r s1 a (.inr s2))
    (ihb : CompileGoal t0 frame β r s2 b s3) :
    CompileGoal t0 frame β r s1 (.seq a b) s3 := by
  rintro n l i cs p1 l1 i1 cs1 cs2 t1 retVal p9
    ⟨hc, hrel, hi, hsyn, hsub, hrec, -, hret, hgood⟩
  rcases ha : compile n l i cs a with ⟨a', la, ia, ca⟩
  rcases hb : compile n la ia ca b with ⟨b', lb, ib, cb⟩
  rw [compile_seq, ha] at hc
  dsimp only at hc
  rw [hb] at hc
  dsimp only at hc
  cases hc
  have hsyn' : syntaxOkAux a ∧ syntaxOkAux b := by simpa [syntaxOk, syntaxOkAux] using hsyn
  obtain ⟨hsa, hna⟩ := syntaxOk_of_aux hsyn'.1
  obtain ⟨hsb, hnb⟩ := syntaxOk_of_aux hsyn'.2
  have hsubA : codeSubset ca cs2 :=
    codeSubset_trans _ _ _ ⟨(compile_IMP_codeSubset b _ _ _ _ _ _ _ _ hb).1, hsub⟩
  obtain ⟨t2, res, hres, hres2, hia, hst2, hret2, hrel2, hcode2⟩ :=
    iha n l i cs a' la ia ca cs2 t1 retVal (.seq b' p9)
      ⟨ha, hrel, hi, hsa, hsubA, hrec, fun body h => absurd h (hna body), hret, hgood⟩
  have hrec2 : ∀ body, r = some body →
      ∃ (l i : Nat) (cs : CodeAcc width) (p1 : WordLangProgHOL (BitVec width)) (l1 i1 : Nat)
        (cs1 : CodeAcc width),
        compile n l i cs body = (p1, l1, i1, cs1) ∧ 0 < i ∧ syntaxOkAux body ∧
          codeSubset cs1 cs2 ∧ sptLookup n t2.code = some (1, .seq p1 (.return 0 [0])) := by
    rw [hcode2]
    exact hrec
  obtain ⟨t3, res3, hres3, hgoal⟩ :=
    ihb n la ia ca _ _ _ _ cs2 t2 retVal p9
      ⟨hb, hrel2, hia, hsb, hsub, hrec2, fun body h => absurd h (hnb body), hret2, hgood⟩
  refine ⟨t3, res3, ?_, ?_⟩
  · rw [← evaluate_seqSeq, ← hres3, ← hres2, hres]
  · cases s3 with
    | inl s =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hgoal
      exact ⟨h1, h2, h3.trans hst2, h4, h5, h6.trans hcode2⟩
    | inr s =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hgoal
      exact ⟨h1, h2, h3.trans hst2, h4, h5, h6.trans hcode2⟩

/-- A live mini-state register is a live temporary holding its value. -/
theorem stateRel_lookup_temp {s : MiniState width} {t t0 : WordSemStateFiniteExact width C F}
    {cs : β × List (CodeEntry width)} {frame : ((BitVec width × WordLocW width) → Prop) → Prop}
    {r : Nat} (h : stateRel s t cs t0 frame) (hr : r ∈ s.regs.dom) :
    t.store.lookup (.temp (BitVec.ofNat 5 r)) = some (.word (holFapply s.regs r)) := by
  cases hl : s.regs.lookup r with
  | none => exact absurd hl hr
  | some v =>
    rw [holFapply_of_lookup hl]
    exact (h.2.2.1 r v hl).2

/-- `If` case. -/
theorem case_ite (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (rec : Option (Mini (BitVec width))) (s1 : MiniState width) (c : Cmp) (r : Nat)
    (ri : WordRegImm (BitVec width)) (pa pb : Mini (BitVec width))
    (s2 : Sum (MiniState width) (MiniState width))
    (hreg : r ∈ s1.regs.dom) (hri : evalRiPre s1 ri)
    (ih : CompileGoal t0 frame β rec s1
      (if wordCmpHOL c (evalExp s1 (.var r)) (evalRi s1 ri) then pa else pb) s2) :
    CompileGoal t0 frame β rec s1 (.ite c r ri pa pb) s2 := by
  rintro n l i cs p1 l1 i1 cs1 cs2 t1 retVal p9
    ⟨hc, hrel, hi, hsyn, hsub, hrec, -, hret, hgood⟩
  rcases ha : compile n l i cs pa with ⟨a', la, ia, ca⟩
  rcases hb : compile n la ia ca pb with ⟨b', lb, ib, cb⟩
  rw [compile_ite, ha] at hc
  dsimp only at hc
  rw [hb] at hc
  dsimp only at hc
  have hsyn' : r < 25 ∧ (∀ r', ri = .reg r' → r' < 25) ∧ syntaxOkAux pa ∧ syntaxOkAux pb := by
    simpa [syntaxOk, syntaxOkAux] using hsyn
  obtain ⟨hsa, hna⟩ := syntaxOk_of_aux hsyn'.2.2.1
  obtain ⟨hsb, hnb⟩ := syntaxOk_of_aux hsyn'.2.2.2
  obtain ⟨hsubB, hib⟩ := compile_IMP_codeSubset pb _ _ _ _ _ _ _ _ hb
  obtain ⟨hsubA, hia⟩ := compile_IMP_codeSubset pa _ _ _ _ _ _ _ _ ha
  have hvr := stateRel_lookup_temp hrel hreg
  have hib0 : 0 < ib := by omega
  have hcs1 : cs1 = cb := by
    cases ri <;> simp only [Prod.mk.injEq] at hc <;> exact hc.2.2.2.symm
  have hsubCb : codeSubset cb cs2 := hcs1 ▸ hsub
  -- Finish from the state `t5` reached after copying the operands, once the
  -- comparison has selected a branch.
  have finish : ∀ (t5 : WordSemStateFiniteExact width C F) (bv : Bool) (i1' : Nat),
      0 < i1' →
      WordSemStateFiniteExact.evaluate (.seq p1 p9) t1 =
        WordSemStateFiniteExact.evaluate (.seq (if bv then a' else b') p9) t5 →
      wordCmpHOL c (evalExp s1 (.var r)) (evalRi s1 ri) = bv →
      stateRel s1 t5 cs2 t0 frame → WordSemStateFiniteExact.getVar 0 t5 = some retVal →
      t5.stack = t1.stack → t5.code = t1.code → i1 = i1' →
      ∃ (t2 : WordSemStateFiniteExact width C F)
        (res : Option (WordSemResult width) × WordSemStateFiniteExact width C F),
        WordSemStateFiniteExact.evaluate (.seq p1 p9) t1 = res ∧
          match (generalizing := false) s2 with
          | .inl s =>
              res = WordSemStateFiniteExact.evaluate (.call none (some n) [0] none) t2 ∧ 0 < i1 ∧
                t2.stack = t1.stack ∧ WordSemStateFiniteExact.getVar 0 t2 = some retVal ∧
                stateRel s t2 cs2 t0 frame ∧ t2.code = t1.code
          | .inr s =>
              res = WordSemStateFiniteExact.evaluate p9 t2 ∧ 0 < i1 ∧
                t2.stack = t1.stack ∧ WordSemStateFiniteExact.getVar 0 t2 = some retVal ∧
                stateRel s t2 cs2 t0 frame ∧ t2.code = t1.code := by
    intro t5 bv i1' hi1' hev hcmp hrel5 hret5 hst5 hcode5 hi1eq
    subst hi1eq
    have hrec5 : ∀ body, rec = some body →
        ∃ (l i : Nat) (cs : CodeAcc width) (p1 : WordLangProgHOL (BitVec width)) (l1 i1 : Nat)
          (cs1 : CodeAcc width),
          compile n l i cs body = (p1, l1, i1, cs1) ∧ 0 < i ∧ syntaxOkAux body ∧
            codeSubset cs1 cs2 ∧ sptLookup n t5.code = some (1, .seq p1 (.return 0 [0])) := by
      rw [hcode5]
      exact hrec
    rw [hcmp] at ih
    cases bv with
    | true =>
      simp only [if_true] at ih hev
      obtain ⟨t2, res, hres, hgoal⟩ := ih n l i cs a' la ia ca cs2 t5 retVal p9
        ⟨ha, hrel5, hi, hsa, codeSubset_trans _ _ _ ⟨hsubB, hsubCb⟩,
          hrec5, fun body h => absurd h (hna body), hret5, hgood⟩
      refine ⟨t2, res, hev.trans hres, ?_⟩
      cases s2 with
      | inl s =>
        obtain ⟨h1, -, h3, h4, h5, h6⟩ := hgoal
        exact ⟨h1, hi1', h3.trans hst5, h4, h5, h6.trans hcode5⟩
      | inr s =>
        obtain ⟨h1, -, h3, h4, h5, h6⟩ := hgoal
        exact ⟨h1, hi1', h3.trans hst5, h4, h5, h6.trans hcode5⟩
    | false =>
      simp only [Bool.false_eq_true, if_false] at ih hev
      obtain ⟨t2, res, hres, hgoal⟩ := ih n la ia ca b' lb ib cb cs2 t5 retVal p9
        ⟨hb, hrel5, by omega, hsb, hsubCb,
          hrec5, fun body h => absurd h (hnb body), hret5, hgood⟩
      refine ⟨t2, res, hev.trans hres, ?_⟩
      cases s2 with
      | inl s =>
        obtain ⟨h1, -, h3, h4, h5, h6⟩ := hgoal
        exact ⟨h1, hi1', h3.trans hst5, h4, h5, h6.trans hcode5⟩
      | inr s =>
        obtain ⟨h1, -, h3, h4, h5, h6⟩ := hgoal
        exact ⟨h1, hi1', h3.trans hst5, h4, h5, h6.trans hcode5⟩
  obtain ⟨t5, i1', hi1', hev, hrel5, hret5, hst5, hcode5, hi1eq⟩ :
      ∃ (t5 : WordSemStateFiniteExact width C F) (i1' : Nat), 0 < i1' ∧
        WordSemStateFiniteExact.evaluate (.seq p1 p9) t1 =
          WordSemStateFiniteExact.evaluate
            (.seq (if wordCmpHOL c (evalExp s1 (.var r)) (evalRi s1 ri) then a' else b') p9) t5 ∧
        stateRel s1 t5 cs2 t0 frame ∧ WordSemStateFiniteExact.getVar 0 t5 = some retVal ∧
        t5.stack = t1.stack ∧ t5.code = t1.code ∧ i1 = i1' := by
    clear finish ih
    cases ri with
    | reg r2 =>
      have hv2 := stateRel_lookup_temp hrel (r := r2) hri
      simp only [Prod.mk.injEq] at hc
      obtain ⟨hp1, -, hi1, -⟩ := hc
      subst hp1
      let t4 := WordSemStateFiniteExact.setVar ib (.word (holFapply s1.regs r)) t1
      let t5 := WordSemStateFiniteExact.setVar (ib + 1) (.word (holFapply s1.regs r2)) t4
      have hev : WordSemStateFiniteExact.evaluate (.seq (seqTemp ib r (seqTemp (ib + 1) r2
            (.ite c ib (.reg (ib + 1)) a' b'))) p9) t1 =
          WordSemStateFiniteExact.evaluate
            (.seq (if wordCmpHOL c (holFapply s1.regs r) (holFapply s1.regs r2) then a' else b')
              p9) t5 := by
        rw [evaluate_seqTemp_live hvr, evaluate_seqTemp_live (t := t4) hv2]
        apply evaluate_seq_ite (x := .word (holFapply s1.regs r))
          (y := .word (holFapply s1.regs r2))
        · simp only [t5, t4, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar]
          rw [sptLookup_sptInsert_ne _ _ _ _ (by omega), sptLookup_sptInsert_same]
        · simp [t5, WordSemStateFiniteExact.getVarImm, WordSemStateFiniteExact.getVar,
            WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
        · rfl
      refine ⟨t5, ib + 2, by omega, ?_, hrel, ?_, rfl, rfl, hi1.symm⟩
      · exact hev
      · simp only [t5, t4]
        rw [getVar_zero_setVar (by omega), getVar_zero_setVar hib0]
        exact hret
    | imm w =>
      simp only [Prod.mk.injEq] at hc
      obtain ⟨hp1, -, hi1, -⟩ := hc
      subst hp1
      let t5 := WordSemStateFiniteExact.setVar ib (.word (holFapply s1.regs r)) t1
      have hev : WordSemStateFiniteExact.evaluate (.seq (seqTemp ib r
            (.ite c ib (.imm w) a' b')) p9) t1 =
          WordSemStateFiniteExact.evaluate
            (.seq (if wordCmpHOL c (holFapply s1.regs r) w then a' else b') p9) t5 := by
        rw [evaluate_seqTemp_live hvr]
        apply evaluate_seq_ite (x := .word (holFapply s1.regs r)) (y := .word w)
        · simp [t5, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
            sptLookup_sptInsert_same]
        · rfl
        · rfl
      refine ⟨t5, ib + 1, by omega, ?_, hrel, ?_, rfl, rfl, hi1.symm⟩
      · exact hev
      · simp only [t5]
        rw [getVar_zero_setVar hib0]
        exact hret

  exact finish t5 _ i1' hi1' hev rfl hrel5 hret5 hst5 hcode5 hi1eq

/-- `Swap` case: the compiled code exchanges the two input array pointers. -/
theorem case_swap (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (r : Option (Mini (BitVec width))) (s : MiniState width) :
    CompileGoal t0 frame β r s .swap
      (.inr (arrayWrite .in1 (s.arrays .in2) (arrayWrite .in2 (s.arrays .in1) s))) := by
  rintro n l i cs p1 l1 i1 cs1 cs2 t1 retVal p9 ⟨hc, hrel, hi, -, -, -, -, hret, -⟩
  rw [compile_swap] at hc
  cases hc
  obtain ⟨hcl, ha, hr, hcode, hdiv, htd, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14⟩ := hrel
  obtain ⟨a1, a2, a3, rest1, rest2, hv1, hv2, hv3, hs1, hs2, hs3⟩ := ha
  have hev : WordSemStateFiniteExact.evaluate
      (.seq (.assign i (.lookup tempIn1)) (.seq (.set tempIn1 (.lookup tempIn2))
        (.set tempIn2 (.var i)))) t1 =
      (none, WordSemStateFiniteExact.setStore tempIn2 (.word a1)
        (WordSemStateFiniteExact.setStore tempIn1 (.word a2)
          (WordSemStateFiniteExact.setVar i (.word a1) t1))) := by
    refine ev_seq (ev_assign (by rw [wordExp_lookup]; exact hv1)) ?_
    refine ev_seq (ev_set (by simp [tempIn1]) (by rw [wordExp_lookup, store_setVar]; exact hv2)) ?_
    exact ev_set (by simp [tempIn2])
      (by rw [wordExp_var, getVar_setStore, getVar_setVar_same])
  refine goal_of_none hev (by omega) rfl ?_ ?_ rfl
  · simp only [WordSemStateFiniteExact.setStore]
    exact (getVar_zero_setVar hi _).trans hret
  · have hlk : ∀ k, (WordSemStateFiniteExact.setStore tempIn2 (.word a1)
        (WordSemStateFiniteExact.setStore tempIn1 (.word a2)
          (WordSemStateFiniteExact.setVar i (.word a1) t1))).store.lookup k =
        if k = tempIn2 then some (.word a1) else if k = tempIn1 then some (.word a2)
        else t1.store.lookup k := fun k => rfl
    refine ⟨hcl, ?_, ?_, hcode, hdiv, htd, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
      ?_, ?_⟩
    · refine ⟨a2, a1, a3, rest2, rest1, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hlk]; simp [tempIn1, tempIn2]
      · rw [hlk]; simp
      · rw [hlk]; simpa [tempIn1, tempIn2, tempOut] using hv3
      · simpa [arrayWrite, Function.update, WordSemStateFiniteExact.setStore,
          WordSemStateFiniteExact.setVar] using hs2
      · simpa [arrayWrite, Function.update, WordSemStateFiniteExact.setStore,
          WordSemStateFiniteExact.setVar] using hs1
      · simpa [arrayWrite, Function.update, WordSemStateFiniteExact.setStore,
          WordSemStateFiniteExact.setVar] using hs3
    · intro a w hw
      obtain ⟨ha25, hl⟩ := hr a w (by simpa [arrayWrite] using hw)
      refine ⟨ha25, ?_⟩
      rw [hlk, if_neg (temp_ne_tempIn2 ha25), if_neg (temp_ne_tempIn1 ha25)]
      exact hl
    · rw [hlk]; simpa [tempIn1, tempIn2, tempOut] using h13
    · intro k hk
      rw [hlk, if_neg (fun h => hk _ (h.trans rfl)), if_neg (fun h => hk _ (h.trans rfl))]
      exact h14 k hk

open Flapjack.Misc.Multiword in
/-- `Mul` case. -/
theorem case_mul (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (r : Option (Mini (BitVec width))) (s : MiniState width) (n1 n2 n3 n4 : Nat)
    (h : n3 ∈ s.regs.dom ∧ n4 ∈ s.regs.dom ∧ n1 ≠ n2) :
    CompileGoal t0 frame β r s (.mul n1 n2 n3 n4)
      (.inr (regWrite n1 (some (singleMul (holFapply s.regs n3) (holFapply s.regs n4) 0).1)
        (regWrite n2 (some (singleMul (holFapply s.regs n3) (holFapply s.regs n4) 0).2) s))) := by
  rintro n l i cs p1 l1 i1 cs1 cs2 t1 retVal p9 ⟨hc, hrel, hi, hsyn, -, -, -, hret, -⟩
  rw [compile_mul] at hc
  cases hc
  have hsyn' : n1 < 25 ∧ n2 < 25 ∧ n3 < 25 ∧ n4 < 25 := by
    simpa [syntaxOk, syntaxOkAux] using hsyn
  obtain ⟨h3, h4, h12⟩ := h
  set x := holFapply s.regs n3
  set y := holFapply s.regs n4
  have hx := stateRel_lookup_temp hrel h3
  have hy := stateRel_lookup_temp hrel h4
  let ta := WordSemStateFiniteExact.setVar (i + 3) (.word y) t1
  let tb := WordSemStateFiniteExact.setVar (i + 2) (.word x) ta
  let tc := WordSemStateFiniteExact.setVar (i + 1) (.word (BitVec.ofNat width (x.toNat * y.toNat)))
    (WordSemStateFiniteExact.setVar i
      (.word (BitVec.ofNat width (x.toNat * y.toNat / 2 ^ width))) tb)
  have hsm : singleMul x y 0 = (BitVec.ofNat width (x.toNat * y.toNat),
      BitVec.ofNat width (x.toNat * y.toNat / 2 ^ width)) := by
    simp only [singleMul, Prod.mk.injEq]
    refine ⟨?_, by simp⟩
    apply BitVec.eq_of_toNat_eq
    simp
  rw [hsm]
  have hinst : WordSemStateFiniteExact.inst (.arith (.longMul i (i + 1) (i + 2) (i + 3))) tb =
      some tc := by
    simp only [WordSemStateFiniteExact.inst, WordSemStateFiniteExact.getVars, tb, ta]
    rw [getVar_setVar_same, getVar_setVar_ne _ _ (show i + 2 ≠ i + 3 by omega), getVar_setVar_same]
  have hev := ev_seqTemp (k := i + 3) hy
    (ev_seqTemp (k := i + 2) (by rw [store_setVar]; exact hx)
      (ev_seq (ev_inst hinst)
        (ev_seq (ev_set (temp_not_special (BitVec.ofNat 5 n2)) (by
            rw [wordExp_var, getVar_setVar_ne _ _ (Nat.succ_ne_self i), getVar_setVar_same]))
          (ev_set (temp_not_special (BitVec.ofNat 5 n1)) (by
            rw [wordExp_var, getVar_setStore, getVar_setVar_same])))))
  refine goal_of_none hev (by omega) rfl ?_ ?_ rfl
  · rw [getVar_setStore, getVar_setStore]
    simp only [tc, tb, ta]
    rw [getVar_zero_setVar (by omega), getVar_zero_setVar hi, getVar_zero_setVar (by omega),
      getVar_zero_setVar (by omega)]
    exact hret
  · exact stateRel_write n1 _ hsyn'.1 (stateRel_write n2 _ hsyn'.2.1
      (show stateRel s tc cs2 t0 frame from hrel))

open Flapjack.Misc.Multiword in
/-- `Div` case: the compiled code calls the division stub described by
`div_code_assum`. -/
theorem case_div (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (r : Option (Mini (BitVec width))) (s : MiniState width) (n1 n2 n3 n4 n5 : Nat)
    (h : n3 ∈ s.regs.dom ∧ n4 ∈ s.regs.dom ∧ n5 ∈ s.regs.dom ∧ n1 ≠ n2 ∧
      singleDivPre (holFapply s.regs n3) (holFapply s.regs n4) (holFapply s.regs n5)) :
    CompileGoal t0 frame β r s (.div n1 n2 n3 n4 n5)
      (.inr (regWrite n1
        (some (singleDiv (holFapply s.regs n3) (holFapply s.regs n4) (holFapply s.regs n5)).1)
        (regWrite n2
          (some (singleDiv (holFapply s.regs n3) (holFapply s.regs n4) (holFapply s.regs n5)).2)
          s))) := by
  rintro n l i cs p1 l1 i1 cs1 cs2 t1 retVal p9 ⟨hc, hrel, hi, hsyn, -, -, -, hret, -⟩
  rw [compile_div] at hc
  cases hc
  have hsyn' : n1 < 25 ∧ n2 < 25 ∧ n3 < 25 ∧ n4 < 25 ∧ n5 < 25 := by
    simpa [syntaxOk, syntaxOkAux] using hsyn
  obtain ⟨h3, h4, h5, h12, hpre⟩ := h
  set w3 := holFapply s.regs n3
  set w4 := holFapply s.regs n4
  set w5 := holFapply s.regs n5
  have hx3 := stateRel_lookup_temp hrel h3
  have hx4 := stateRel_lookup_temp hrel h4
  have hx5 := stateRel_lookup_temp hrel h5
  rcases hsd : singleDiv w3 w4 w5 with ⟨q, rm⟩
  simp only
  obtain ⟨max, hdc⟩ := hrel.2.2.2.2.1 t1 n l i (i + 1) (i + 2) (i + 3) (i + 4) w3 w4 w5 retVal
    ⟨by omega, by omega, by omega, by omega, by omega, by simp, rfl, hrel.2.2.2.2.2.1, hret, hpre⟩
  rw [hsd] at hdc
  simp only at hdc
  let t3 : WordSemStateFiniteExact width C F :=
    { t1 with permute := (fun n => t1.permute (n + 1)), locals := .ln, stackMax := max }
  let td := WordSemStateFiniteExact.setVar 0 retVal
    (WordSemStateFiniteExact.setVar (i + 1) (.word rm)
      (WordSemStateFiniteExact.setVar i (.word q)
        (WordSemStateFiniteExact.setStore (.temp (BitVec.ofNat 5 28)) (.word rm) t3)))
  have hin : WordSemStateFiniteExact.setVar (i + 2) (.word w3)
      (WordSemStateFiniteExact.setVar (i + 3) (.word w4)
        (WordSemStateFiniteExact.setVar (i + 4) (.word w5) t1)) =
      { t1 with locals := sptInsert (i + 2) (.word w3) (sptInsert (i + 3) (.word w4)
          (sptInsert (i + 4) (.word w5) t1.locals)) } := rfl
  have hev := ev_seqTemp (k := i + 4) hx5
    (ev_seqTemp (k := i + 3) (by rw [store_setVar]; exact hx4)
      (ev_seqTemp (k := i + 2) (by rw [store_setVar, store_setVar]; exact hx3)
        (ev_seq (by rw [hin]; exact hdc)
          (ev_seq (ev_set (temp_not_special (BitVec.ofNat 5 n1)) (v := .word q) (by
              rw [wordExp_var]
              rw [getVar_setVar_ne _ _ (show 0 ≠ i by omega),
                getVar_setVar_ne _ _ (show i + 1 ≠ i by omega), getVar_setVar_same]))
            (ev_set (temp_not_special (BitVec.ofNat 5 n2)) (v := .word rm) (by
              rw [wordExp_var, getVar_setStore]
              rw [getVar_setVar_ne _ _ (show 0 ≠ i + 1 by omega), getVar_setVar_same]))))))
  refine goal_of_none hev (by omega) rfl ?_ ?_ rfl
  · rw [getVar_setStore, getVar_setStore]
    exact getVar_setVar_same _ _ _
  · rw [setStore_comm _ _ _ (fun he => h12 (temp_ofNat_inj (by omega) (by omega) he).symm)]
    have hb : stateRel s td cs2 t0 frame :=
      stateRel_setStore_free (t := t3) 28 _ (by omega) (by omega) hrel
    exact stateRel_write n1 q hsyn'.1 (stateRel_write n2 rm hsyn'.2.1 hb)

theorem riStoreValue_of_pre {s : MiniState width} {t t0 : WordSemStateFiniteExact width C F}
    {cs : β × List (CodeEntry width)} {frame : ((BitVec width × WordLocW width) → Prop) → Prop}
    {ri : WordRegImm (BitVec width)} (h : stateRel s t cs t0 frame) (hri : evalRiPre s ri) :
    riStoreValue t ri = some (.word (evalRi s ri)) := by
  cases ri with
  | reg r => exact stateRel_lookup_temp h hri
  | imm w => rfl

theorem ev_addCarry_tail {tb : WordSemStateFiniteExact width C F} {i n1 n2 : Nat}
    {x y c : BitVec width}
    (hx : WordSemStateFiniteExact.getVar (i + 2) tb = some (.word x))
    (hy : WordSemStateFiniteExact.getVar (i + 3) tb = some (.word y))
    (hc : WordSemStateFiniteExact.getVar (i + 4) tb = some (.word c)) :
    WordSemStateFiniteExact.evaluate
      (.seq (.inst (.arith (.addCarry (i + 1) (i + 2) (i + 3) (i + 4))))
        (.seq (.set (.temp (BitVec.ofNat 5 n1)) (.var (i + 1)))
          (.set (.temp (BitVec.ofNat 5 n2)) (.var (i + 4))))) tb =
      (none, WordSemStateFiniteExact.setStore (.temp (BitVec.ofNat 5 n2))
        (.word (wordAddCarryHOL x y c).2)
        (WordSemStateFiniteExact.setStore (.temp (BitVec.ofNat 5 n1))
          (.word (wordAddCarryHOL x y c).1)
          (WordSemStateFiniteExact.setVar (i + 4) (.word (wordAddCarryHOL x y c).2)
            (WordSemStateFiniteExact.setVar (i + 1) (.word (wordAddCarryHOL x y c).1) tb)))) := by
  have hinst : WordSemStateFiniteExact.inst (.arith (.addCarry (i + 1) (i + 2) (i + 3) (i + 4))) tb =
      some (WordSemStateFiniteExact.setVar (i + 4) (.word (wordAddCarryHOL x y c).2)
            (WordSemStateFiniteExact.setVar (i + 1) (.word (wordAddCarryHOL x y c).1) tb)) := by
    simp only [WordSemStateFiniteExact.inst, WordSemStateFiniteExact.getVars, hx, hy, hc]
  refine ev_seq (ev_inst hinst) (ev_seq (ev_set (temp_not_special _) ?_)
    (ev_set (temp_not_special _) ?_))
  · rw [wordExp_var, getVar_setVar_ne _ _ (show i + 4 ≠ i + 1 by omega), getVar_setVar_same]
  · rw [wordExp_var, getVar_setStore, getVar_setVar_same]

open Flapjack.Misc.Multiword in
/-- Shared tail of the `Add` and `Sub` cases, once the three operands are in
locals `i + 2`, `i + 3`, `i + 4`. -/
theorem addsub_finish {t0 t1 tb : WordSemStateFiniteExact width C F}
    {frame : ((BitVec width × WordLocW width) → Prop) → Prop} {cs2 : β × List (CodeEntry width)}
    {s : MiniState width} {p1 p9 : WordLangProgHOL (BitVec width)} {i n1 n2 : Nat}
    {x y c r1 r2 : BitVec width} {retVal : WordLocW width}
    (hpre : ∀ res, WordSemStateFiniteExact.evaluate
      (.seq (.inst (.arith (.addCarry (i + 1) (i + 2) (i + 3) (i + 4))))
        (.seq (.set (.temp (BitVec.ofNat 5 n1)) (.var (i + 1)))
          (.set (.temp (BitVec.ofNat 5 n2)) (.var (i + 4))))) tb = res →
      WordSemStateFiniteExact.evaluate p1 t1 = res)
    (hx : WordSemStateFiniteExact.getVar (i + 2) tb = some (.word x))
    (hy : WordSemStateFiniteExact.getVar (i + 3) tb = some (.word y))
    (hc : WordSemStateFiniteExact.getVar (i + 4) tb = some (.word c))
    (hsum : singleAddWord x y c = (r1, r2))
    (hrel : stateRel s tb cs2 t0 frame) (hret : WordSemStateFiniteExact.getVar 0 tb = some retVal)
    (hst : tb.stack = t1.stack) (hcode : tb.code = t1.code) (hi : 0 < i)
    (h1 : n1 < 25) (h2 : n2 < 25) (h12 : n1 ≠ n2) :
    ∃ (t2 : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width) × WordSemStateFiniteExact width C F),
      WordSemStateFiniteExact.evaluate (.seq p1 p9) t1 = res ∧
        res = WordSemStateFiniteExact.evaluate p9 t2 ∧ 0 < i + 5 ∧
          t2.stack = t1.stack ∧ WordSemStateFiniteExact.getVar 0 t2 = some retVal ∧
          stateRel (regWrite n1 (some r1) (regWrite n2 (some r2) s)) t2 cs2 t0 frame ∧
          t2.code = t1.code := by
  have hev := hpre _ (ev_addCarry_tail (n1 := n1) (n2 := n2) hx hy hc)
  rw [wordAddCarry_eq_singleAddWord, hsum] at hev
  refine goal_of_none hev (by omega) hst ?_ ?_ hcode
  · rw [getVar_setStore, getVar_setStore, getVar_zero_setVar (by omega),
      getVar_zero_setVar (by omega)]
    exact hret
  · rw [setStore_comm _ _ _ (fun he => h12 (temp_ofNat_inj (by omega) (by omega) he).symm)]
    exact stateRel_write n1 r1 h1 (stateRel_write n2 r2 h2
      (show stateRel s (WordSemStateFiniteExact.setVar (i + 4) (.word r2)
        (WordSemStateFiniteExact.setVar (i + 1) (.word r1) tb)) cs2 t0 frame from hrel))

open Flapjack.Misc.Multiword in
/-- `Add` case. -/
theorem case_add (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (n1 n2 n3 : Nat) (n4 n5 : WordRegImm (BitVec width))
    (r : Option (Mini (BitVec width))) (s : MiniState width) (r1 r2 : BitVec width)
    (h : n3 ∈ s.regs.dom ∧ evalRiPre s n4 ∧ evalRiPre s n5 ∧
      (evalRi s n5 ≠ 0 → evalRi s n5 = 1) ∧ n1 ≠ n2 ∧
      singleAddWord (holFapply s.regs n3) (evalRi s n4) (evalRi s n5) = (r1, r2)) :
    CompileGoal t0 frame β r s (.add n1 n2 n3 n4 n5)
      (.inr (regWrite n1 (some r1) (regWrite n2 (some r2) s))) := by
  rintro n l i cs p1 l1 i1 cs1 cs2 t1 retVal p9 ⟨hc, hrel, hi, hsyn, -, -, -, hret, -⟩
  rw [compile_add] at hc
  cases hc
  have hsyn' : n1 < 25 ∧ n2 < 25 ∧ n3 < 25 ∧ (∀ r, n4 = .reg r → r < 25) ∧
      (∀ r, n5 = .reg r → r < 25) := by
    simpa [syntaxOk, syntaxOkAux] using hsyn
  obtain ⟨h3, h4, h5, -, h12, hsum⟩ := h
  let ta := WordSemStateFiniteExact.setVar (i + 4) (.word (evalRi s n5)) t1
  let tb' := WordSemStateFiniteExact.setVar (i + 3) (.word (evalRi s n4)) ta
  let tb := WordSemStateFiniteExact.setVar (i + 2) (.word (holFapply s.regs n3)) tb'
  exact addsub_finish (tb := tb)
    (fun res hres => ev_seqTempImm (riStoreValue_of_pre hrel h5)
      (ev_seqTempImm (riStoreValue_of_pre (t := ta) hrel h4)
        (ev_seqTemp (stateRel_lookup_temp (t := tb') hrel h3) hres)))
    (getVar_setVar_same _ _ _)
    (by simp only [tb]; rw [getVar_setVar_ne _ _ (show i + 2 ≠ i + 3 by omega),
      getVar_setVar_same])
    (by simp only [tb, tb']; rw [getVar_setVar_ne _ _ (show i + 2 ≠ i + 4 by omega),
      getVar_setVar_ne _ _ (show i + 3 ≠ i + 4 by omega), getVar_setVar_same])
    hsum hrel
    (by simp only [tb, tb', ta]; rw [getVar_zero_setVar (by omega),
      getVar_zero_setVar (by omega), getVar_zero_setVar (by omega)]; exact hret)
    rfl rfl hi hsyn'.1 hsyn'.2.1 h12

open Flapjack.Misc.Multiword in
/-- `Sub` case. -/
theorem case_sub (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (r : Option (Mini (BitVec width))) (s : MiniState width)
    (n1 n2 n3 : Nat) (n4 n5 : WordRegImm (BitVec width)) (r1 r2 : BitVec width)
    (h : n3 ∈ s.regs.dom ∧ evalRiPre s n4 ∧ evalRiPre s n5 ∧
      (evalRi s n5 ≠ 0 → evalRi s n5 = 1) ∧ n1 ≠ n2 ∧
      singleSubWord (holFapply s.regs n3) (evalRi s n4) (evalRi s n5) = (r1, r2)) :
    CompileGoal t0 frame β r s (.sub n1 n2 n3 n4 n5)
      (.inr (regWrite n1 (some r1) (regWrite n2 (some r2) s))) := by
  rintro n l i cs p1 l1 i1 cs1 cs2 t1 retVal p9 ⟨hc, hrel, hi, hsyn, -, -, -, hret, -⟩
  rw [compile_sub] at hc
  cases hc
  have hsyn' : n1 < 25 ∧ n2 < 25 ∧ n3 < 25 ∧ (∀ r, n4 = .reg r → r < 25) ∧
      (∀ r, n5 = .reg r → r < 25) := by
    simpa [syntaxOk, syntaxOkAux] using hsyn
  obtain ⟨h3, h4, h5, -, h12, hsum⟩ := h
  have hsum' : singleAddWord (holFapply s.regs n3) (~~~(evalRi s n4)) (evalRi s n5) = (r1, r2) :=
    hsum
  let ta := WordSemStateFiniteExact.setVar (i + 4) (.word (evalRi s n5)) t1
  let tb' := WordSemStateFiniteExact.setVar (i + 3) (.word (~~~(evalRi s n4))) ta
  let tb := WordSemStateFiniteExact.setVar (i + 2) (.word (holFapply s.regs n3)) tb'
  exact addsub_finish (tb := tb)
    (fun res hres => ev_seqTempImm (riStoreValue_of_pre hrel h5)
      (ev_seqTempImmNot (riStoreValue_of_pre (t := ta) hrel h4)
        (ev_seqTemp (stateRel_lookup_temp (t := tb') hrel h3) hres)))
    (getVar_setVar_same _ _ _)
    (by simp only [tb]; rw [getVar_setVar_ne _ _ (show i + 2 ≠ i + 3 by omega),
      getVar_setVar_same])
    (by simp only [tb, tb']; rw [getVar_setVar_ne _ _ (show i + 2 ≠ i + 4 by omega),
      getVar_setVar_ne _ _ (show i + 3 ≠ i + 4 by omega), getVar_setVar_same])
    hsum' hrel
    (by simp only [tb, tb', ta]; rw [getVar_zero_setVar (by omega),
      getVar_zero_setVar (by omega), getVar_zero_setVar (by omega)]; exact hret)
    rfl rfl hi hsyn'.1 hsyn'.2.1 h12

/-- `LoopBody` case for a body that finishes. -/
theorem case_loopBodyReturn (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (r : Option (Mini (BitVec width))) (s1 : MiniState width) (p : Mini (BitVec width))
    (s2 : MiniState width) (ih : CompileGoal t0 frame β r s1 p (.inr s2)) :
    CompileGoal t0 frame β r s1 (.loopBody p) (.inr s2) := by
  rintro n l i cs p1 l1 i1 cs1 cs2 t1 retVal p9
    ⟨hc, hrel, hi, hsyn, hsub, hrec, -, hret, hgood⟩
  rw [compile_loopBody] at hc
  have hsyn' : syntaxOkAux p := by simpa [syntaxOk] using hsyn
  obtain ⟨hs, hnb⟩ := syntaxOk_of_aux hsyn'
  exact ih n l i cs p1 l1 i1 cs1 cs2 t1 retVal p9
    ⟨hc, hrel, hi, hs, hsub, hrec, fun body h => absurd h (hnb body), hret, hgood⟩

/-- A `Return` never finishes normally, so a tail call to code ending in one
returns that result. -/
theorem evaluate_return_not_bad (t : WordSemStateFiniteExact width C F) (n : Nat) (ms : List Nat) :
    wordSemBadFunReturn (WordSemStateFiniteExact.evaluate (.return n ms) t).1 = false := by
  rw [evaluate_return]
  split <;> rfl

theorem getVar_zero_callEnv (t : WordSemStateFiniteExact width C F) (v : WordLocW width)
    (ss : Option Nat) :
    WordSemStateFiniteExact.getVar 0 (WordSemStateFiniteExact.callEnv [v] ss t) = some v := by
  simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.callEnv, sptFromList2,
    sptInsert, sptLookup]

theorem stateRel_callEnv_decClock {s : MiniState width} {t t0 : WordSemStateFiniteExact width C F}
    {cs : β × List (CodeEntry width)} {frame : ((BitVec width × WordLocW width) → Prop) → Prop}
    (args : List (WordLocW width)) (ss : Option Nat) (h : stateRel s t cs t0 frame) :
    stateRel (decClock s)
      (WordSemStateFiniteExact.callEnv args ss (WordSemStateFiniteExact.decClock t)) cs t0 frame := by
  obtain ⟨hc, rest⟩ := h
  exact ⟨by simp [decClock, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock, hc],
    rest⟩

/-- `LoopBody` case for a body that continues: the compiled body ends in a
tail call back to itself. -/
theorem case_loopBodyContinue (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (r : Option (Mini (BitVec width))) (s1 s2 s3 : MiniState width) (p : Mini (BitVec width))
    (hclock : s2.clock ≠ 0)
    (ih1 : CompileGoal t0 frame β r s1 p (.inl s2))
    (ih2 : CompileGoal t0 frame β r (decClock s2) (.loopBody p) (.inr s3)) :
    CompileGoal t0 frame β r s1 (.loopBody p) (.inr s3) := by
  rintro n l i cs p1 l1 i1 cs1 cs2 t1 retVal p9
    ⟨hc, hrel, hi, hsyn, hsub, hrec, hlb, hret, hgood⟩
  obtain ⟨hp9, hlook⟩ := hlb p rfl
  have hc' := hc
  rw [compile_loopBody] at hc'
  have hsyn' : syntaxOkAux p := by simpa [syntaxOk] using hsyn
  obtain ⟨hs, hnb⟩ := syntaxOk_of_aux hsyn'
  obtain ⟨t2, res, hres, hcall, hi1, hst2, hret2, hrel2, hcode2⟩ :=
    ih1 n l i cs p1 l1 i1 cs1 cs2 t1 retVal p9
      ⟨hc', hrel, hi, hs, hsub, hrec, fun body h => absurd h (hnb body), hret, hgood⟩
  let ss := sptLookup n t2.stackSize
  let t3 := WordSemStateFiniteExact.callEnv [retVal] ss (WordSemStateFiniteExact.decClock t2)
  have hrec3 : ∀ body, r = some body →
      ∃ (l i : Nat) (cs : CodeAcc width) (p1 : WordLangProgHOL (BitVec width)) (l1 i1 : Nat)
        (cs1 : CodeAcc width),
        compile n l i cs body = (p1, l1, i1, cs1) ∧ 0 < i ∧ syntaxOkAux body ∧
          codeSubset cs1 cs2 ∧ sptLookup n t3.code = some (1, .seq p1 (.return 0 [0])) := by
    have : t3.code = t1.code := hcode2
    rw [this]
    exact hrec
  have hlook3 : sptLookup n t3.code = some (1, .seq p1 (.return 0 [0])) := by
    have : t3.code = t1.code := hcode2
    rw [this]
    exact hlook
  obtain ⟨t4, res4, hres4, hret4, hi14, hst4, hretv4, hrel4, hcode4⟩ :=
    ih2 n l i cs p1 l1 i1 cs1 cs2 t3 retVal (.return 0 [0])
      ⟨hc, stateRel_callEnv_decClock [retVal] ss hrel2, hi, hsyn, hsub, hrec3,
        fun _ _ => ⟨rfl, hlook3⟩, getVar_zero_callEnv _ _ _, hgood⟩
  have hclock2 : t2.clock ≠ 0 := by rw [← hrel2.1]; exact hclock
  have hcallEq : WordSemStateFiniteExact.evaluate (.call none (some n) [0] none) t2 =
      WordSemStateFiniteExact.evaluate (.return 0 [0]) t4 := by
    rw [evaluate_call]
    have hgv : WordSemStateFiniteExact.getVars [0] t2 = some [retVal] := by
      simp [WordSemStateFiniteExact.getVars, hret2]
    have hfc : wordSemFindCode (some n) [retVal] t2.code t2.stackSize =
        some ([retVal], .seq p1 (.return 0 [0]), ss) := by
      have : t2.code = t1.code := hcode2
      simp [wordSemFindCode, this, hlook, ss]
    simp only [hgv, wordSemBadDestArgs, Bool.false_eq_true, if_false, wordSemAddRetLoc]
    rw [hfc]
    simp only [hclock2, ite_false]
    have h3 : WordSemStateFiniteExact.evaluate (.seq p1 (.return 0 [0])) t3 =
        WordSemStateFiniteExact.evaluate (.return 0 [0]) t4 := by rw [hres4, hret4]
    rw [show WordSemStateFiniteExact.callEnv [retVal] ss (WordSemStateFiniteExact.decClock t2) = t3
      from rfl, h3]
    rcases hr : WordSemStateFiniteExact.evaluate (.return 0 [0]) t4 with ⟨rr, ts⟩
    have hnb := evaluate_return_not_bad t4 0 [0]
    rw [hr] at hnb
    simp [hnb]
  refine ⟨t4, _, rfl, ?_, hi1, ?_, hretv4, hrel4, ?_⟩
  · rw [hres, hcall, hcallEq, hp9]
  · rw [hst4]
    show t2.stack = t1.stack
    exact hst2
  · rw [hcode4]; exact hcode2

theorem stateRel_loopEntry {s : MiniState width} {t t0 : WordSemStateFiniteExact width C F}
    {cs : β × List (CodeEntry width)} {frame : ((BitVec width × WordLocW width) → Prop) → Prop}
    (args : List (WordLocW width)) (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (h : stateRel s t cs t0 frame) :
    stateRel (decClock s)
      (WordSemStateFiniteExact.callEnv args ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock t))) cs t0 frame := by
  obtain ⟨hc, rest⟩ := h
  exact ⟨by simp [decClock, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
    WordSemStateFiniteExact.pushEnv, hc], rest⟩

/-- `Loop` case: the loop compiles to a call of its installed body. -/
theorem case_loop (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (r : Option (Mini (BitVec width))) (s1 : MiniState width) (p : Mini (BitVec width))
    (vs : List Nat) (s2 : MiniState width) (rec : Bool) (hclock : s1.clock ≠ 0)
    (ih : CompileGoal t0 frame β (if rec then some p else none) (deleteVars vs (decClock s1))
      (.loopBody p) (.inr s2)) :
    CompileGoal t0 frame β r s1 (.loop rec vs p) (.inr s2) := by
  rintro n l i cs p1 l1 i1 cs1 cs2 t1 retVal p9 ⟨hc, hrel, hi, hsyn, hsub, -, -, hret, hgood⟩
  have hsynP : syntaxOkAux p := by simpa [syntaxOk, syntaxOkAux] using hsyn
  obtain ⟨y, hp1, hi1, hcomp⟩ : ∃ y,
      p1 = .call (some ([i], (.ls (), .ln), .skip, n, l)) (some y) [] none ∧ i1 = i + 1 ∧
        hasCompiledHOL p cs1 = .inl y := by
    rw [compile_loop] at hc
    cases hcs : hasCompiled p cs with
    | inl existing =>
      rw [hcs] at hc
      simp only [Prod.mk.injEq] at hc
      obtain ⟨h1, -, h3, h4⟩ := hc
      subst h4
      exact ⟨existing, h1.symm, h3.symm, by rw [← hasCompiled_eq_HOL]; exact hcs⟩
    | inr index =>
      rcases hb : compile index 2 1 (codeAccNext cs) p with ⟨body', lb, ib, cb⟩
      rw [hcs] at hc
      dsimp only at hc
      rw [hb] at hc
      simp only [Prod.mk.injEq] at hc
      obtain ⟨h1, -, h3, h4⟩ := hc
      subst h4
      refine ⟨index, h1.symm, h3.symm, ?_⟩
      rw [← hasCompiled_eq_HOL]
      simp [hasCompiled, install, List.lookup]
  obtain ⟨p1', l1', i1', cs', cs1', hcomp', hsub', hlook⟩ :=
    has_compiled_lemma s1 t1 cs2 t0 frame p cs1 y ⟨hrel, hcomp, hsub⟩
  have hclock1 : t1.clock ≠ 0 := by rw [← hrel.1]; exact hclock
  let t5 := WordSemStateFiniteExact.callEnv [.loc n l] (sptLookup y t1.stackSize)
    (WordSemStateFiniteExact.pushEnv (.ls retVal, .ln) none (WordSemStateFiniteExact.decClock t1))
  have hrel5 : stateRel (deleteVars vs (decClock s1)) t5 cs2 t0 frame :=
    stateRel_delete_vars vs _ _ _ _ _ (stateRel_loopEntry _ _ _ hrel)
  obtain ⟨t2', res, hres, hres2, -, hst, hretv, hrel2, hcode2⟩ :=
    ih y 2 1 cs' p1' l1' i1' cs1' cs2 t5 (.loc n l) (.return 0 [0])
      ⟨by rw [compile_loopBody]; exact hcomp', hrel5, by omega, by simpa [syntaxOk] using hsynP,
        hsub', fun body hb => by
          cases rec
          · simp at hb
          · simp only [if_true, Option.some.injEq] at hb
            subst hb
            exact ⟨2, 1, cs', p1', l1', i1', cs1', hcomp', by omega, hsynP, hsub', hlook⟩,
        fun _ _ => ⟨rfl, hlook⟩, getVar_zero_callEnv _ _ _, hgood⟩
  have hev := evaluate_loopCall (p9 := p9) hi hret hlook hclock1 (hres.trans hres2) hretv hst
  subst hp1 hi1
  refine ⟨loopFrame t2' i n l retVal t1.stack t1.localsSize, _, hev, rfl, by omega, rfl,
    getVar_zero_loopFrame _ hi _ _ _, hrel2, ?_⟩
  show t2'.code = t1.code
  exact hcode2

/-- An element read from a word list that is the first factor of a framed
heap assertion. -/
theorem wordList_read_first {a : BitVec width} {xs : List (WordLocW width)}
    {q r : ((BitVec width × WordLocW width) → Prop) → Prop}
    {m : BitVec width → WordLocW width} {dm : BitVec width → Bool} {k : Nat}
    (hk : k < xs.length)
    (h : SetSep.star (SetSep.star (Misc.wordList a xs) q) r (SetSep.fun2Set (m, fun x => dm x = true))) :
    m (a + Compiler.Backend.StackRemove.bytesInWord width * BitVec.ofNat width k) = xs[k] ∧
      dm (a + Compiler.Backend.StackRemove.bytesInWord width * BitVec.ofNat width k) = true := by
  rcases h with ⟨left, right, outer, ⟨first, middle, inner, listHeap, _⟩, _⟩
  have member := Compiler.Backend.StackRemove.StackHeap.wordListNth a xs first k hk listHeap
  have graph : SetSep.fun2Set (m, fun x => dm x = true)
      (a + Compiler.Backend.StackRemove.bytesInWord width * BitVec.ofNat width k, xs[k]) := by
    rw [← outer.1]
    refine Or.inl ?_
    rw [← inner.1]
    exact Or.inl member
  exact (SetSep.fun2SetThm _ _ _ _).mp graph

/-- An element read from a word list that is the second factor of a framed
heap assertion. -/
theorem wordList_read_second {a b : BitVec width} {xs ys : List (WordLocW width)}
    {r : ((BitVec width × WordLocW width) → Prop) → Prop}
    {m : BitVec width → WordLocW width} {dm : BitVec width → Bool} {k : Nat}
    (hk : k < ys.length)
    (h : SetSep.star (SetSep.star (Misc.wordList a xs) (Misc.wordList b ys)) r
      (SetSep.fun2Set (m, fun x => dm x = true))) :
    m (b + Compiler.Backend.StackRemove.bytesInWord width * BitVec.ofNat width k) = ys[k] ∧
      dm (b + Compiler.Backend.StackRemove.bytesInWord width * BitVec.ofNat width k) = true := by
  rcases h with ⟨left, right, outer, ⟨first, middle, inner, _, listHeap⟩, _⟩
  have member := Compiler.Backend.StackRemove.StackHeap.wordListNth b ys middle k hk listHeap
  have graph : SetSep.fun2Set (m, fun x => dm x = true)
      (b + Compiler.Backend.StackRemove.bytesInWord width * BitVec.ofNat width k, ys[k]) := by
    rw [← outer.1]
    refine Or.inl ?_
    rw [← inner.1]
    exact Or.inr member
  exact (SetSep.fun2SetThm _ _ _ _).mp graph

/-- The base register of an array, as `SeqIndex` selects it. -/
def arrayBase : Address → WordStoreHOL
  | .out => tempOut
  | .in2 => tempIn2
  | .in1 => tempIn1

/-- Reading an array element through its base temporary. -/
theorem arrayRel_read {arr : Address → List (BitVec width)} {m : BitVec width → WordLocW width}
    {dm : BitVec width → Bool} {frame : ((BitVec width × WordLocW width) → Prop) → Prop}
    {store : WordStoreHOL → Option (WordLocW width)}
    (h : arrayRel arr (store tempIn1) (store tempIn2) (store tempOut) m dm frame)
    (a : Address) (k : Nat) (hk : k < (arr a).length) :
    ∃ base, store (arrayBase a) = some (.word base) ∧
      m (base + Compiler.Backend.StackRemove.bytesInWord width * BitVec.ofNat width k) =
        .word ((arr a)[k]) ∧
      dm (base + Compiler.Backend.StackRemove.bytesInWord width * BitVec.ofNat width k) = true := by
  obtain ⟨a1, a2, a3, rest1, rest2, h1, h2, h3, s1, s2, s3⟩ := h
  cases a with
  | in1 =>
    have := wordList_read_first (k := k) (by simpa using hk) s1
    exact ⟨a1, h1, by simpa using this.1, this.2⟩
  | in2 =>
    have := wordList_read_first (k := k) (by simpa using hk) s2
    exact ⟨a2, h2, by simpa using this.1, this.2⟩
  | out =>
    have := wordList_read_second (k := k) (by simpa using hk) s1
    exact ⟨a3, h3, by simpa using this.1, this.2⟩

/-- The `SeqIndex` address computation. -/
theorem wordExp_index {t : WordSemStateFiniteExact width C F} {a : Address} {r : Nat}
    {base w : BitVec width} (hgood : goodDimindex width)
    (hb : t.store.lookup (arrayBase a) = some (.word base))
    (hw : t.store.lookup (.temp (BitVec.ofNat 5 r)) = some (.word w)) :
    WordSemStateFiniteExact.wordExp t (.op .add [.lookup (arrayBase a),
      .shift .lsl (.lookup (.temp (BitVec.ofNat 5 r)))
        (.const (BitVec.ofNat width (wordShiftAmount width)))]) =
      some (.word (base + Compiler.Backend.StackRemove.bytesInWord width *
        BitVec.ofNat width w.toNat)) := by
  have hsh : (BitVec.ofNat width (wordShiftAmount width)).toNat = wordShiftAmount width % 2 ^ width := by
    simp
  have hrange : ¬ (wordShiftAmount width % 2 ^ width ≠ 0 ∧
      width ≤ wordShiftAmount width % 2 ^ width) := by
    rcases hgood with h | h <;> subst h <;> simp [wordShiftAmount]
  have hmul := shiftEqBytesInWord w hgood
  rw [WordSemStateFiniteExact.wordExp]
  simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore, hb, hw, theWords,
    wordShiftHOL, hrange, hsh, hmul, wordOpHOL, wordOp, BitVec.mul_comm]

/-- `Load` case. -/
theorem case_load (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (rec : Option (Mini (BitVec width))) (s : MiniState width) (r i' : Nat) (a : Address)
    (w : BitVec width) (h : s.regs.lookup i' = some w ∧ w.toNat < (s.arrays a).length) :
    CompileGoal t0 frame β rec s (.load r i' a)
      (.inr (regWrite r (some (holEl w.toNat (s.arrays a))) s)) := by
  rintro n l i cs p1 l1 i1 cs1 cs2 t1 retVal p9 ⟨hc, hrel, hi, hsyn, -, -, -, hret, hgood⟩
  rw [compile_load] at hc
  cases hc
  have hsyn' : r < 25 ∧ i' < 25 := by simpa [syntaxOk, syntaxOkAux] using hsyn
  obtain ⟨hlk, hbound⟩ := h
  have hw := (hrel.2.2.1 i' w hlk).2
  obtain ⟨base, hb, hm, hdm⟩ := arrayRel_read hrel.2.1 a w.toNat hbound
  have hbase : t1.store.lookup (arrayBase a) = some (.word base) := by
    cases a <;> exact hb
  have hel : holEl w.toNat (s.arrays a) = (s.arrays a)[w.toNat] := holEl_eq_getElem _ _ hbound
  rw [hel]
  have hseq : seqIndex i i' a (.seq (.assign (i + 1) (.load (.var i)))
      (.set (.temp (BitVec.ofNat 5 r)) (.var (i + 1)))) =
      .seq (.assign i (.op .add [.lookup (arrayBase a),
        .shift .lsl (.lookup (.temp (BitVec.ofNat 5 i')))
          (.const (BitVec.ofNat width (wordShiftAmount width)))]))
        (.seq (.assign (i + 1) (.load (.var i))) (.set (.temp (BitVec.ofNat 5 r)) (.var (i + 1)))) := by
    cases a <;> rfl
  have hev : WordSemStateFiniteExact.evaluate (seqIndex i i' a (.seq (.assign (i + 1) (.load (.var i)))
      (.set (.temp (BitVec.ofNat 5 r)) (.var (i + 1))))) t1 =
      (none, WordSemStateFiniteExact.setStore (.temp (BitVec.ofNat 5 r)) (.word ((s.arrays a)[w.toNat]))
        (WordSemStateFiniteExact.setVar (i + 1) (.word ((s.arrays a)[w.toNat]))
          (WordSemStateFiniteExact.setVar i (.word (base +
            Compiler.Backend.StackRemove.bytesInWord width * BitVec.ofNat width w.toNat)) t1))) := by
    rw [hseq]
    refine ev_seq (ev_assign (wordExp_index hgood hbase hw)) (ev_seq (ev_assign ?_)
      (ev_set (temp_not_special _) ?_))
    · simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hm hdm
      simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
        WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same, WordSemStateFiniteExact.memLoad,
        hdm, hm]
    · rw [wordExp_var, getVar_setVar_same]
  refine goal_of_none hev (by omega) rfl ?_ ?_ rfl
  · rw [getVar_setStore, getVar_zero_setVar (by omega), getVar_zero_setVar hi]
    exact hret
  · exact stateRel_write r _ hsyn'.1 (show stateRel s _ cs2 t0 frame from hrel)

end Flapjack.Compiler.Backend.WordBignum.CompileThmSupport
