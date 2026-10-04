import Flapjack.Compiler.Backend.WordInst.Proofs.InstSelect
import Flapjack.Pancake.WordConvs

/-!
# `word_instProof`: semantics of `three_to_two_reg`

Counterpart of `cakeml/compiler/backend/proofs/word_instProofScript.sml:985-1254`:
`locals_rel_cut_envs_local`, `three_to_two_reg_Loop`, `three_to_two_reg_correct` and
`evaluate_three_to_two_reg_prog`, over the exact wordSem evaluator.

HOL's `distinct_tar_reg` on the wordLang instruction carrier is rendered by the
clause-for-clause `distinctTarReg` of `Flapjack.Pancake.WordConvs` (untagged only
because its own binder admits width zero); every use below instantiates it at the
positive width of the surrounding theorem.
-/

namespace Flapjack

namespace WordInstThreeToTwoSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordInstThreeToTwoSupport

namespace Compiler.Backend.WordInst

open WordSemStateFiniteExact Flapjack.Compiler.Encoders.Asm

/-- Exact HOL local `locals_rel_cut_envs_local` (`word_instProofScript.sml:985-1004`),
    the same statement as wordProps `locals_rel_cut_envs`. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "locals_rel_cut_envs_local"
  (words_as_type_indexed_bitvec)]
theorem locals_rel_cut_envs_local {width : Nat} [NeZero width] (temp : Nat)
    (loc loc' : Spt (WordLocW width)) (names : WordLangCutsetsHOL)
    (x : Spt (WordLocW width) × Spt (WordLocW width)) :
    wordLocalsRel temp loc loc' ∧ everyNameHOL (fun x => decide (x < temp)) names = true ∧
      wordSemCutEnvs names loc = some x →
      wordSemCutEnvs names loc' = some x :=
  locals_rel_cut_envs temp loc loc' names x

set_option linter.unusedSimpArgs false in
/-- Exact HOL `three_to_two_reg_Loop` (`word_instProofScript.sml:1144-1169`), by
    strong induction on the clock as HOL. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "three_to_two_reg_Loop"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem three_to_two_reg_Loop {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (s : WordSemStateFiniteExact width C F) (names : WordLangNumSetHOL)
      (prog : WordLangProgHOL (BitVec width)) (exit_names : WordLangNumSetHOL)
      (res : Option (WordSemResult width)) (s' : WordSemStateFiniteExact width C F),
      (∀ (v : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
          (s' : WordSemStateFiniteExact width C F),
          evaluate prog v = (res, s') ∧ res ≠ some .error →
          evaluate (threeToTwoReg prog) v = (res, s')) ∧
        evaluate (.loop names prog exit_names) s = (res, s') ∧ res ≠ some .error →
      evaluate (.loop names (threeToTwoReg prog) exit_names) s = (res, s') := by
  intro s
  generalize hn : s.clock = n
  induction n using Nat.strongRecOn generalizing s with
  | _ n IH =>
  rintro names prog exitNames res s' ⟨ih, he, herr⟩
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [ht] at he ⊢
  rcases hcs : cutState (names, .ln) s with _ | x
  · rw [hcs] at he; exact he
  rw [hcs] at he
  simp only at he ⊢
  rcases hb : evaluate prog x with ⟨r1, s1⟩
  rw [hb] at he
  have hr1 : r1 ≠ some .error := by
    rintro rfl
    simp [wordSemContLoop, wordSemExitLoop] at he
    exact herr he.1.symm
  rw [ih x r1 s1 ⟨hb, hr1⟩]
  simp only
  by_cases hcont : wordSemContLoop r1 = true
  · simp only [hcont, if_true] at he ⊢
    by_cases hz : s1.clock = 0
    · simp only [hz, if_true] at he ⊢; exact he
    · simp only [hz, if_false] at he ⊢
      have hc1 := evaluate_clock prog x r1 s1 hb
      have hcx := cutState_clock_termdep _ _ _ hcs
      have hlt : (decClock s1).clock < n := by
        simp only [decClock]; omega
      exact IH _ hlt (decClock s1) rfl names prog exitNames res s' ⟨ih, he, herr⟩
  · simp only [hcont, Bool.false_eq_true, if_false] at he ⊢
    exact he

section Arith

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

theorem evaluate_move1 (r1 r2 : Nat) (v : WordLocW width) (s : WordSemStateFiniteExact width C F)
    (hg : getVar r2 s = some v) :
    evaluate (.move 0 [(r1, r2)]) s = (none, { s with locals := sptInsert r1 v s.locals }) := by
  have hm := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.1
  rw [hm]
  simp [WordSemStateFiniteExact.getVars, hg, setVars, LoopSemStateFiniteExact.sptAlistInsert]

theorem getVar_insert_ne (s : WordSemStateFiniteExact width C F) (r1 r : Nat) (v : WordLocW width)
    (h : r ≠ r1) : getVar r { s with locals := sptInsert r1 v s.locals } = getVar r s := by
  show sptLookup r (sptInsert r1 v s.locals) = sptLookup r s.locals
  rw [sptLookup_sptInsert_ne _ _ _ _ h]

set_option linter.unusedSimpArgs false in
theorem ttr_binop (bop : BinOp) (r1 r2 : Nat) (ri : WordRegImm (BitVec width))
    (s s' : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (hd : distinctTarReg (WordLangInst.arith (.binop bop r1 r2 ri)) = true)
    (he : evaluate (.inst (.arith (.binop bop r1 r2 ri))) s = (res, s'))
    (herr : res ≠ some .error) :
    evaluate (.seq (.move 0 [(r1, r2)]) (.inst (.arith (.binop bop r1 r1 ri)))) s = (res, s') := by
  rw [evaluate_inst_eq] at he
  cases ri with
  | reg r =>
    simp only [distinctTarReg, decide_eq_true_eq] at hd
    simp only [inst, assign] at he
    rcases hw : wordExp s (.op bop [.var r2, .var r]) with _ | w
    · simp [hw] at he; exact absurd he.1.symm herr
    simp only [hw, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨w1, w2, x, h1, h2, hx, rfl⟩ := wordExp_op2_some s bop _ _ _ hw
    have hg : getVar r2 s = some (.word w1) := by simpa [wordExp] using h1
    rw [evaluate_seq_none _ _ _ _ (evaluate_move1 r1 r2 _ s hg), evaluate_inst_eq]
    have hv : wordExp { s with locals := sptInsert r1 (.word w1) s.locals }
        (.op bop [.var r1, .var r]) = some (.word x) := by
      rw [← hw]
      apply wordExp_op2_congr
      · simp [wordExp, getVar, sptLookup_sptInsert_same, h1]
      · rw [wordExp, wordExp, getVar_insert_ne s r1 r _ hd]
    simp only [inst, assign, hv, setVar, sptInsert_insert_shadow]
  | imm wi =>
    simp only [inst, assign] at he
    rcases hw : wordExp s (.op bop [.var r2, .const wi]) with _ | w
    · simp [hw] at he; exact absurd he.1.symm herr
    simp only [hw, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨w1, w2, x, h1, h2, hx, rfl⟩ := wordExp_op2_some s bop _ _ _ hw
    have hg : getVar r2 s = some (.word w1) := by simpa [wordExp] using h1
    rw [evaluate_seq_none _ _ _ _ (evaluate_move1 r1 r2 _ s hg), evaluate_inst_eq]
    have hv : wordExp { s with locals := sptInsert r1 (.word w1) s.locals }
        (.op bop [.var r1, .const wi]) = some (.word x) := by
      rw [← hw]
      apply wordExp_op2_congr
      · simp [wordExp, getVar, sptLookup_sptInsert_same, h1]
      · rw [wordExp, wordExp]
    simp only [inst, assign, hv, setVar, sptInsert_insert_shadow]

theorem wordExp_shift_congr (s1 s2 : WordSemStateFiniteExact width C F) (sh : Shift)
    (a1 a2 b1 b2 : WordLangExpHOL (BitVec width))
    (h1 : wordExp s1 a1 = wordExp s2 b1) (h2 : wordExp s1 a2 = wordExp s2 b2) :
    wordExp s1 (.shift sh a1 a2) = wordExp s2 (.shift sh b1 b2) := by
  rw [wordExp, wordExp, h1, h2]

set_option linter.unusedSimpArgs false in
theorem ttr_shift (sh : Shift) (r1 r2 : Nat) (ri : WordRegImm (BitVec width))
    (s s' : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (hd : distinctTarReg (WordLangInst.arith (.shift sh r1 r2 ri)) = true)
    (he : evaluate (.inst (.arith (.shift sh r1 r2 ri))) s = (res, s'))
    (herr : res ≠ some .error) :
    evaluate (.seq (.move 0 [(r1, r2)]) (.inst (.arith (.shift sh r1 r1 ri)))) s = (res, s') := by
  rw [evaluate_inst_eq] at he
  rcases hg : getVar r2 s with _ | v
  · cases ri <;> simp [inst, assign, wordExp, hg] at he <;> exact absurd he.1.symm herr
  rw [evaluate_seq_none _ _ _ _ (evaluate_move1 r1 r2 _ s hg), evaluate_inst_eq]
  have hE : ∀ E : WordLangExpHOL (BitVec width),
      wordExp { s with locals := sptInsert r1 v s.locals } E = wordExp s E →
      wordExp { s with locals := sptInsert r1 v s.locals } (.shift sh (.var r1) E) =
        wordExp s (.shift sh (.var r2) E) := by
    intro E hEq
    apply wordExp_shift_congr _ _ _ _ _ _ _ _ hEq
    simp [wordExp, getVar, sptLookup_sptInsert_same]
    exact hg.symm
  cases ri with
  | reg r =>
    simp only [distinctTarReg, decide_eq_true_eq] at hd
    simp only [inst, assign] at he ⊢
    rw [hE (.var r) (by rw [wordExp, wordExp, getVar_insert_ne s r1 r _ hd])]
    rcases hw : wordExp s (.shift sh (.var r2) (.var r)) with _ | w
    · simp [hw] at he; exact absurd he.1.symm herr
    simp only [hw, Prod.mk.injEq] at he ⊢
    obtain ⟨rfl, rfl⟩ := he
    simp only [setVar, sptInsert_insert_shadow, and_self]
  | imm wi =>
    simp only [inst, assign] at he ⊢
    rw [hE (.const wi) (by rw [wordExp, wordExp])]
    rcases hw : wordExp s (.shift sh (.var r2) (.const wi)) with _ | w
    · simp [hw] at he; exact absurd he.1.symm herr
    simp only [hw, Prod.mk.injEq] at he ⊢
    obtain ⟨rfl, rfl⟩ := he
    simp only [setVar, sptInsert_insert_shadow, and_self]

theorem getVar_insert_same (s : WordSemStateFiniteExact width C F) (r1 : Nat) (v : WordLocW width) :
    getVar r1 { s with locals := sptInsert r1 v s.locals } = some v := by
  show sptLookup r1 (sptInsert r1 v s.locals) = some v
  rw [sptLookup_sptInsert_same]

set_option linter.unusedSimpArgs false in
/-- The two-register form of `AddCarry`/`AddOverflow`/`SubOverflow`, run after the
    copy `r1 := r2`, gives the original instruction's result. -/
theorem ttr_inst3 (i i' : WordLangInst (BitVec width)) (r1 r2 : Nat)
    (s : WordSemStateFiniteExact width C F) (v : WordLocW width) (hg : getVar r2 s = some v)
    (hi : inst i' { s with locals := sptInsert r1 v s.locals } = inst i s)
    (s' : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (he : evaluate (.inst i) s = (res, s')) (herr : res ≠ some .error) :
    evaluate (.seq (.move 0 [(r1, r2)]) (.inst i')) s = (res, s') := by
  rw [evaluate_seq_none _ _ _ _ (evaluate_move1 r1 r2 _ s hg), evaluate_inst_eq, hi]
  rw [evaluate_inst_eq] at he
  rcases h : inst i s with _ | s2 <;> simp only [h] at he ⊢
  · simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr
  · exact he

set_option linter.unusedSimpArgs false in
theorem ttr_addCarry_inst (r1 r2 r3 r4 : Nat) (s : WordSemStateFiniteExact width C F)
    (v : WordLocW width) (hg : getVar r2 s = some v) (hd : r1 ≠ r3 ∧ r1 ≠ r4) :
    inst (.arith (.addCarry r1 r1 r3 r4)) { s with locals := sptInsert r1 v s.locals } =
      inst (.arith (.addCarry r1 r2 r3 r4)) s := by
  simp only [inst, WordSemStateFiniteExact.getVars, getVar_insert_same, hg,
    getVar_insert_ne s r1 r3 v (Ne.symm hd.1), getVar_insert_ne s r1 r4 v (Ne.symm hd.2)]
  split <;> simp_all [setVar, sptInsert_insert_shadow]

set_option linter.unusedSimpArgs false in
theorem ttr_addOverflow_inst (r1 r2 r3 r4 : Nat) (s : WordSemStateFiniteExact width C F)
    (v : WordLocW width) (hg : getVar r2 s = some v) (hd : r1 ≠ r3) :
    inst (.arith (.addOverflow r1 r1 r3 r4)) { s with locals := sptInsert r1 v s.locals } =
      inst (.arith (.addOverflow r1 r2 r3 r4)) s := by
  simp only [inst, WordSemStateFiniteExact.getVars, getVar_insert_same, hg,
    getVar_insert_ne s r1 r3 v (Ne.symm hd)]
  split <;> simp_all [setVar, sptInsert_insert_shadow]

set_option linter.unusedSimpArgs false in
theorem ttr_subOverflow_inst (r1 r2 r3 r4 : Nat) (s : WordSemStateFiniteExact width C F)
    (v : WordLocW width) (hg : getVar r2 s = some v) (hd : r1 ≠ r3) :
    inst (.arith (.subOverflow r1 r1 r3 r4)) { s with locals := sptInsert r1 v s.locals } =
      inst (.arith (.subOverflow r1 r2 r3 r4)) s := by
  simp only [inst, WordSemStateFiniteExact.getVars, getVar_insert_same, hg,
    getVar_insert_ne s r1 r3 v (Ne.symm hd)]
  split <;> simp_all [setVar, sptInsert_insert_shadow]

end Arith

set_option linter.unusedSimpArgs false in
/-- The returning `Call` case of `three_to_two_reg_correct`, with the induction
    hypotheses for the return handler and the exception handler as premises
    (Flapjack infrastructure). -/
theorem ttr_call_some {width : Nat} [NeZero width] {C : Type} {F : Type}
    (n : List Nat) (names : WordLangCutsetsHOL) (retHandler : WordLangProgHOL (BitVec width))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (s' : WordSemStateFiniteExact width C F)
    (hd : everyInst distinctTarReg (.call (some (n, names, retHandler, l1, l2)) dest args handler) = true)
    (he : evaluate (.call (some (n, names, retHandler, l1, l2)) dest args handler) s = (res, s'))
    (herr : res ≠ some .error)
    (ihr : ∀ (s : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
      (s' : WordSemStateFiniteExact width C F),
      everyInst distinctTarReg retHandler = true ∧ evaluate retHandler s = (res, s') ∧
        res ≠ some .error → evaluate (threeToTwoReg retHandler) s = (res, s'))
    (ihh : ∀ (n' : Nat) (hp : WordLangProgHOL (BitVec width)) (l1' l2' : Nat),
      handler = some (n', hp, l1', l2') →
      ∀ (s : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
        (s' : WordSemStateFiniteExact width C F),
        everyInst distinctTarReg hp = true ∧ evaluate hp s = (res, s') ∧ res ≠ some .error →
        evaluate (threeToTwoReg hp) s = (res, s')) :
    evaluate (threeToTwoReg (.call (some (n, names, retHandler, l1, l2)) dest args handler)) s =
      (res, s') := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hdr : everyInst distinctTarReg retHandler = true := by
    rcases handler with _ | ⟨_, _, _, _⟩ <;>
      simp only [everyInst, Bool.and_eq_true] at hd <;> first | exact hd | exact hd.1
  have hsel : threeToTwoReg (.call (some (n, names, retHandler, l1, l2)) dest args handler) =
      .call (some (n, names, threeToTwoReg retHandler, l1, l2)) dest args
        (handler.map (fun hv => (hv.1, threeToTwoReg hv.2.1, hv.2.2.1, hv.2.2.2))) := by
    rcases handler with _ | ⟨_, _, _, _⟩ <;> rfl
  have hpm : ∀ (envs : Spt (WordLocW width) × Spt (WordLocW width))
      (t : WordSemStateFiniteExact width C F),
      pushEnv envs (handler.map (fun hv => (hv.1, threeToTwoReg hv.2.1, hv.2.2.1, hv.2.2.2)))
        t = pushEnv envs handler t := by
    intro envs t
    rcases handler with _ | ⟨_, _, _, _⟩ <;> rfl
  rw [hsel]
  rw [ht] at he ⊢
  rcases hg : WordSemStateFiniteExact.getVars args s with _ | xs
  · simp only [hg, Prod.mk.injEq] at he; exact absurd he.1.symm herr
  simp only [hg] at he ⊢
  by_cases hbad : wordSemBadDestArgs dest args = true
  · simp only [hbad, if_true, Prod.mk.injEq] at he; exact absurd he.1.symm herr
  simp only [hbad, Bool.false_eq_true, if_false] at he ⊢
  simp only [wordSemAddRetLoc] at he ⊢
  rcases hf : wordSemFindCode dest (.loc l1 l2 :: xs) s.code s.stackSize with
    _ | ⟨args1, prog, ss⟩
  · simp only [hf, Prod.mk.injEq] at he; exact absurd he.1.symm herr
  simp only [hf] at he ⊢
  by_cases hdc : sptDomainEmpty names.fst ∨ ¬ n.Nodup
  · simp only [hdc, if_true, Prod.mk.injEq] at he; exact absurd he.1.symm herr
  simp only [hdc, if_false] at he ⊢
  rcases hce : wordSemCutEnvs names s.locals with _ | envs
  · simp only [hce, Prod.mk.injEq] at he; exact absurd he.1.symm herr
  simp only [hce] at he ⊢
  simp only [hpm]
  by_cases hz : s.clock = 0
  · rw [if_pos hz] at he ⊢; exact he
  rw [if_neg hz] at he ⊢
  rcases hcv : evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) with
    ⟨rc, s2⟩
  rw [hcv] at he
  rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
  rotate_left
  · simp only at he ⊢
    by_cases hx : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ n.length
    · simp only [hx, if_true] at he ⊢; exact he
    simp only [hx, if_false] at he ⊢
    rcases hp : popEnv s2 with _ | s1
    · simp only [hp] at he ⊢; exact he
    simp only [hp] at he ⊢
    by_cases hdom : sptDomainEqUnion s1.locals envs.fst envs.snd
    · simp only [hdom, if_true] at he ⊢
      exact ihr _ res s' ⟨hdr, he, herr⟩
    · simp only [hdom, if_false] at he ⊢; exact he
  · cases handler with
    | none => exact he
    | some hdl =>
      obtain ⟨n', hprog, l1', l2'⟩ := hdl
      have hdh : everyInst distinctTarReg hprog = true := by
        simp only [everyInst, Bool.and_eq_true] at hd
        exact hd.2
      simp only [Option.map_some] at he ⊢
      by_cases hx : x ≠ WordLocW.loc l1' l2'
      · rw [if_pos hx] at he ⊢; exact he
      rw [if_neg hx] at he ⊢
      by_cases hdom : sptDomainEqUnion s2.locals envs.fst envs.snd
      · rw [if_pos hdom] at he ⊢
        exact ihh n' hprog l1' l2' rfl _ res s' ⟨hdh, he, herr⟩
      · rw [if_neg hdom] at he ⊢; exact he
  all_goals exact he

set_option linter.unusedSimpArgs false in
/-- Exact HOL `three_to_two_reg_correct` (`word_instProofScript.sml:1172-1243`):
    `every_inst distinct_tar_reg prog ∧ evaluate (prog,s) = (res,s') ∧ res ≠ SOME Error
    ⇒ evaluate (three_to_two_reg prog,s) = (res,s')`, by recursion on the program
    (HOL `three_to_two_reg_ind`). -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "three_to_two_reg_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem three_to_two_reg_correct {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (prog : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (s' : WordSemStateFiniteExact width C F),
      everyInst distinctTarReg prog = true ∧ evaluate prog s = (res, s') ∧ res ≠ some .error →
      evaluate (threeToTwoReg prog) s = (res, s')
  | .inst i, s, res, s', ⟨hd, he, herr⟩ => by
      simp only [everyInst] at hd
      cases i with
      | arith a =>
        cases a with
        | binop bop r1 r2 ri => exact ttr_binop bop r1 r2 ri s s' res hd he herr
        | shift sh r1 r2 ri => exact ttr_shift sh r1 r2 ri s s' res hd he herr
        | addCarry r1 r2 r3 r4 =>
          simp only [distinctTarReg, decide_eq_true_eq] at hd
          rcases hg : getVar r2 s with _ | v
          · rw [evaluate_inst_eq] at he
            simp [inst, WordSemStateFiniteExact.getVars, hg] at he
            exact absurd he.1.symm herr
          exact ttr_inst3 _ _ r1 r2 s v hg (ttr_addCarry_inst r1 r2 r3 r4 s v hg hd) s' res he herr
        | addOverflow r1 r2 r3 r4 =>
          simp only [distinctTarReg, decide_eq_true_eq] at hd
          rcases hg : getVar r2 s with _ | v
          · rw [evaluate_inst_eq] at he
            simp [inst, WordSemStateFiniteExact.getVars, hg] at he
            exact absurd he.1.symm herr
          exact ttr_inst3 _ _ r1 r2 s v hg (ttr_addOverflow_inst r1 r2 r3 r4 s v hg hd) s' res he herr
        | subOverflow r1 r2 r3 r4 =>
          simp only [distinctTarReg, decide_eq_true_eq] at hd
          rcases hg : getVar r2 s with _ | v
          · rw [evaluate_inst_eq] at he
            simp [inst, WordSemStateFiniteExact.getVars, hg] at he
            exact absurd he.1.symm herr
          exact ttr_inst3 _ _ r1 r2 s v hg (ttr_subOverflow_inst r1 r2 r3 r4 s v hg hd) s' res he herr
        | div r1 r2 r3 => exact he
        | longMul r1 r2 r3 r4 => exact he
        | longDiv r1 r2 r3 r4 r5 => exact he
      | skip => exact he
      | const r w => exact he
      | mem op r a => exact he
      | fp f => exact he
  | .opCurrHeap bop r1 r2, s, res, s', ⟨_, he, herr⟩ => by
      have hoc := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.1
      rw [hoc] at he
      rcases hw : wordExp s (.op bop [.var r2, .lookup .currHeap]) with _ | w
      · simp only [hw, Prod.mk.injEq] at he; exact absurd he.1.symm herr
      simp only [hw, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨w1, w2, x, h1, h2, hx, rfl⟩ := wordExp_op2_some s bop _ _ _ hw
      have hg : getVar r2 s = some (.word w1) := by simpa [wordExp] using h1
      show evaluate (.seq (.move 0 [(r1, r2)]) (.opCurrHeap bop r1 r1)) s = _
      rw [evaluate_seq_none _ _ _ _ (evaluate_move1 r1 r2 _ s hg), hoc]
      have hv : wordExp { s with locals := sptInsert r1 (.word w1) s.locals }
          (.op bop [.var r1, .lookup .currHeap]) = some (.word x) := by
        rw [← hw]
        apply wordExp_op2_congr
        · rw [wordExp, wordExp, getVar_insert_same, hg]
        · rw [wordExp, wordExp]; rfl
      simp only [hv, setVar, sptInsert_insert_shadow]
  | .seq p1 p2, s, res, s', ⟨hd, he, herr⟩ => by
      have hq := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
      simp only [everyInst, Bool.and_eq_true] at hd
      rw [hq] at he
      show evaluate (.seq (threeToTwoReg p1) (threeToTwoReg p2)) s = _
      rw [hq]
      rcases h1 : evaluate p1 s with ⟨r1, s1⟩
      rw [h1] at he
      have hr1 : r1 ≠ some .error := by
        rintro rfl; simp only [Prod.mk.injEq] at he; exact herr he.1.symm
      rw [three_to_two_reg_correct p1 s r1 s1 ⟨hd.1, h1, hr1⟩]
      cases r1 with
      | none => exact three_to_two_reg_correct p2 s1 res s' ⟨hd.2, he, herr⟩
      | some x => exact he
  | .mustTerminate p, s, res, s', ⟨hd, he, herr⟩ => by
      have hm := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      simp only [everyInst] at hd
      rw [hm] at he
      show evaluate (.mustTerminate (threeToTwoReg p)) s = _
      rw [hm]
      by_cases hz : s.termdep = 0
      · rw [if_pos hz] at he ⊢; exact he
      rw [if_neg hz] at he ⊢
      rcases hq : evaluate p { s with
          clock := wordSemMustTerminateLimit width
          termdep := s.termdep - 1 } with ⟨r1, s1⟩
      rw [hq] at he
      have hr1 : r1 ≠ some .error := by
        rintro rfl; simp only [Prod.mk.injEq] at he; exact herr he.1.symm
      rw [three_to_two_reg_correct p _ r1 s1 ⟨hd, hq, hr1⟩]
      exact he
  | .ite cmp r1 ri c1 c2, s, res, s', ⟨hd, he, herr⟩ => by
      have hi := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      simp only [everyInst, Bool.and_eq_true] at hd
      rw [hi] at he
      show evaluate (.ite cmp r1 ri (threeToTwoReg c1) (threeToTwoReg c2)) s = _
      rw [hi]
      rcases hx : getVar r1 s with _ | x
      · simp only [hx] at he ⊢; exact he
      rcases hy : WordSemStateFiniteExact.getVarImm ri s with _ | y
      · simp only [hx, hy] at he ⊢; exact he
      simp only [hx, hy] at he ⊢
      rcases hw : wordSemWordCmp cmp x y with _ | (_ | _)
      · simp only [hw] at he ⊢; exact he
      · simp only [hw] at he ⊢; exact three_to_two_reg_correct c2 s res s' ⟨hd.2, he, herr⟩
      · simp only [hw] at he ⊢; exact three_to_two_reg_correct c1 s res s' ⟨hd.1, he, herr⟩
  | .loop names body exitNames, s, res, s', ⟨hd, he, herr⟩ => by
      simp only [everyInst] at hd
      exact three_to_two_reg_Loop s names body exitNames res s'
        ⟨fun v r s'' ⟨h1, h2⟩ => three_to_two_reg_correct body v r s'' ⟨hd, h1, h2⟩, he, herr⟩
  | .call none dest args handler, s, res, s', ⟨hd, he, herr⟩ => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      rcases handler with _ | hv
      · exact he
      · exfalso
        rw [ht] at he
        rcases hg : WordSemStateFiniteExact.getVars args s with _ | xs <;> simp only [hg] at he
        · simp only [Prod.mk.injEq] at he; exact herr he.1.symm
        by_cases hbad : wordSemBadDestArgs dest args = true
        · simp only [hbad, if_true, Prod.mk.injEq] at he; exact herr he.1.symm
        simp only [hbad, Bool.false_eq_true, if_false] at he
        rcases hf : wordSemFindCode dest (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat)) xs) s.code s.stackSize with
          _ | ⟨a1, pr, ss⟩ <;> simp only [hf, Prod.mk.injEq] at he <;> exact herr he.1.symm
  | .call (some (n, names, retHandler, l1, l2)) dest args handler, s, res, s', ⟨hd, he, herr⟩ =>
      ttr_call_some n names retHandler l1 l2 dest args handler s res s' hd he herr
        (fun s r s'' h => three_to_two_reg_correct retHandler s r s'' h)
        (fun n' hp l1' l2' _ s r s'' h => three_to_two_reg_correct hp s r s'' h)
  | .skip, _, _, _, ⟨_, he, _⟩ => he
  | .move a b, _, _, _, ⟨_, he, _⟩ => he
  | .assign a b, _, _, _, ⟨_, he, _⟩ => he
  | .get a b, _, _, _, ⟨_, he, _⟩ => he
  | .set a b, _, _, _, ⟨_, he, _⟩ => he
  | .store a b, _, _, _, ⟨_, he, _⟩ => he
  | .alloc a b, _, _, _, ⟨_, he, _⟩ => he
  | .storeConsts a b d e f, _, _, _, ⟨_, he, _⟩ => he
  | .raise a, _, _, _, ⟨_, he, _⟩ => he
  | WordLangProgHOL.return a b, _, _, _, ⟨_, he, _⟩ => he
  | WordLangProgHOL.break a, _, _, _, ⟨_, he, _⟩ => he
  | WordLangProgHOL.continue a, _, _, _, ⟨_, he, _⟩ => he
  | .tick, _, _, _, ⟨_, he, _⟩ => he
  | .locValue a b, _, _, _, ⟨_, he, _⟩ => he
  | .install a b d e f, _, _, _, ⟨_, he, _⟩ => he
  | .codeBufferWrite a b, _, _, _, ⟨_, he, _⟩ => he
  | .dataBufferWrite a b, _, _, _, ⟨_, he, _⟩ => he
  | .ffi a b d e f g, _, _, _, ⟨_, he, _⟩ => he
  | .shareInst a b d, _, _, _, ⟨_, he, _⟩ => he
termination_by p => sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals (try subst_vars)
  all_goals (try simp only [Option.some.sizeOf_spec, Prod.mk.sizeOf_spec])
  all_goals omega

/-- Exact HOL `evaluate_three_to_two_reg_prog` (`word_instProofScript.sml:1245-1254`);
    HOL's free variables are explicit binders. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "evaluate_three_to_two_reg_prog"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_three_to_two_reg_prog {width : Nat} [NeZero width] {C : Type} {F : Type}
    (prog : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (s' : WordSemStateFiniteExact width C F) (t : Bool) :
    evaluate prog s = (res, s') ∧ res ≠ some .error ∧ everyInst distinctTarReg prog = true →
    evaluate (threeToTwoRegProg t prog) s = (res, s') := by
  rintro ⟨he, herr, hd⟩
  cases t
  · exact he
  · exact three_to_two_reg_correct prog s res s' ⟨hd, he, herr⟩

end Compiler.Backend.WordInst

end Flapjack
