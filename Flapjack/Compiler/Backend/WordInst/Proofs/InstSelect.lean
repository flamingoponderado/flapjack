import Flapjack.Compiler.Backend.WordInst.Proofs.PullExp
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.LocalsRel

/-!
# `word_instProof`: correctness of instruction selection

Counterpart of `cakeml/compiler/backend/proofs/word_instProofScript.sml:426-749`:
`inst_select_exp_thm`, `locals_rm` and `inst_select_thm`, over the exact wordSem
evaluator and the tagged `inst_select_exp`/`inst_select` definitions.
-/

namespace Flapjack

namespace WordInstSelectSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordInstSelectSupport

namespace Compiler.Backend.WordInst

open WordSemStateFiniteExact Flapjack.Compiler.Encoders.Asm

section Helpers

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

/-- HOL's locals postcondition of `inst_select_exp_thm`. -/
def instSelPost (tar temp : Nat) (w : WordLocW width) (old new : Spt (WordLocW width)) : Prop :=
  ∀ x, if x = tar then sptLookup x new = some w
    else if x < temp then sptLookup x new = sptLookup x old else True

theorem instSelPost_insert (tar temp : Nat) (w : WordLocW width)
    (old l : Spt (WordLocW width)) (h : ∀ x, x < temp → sptLookup x l = sptLookup x old) :
    instSelPost tar temp w old (sptInsert tar w l) := by
  intro x
  by_cases hx : x = tar
  · subst hx; simp only [if_true, sptLookup_sptInsert_same]
  · simp only [hx, if_false]
    split
    · rw [sptLookup_sptInsert_ne _ _ _ _ hx]; exact h x ‹_›
    · trivial

theorem evaluate_seq_none (p q : WordLangProgHOL (BitVec width))
    (s s' : WordSemStateFiniteExact width C F) (h : evaluate p s = (none, s')) :
    evaluate (.seq p q) s = evaluate q s' := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [ht, h]

theorem evaluate_inst_eq (i : WordLangInst (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    evaluate (.inst i) s = match inst i s with
      | some s1 => (none, s1)
      | none => (some .error, s) :=
  (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.1 s i

theorem wordExp_op2_congr (s1 s2 : WordSemStateFiniteExact width C F) (op : BinOp)
    (a1 a2 b1 b2 : WordLangExpHOL (BitVec width))
    (h1 : wordExp s1 a1 = wordExp s2 b1) (h2 : wordExp s1 a2 = wordExp s2 b2) :
    wordExp s1 (.op op [a1, a2]) = wordExp s2 (.op op [b1, b2]) := by
  rw [wordExp_op, wordExp_op]
  simp only [List.map, h1, h2]

/-- The common tail of `inst_select_exp_thm`: a selected subprogram has left
    its value in `temp`, preserving every register below `temp`. -/
theorem instSelPost_temp {temp : Nat} {w : WordLocW width} {old new : Spt (WordLocW width)}
    (h : instSelPost temp temp w old new) :
    sptLookup temp new = some w ∧ ∀ x, x < temp → sptLookup x new = sptLookup x old := by
  refine ⟨by simpa using h temp, fun x hx => ?_⟩
  have := h x
  rw [if_neg (by omega), if_pos hx] at this
  exact this

theorem wordOpHOL_comm2 (op : BinOp) (hop : op ≠ .sub) (a b : BitVec width) :
    wordOpHOL op [a, b] = wordOpHOL op [b, a] := by
  cases op
  · simp only [wordOpHOL, wordOp, List.foldr]
    congr 1
    ac_rfl
  · exact absurd rfl hop
  · simp only [wordOpHOL, wordOp, List.foldr]
    change some (a &&& (b &&& ~~~0#width)) = some (b &&& (a &&& ~~~0#width))
    congr 1
    ac_rfl
  · simp only [wordOpHOL, wordOp, List.foldr]
    change some (a ||| (b ||| 0#width)) = some (b ||| (a ||| 0#width))
    congr 1
    ac_rfl
  · simp only [wordOpHOL, wordOp, List.foldr]
    congr 1
    ac_rfl

theorem wordExp_op2_some (s : WordSemStateFiniteExact width C F) (op : BinOp)
    (e1 e2 : WordLangExpHOL (BitVec width)) (w : WordLocW width)
    (h : wordExp s (.op op [e1, e2]) = some w) :
    ∃ w1 w2 x, wordExp s e1 = some (.word w1) ∧ wordExp s e2 = some (.word w2) ∧
      wordOpHOL op [w1, w2] = some x ∧ w = .word x := by
  rw [wordExp_op] at h
  rcases h1 : wordExp s e1 with _ | (w1 | ⟨_, _⟩) <;>
    rcases h2 : wordExp s e2 with _ | (w2 | ⟨_, _⟩) <;>
    simp [h1, h2, theWords] at h
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨w1, w2, x, rfl, rfl, hx, rfl⟩

theorem theWords_length :
    ∀ (ls : List (Option (WordLocW width))) (ws : List (BitVec width)),
      theWords ls = some ws → ws.length = ls.length
  | [], ws, h => by simp [theWords] at h; subst h; rfl
  | o :: ls, ws, h => by
      rcases o with _ | (a | ⟨_, _⟩) <;> simp [theWords] at h
      rcases hl : theWords ls with _ | xs <;> simp [hl] at h
      subst h
      simp [theWords_length ls xs hl]

theorem binaryBranchExp_op2 (op : BinOp) (e1 e2 : WordLangExpHOL (BitVec width))
    (h : binaryBranchExp (.op op [e1, e2]) = true) :
    binaryBranchExp e1 = true ∧ binaryBranchExp e2 = true := by
  by_cases hop : op = .sub
  · subst hop
    rw [binaryBranchExp] at h
    simpa using h
  · rw [binaryBranchExp] at h
    · simpa using h
    · exact hop

theorem op_length_two (s : WordSemStateFiniteExact width C F) (op : BinOp)
    (ls : List (WordLangExpHOL (BitVec width))) (w : WordLocW width)
    (hb : binaryBranchExp (.op op ls) = true) (he : wordExp s (.op op ls) = some w) :
    ∃ e1 e2, ls = [e1, e2] := by
  suffices h2 : ls.length = 2 by
    match ls, h2 with
    | [e1, e2], _ => exact ⟨e1, e2, rfl⟩
  by_cases hop : op = .sub
  · subst hop
    rw [wordExp_op] at he
    rcases htw : theWords (ls.map (fun a => wordExp s a)) with _ | ws <;> simp [htw] at he
    have hlen := theWords_length _ _ htw
    simp only [List.length_map] at hlen
    rw [← hlen]
    match ws, he with
    | [_, _], _ => rfl
  · rw [binaryBranchExp] at hb
    · simp at hb; exact hb.1
    · exact hop

theorem memLoad_withLocals (a : BitVec width) (s : WordSemStateFiniteExact width C F)
    (l : Spt (WordLocW width)) : memLoad a { s with locals := l } = memLoad a s := rfl

end Helpers

set_option linter.unusedSimpArgs false in
/-- Exact HOL local `inst_select_exp_thm` (`word_instProofScript.sml:430-712`),
    by recursion on the expression as HOL's `completeInduct_on exp_size`. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "inst_select_exp_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem inst_select_exp_thm {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (c : AsmConfigExact width) (tar temp : Nat) (exp : WordLangExpHOL (BitVec width))
      (s : WordSemStateFiniteExact width C F) (w : WordLocW width) (loc : Spt (WordLocW width)),
      binaryBranchExp exp = true ∧ everyVarExpHOL (fun x => decide (x < temp)) exp = true ∧
        wordLocalsRel temp s.locals loc ∧ wordExp s exp = some w →
      ∃ loc', evaluate (instSelectExp c tar temp exp) { s with locals := loc } =
          ((none : Option (WordSemResult width)), { s with locals := loc' }) ∧
        ∀ x, if x = tar then sptLookup x loc' = some w
          else if x < temp then sptLookup x loc' = sptLookup x s.locals else True
  | c, tar, temp, .const w0, s, w, loc, ⟨_, _, hl, he⟩ => by
      simp only [wordExp, Option.some.injEq] at he
      subst he
      refine ⟨sptInsert tar (.word w0) loc, ?_,
        instSelPost_insert tar temp _ s.locals loc (fun x hx => (hl x hx).symm)⟩
      rw [instSelectExp, evaluate_inst_eq]
      simp only [inst, assign, wordExp]
      rfl
  | c, tar, temp, .var v, s, w, loc, ⟨_, hev, hl, he⟩ => by
      simp only [everyVarExpHOL, decide_eq_true_eq] at hev
      simp only [wordExp, getVar] at he
      refine ⟨sptInsert tar w loc, ?_,
        instSelPost_insert tar temp _ s.locals loc (fun x hx => (hl x hx).symm)⟩
      have hm := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.1
      rw [instSelectExp, hm]
      have hv : sptLookup v loc = some w := by rw [← hl v hev]; exact he
      simp [WordSemStateFiniteExact.getVars, getVar, hv, setVars,
        LoopSemStateFiniteExact.sptAlistInsert]
  | c, tar, temp, .lookup nm, s, w, loc, ⟨_, _, hl, he⟩ => by
      simp only [wordExp] at he
      refine ⟨sptInsert tar w loc, ?_,
        instSelPost_insert tar temp _ s.locals loc (fun x hx => (hl x hx).symm)⟩
      have hg := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.1
      rw [instSelectExp, hg]
      have he' : getStore nm { s with locals := loc } = some w := he
      simp only [he']
      rfl
  | c, tar, temp, .load e, s, w, loc, ⟨hb, hev, hl, he⟩ => by
      rw [binaryBranchExp] at hb
      simp only [everyVarExpHOL] at hev
      simp only [wordExp] at he
      rcases hwe : wordExp s e with _ | (a | ⟨_, _⟩)
      all_goals first | (simp [hwe] at he; done) | skip
      simp only [hwe] at he
      have tail : ∀ (off : BitVec width) (loc'' : Spt (WordLocW width)),
          wordExp { s with locals := loc'' } (.op .add [.var temp, .const off]) =
            some (.word a) →
          evaluate (.inst (.mem .load tar (.addr temp off))) { s with locals := loc'' } =
            (none, { s with locals := sptInsert tar w loc'' }) := by
        intro off loc'' hw
        rw [evaluate_inst_eq]
        simp only [inst, hw, memLoad_withLocals, he]
        rfl
      by_cases hpat : ∃ e' off, e = .op .add [e', .const off]
      · obtain ⟨e', off, rfl⟩ := hpat
        rw [instSelectExp]
        simp only
        by_cases hoff : addrOffsetOk c off = true
        · simp only [hoff, if_true]
          have hb' : binaryBranchExp e' = true := by
            rw [binaryBranchExp] at hb
            · simp at hb; exact hb.1
            · nofun
          have hev' : everyVarExpHOL (fun x => decide (x < temp)) e' = true := by
            simp [everyVarExpHOL, everyVarExpsHOL] at hev
            simpa using hev
          rw [wordExp_op] at hwe
          rcases hw1 : wordExp s e' with _ | (w1 | ⟨_, _⟩) <;>
            simp [hw1, theWords, wordExp] at hwe
          obtain ⟨loc'', hev'', hpost⟩ :=
            inst_select_exp_thm c temp temp e' s (.word w1) loc ⟨hb', hev', hl, hw1⟩
          obtain ⟨ht, hlow⟩ := instSelPost_temp (temp := temp) hpost
          refine ⟨sptInsert tar w loc'', ?_, instSelPost_insert tar temp w s.locals loc'' hlow⟩
          rw [evaluate_seq_none _ _ _ _ hev'', tail off loc'']
          rw [wordExp_op]
          simp [wordExp, getVar, ht, theWords, hwe]
        · simp only [hoff, Bool.false_eq_true, if_false]
          obtain ⟨loc'', hev'', hpost⟩ := inst_select_exp_thm c temp temp
            (.op .add [e', .const off]) s (.word a) loc ⟨hb, hev, hl, hwe⟩
          obtain ⟨ht, hlow⟩ := instSelPost_temp (temp := temp) hpost
          refine ⟨sptInsert tar w loc'', ?_, instSelPost_insert tar temp w s.locals loc'' hlow⟩
          rw [evaluate_seq_none _ _ _ _ hev'', tail 0 loc'']
          rw [wordExp_op]
          simp [wordExp, getVar, ht, theWords, wordOpHOL, wordOp]
      · have hgen : instSelectExp c tar temp (.load e) =
            .seq (instSelectExp c temp temp e) (.inst (.mem .load tar (.addr temp 0))) := by
          rw [instSelectExp]
          exact fun e' off h => hpat ⟨e', off, h⟩
        obtain ⟨loc'', hev'', hpost⟩ := inst_select_exp_thm c temp temp e s (.word a) loc
          ⟨hb, hev, hl, hwe⟩
        obtain ⟨ht, hlow⟩ := instSelPost_temp (temp := temp) hpost
        refine ⟨sptInsert tar w loc'', ?_, instSelPost_insert tar temp w s.locals loc'' hlow⟩
        rw [hgen, evaluate_seq_none _ _ _ _ hev'', tail 0 loc'']
        rw [wordExp_op]
        simp [wordExp, getVar, ht, theWords, wordOpHOL, wordOp]
  | c, tar, temp, .op op ls, s, w, loc, ⟨hb, hev, hl, he⟩ => by
      obtain ⟨e1, e2, rfl⟩ := op_length_two s op ls w hb he
      obtain ⟨w1, w2, x, hw1, hw2, hx, rfl⟩ := wordExp_op2_some s op e1 e2 w he
      obtain ⟨hb1, hb2⟩ := binaryBranchExp_op2 op e1 e2 hb
      have hev12 : everyVarExpHOL (fun x => decide (x < temp)) e1 = true ∧
          everyVarExpHOL (fun x => decide (x < temp)) e2 = true := by
        simpa [everyVarExpHOL, everyVarExpsHOL] using hev
      have hoc := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.1
      by_cases hA : isLookupCurrHeap e2 = true
      · have he2 : e2 = .lookup .currHeap := by
          cases e2 <;> simp [isLookupCurrHeap] at hA
          rename_i nm
          cases nm <;> simp [isLookupCurrHeap] at hA ⊢
        subst he2
        obtain ⟨loc'', hev'', hpost⟩ :=
          inst_select_exp_thm c temp temp e1 s (.word w1) loc ⟨hb1, hev12.1, hl, hw1⟩
        obtain ⟨ht, hlow⟩ := instSelPost_temp (temp := temp) hpost
        refine ⟨sptInsert tar (.word x) loc'', ?_,
          instSelPost_insert tar temp _ s.locals loc'' hlow⟩
        rw [instSelectExp]
        simp only [isLookupCurrHeap, if_true]
        rw [evaluate_seq_none _ _ _ _ hev'', hoc]
        have hv : wordExp { s with locals := loc'' } (.op op [.var temp, .lookup .currHeap]) =
            some (.word x) := by
          rw [← he]
          apply wordExp_op2_congr
          · simp [wordExp, getVar, ht, hw1]
          · rw [wordExp, wordExp]; rfl
        simp only [hv]
        rfl
      by_cases hB : isLookupCurrHeap e1 = true ∧ op ≠ .sub
      · have he1 : e1 = .lookup .currHeap := by
          have hB1 := hB.1
          cases e1 <;> simp [isLookupCurrHeap] at hB1
          rename_i nm
          cases nm <;> simp [isLookupCurrHeap] at hB1 ⊢
        subst he1
        obtain ⟨loc'', hev'', hpost⟩ :=
          inst_select_exp_thm c temp temp e2 s (.word w2) loc ⟨hb2, hev12.2, hl, hw2⟩
        obtain ⟨ht, hlow⟩ := instSelPost_temp (temp := temp) hpost
        refine ⟨sptInsert tar (.word x) loc'', ?_,
          instSelPost_insert tar temp _ s.locals loc'' hlow⟩
        rw [instSelectExp, if_neg hA, if_pos hB, evaluate_seq_none _ _ _ _ hev'', hoc]
        have hv : wordExp { s with locals := loc'' } (.op op [.var temp, .lookup .currHeap]) =
            some (.word x) := by
          rw [wordExp_op2_congr _ s op _ _ e2 (.lookup .currHeap)
            (by simp [wordExp, getVar, ht, hw2]) (by rw [wordExp, wordExp]; rfl), wordExp_op]
          simp only [List.map, hw2, hw1, theWords]
          rw [wordOpHOL_comm2 op hB.2, hx]
          rfl
        simp only [hv]
        rfl
      obtain ⟨loc'', hev'', hpost⟩ :=
        inst_select_exp_thm c temp temp e1 s (.word w1) loc ⟨hb1, hev12.1, hl, hw1⟩
      obtain ⟨ht, hlow⟩ := instSelPost_temp (temp := temp) hpost
      have hvt : wordExp { s with locals := loc'' } (.var temp) = wordExp s e1 := by
        simp [wordExp, getVar, ht, hw1]
      by_cases hc : ∃ w0, e2 = .const w0
      · obtain ⟨w0, rfl⟩ := hc
        have hw20 : w0 = w2 := by rw [wordExp] at hw2; simpa using hw2
        subst hw20
        have hvc : ∀ (t : WordSemStateFiniteExact width C F),
            wordExp t (.const w0) = wordExp s (.const w0) := fun t => by
          rw [wordExp, wordExp]
        rw [instSelectExp, if_neg hA, if_neg hB]
        simp only
        by_cases hv : c.validImm (.inl op) w0 = true
        · rw [if_pos hv, evaluate_seq_none _ _ _ _ hev'', evaluate_inst_eq]
          refine ⟨sptInsert tar (.word x) loc'', ?_,
            instSelPost_insert tar temp _ s.locals loc'' hlow⟩
          have hval : wordExp { s with locals := loc'' } (.op op [.var temp, .const w0]) =
              some (.word x) := by
            rw [← he]; exact wordExp_op2_congr _ _ _ _ _ _ _ hvt (hvc _)
          simp only [inst, assign, hval]
          rfl
        · rw [if_neg hv]
          by_cases hadd : op = .add ∧ c.validImm (.inl .sub) (-w0) = true
          · rw [if_pos hadd, evaluate_seq_none _ _ _ _ hev'', evaluate_inst_eq]
            obtain ⟨rfl, _⟩ := hadd
            refine ⟨sptInsert tar (.word x) loc'', ?_,
              instSelPost_insert tar temp _ s.locals loc'' hlow⟩
            have hval : wordExp { s with locals := loc'' } (.op .sub [.var temp, .const (-w0)]) =
                some (.word x) := by
              have h1 : wordExp { s with locals := loc'' } (.var temp) = some (.word w1) :=
                hvt.trans hw1
              have h2 : wordExp { s with locals := loc'' } (.const (-w0)) =
                  some (.word (-w0)) := by rw [wordExp]
              rw [wordExp_op]
              simp only [List.map, h1, h2, theWords, wordOpHOL, wordOp, Option.map_some]
              simp only [wordOpHOL, wordOp, List.foldr, Option.some.injEq] at hx
              subst hx
              simp [BitVec.sub_eq_add_neg]
            simp only [inst, assign, hval]
            rfl
          · rw [if_neg hadd, evaluate_seq_none _ _ _ _ hev'']
            have hp2 : evaluate (.inst (.const (temp + 1) w0)) { s with locals := loc'' } =
                (none, { s with locals := sptInsert (temp + 1) (.word w0) loc'' }) := by
              rw [evaluate_inst_eq]; simp only [inst, assign, wordExp]; rfl
            rw [evaluate_seq_none _ _ _ _ hp2, evaluate_inst_eq]
            have hlow3 : ∀ y, y < temp →
                sptLookup y (sptInsert (temp + 1) (.word w0) loc'') = sptLookup y s.locals :=
              fun y hy => by rw [sptLookup_sptInsert_ne _ _ _ _ (by omega)]; exact hlow y hy
            refine ⟨sptInsert tar (.word x) (sptInsert (temp + 1) (.word w0) loc''), ?_,
              instSelPost_insert tar temp _ s.locals _ hlow3⟩
            have hval : wordExp { s with locals := sptInsert (temp + 1) (.word w0) loc'' }
                (.op op [.var temp, .var (temp + 1)]) = some (.word x) := by
              rw [← he]
              apply wordExp_op2_congr
              · simp [wordExp, getVar, sptLookup_sptInsert_ne _ _ _ _ (show temp ≠ temp + 1 by omega),
                  ht, hw1]
              · simp [wordExp, getVar, sptLookup_sptInsert_same]
            simp only [inst, assign, hval]
            rfl
      · rw [instSelectExp, if_neg hA, if_neg hB]
        simp only
        split
        · exact absurd ⟨_, rfl⟩ hc
        · have hrel : wordLocalsRel temp s.locals loc'' := fun y hy => (hlow y hy).symm
          have hw2' : wordExp { s with locals := loc'' } e2 = some (.word w2) := by
            rw [locals_rel_word_exp_simp temp loc'' s e2 ⟨hev12.2, hrel⟩]; exact hw2
          have hev2' : everyVarExpHOL (fun y => decide (y < temp + 1)) e2 = true :=
            everyVarExpMono _ e2 _ ⟨fun y hy => by simp at hy ⊢; omega, hev12.2⟩
          obtain ⟨loc3, hev3, hpost3⟩ := inst_select_exp_thm c (temp + 1) (temp + 1) e2
            { s with locals := loc'' } (.word w2) loc'' ⟨hb2, hev2', fun _ _ => rfl, hw2'⟩
          obtain ⟨ht3, hlow3⟩ := instSelPost_temp (temp := temp + 1) hpost3
          have hev3' : evaluate (instSelectExp c (temp + 1) (temp + 1) e2)
              { s with locals := loc'' } = (none, { s with locals := loc3 }) := hev3
          rw [evaluate_seq_none _ _ _ _ hev'', evaluate_seq_none _ _ _ _ hev3', evaluate_inst_eq]
          have hlow3' : ∀ y, y < temp → sptLookup y loc3 = sptLookup y s.locals :=
            fun y hy => (hlow3 y (by omega)).trans (hlow y hy)
          refine ⟨sptInsert tar (.word x) loc3, ?_,
            instSelPost_insert tar temp _ s.locals loc3 hlow3'⟩
          have htemp3 : sptLookup temp loc3 = some (.word w1) :=
            (hlow3 temp (by omega)).trans ht
          have hval : wordExp { s with locals := loc3 } (.op op [.var temp, .var (temp + 1)]) =
              some (.word x) := by
            rw [← he]
            apply wordExp_op2_congr
            · simp [wordExp, getVar, htemp3, hw1]
            · simp [wordExp, getVar, ht3, hw2]
          simp only [inst, assign, hval]
          rfl
  | c, tar, temp, .shift sh e e1, s, w, loc, ⟨hb, hev, hl, he⟩ => by
      rw [binaryBranchExp] at hb
      simp only [Bool.and_eq_true] at hb
      simp only [everyVarExpHOL, Bool.and_eq_true] at hev
      rw [wordExp] at he
      rcases hwe : wordExp s e with _ | (v | ⟨_, _⟩) <;>
        rcases hwe1 : wordExp s e1 with _ | (v1 | ⟨_, _⟩) <;>
        simp [hwe, hwe1] at he
      obtain ⟨y, hy, rfl⟩ := he
      obtain ⟨loc'', hev'', hpost⟩ :=
        inst_select_exp_thm c temp temp e s (.word v) loc ⟨hb.1, hev.1, hl, hwe⟩
      obtain ⟨ht, hlow⟩ := instSelPost_temp (temp := temp) hpost
      by_cases hc : ∃ n, e1 = .const n
      · obtain ⟨n, rfl⟩ := hc
        have hn : n = v1 := by rw [wordExp] at hwe1; simpa using hwe1
        subst hn
        rw [instSelectExp]
        simp only
        by_cases hlt : n.toNat < width
        · rw [if_pos hlt]
          by_cases h0 : n.toNat = 0
          · rw [if_pos h0, evaluate_seq_none _ _ _ _ hev'']
            have hyv : y = v := by
              cases sh <;> simp [wordShiftHOL, h0, BitVec.rotateRight, BitVec.rotateRightAux] at hy <;>
                exact hy.symm
            subst hyv
            refine ⟨sptInsert tar (.word y) loc'', ?_,
              instSelPost_insert tar temp _ s.locals loc'' hlow⟩
            have hm := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.1
            rw [hm]
            simp [WordSemStateFiniteExact.getVars, getVar, ht, setVars,
              LoopSemStateFiniteExact.sptAlistInsert]
          · rw [if_neg h0, evaluate_seq_none _ _ _ _ hev'', evaluate_inst_eq]
            refine ⟨sptInsert tar (.word y) loc'', ?_,
              instSelPost_insert tar temp _ s.locals loc'' hlow⟩
            have hval : wordExp { s with locals := loc'' }
                (.shift sh (.var temp) (.const (BitVec.ofNat width n.toNat))) =
                some (.word y) := by
              rw [wordExp]
              simp [wordExp, getVar, ht, hy]
            simp only [inst, assign, hval]
            rfl
        · exfalso
          have hw0 : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
          simp only [wordShiftHOL] at hy
          rw [if_pos ⟨by omega, by omega⟩] at hy
          cases hy
      · have hgen : instSelectExp c tar temp (.shift sh e e1) =
            .seq (instSelectExp c temp temp e) (.seq (instSelectExp c (temp + 1) (temp + 1) e1)
              (.inst (.arith (.shift sh tar temp (.reg (temp + 1)))))) := by
          rw [instSelectExp]
          exact fun n h => hc ⟨n, h⟩
        rw [hgen]
        have hrel : wordLocalsRel temp s.locals loc'' := fun z hz => (hlow z hz).symm
        have hw1' : wordExp { s with locals := loc'' } e1 = some (.word v1) := by
          rw [locals_rel_word_exp_simp temp loc'' s e1 ⟨hev.2, hrel⟩]; exact hwe1
        have hev1' : everyVarExpHOL (fun z => decide (z < temp + 1)) e1 = true :=
          everyVarExpMono _ e1 _ ⟨fun z hz => by simp at hz ⊢; omega, hev.2⟩
        obtain ⟨loc3, hev3, hpost3⟩ := inst_select_exp_thm c (temp + 1) (temp + 1) e1
          { s with locals := loc'' } (.word v1) loc'' ⟨hb.2, hev1', fun _ _ => rfl, hw1'⟩
        obtain ⟨ht3, hlow3⟩ := instSelPost_temp (temp := temp + 1) hpost3
        have hev3' : evaluate (instSelectExp c (temp + 1) (temp + 1) e1)
            { s with locals := loc'' } = (none, { s with locals := loc3 }) := hev3
        rw [evaluate_seq_none _ _ _ _ hev'', evaluate_seq_none _ _ _ _ hev3', evaluate_inst_eq]
        have hlow3' : ∀ z, z < temp → sptLookup z loc3 = sptLookup z s.locals :=
          fun z hz => (hlow3 z (by omega)).trans (hlow z hz)
        refine ⟨sptInsert tar (.word y) loc3, ?_,
          instSelPost_insert tar temp _ s.locals loc3 hlow3'⟩
        have htemp3 : sptLookup temp loc3 = some (.word v) := (hlow3 temp (by omega)).trans ht
        have hval : wordExp { s with locals := loc3 } (.shift sh (.var temp) (.var (temp + 1))) =
            some (.word y) := by
          rw [wordExp]
          simp [wordExp, getVar, htemp3, ht3, hy]
        simp only [inst, assign, hval]
        rfl
termination_by _ _ _ e => sizeOf e

/-- Exact HOL local `locals_rm` (`word_instProofScript.sml:714-718`):
    `D with locals := D.locals = D`. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "locals_rm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem locals_rm {width : Nat} [NeZero width] {C : Type} {F : Type}
    (D : WordSemStateFiniteExact width C F) : { D with locals := D.locals } = D := rfl

section InstSelectThm

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

/-- `inst_select_thm` for one program, in the `LrPost` form of the locals
    relation (Flapjack infrastructure). -/
def InstSelGoal (c : AsmConfigExact width) (temp : Nat) (p : WordLangProgHOL (BitVec width)) :
    Prop :=
  ∀ (st : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (rst : WordSemStateFiniteExact width C F) (loc : Spt (WordLocW width)),
    evaluate p st = (res, rst) → everyVarHOL (fun x => decide (x < temp)) p = true →
      res ≠ some .error → wordLocalsRel temp st.locals loc →
      ∃ loc', evaluate (instSelect c temp p) { st with locals := loc } =
          (res, { rst with locals := loc' }) ∧ LrPost temp res rst.locals loc'

/-- Statements that `inst_select` leaves unchanged follow from
    `locals_rel_evaluate_thm`. -/
theorem instSel_default (c : AsmConfigExact width) (temp : Nat)
    (p : WordLangProgHOL (BitVec width)) (h : instSelect c temp p = p) :
    InstSelGoal (C := C) (F := F) c temp p := by
  intro st res rst loc he hv herr hl
  rw [h]
  exact lr_aux temp p st res rst loc he herr hv hl

set_option linter.unusedSimpArgs false in
/-- `inst_select_Loop_helper` in the `LrPost` form, by strong induction on the
    clock (Flapjack infrastructure). -/
theorem instSel_loop_aux (c : AsmConfigExact width) (temp : Nat)
    (names exitNames : WordLangNumSetHOL) (prog : WordLangProgHOL (BitVec width))
    (ih : ∀ (st : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
      (rst : WordSemStateFiniteExact width C F) (loc : Spt (WordLocW width)),
      evaluate prog st = (res, rst) → res ≠ some .error → wordLocalsRel temp st.locals loc →
      ∃ loc', evaluate (instSelect c temp prog) { st with locals := loc } =
        (res, { rst with locals := loc' }) ∧ LrPost temp res rst.locals loc')
    (hn : everyNameHOL (fun x => decide (x < temp)) (names, .ln) = true)
    (hx : everyNameHOL (fun x => decide (x < temp)) (exitNames, .ln) = true) :
    ∀ (n : Nat) (s : WordSemStateFiniteExact width C F), s.clock = n →
      ∀ (res : Option (WordSemResult width)) (rst : WordSemStateFiniteExact width C F)
        (loc : Spt (WordLocW width)),
        evaluate (.loop names prog exitNames) s = (res, rst) → res ≠ some .error →
        wordLocalsRel temp s.locals loc →
        ∃ loc', evaluate (.loop names (instSelect c temp prog) exitNames) { s with locals := loc } =
          (res, { rst with locals := loc' }) ∧ LrPost temp res rst.locals loc' := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n IH =>
  intro s hsn res rst loc he herr hl
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [ht] at he
  rcases hc : wordSemCutEnv (names, .ln) s.locals with _ | env
  · have hcs : cutState (names, .ln) s = none := by unfold cutState; rw [hc]
    rw [hcs] at he; simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr
  have hc' := locals_rel_cut_env temp s.locals loc (names, .ln) env ⟨hl, hn, hc⟩
  have hcs : cutState (names, .ln) s = some { s with locals := env } := by
    unfold cutState; rw [hc]
  have hcs' : cutState (names, .ln) { s with locals := loc } = some { s with locals := env } := by
    unfold cutState
    show (match wordSemCutEnv (names, .ln) loc with
      | none => none
      | some env => some { { s with locals := loc } with locals := env }) = _
    rw [hc']
  rw [hcs] at he
  simp only at he
  rcases hb : evaluate prog { s with locals := env } with ⟨r1, s1⟩
  rw [hb] at he
  have hc1 := evaluate_clock prog _ r1 s1 hb
  have hr1 : r1 ≠ some .error := by
    rintro rfl
    simp [wordSemContLoop, wordSemExitLoop] at he
    exact herr he.1.symm
  obtain ⟨loc1, hev1, hpost1⟩ := ih { s with locals := env } r1 s1 env hb hr1 (fun _ _ => rfl)
  have hev1' : evaluate (instSelect c temp prog) { s with locals := env } =
      (r1, { s1 with locals := loc1 }) := hev1
  rw [ht, hcs']
  simp only
  rw [hev1']
  simp only
  by_cases hcont : wordSemContLoop r1 = true
  · simp only [hcont, if_true] at he ⊢
    have hrel1 : wordLocalsRel temp s1.locals loc1 := by
      rcases r1 with _ | (_ | _ | _ | (_ | k) | _ | _ | _ | _) <;>
        simp [wordSemContLoop] at hcont <;> exact hpost1
    by_cases hz : s1.clock = 0
    · simp only [hz, if_true, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨(flushState true s1).locals, ?_, lrPost_refl temp _ _⟩
      rw [if_pos (show ({ s1 with locals := loc1 } : WordSemStateFiniteExact width C F).clock = 0
        from hz), flushState_withLocals]
    · simp only [hz, if_false] at he
      have hlt : (decClock s1).clock < n := by
        simp only [decClock] at hc1 ⊢; omega
      obtain ⟨loc', h1, h2⟩ := IH _ hlt (decClock s1) rfl res rst loc1 he herr hrel1
      refine ⟨loc', ?_, h2⟩
      rw [if_neg (show ¬ ({ s1 with locals := loc1 } : WordSemStateFiniteExact width C F).clock = 0
        from hz), decClock_withLocals]
      exact h1
  · simp only [hcont, Bool.false_eq_true, if_false] at he ⊢
    rcases r1 with _ | (_ | _ | (_ | k) | (_ | k) | _ | _ | _ | _)
    all_goals try (simp [wordSemContLoop] at hcont; done)
    all_goals simp only at he ⊢
    all_goals try (simp only [Prod.mk.injEq] at he
                   obtain ⟨rfl, rfl⟩ := he
                   first
                     | exact absurd rfl hr1
                     | exact ⟨loc1, rfl, hpost1⟩)
    -- `Break 0`
    rcases hce : wordSemCutEnv (exitNames, .ln) s1.locals with _ | env2
    · have : cutState (exitNames, .ln) s1 = none := by unfold cutState; rw [hce]
      rw [this] at he; simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr
    have hce' := locals_rel_cut_env temp s1.locals loc1 (exitNames, .ln) env2 ⟨hpost1, hx, hce⟩
    have h1 : cutState (exitNames, .ln) s1 = some { s1 with locals := env2 } := by
      unfold cutState; rw [hce]
    have h2 : cutState (exitNames, .ln) { s1 with locals := loc1 } =
        some { s1 with locals := env2 } := by
      unfold cutState
      show (match wordSemCutEnv (exitNames, .ln) loc1 with
        | none => none
        | some env => some { { s1 with locals := loc1 } with locals := env }) = _
      rw [hce']
    rw [h1] at he
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨env2, by rw [h2], fun _ _ => rfl⟩

set_option linter.unusedSimpArgs false in
theorem instSel_aux (c : AsmConfigExact width) (temp : Nat) :
    ∀ p : WordLangProgHOL (BitVec width), InstSelGoal (C := C) (F := F) c temp p
  | .assign v exp => by
      intro st res rst loc he hv herr hl
      have ha := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.1
      rw [ha] at he
      simp only [everyVarHOL, Bool.and_eq_true, decide_eq_true_eq] at hv
      rcases hw : wordExp st exp with _ | w
      · simp only [hw, Prod.mk.injEq] at he; exact absurd he.1.symm herr
      simp only [hw, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hE := flatten_exp_ok _ st w (pull_exp_ok exp st w hw)
      have hEv := flatten_exp_every_var_exp _ _ (pull_exp_every_var_exp _ exp hv.2)
      obtain ⟨loc', hev, hpost⟩ := inst_select_exp_thm c v temp (flattenExp (pullExp exp)) st w loc
        ⟨flatten_exp_binary_branch_exp _, hEv, hl, hE⟩
      refine ⟨loc', hev, ?_⟩
      intro x hx
      have hp := hpost x
      by_cases hxv : x = v
      · subst hxv
        rw [if_pos rfl] at hp
        show sptLookup x (sptInsert x w st.locals) = sptLookup x loc'
        rw [sptLookup_sptInsert_same, hp]
      · rw [if_neg hxv, if_pos hx] at hp
        show sptLookup x (sptInsert v w st.locals) = sptLookup x loc'
        rw [sptLookup_sptInsert_ne _ _ _ _ hxv, hp]
  | .set nm exp => by
      intro st res rst loc he hv herr hl
      have hs := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.1
      rw [hs] at he
      simp only [everyVarHOL] at hv
      by_cases hnm : nm = .handler ∨ nm = .bitmapBase
      · rw [if_pos hnm, Prod.mk.injEq] at he; exact absurd he.1.symm herr
      rw [if_neg hnm] at he
      rcases hw : wordExp st exp with _ | w
      · simp only [hw, Prod.mk.injEq] at he; exact absurd he.1.symm herr
      simp only [hw, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hE := flatten_exp_ok _ st w (pull_exp_ok exp st w hw)
      have hEv := flatten_exp_every_var_exp _ _ (pull_exp_every_var_exp _ exp hv)
      obtain ⟨loc', hev, hpost⟩ := inst_select_exp_thm c temp temp (flattenExp (pullExp exp)) st w
        loc ⟨flatten_exp_binary_branch_exp _, hEv, hl, hE⟩
      obtain ⟨ht, hlow⟩ := instSelPost_temp (temp := temp) hpost
      refine ⟨loc', ?_, fun x hx => (hlow x hx).symm⟩
      show evaluate (.seq (instSelectExp c temp temp (flattenExp (pullExp exp)))
        (.set nm (.var temp))) { st with locals := loc } = _
      rw [evaluate_seq_none _ _ _ _ hev, hs, if_neg hnm]
      have hv' : wordExp { st with locals := loc' } (.var temp) = some w := by
        simp [wordExp, getVar, ht]
      simp only [hv']
      rfl
  | .store exp var => by
      intro st res rst loc he hv herr hl
      have hs := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.1
      rw [hs] at he
      simp only [everyVarHOL, Bool.and_eq_true, decide_eq_true_eq] at hv
      rcases hw : wordExp st exp with _ | (a | ⟨_, _⟩)
      all_goals first | (simp only [hw, Prod.mk.injEq] at he; exact absurd he.1.symm herr) | skip
      rcases hg : getVar var st with _ | x
      · simp only [hw, hg, Prod.mk.injEq] at he; exact absurd he.1.symm herr
      simp only [hw, hg] at he
      rcases hm : memStore a x st with _ | s1
      · simp only [hm, Prod.mk.injEq] at he; exact absurd he.1.symm herr
      simp only [hm, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hs1 : s1.locals = st.locals := by
        unfold memStore at hm; split at hm <;> cases hm; rfl
      have hE := flatten_exp_ok _ st _ (pull_exp_ok exp st _ hw)
      have hEv := flatten_exp_every_var_exp _ _ (pull_exp_every_var_exp _ exp hv.2)
      have hEb := flatten_exp_binary_branch_exp (pullExp exp)
      have tail : ∀ (off : BitVec width) (loc' : Spt (WordLocW width)),
          (∀ y, y < temp → sptLookup y loc' = sptLookup y st.locals) →
          wordExp { st with locals := loc' } (.op .add [.var temp, .const off]) =
            some (.word a) →
          ∃ loc'', evaluate (.inst (.mem .store var (.addr temp off))) { st with locals := loc' } =
            (none, { s1 with locals := loc'' }) ∧ LrPost temp none s1.locals loc'' := by
        intro off loc' hlow hwa
        refine ⟨loc', ?_, fun y hy => by rw [hs1, hlow y hy]⟩
        have hgv : getVar var { st with locals := loc' } = some x := by
          show sptLookup var loc' = some x
          rw [hlow var hv.1]; exact hg
        rw [evaluate_inst_eq]
        simp only [inst, hwa, hgv, memStore_withLocals, hm, Option.map_some]
      by_cases hpat : ∃ e' off, flattenExp (pullExp exp) = .op .add [e', .const off]
      · obtain ⟨e', off, hpe⟩ := hpat
        by_cases hoff : addrOffsetOk c off = true
        · have hsel : instSelect c temp (.store exp var) =
              .seq (instSelectExp c temp temp e') (.inst (.mem .store var (.addr temp off))) := by
            simp only [instSelect, hpe, hoff, if_true]
          rw [hpe] at hE hEv hEb
          have hb' : binaryBranchExp e' = true := by
            rw [binaryBranchExp] at hEb
            · simp at hEb; exact hEb.1
            · nofun
          have hev' : everyVarExpHOL (fun x => decide (x < temp)) e' = true := by
            simp [everyVarExpHOL, everyVarExpsHOL] at hEv
            simpa using hEv
          rw [wordExp_op] at hE
          rcases hw1 : wordExp st e' with _ | (w1 | ⟨_, _⟩) <;>
            simp [hw1, theWords, wordExp] at hE
          obtain ⟨loc', hev'', hpost⟩ :=
            inst_select_exp_thm c temp temp e' st (.word w1) loc ⟨hb', hev', hl, hw1⟩
          obtain ⟨ht, hlow⟩ := instSelPost_temp (temp := temp) hpost
          obtain ⟨loc'', h1, h2⟩ := tail off loc' hlow (by
            rw [wordExp_op]; simp [wordExp, getVar, ht, theWords, hE])
          exact ⟨loc'', by rw [hsel, evaluate_seq_none _ _ _ _ hev'']; exact h1, h2⟩
        · have hsel : instSelect c temp (.store exp var) =
              .seq (instSelectExp c temp temp (flattenExp (pullExp exp)))
                (.inst (.mem .store var (.addr temp 0))) := by
            simp only [instSelect, hpe, hoff, Bool.false_eq_true, if_false]
          obtain ⟨loc', hev'', hpost⟩ := inst_select_exp_thm c temp temp _ st (.word a) loc
            ⟨hEb, hEv, hl, hE⟩
          obtain ⟨ht, hlow⟩ := instSelPost_temp (temp := temp) hpost
          obtain ⟨loc'', h1, h2⟩ := tail 0 loc' hlow (by
            rw [wordExp_op]; simp [wordExp, getVar, ht, theWords, wordOpHOL, wordOp])
          exact ⟨loc'', by rw [hsel, evaluate_seq_none _ _ _ _ hev'']; exact h1, h2⟩
      · have hsel : instSelect c temp (.store exp var) =
            .seq (instSelectExp c temp temp (flattenExp (pullExp exp)))
              (.inst (.mem .store var (.addr temp 0))) := by
          simp only [instSelect]
          split
          · exact absurd ⟨_, _, ‹_›⟩ hpat
          · rfl
        obtain ⟨loc', hev'', hpost⟩ := inst_select_exp_thm c temp temp _ st (.word a) loc
          ⟨hEb, hEv, hl, hE⟩
        obtain ⟨ht, hlow⟩ := instSelPost_temp (temp := temp) hpost
        obtain ⟨loc'', h1, h2⟩ := tail 0 loc' hlow (by
          rw [wordExp_op]; simp [wordExp, getVar, ht, theWords, wordOpHOL, wordOp])
        exact ⟨loc'', by rw [hsel, evaluate_seq_none _ _ _ _ hev'']; exact h1, h2⟩
  | .seq p1 p2 => by
      intro st res rst loc he hv herr hl
      have hq := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [hq] at he
      simp only [everyVarHOL, Bool.and_eq_true] at hv
      rcases h1 : evaluate p1 st with ⟨r1, s1⟩
      rw [h1] at he
      have hr1 : r1 ≠ some .error := by
        rintro rfl; simp only [Prod.mk.injEq] at he; exact herr he.1.symm
      obtain ⟨loc1, hev1, hpost1⟩ := instSel_aux c temp p1 st r1 s1 loc h1 hv.1 hr1 hl
      show ∃ loc', evaluate (.seq (instSelect c temp p1) (instSelect c temp p2))
        { st with locals := loc } = _ ∧ _
      cases r1 with
      | none =>
        simp only at he
        obtain ⟨loc2, hev2, hpost2⟩ := instSel_aux c temp p2 s1 res rst loc1 he hv.2 herr hpost1
        exact ⟨loc2, by rw [evaluate_seq_none _ _ _ _ hev1]; exact hev2, hpost2⟩
      | some x =>
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨loc1, by rw [hq, hev1], hpost1⟩
  | .mustTerminate p1 => by
      intro st res rst loc he hv herr hl
      have hm := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      rw [hm] at he
      simp only [everyVarHOL] at hv
      by_cases hz : st.termdep = 0
      · rw [if_pos hz, Prod.mk.injEq] at he; exact absurd he.1.symm herr
      rw [if_neg hz] at he
      rcases hq : evaluate p1 { st with
          clock := wordSemMustTerminateLimit width
          termdep := st.termdep - 1 } with ⟨r1, s1⟩
      rw [hq] at he
      have key : r1 ≠ some .timeOut ∧ res = r1 ∧
          rst = { s1 with clock := st.clock, termdep := st.termdep } := by
        rcases r1 with _ | (_ | _ | _ | _ | _ | _ | _ | _) <;>
          simp only [Prod.mk.injEq] at he <;>
          first
            | exact absurd he.1.symm herr
            | exact ⟨by simp, he.1.symm, he.2.symm⟩
      obtain ⟨hr1, rfl, rfl⟩ := key
      obtain ⟨loc1, hev1, hpost1⟩ := instSel_aux c temp p1 _ _ s1 loc hq hv herr hl
      refine ⟨loc1, ?_, hpost1⟩
      show evaluate (.mustTerminate (instSelect c temp p1)) { st with locals := loc } = _
      rw [hm, if_neg hz]
      have hev1' : evaluate (instSelect c temp p1) { { st with locals := loc } with
          clock := wordSemMustTerminateLimit width
          termdep := st.termdep - 1 } = (res, { s1 with locals := loc1 }) := hev1
      rw [hev1']
      rcases res with _ | (_ | _ | _ | _ | _ | _ | _ | _) <;> first | exact absurd rfl hr1 | rfl
  | .shareInst op v exp => by
      intro st res rst loc he hv herr hl
      simp only [everyVarHOL, Bool.and_eq_true, decide_eq_true_eq] at hv
      have hsi : ∀ (s : WordSemStateFiniteExact width C F) (e1 e2 : WordLangExpHOL (BitVec width)),
          wordExp s e1 = wordExp s e2 →
            evaluate (.shareInst op v e1) s = evaluate (.shareInst op v e2) s := by
        intro s e1 e2 h; rw [evaluate, evaluate, h]
      rcases hw : wordExp st exp with _ | (ad | ⟨_, _⟩)
      all_goals first
        | (rw [evaluate, hw] at he; simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr)
        | skip
      have hc : wordExp st (.const ad) = some (.word ad) := by rw [wordExp]
      have he' : evaluate (.shareInst op v (.const ad)) st = (res, rst) := by
        rw [← hsi st exp _ (hw.trans hc.symm)]; exact he
      have hvc : everyVarHOL (fun x => decide (x < temp)) (.shareInst op v (.const ad)) = true := by
        simp [everyVarHOL, everyVarExpHOL, hv.1]
      have finish : ∀ (X : WordLangExpHOL (BitVec width)) (loc' : Spt (WordLocW width)),
          (∀ y, y < temp → sptLookup y loc' = sptLookup y st.locals) →
          wordExp { st with locals := loc' } X = some (.word ad) →
          ∃ loc'', evaluate (.shareInst op v X) { st with locals := loc' } =
            (res, { rst with locals := loc'' }) ∧ LrPost temp res rst.locals loc'' := by
        intro X loc' hlow hX
        obtain ⟨loc'', h1, h2⟩ := lr_shareInst temp op v (.const ad) st res rst loc' he' herr hvc
          (fun y hy => (hlow y hy).symm)
        refine ⟨loc'', ?_, h2⟩
        rw [hsi _ X (.const ad) (by rw [hX, wordExp])]
        exact h1
      have hE := flatten_exp_ok _ st _ (pull_exp_ok exp st _ hw)
      have hEv := flatten_exp_every_var_exp _ _ (pull_exp_every_var_exp _ exp hv.2)
      have hEb := flatten_exp_binary_branch_exp (pullExp exp)
      have generic : instSelect c temp (.shareInst op v exp) =
          .seq (instSelectExp c temp temp (flattenExp (pullExp exp))) (.shareInst op v (.var temp)) →
          ∃ loc', evaluate (instSelect c temp (.shareInst op v exp)) { st with locals := loc } =
            (res, { rst with locals := loc' }) ∧ LrPost temp res rst.locals loc' := by
        intro hsel
        obtain ⟨loc', hev'', hpost⟩ := inst_select_exp_thm c temp temp _ st (.word ad) loc
          ⟨hEb, hEv, hl, hE⟩
        obtain ⟨ht, hlow⟩ := instSelPost_temp (temp := temp) hpost
        obtain ⟨loc'', h1, h2⟩ := finish (.var temp) loc' hlow (by simp [wordExp, getVar, ht])
        exact ⟨loc'', by rw [hsel, evaluate_seq_none _ _ _ _ hev'']; exact h1, h2⟩
      by_cases hpat : ∃ e' off, flattenExp (pullExp exp) = .op .add [e', .const off]
      · obtain ⟨e', off, hpe⟩ := hpat
        by_cases hcond : ((op = .load ∨ op = .store) ∧ addrOffsetOk c off = true) ∨
            ((op = .load32 ∨ op = .store32) ∧ addrOffsetOk c off = true) ∨
            ((op = .load16 ∨ op = .store16) ∧ hwOffsetOk c off = true) ∨
            ((op = .load8 ∨ op = .store8) ∧ byteOffsetOk c off = true)
        · have hsel : instSelect c temp (.shareInst op v exp) =
              .seq (instSelectExp c temp temp e')
                (.shareInst op v (.op .add [.var temp, .const off])) := by
            simp only [instSelect, hpe]
            rw [if_pos hcond]
          rw [hpe] at hE hEv hEb
          have hb' : binaryBranchExp e' = true := by
            rw [binaryBranchExp] at hEb
            · simp at hEb; exact hEb.1
            · nofun
          have hev' : everyVarExpHOL (fun x => decide (x < temp)) e' = true := by
            simp [everyVarExpHOL, everyVarExpsHOL] at hEv
            simpa using hEv
          rw [wordExp_op] at hE
          rcases hw1 : wordExp st e' with _ | (w1 | ⟨_, _⟩) <;>
            simp [hw1, theWords, wordExp] at hE
          obtain ⟨loc', hev'', hpost⟩ :=
            inst_select_exp_thm c temp temp e' st (.word w1) loc ⟨hb', hev', hl, hw1⟩
          obtain ⟨ht, hlow⟩ := instSelPost_temp (temp := temp) hpost
          obtain ⟨loc'', h1, h2⟩ := finish (.op .add [.var temp, .const off]) loc' hlow (by
            rw [wordExp_op]; simp [wordExp, getVar, ht, theWords, hE])
          exact ⟨loc'', by rw [hsel, evaluate_seq_none _ _ _ _ hev'']; exact h1, h2⟩
        · apply generic
          simp only [instSelect, hpe]
          rw [if_neg hcond]
      · apply generic
        simp only [instSelect]
        split
        · exact absurd ⟨_, _, ‹_›⟩ hpat
        · rfl
  | .ite cmp r1 ri c1 c2 => by
      intro st res rst loc he hv herr hl
      have hi := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [hi] at he
      simp only [everyVarHOL, Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨⟨⟨hr1, hri⟩, hc1⟩, hc2⟩ := hv
      have hgv := locals_rel_get_var_simp r1 temp st loc ⟨hr1, hl⟩
      have hgi := locals_rel_get_var_imm_simp temp ri st loc ⟨hri, hl⟩
      show ∃ loc', evaluate (.ite cmp r1 ri (instSelect c temp c1) (instSelect c temp c2))
        { st with locals := loc } = _ ∧ _
      rw [hi, hgv, hgi]
      rcases hx : getVar r1 st with _ | x
      · simp only [hx, Prod.mk.injEq] at he; exact absurd he.1.symm herr
      rcases hy : WordSemStateFiniteExact.getVarImm ri st with _ | y
      · simp only [hx, hy, Prod.mk.injEq] at he; exact absurd he.1.symm herr
      simp only [hx, hy] at he ⊢
      rcases hw : wordSemWordCmp cmp x y with _ | (_ | _)
      · simp only [hw, Prod.mk.injEq] at he; exact absurd he.1.symm herr
      · simp only [hw] at he ⊢
        exact instSel_aux c temp c2 st res rst loc he hc2 herr hl
      · simp only [hw] at he ⊢
        exact instSel_aux c temp c1 st res rst loc he hc1 herr hl
  | .call ret dest args handler => by
      intro st res rst loc he hv herr hl
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      cases ret with
      | none =>
        cases handler with
        | none => exact lr_call temp none dest args none st res rst loc he herr hv hl
        | some hd =>
          exfalso
          rw [ht] at he
          rcases hg : WordSemStateFiniteExact.getVars args st with _ | xs <;> simp only [hg] at he
          · simp only [Prod.mk.injEq] at he; exact herr he.1.symm
          by_cases hbad : wordSemBadDestArgs dest args = true
          · simp only [hbad, if_true, Prod.mk.injEq] at he; exact herr he.1.symm
          simp only [hbad, Bool.false_eq_true, if_false] at he
          rcases hf : wordSemFindCode dest (wordSemAddRetLoc none xs) st.code st.stackSize with
            _ | ⟨a1, pr, ss⟩ <;> simp only [hf, Prod.mk.injEq] at he <;> exact herr he.1.symm
      | some rv =>
        obtain ⟨n, names, retHandler, l1, l2⟩ := rv
        have hargs : ∀ x ∈ args, x < temp := by
          rcases handler with _ | ⟨a, b, c', d⟩ <;>
            simp only [everyVarHOL, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv <;>
            exact hv.1
        have hnm : everyNameHOL (fun x => decide (x < temp)) names = true := by
          rcases handler with _ | ⟨a, b, c', d⟩ <;>
            simp only [everyVarHOL, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv <;>
            exact hv.2.1.1.2
        have hret : everyVarHOL (fun x => decide (x < temp)) retHandler = true := by
          rcases handler with _ | ⟨a, b, c', d⟩ <;>
            simp only [everyVarHOL, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv <;>
            exact hv.2.1.2
        have hsel : instSelect c temp (.call (some (n, names, retHandler, l1, l2)) dest args handler) =
            .call (some (n, names, instSelect c temp retHandler, l1, l2)) dest args
              (handler.map (fun hv => (hv.1, instSelect c temp hv.2.1, hv.2.2.1, hv.2.2.2))) := by
          rcases handler with _ | ⟨_, _, _, _⟩ <;> rfl
        have hpm : ∀ (envs : Spt (WordLocW width) × Spt (WordLocW width))
            (t : WordSemStateFiniteExact width C F),
            pushEnv envs (handler.map (fun hv => (hv.1, instSelect c temp hv.2.1, hv.2.2.1, hv.2.2.2)))
              t = pushEnv envs handler t := by
          intro envs t
          rcases handler with _ | ⟨_, _, _, _⟩ <;> rfl
        rw [hsel]
        rw [ht] at he ⊢
        rw [locals_rel_get_vars_simp args temp st loc ⟨hargs, hl⟩]
        rcases hg : WordSemStateFiniteExact.getVars args st with _ | xs
        · simp only [hg, Prod.mk.injEq] at he; exact absurd he.1.symm herr
        simp only [hg] at he ⊢
        by_cases hbad : wordSemBadDestArgs dest args = true
        · simp only [hbad, if_true, Prod.mk.injEq] at he; exact absurd he.1.symm herr
        simp only [hbad, Bool.false_eq_true, if_false] at he ⊢
        simp only [wordSemAddRetLoc] at he ⊢
        rcases hf : wordSemFindCode dest (.loc l1 l2 :: xs) st.code st.stackSize with
          _ | ⟨args1, prog, ss⟩
        · simp only [hf, Prod.mk.injEq] at he; exact absurd he.1.symm herr
        have hf' : wordSemFindCode dest (.loc l1 l2 :: xs) ({ st with locals := loc } :
            WordSemStateFiniteExact width C F).code st.stackSize = some (args1, prog, ss) := hf
        simp only [hf] at he
        simp only [hf']
        by_cases hdc : sptDomainEmpty names.fst ∨ ¬ n.Nodup
        · simp only [hdc, if_true, Prod.mk.injEq] at he; exact absurd he.1.symm herr
        simp only [hdc, if_false] at he ⊢
        rcases hce : wordSemCutEnvs names st.locals with _ | envs
        · simp only [hce, Prod.mk.injEq] at he; exact absurd he.1.symm herr
        have hce' := locals_rel_cut_envs temp st.locals loc names envs ⟨hl, hnm, hce⟩
        simp only [hce] at he
        rw [show wordSemCutEnvs names ({ st with locals := loc } :
            WordSemStateFiniteExact width C F).locals = some envs from hce']
        simp only
        have e1 : WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs (handler.map (fun hv => (hv.1, instSelect c temp hv.2.1, hv.2.2.1, hv.2.2.2)))
              (decClock { st with locals := loc })) =
            WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock st)) := by
          rw [hpm]
          rcases handler with _ | ⟨_, _, _, _⟩ <;> rfl
        have e2 : (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs (handler.map (fun hv => (hv.1, instSelect c temp hv.2.1, hv.2.2.1, hv.2.2.2)))
              { st with locals := loc })).stackMax =
            (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler st)).stackMax := by
          rw [hpm]
          rcases handler with _ | ⟨_, _, _, _⟩ <;> rfl
        rw [e1, e2]
        by_cases hz : st.clock = 0
        · have hz' : ({ st with locals := loc } : WordSemStateFiniteExact width C F).clock = 0 := hz
          rw [if_pos hz'] 
          rw [if_pos hz, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact ⟨_, rfl, lrPost_refl temp _ _⟩
        have hz' : ¬ ({ st with locals := loc } : WordSemStateFiniteExact width C F).clock = 0 := hz
        rw [if_neg hz']
        rw [if_neg hz] at he
        rcases hcv : evaluate prog
            (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock st))) with
          ⟨rc, s2⟩
        rw [hcv] at he
        rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
        rotate_left
        · simp only at he ⊢
          by_cases hx : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ n.length
          · simp only [hx, if_true, Prod.mk.injEq] at he; exact absurd he.1.symm herr
          simp only [hx, if_false] at he ⊢
          rcases hp : popEnv s2 with _ | s1
          · simp only [hp, Prod.mk.injEq] at he; exact absurd he.1.symm herr
          simp only [hp] at he ⊢
          by_cases hdom : sptDomainEqUnion s1.locals envs.fst envs.snd
          · simp only [hdom, if_true] at he ⊢
            obtain ⟨loc', h1, h2⟩ := instSel_aux c temp retHandler (setVars n ys s1) res rst
              (setVars n ys s1).locals he hret herr (fun _ _ => rfl)
            exact ⟨loc', h1, h2⟩
          · simp only [hdom, if_false, Prod.mk.injEq] at he; exact absurd he.1.symm herr
        · cases handler with
          | none =>
            simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            exact ⟨_, rfl, lrPost_refl temp _ _⟩
          | some hd =>
            obtain ⟨n', hprog, l1', l2'⟩ := hd
            have hhp : everyVarHOL (fun x => decide (x < temp)) hprog = true := by
              simp only [everyVarHOL, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv
              exact hv.2.2.2
            simp only [Option.map_some] at he ⊢
            by_cases hx : x ≠ WordLocW.loc l1' l2'
            · rw [if_pos hx, Prod.mk.injEq] at he; exact absurd he.1.symm herr
            rw [if_neg hx] at he ⊢
            by_cases hdom : sptDomainEqUnion s2.locals envs.fst envs.snd
            · rw [if_pos hdom] at he ⊢
              exact instSel_aux c temp hprog (setVar n' y s2) res rst (setVar n' y s2).locals he
                hhp herr (fun _ _ => rfl)
            · rw [if_neg hdom, Prod.mk.injEq] at he; exact absurd he.1.symm herr
        all_goals
          simp only [Prod.mk.injEq] at he
          first
            | exact absurd he.1.symm herr
            | (obtain ⟨rfl, rfl⟩ := he
               exact ⟨_, rfl, lrPost_refl temp _ _⟩)
  | .loop names body exitNames => by
      intro st res rst loc he hv herr hl
      simp only [everyVarHOL, Bool.and_eq_true] at hv
      have hn : everyNameHOL (fun x => decide (x < temp)) (names, .ln) = true := by
        simp only [everyNameHOL, hv.1.1, Bool.true_and]
        rfl
      have hx : everyNameHOL (fun x => decide (x < temp)) (exitNames, .ln) = true := by
        simp only [everyNameHOL, hv.2, Bool.true_and]
        rfl
      exact instSel_loop_aux c temp names exitNames body
        (fun st' r rs l h1 h2 h3 => instSel_aux c temp body st' r rs l h1 hv.1.2 h2 h3)
        hn hx _ st rfl res rst loc he herr hl
  | .skip => instSel_default c temp _ rfl
  | .move a b => instSel_default c temp _ rfl
  | .inst a => instSel_default c temp _ rfl
  | .get a b => instSel_default c temp _ rfl
  | .alloc a b => instSel_default c temp _ rfl
  | .storeConsts a b d e f => instSel_default c temp _ rfl
  | .raise a => instSel_default c temp _ rfl
  | WordLangProgHOL.return a b => instSel_default c temp _ rfl
  | WordLangProgHOL.break a => instSel_default c temp _ rfl
  | WordLangProgHOL.continue a => instSel_default c temp _ rfl
  | .opCurrHeap a b d => instSel_default c temp _ rfl
  | .tick => instSel_default c temp _ rfl
  | .locValue a b => instSel_default c temp _ rfl
  | .install a b d e f => instSel_default c temp _ rfl
  | .codeBufferWrite a b => instSel_default c temp _ rfl
  | .dataBufferWrite a b => instSel_default c temp _ rfl
  | .ffi a b d e f g => instSel_default c temp _ rfl
termination_by p => sizeOf p

end InstSelectThm

/-- Exact HOL `inst_select_Loop_helper` (`word_instProofScript.sml:1066-1131`). -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "inst_select_Loop_helper"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem inst_select_Loop_helper {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (s : WordSemStateFiniteExact width C F) (names : WordLangNumSetHOL)
      (prog : WordLangProgHOL (BitVec width)) (exit_names : WordLangNumSetHOL)
      (res : Option (WordSemResult width)) (rst : WordSemStateFiniteExact width C F)
      (c : AsmConfigExact width) (temp : Nat) (loc : Spt (WordLocW width)),
      (∀ (st : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
          (rst : WordSemStateFiniteExact width C F) (loc : Spt (WordLocW width)),
          evaluate prog st = (res, rst) ∧ res ≠ some .error ∧ wordLocalsRel temp st.locals loc →
          ∃ loc', evaluate (instSelect c temp prog) { st with locals := loc } =
              (res, { rst with locals := loc' }) ∧
            match res with
            | none => wordLocalsRel temp rst.locals loc'
            | some (.break _) => wordLocalsRel temp rst.locals loc'
            | some (.continue _) => wordLocalsRel temp rst.locals loc'
            | some _ => rst.locals = loc') ∧
        evaluate (.loop names prog exit_names) s = (res, rst) ∧ res ≠ some .error ∧
        everyVarHOL (fun x => decide (x < temp)) prog = true ∧
        everyNameHOL (fun x => decide (x < temp)) (names, .ln) = true ∧
        everyNameHOL (fun x => decide (x < temp)) (exit_names, .ln) = true ∧
        wordLocalsRel temp s.locals loc →
      ∃ loc', evaluate (.loop names (instSelect c temp prog) exit_names) { s with locals := loc } =
          (res, { rst with locals := loc' }) ∧
        match res with
        | none => wordLocalsRel temp rst.locals loc'
        | some (.break _) => wordLocalsRel temp rst.locals loc'
        | some (.continue _) => wordLocalsRel temp rst.locals loc'
        | some _ => rst.locals = loc' := by
  rintro s names prog exitNames res rst c temp loc ⟨ih, he, herr, _, hn, hx, hl⟩
  have ih' : ∀ (st : WordSemStateFiniteExact width C F) (r : Option (WordSemResult width))
      (rs : WordSemStateFiniteExact width C F) (l : Spt (WordLocW width)),
      evaluate prog st = (r, rs) → r ≠ some .error → wordLocalsRel temp st.locals l →
      ∃ loc', evaluate (instSelect c temp prog) { st with locals := l } =
        (r, { rs with locals := loc' }) ∧ LrPost temp r rs.locals loc' := by
    intro st r rs l h1 h2 h3
    obtain ⟨loc', e1, e2⟩ := ih st r rs l ⟨h1, h2, h3⟩
    refine ⟨loc', e1, ?_⟩
    rcases r with _ | (_ | _ | _ | _ | _ | _ | _ | _) <;> exact e2
  obtain ⟨loc', h1, h2⟩ :=
    instSel_loop_aux c temp names exitNames prog ih' hn hx _ s rfl res rst loc he herr hl
  rcases res with _ | (_ | _ | _ | _ | _ | _ | _ | _) <;> exact ⟨loc', h1, h2⟩

/-- Exact HOL `inst_select_thm` (`word_instProofScript.sml:724-749`, with its
    resumed `Assign`, `Set`, `Store`, `Seq`, `MustTerminate`, `ShareInst`, `If`,
    `Call` and `Loop` cases): the instruction-selected program gives the same
    result with possibly more locals used. -/
@[hol "cakeml/compiler/backend/proofs/word_instProofScript.sml" "inst_select_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem inst_select_thm {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (c : AsmConfigExact width) (temp : Nat) (prog : WordLangProgHOL (BitVec width))
      (st : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
      (rst : WordSemStateFiniteExact width C F) (loc : Spt (WordLocW width)),
      evaluate prog st = (res, rst) ∧ everyVarHOL (fun x => decide (x < temp)) prog = true ∧
        res ≠ some .error ∧ wordLocalsRel temp st.locals loc →
      ∃ loc', evaluate (instSelect c temp prog) { st with locals := loc } =
          (res, { rst with locals := loc' }) ∧
        match res with
        | none => wordLocalsRel temp rst.locals loc'
        | some (.break _) => wordLocalsRel temp rst.locals loc'
        | some (.continue _) => wordLocalsRel temp rst.locals loc'
        | some _ => rst.locals = loc' := by
  rintro c temp prog st res rst loc ⟨he, hv, herr, hl⟩
  obtain ⟨loc', h1, h2⟩ := instSel_aux c temp prog st res rst loc he hv herr hl
  rcases res with _ | (_ | _ | _ | _ | _ | _ | _ | _) <;> exact ⟨loc', h1, h2⟩

end Compiler.Backend.WordInst

end Flapjack
