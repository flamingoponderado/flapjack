module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Assembly
public import Flapjack.Compiler.Backend.DataToWord.Proofs.StateRelExt
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GcFunConstOk
public import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileWordToWord

@[expose] public section

/-! Drafts of `compile_correct_lemma` and `compile_correct` (`data_to_wordProofScript.sml` lines
1157-1289) taking the not-yet-ported `Assign` case of `data_compile_correct` as
a hypothesis. This is Flapjack proof infrastructure, not a HOL port: once
`assign_thm` lands, discharging `assignCase` gives the tagged theorem. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- `compile_correct_lemma`, modulo the `Assign` case. -/
theorem compileCorrectLemma_of_assign {width : Nat} [NeZero width] {C F : Type}
    (assignCase : ∀ (dest : Nat) (op : ClosLang.Op) (names : List Nat) (live : Option NumSet)
      (s : Flapjack.Compiler.Backend.DataSem.State C F),
      dataCompileCorrectInduction (width := width) (.assign dest op names live) s)
    (s : Flapjack.Compiler.Backend.DataSem.State C F) (c : Flapjack.Compiler.Backend.DataToWord.Config)
    (l1 l2 : Nat)
    (res : Option (Result (List Flapjack.Compiler.Backend.DataSem.Value) Flapjack.Compiler.Backend.DataSem.Value))
    (s1 : Flapjack.Compiler.Backend.DataSem.State C F) (t : WordSemStateFiniteExact width C F)
    (start : Nat)
    (premises : DataSem.evaluate (.call none (some start) [] none) s = (res, s1) ∧
      res ≠ some (.err (.abort .typeError)) ∧ t.termdep > 1 ∧ stateRel c l1 l2 s t none []) :
    ∃ t1 res1,
      WordSemStateFiniteExact.evaluate (.call none (some start) [0] none) t = (res1, t1) ∧
      optionLe t1.stackMax s1.stackMax ∧
      (res1 = some .notEnoughSpace →
        t1.ffi.ioEvents.IsPrefix s1.ffi.ioEvents ∧ (c.gcKind ≠ .none → s1.safeForSpace = false)) ∧
      (res1 ≠ some .notEnoughSpace →
        match res with
        | none => t1.ffi = s1.ffi ∧ res1 = none
        | some (.val _) => t1.ffi = s1.ffi ∧ ∃ w, res1 = some (.result (.loc l1 l2) w)
        | some (.err (.raise _)) => t1.ffi = s1.ffi ∧ ∃ v w, res1 = some (.exception v w)
        | some (.err (.abort (.ffiError f))) => res1 = some (.finalFfi f) ∧ t1.ffi = s1.ffi
        | some (.err (.abort _)) => res1 = some .timeOut ∧ t1.ffi = s1.ffi) := by
  obtain ⟨run, notTypeError, depth, related⟩ := premises
  have compiled : (compileControl (width := width) c 0 0 (.call none (some start) [] none)).1 =
      .call none (some start) [0] none := by
    have h := compileControl_option (width := width) c 0 0 (.call none (some start) [] none)
    simp [compileControl?] at h
    rw [← h]
  obtain ⟨t1, res1, wordRun, stackBound, space, result⟩ :=
    dataCompileCorrect_of_assign assignCase (.call none (some start) [] none) s c 0 0 l1 l2 res s1 t []
      run notTypeError related depth
  rw [compiled] at wordRun
  refine ⟨t1, res1, wordRun, stackBound, space, fun hs => ?_⟩
  have h := result hs
  rcases res with _ | (values | (value | (_ | _ | f)))
  · exact ⟨h.1.1, h.2⟩
  · obtain ⟨w, _, rel, hr⟩ := h
    exact ⟨rel.1, w, hr⟩
  · obtain ⟨hf, w, _, _, _, hr, _⟩ := h
    exact ⟨hf, _, w, hr⟩
  · exact h
  · exact h
  · exact h

/-- Every sparse tree whose entries all have suitable preimages is the
`sptMap` image of a tree whose entries satisfy the chosen property.
Flapjack sparse-tree infrastructure (HOL builds such a tree with
`copy_shape`/`mapi` in `compile_correct`). -/
theorem sptMap_preimage {α β : Type} (f : α → β) :
    ∀ (l : Spt β) (P : Nat → α → Prop),
      (∀ n x, sptLookup n l = some x → ∃ y, P n y ∧ f y = x) →
      ∃ l' : Spt α, sptMap f l' = l ∧ ∀ n y, sptLookup n l' = some y → P n y := by
  intro l
  induction l with
  | ln => exact fun _ _ => ⟨.ln, rfl, fun _ _ h => by simp [sptLookup] at h⟩
  | ls x =>
    intro P h
    obtain ⟨y, hy, rfl⟩ := h 0 x (by simp [sptLookup])
    refine ⟨.ls y, rfl, fun n z hz => ?_⟩
    by_cases hn : n = 0
    · subst hn; simp [sptLookup] at hz; subst hz; exact hy
    · simp [sptLookup, hn] at hz
  | bn left right ihl ihr =>
    intro P h
    obtain ⟨l1, hl1, pl1⟩ := ihl (fun i => P (2 * i + 2)) (fun i x hx => h (2 * i + 2) x (by
      rw [sptLookup, if_neg (by omega), if_pos (by omega), show (2 * i + 2 - 1) / 2 = i by omega]; exact hx))
    obtain ⟨r1, hr1, pr1⟩ := ihr (fun i => P (2 * i + 1)) (fun i x hx => h (2 * i + 1) x (by
      rw [sptLookup, if_neg (by omega), if_neg (by omega), show (2 * i + 1 - 1) / 2 = i by omega]; exact hx))
    refine ⟨.bn l1 r1, by simp [sptMap, hl1, hr1], fun n z hz => ?_⟩
    by_cases hn : n = 0
    · simp [sptLookup, hn] at hz
    · by_cases he : n % 2 = 0
      · simp [sptLookup, hn, he] at hz
        have := pl1 _ z hz
        rwa [show 2 * ((n - 1) / 2) + 2 = n by omega] at this
      · simp [sptLookup, hn, he] at hz
        have := pr1 _ z hz
        rwa [show 2 * ((n - 1) / 2) + 1 = n by omega] at this
  | bs left x right ihl ihr =>
    intro P h
    obtain ⟨y, hy, rfl⟩ := h 0 x (by simp [sptLookup])
    obtain ⟨l1, hl1, pl1⟩ := ihl (fun i => P (2 * i + 2)) (fun i x hx => h (2 * i + 2) x (by
      rw [sptLookup, if_neg (by omega), if_pos (by omega), show (2 * i + 2 - 1) / 2 = i by omega]; exact hx))
    obtain ⟨r1, hr1, pr1⟩ := ihr (fun i => P (2 * i + 1)) (fun i x hx => h (2 * i + 1) x (by
      rw [sptLookup, if_neg (by omega), if_neg (by omega), show (2 * i + 1 - 1) / 2 = i by omega]; exact hx))
    refine ⟨.bs l1 y r1, by simp [sptMap, hl1, hr1], fun n z hz => ?_⟩
    by_cases hn : n = 0
    · subst hn; simp [sptLookup] at hz; subst hz; exact hy
    · by_cases he : n % 2 = 0
      · simp [sptLookup, hn, he] at hz
        have := pl1 _ z hz
        rwa [show 2 * ((n - 1) / 2) + 2 = n by omega] at this
      · simp [sptLookup, hn, he] at hz
        have := pr1 _ z hz
        rwa [show 2 * ((n - 1) / 2) + 1 = n by omega] at this

/-- `compile_correct`, modulo the `Assign` case of `data_compile_correct`. -/
theorem compileCorrect_of_assign {width : Nat} [NeZero width] {C F : Type}
    (assignCase : ∀ (dest : Nat) (op : ClosLang.Op) (names : List Nat) (live : Option NumSet)
      (s : Flapjack.Compiler.Backend.DataSem.State C F),
      dataCompileCorrectInduction (width := width) (.assign dest op names live) s)
    (x : Flapjack.Compiler.Backend.DataToWord.Config) (s : Flapjack.Compiler.Backend.DataSem.State C F)
    (l1 l2 : Nat)
    (res : Option (Result (List Flapjack.Compiler.Backend.DataSem.Value) Flapjack.Compiler.Backend.DataSem.Value))
    (s1 : Flapjack.Compiler.Backend.DataSem.State C F) (t : WordSemStateFiniteExact width C F)
    (start : Nat)
    (premises : DataSem.evaluate (.call none (some start) [] none) s = (res, s1) ∧
      res ≠ some (.err (.abort .typeError)) ∧ stateRelExt x l1 l2 s t) :
    ∃ ck t1 res1,
      WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
        (WordSemStateFiniteExact.incClock ck t) = (res1, t1) ∧
      optionLe t1.stackMax s1.stackMax ∧
      (res1 = some .notEnoughSpace →
        t1.ffi.ioEvents.IsPrefix s1.ffi.ioEvents ∧ (x.gcKind ≠ .none → s1.safeForSpace = false)) ∧
      (res1 ≠ some .notEnoughSpace →
        t1.ffi = s1.ffi ∧
        match res with
        | none => res1 = none
        | some (.val _) => ∃ w, res1 = some (.result (.loc l1 l2) w)
        | some (.err (.raise _)) => ∃ v w, res1 = some (.exception v w)
        | some (.err (.abort (.ffiError f))) => res1 = some (.finalFfi f)
        | some (.err (.abort _)) => res1 = some .timeOut) := by
  obtain ⟨run, notTypeError, t2, l, rel, dom, depth, ⟨tt, kk, aa, co, horacle, hcomp⟩, hcode, ht⟩ :=
    premises
  -- a word-to-word code table whose MustTerminate-free image is `l`
  let rmt : Nat × WordLangProgHOL (BitVec width) → Nat × WordLangProgHOL (BitVec width) :=
    fun p => (p.1, WordRemove.removeMustTerminate p.2)
  obtain ⟨l2', hmap, hl2'⟩ := sptMap_preimage rmt l
    (fun n y => ∃ v, sptLookup n t2.code = some v ∧ ∃ (col : Option (Spt Nat)) (t' : Bool) (k a : Nat)
      (c : Compiler.Encoders.Asm.AsmConfigExact width),
      y = (WordToWord.compileSingle t' k a c ((n, v), col)).2)
    (fun n p hp => by
      have hd : sptDomain t2.code n := by
        rw [dom]; simp [sptDomain, hp]
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hd
      obtain ⟨t', k', a', c', col, hl⟩ := hcode n v hv
      rw [hp] at hl
      cases hl
      exact ⟨_, ⟨v, hv, col, t', k', a', c', rfl⟩, rfl⟩)
  have codeRel2 : WordToWord.codeRel t2.code l2' := by
    intro n v hv
    have hd : sptDomain l n := by
      rw [← dom]; simp [sptDomain, hv]
    rw [← hmap] at hd
    simp only [sptDomain, sptLookup_sptMap] at hd
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (by simpa using hd)
    obtain ⟨v', hv', col, t', k, a, c, rfl⟩ := hl2' n y hy
    rw [hv] at hv'
    cases hv'
    exact ⟨col, t', k, a, c, hy⟩
  have dom2 : sptDomain t2.code = sptDomain l2' := by
    rw [dom, ← hmap]
    funext n
    simp [sptDomain, sptLookup_sptMap]
  have gcOk : Compiler.Backend.WordSimp.gcFunConstOk t2.gcFun := by
    rw [rel.2.2.2.1]
    exact gcFunConstOkWordGcFun
  obtain ⟨perm', clk, hw2w⟩ := WordToWord.compile_word_to_word_thm t2 l2' t.compile t.compileOracle
    tt kk aa co start ⟨codeRel2, dom2, hcomp, horacle, gcOk⟩
  have relPerm : stateRel x l1 l2 s { t2 with permute := perm' } none [] := rel
  obtain ⟨t1, res1, wordRun, stackBound, space, result⟩ :=
    compileCorrectLemma_of_assign assignCase s x l1 l2 res s1 { t2 with permute := perm' } start
      ⟨run, notTypeError, depth, relPerm⟩
  simp only at hw2w
  rw [wordRun] at hw2w
  have notErr : res1 ≠ some .error := by
    intro he
    subst he
    have h := result (by simp)
    rcases res with _ | (values | (value | (_ | _ | f)))
    all_goals simp at h
  simp only [notErr, if_false] at hw2w
  have hS : WordSemStateFiniteExact.incClock clk t =
      { t2 with
        code := sptMap (fun p => (p.1, WordRemove.removeMustTerminate p.2)) l2'
        clock := t2.clock + clk
        termdep := 0
        compile := t.compile
        compileOracle := t.compileOracle } := by
    have hm : sptMap (fun p => (p.1, WordRemove.removeMustTerminate p.2)) l2' = l := hmap
    rw [hm]
    conv_lhs => rw [ht]
    rfl
  rw [← hS] at hw2w
  cases hrun : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      (WordSemStateFiniteExact.incClock clk t) with
  | mk r1 rst1 =>
  rw [hrun] at hw2w
  obtain ⟨rfl, _, hffi, hmax⟩ := hw2w
  refine ⟨clk, rst1, r1, hrun, by rw [hmax]; exact stackBound, ?_, ?_⟩
  · intro hn
    rw [hffi]
    exact space hn
  · intro hn
    have h := result hn
    rcases res with _ | (values | (value | (_ | _ | f)))
    · exact ⟨hffi.trans h.1, h.2⟩
    · exact ⟨hffi.trans h.1, h.2⟩
    · exact ⟨hffi.trans h.1, h.2⟩
    · exact ⟨hffi.trans h.2, h.1⟩
    · exact ⟨hffi.trans h.2, h.1⟩
    · exact ⟨hffi.trans h.2, h.1⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs
