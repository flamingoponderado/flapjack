module

public import Flapjack.Compiler.Backend.DataToWord.CompleteStubs
public import Flapjack.Compiler.Backend.WordBignum.Proofs.CompileIndices
public import Flapjack.Compiler.Backend.DataToWord.Proofs.LabPres

@[expose] public section

set_option autoImplicit false

/-! Facts about the data-to-word stub table (`data_to_wordProofScript.sml`,
`stub_labels`, `stubs_no_share_inst`, `ALL_DISTINCT_MAP_FST_stubs`,
`MAP_FST_stubs_bound`, `stubs_fst_def` and `stubs_fst_eq`). HOL proves them
by `EVAL`; here the fixed stubs are unfolded by `simp`, and the generated
bignum stubs use the width-independent index computation of
`WordBignum.Proofs.CompileIndices` and a structural label invariant of the
mini compiler. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.Compiler.Backend.BackendCommon Flapjack.Compiler.Backend.DataToWord

/-! ### Code indices -/

/-- Keys and entries of a table built by an option-valued `mapM` (Flapjack
infrastructure). -/
theorem mapM_keyed' {β : Type} (f : Nat → Option (Nat × β))
    (F : Nat → Option (Nat × Nat × β))
    (hF : ∀ loc r, F loc = some r → r.1 = loc ∧ f loc = some (r.2.1, r.2.2)) :
    ∀ (xs : List Nat) (L : List (Nat × Nat × β)), xs.mapM F = some L →
      L.map Prod.fst = xs ∧ ∀ e ∈ L, f e.1 = some (e.2.1, e.2.2) := by
  intro xs
  induction xs with
  | nil => intro L h; simp at h; subst h; simp
  | cons x xs ih =>
    intro L h
    rw [List.mapM_cons] at h
    rcases hx : F x with _ | r
    · simp [hx] at h
    rcases hxs : xs.mapM F with _ | L'
    · simp [hx, hxs] at h
    simp [hx, hxs] at h
    subst h
    obtain ⟨h1, h2⟩ := ih L' hxs
    obtain ⟨h3, h4⟩ := hF x r hx
    refine ⟨by simp [h1, h3], ?_⟩
    intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · rw [h3]; exact h4
    · exact h2 e he

/-- Keys and entries of the fixed table built by `mapM` (Flapjack infrastructure). -/
theorem mapM_keyed {β : Type} (f : Nat → Option (Nat × β)) (xs : List Nat)
    (L : List (Nat × Nat × β))
    (h : xs.mapM (fun loc => do let (a, b) ← f loc; pure (loc, a, b)) = some L) :
    L.map Prod.fst = xs ∧ ∀ e ∈ L, f e.1 = some (e.2.1, e.2.2) := by
  refine mapM_keyed' f _ ?_ xs L h
  intro loc r hr
  rcases hf : f loc with _ | ⟨a, b⟩
  · simp [hf] at hr
  · simp [hf] at hr; subst hr; simp

/-- The fixed stub locations, in table order. -/
def fixedLocations : List Nat :=
  [fromListLocation, fromList1Location, refByteLocation, refArrayLocation, replicateLocation,
   anyArithLocation, addLocation, subLocation, mulLocation, divLocation, modLocation,
   compare1Location, compareLocation, equal1Location, equalLocation, longDiv1Location,
   longDivLocation, installLocation, installCodeLocation, installDataLocation, appendLocation,
   appendMainLoopLocation, appendLenLoopLocation, xorLoopLocation, unusedLocation,
   stringCmpLoopLocation, memCopyLocation, byteCopyLocation, byteCopyAddLocation,
   byteCopySubLocation, byteCopyNewLocation, dummyLocation]

theorem fixedStubs_keyed {width : Nat} [NeZero width] (conf : Config)
    (L : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (h : fixedStubs? (width := width) conf = some L) :
    L.map Prod.fst = fixedLocations ∧
      ∀ e ∈ L, compileConfiguredStub? conf e.1 = some (e.2.1, e.2.2) :=
  mapM_keyed (compileConfiguredStub? (width := width) conf) fixedLocations L h

/-- The stub table is the fixed table followed by the generated bignum stubs. -/
theorem stubs_eq {width : Nat} [NeZero width] (conf : Config) :
    ∃ L, fixedStubs? (width := width) conf = some L ∧
      stubs (width := width) conf = L ++ WordBignum.generatedBignumStubs width bignumLocation := by
  obtain ⟨L, h⟩ := fixedStubs_succeeds (width := width) conf
  exact ⟨L, h, by simp [stubs, h]⟩

/-- HOL `stubs_fst`, the evaluated list of stub code indices. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "stubs_fst_def"]
def stubsFst : List Nat :=
  [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 29, 30, 31, 33, 34, 35, 36,
   37, 38, 24, 25, 26, 27, 28, 32, 39, 61, 60, 59, 58, 54, 57, 56, 55, 53, 52, 51, 50, 49, 47,
   48, 46, 45, 44, 43, 42, 41, 40]

/-- Exact HOL `stubs_fst_eq`: `MAP FST (stubs (:α) c) = stubs_fst`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "stubs_fst_eq"
  (words_as_type_indexed_bitvec)]
theorem stubsFst_eq {width : Nat} [NeZero width] (c : Config) :
    (stubs c : List (Nat × Nat × WordLangProgHOL (BitVec width))).map Prod.fst = stubsFst := by
  obtain ⟨L, hL, hs⟩ := stubs_eq (width := width) c
  rw [hs, List.map_append, (fixedStubs_keyed c L hL).1]
  have hb : bignumLocation = 39 := rfl
  rw [hb, WordBignum.Indices.generatedBignumStubs_map_fst]
  rfl

/-- Exact HOL `ALL_DISTINCT_MAP_FST_stubs`. The HOL `a : α itself` is the
word width. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "ALL_DISTINCT_MAP_FST_stubs"
  (words_as_type_indexed_bitvec)]
theorem allDistinct_mapFst_stubs {width : Nat} [NeZero width] (c : Config) :
    ((stubs c : List (Nat × Nat × WordLangProgHOL (BitVec width))).map Prod.fst).Nodup := by
  rw [stubsFst_eq]
  decide

/-- Exact HOL `MAP_FST_stubs_bound`. The HOL `a : α itself` is the word width. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "MAP_FST_stubs_bound"
  (words_as_type_indexed_bitvec)]
theorem mapFst_stubs_bound {width : Nat} [NeZero width] (c : Config) (n : Nat) :
    n ∈ (stubs c : List (Nat × Nat × WordLangProgHOL (BitVec width))).map Prod.fst →
      n < dataNumStubs := by
  rw [stubsFst_eq]
  have : ∀ m ∈ stubsFst, m < 62 := by decide
  exact this n

/-! ### Labels and `ShareInst` of the generated bignum stubs -/

/-- A compiled bignum code entry: labels at its own index from 2, distinct,
and no `ShareInst` (Flapjack infrastructure). -/
def GoodCode {width : Nat} [NeZero width] (idx : Nat) (p : WordLangProgHOL (BitVec width)) :
    Prop :=
  (∀ q ∈ extractLabels p, q.1 = idx ∧ 2 ≤ q.2) ∧ (extractLabels p).Nodup ∧
    noShareInstSubprogsHOL p = true

/-- The invariant of one compilation step: the program's labels are at `n` in
the label range it consumes, it has no `ShareInst`, and every cached entry is
good (Flapjack infrastructure). -/
def CompOk {width : Nat} [NeZero width] (n l : Nat)
    (r : WordLangProgHOL (BitVec width) × Nat × Nat × WordBignum.CodeAcc width) : Prop :=
  l ≤ r.2.1 ∧ (∀ q ∈ extractLabels r.1, q.1 = n ∧ l ≤ q.2 ∧ q.2 < r.2.1) ∧
    (extractLabels r.1).Nodup ∧ noShareInstSubprogsHOL r.1 = true ∧
    ∀ e ∈ r.2.2.2.2, GoodCode e.2.1 e.2.2

theorem extractLabels_loadRegs {width : Nat} [NeZero width] (xs : List Nat)
    (p : WordLangProgHOL (BitVec width)) :
    extractLabels (WordBignum.loadRegs xs p) = extractLabels p ∧
      noShareInstSubprogsHOL (WordBignum.loadRegs xs p) = noShareInstSubprogsHOL p := by
  induction xs with
  | nil => simp [WordBignum.loadRegs]
  | cons x xs ih =>
    simp [WordBignum.loadRegs, extractLabels, ih.1]
    simpa [noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp] using ih.2

theorem extractLabels_saveRegs {width : Nat} [NeZero width] (xs : List Nat) :
    extractLabels (WordBignum.saveRegs (width := width) xs) = [] ∧
      noShareInstSubprogsHOL (WordBignum.saveRegs (width := width) xs) = true := by
  induction xs with
  | nil => simp [WordBignum.saveRegs, extractLabels, noShareInstSubprogsHOL,
      notCreatedSubprogsWithMemOp]
  | cons x xs ih =>
    simp [WordBignum.saveRegs, extractLabels, ih.1]
    simpa [noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp] using ih.2

local macro "stub_simp" : tactic => `(tactic| simp [CompOk, extractLabels, noShareInstSubprogsHOL,
  notCreatedSubprogsWithMemOp, WordBignum.seqTemp, WordBignum.seqTempImm,
  WordBignum.seqTempImmNot, WordBignum.seqIndex, WordBignum.divCode])

theorem compile_compOk {width : Nat} [NeZero width] (c : WordBignum.Mini (BitVec width)) :
    ∀ (n l i : Nat) (cs : WordBignum.CodeAcc width), (∀ e ∈ cs.2, GoodCode e.2.1 e.2.2) →
      CompOk n l (WordBignum.compile n l i cs c) := by
  induction c with
  | seq a b iha ihb =>
    intro n l i cs hcs
    rw [WordBignum.compile_seq]
    have ha := iha n l i cs hcs
    rcases hca : WordBignum.compile n l i cs a with ⟨a', la, ia, ca⟩
    rw [hca] at ha
    dsimp only
    have hb := ihb n la ia ca ha.2.2.2.2
    rcases hcb : WordBignum.compile n la ia ca b with ⟨b', lb, ib, cb⟩
    rw [hcb] at hb
    dsimp only
    obtain ⟨a1, a2, a3, a4, _⟩ := ha
    obtain ⟨b1, b2, b3, b4, b5⟩ := hb
    have := labRange_append n l la lb _ _ a2 a3 b2 b3 a1 b1
    exact ⟨by simp only at a1 b1 ⊢; omega, by simpa [extractLabels] using this.1,
      by simpa [extractLabels] using this.2,
      by simp_all [noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp], b5⟩
  | ite op r arg a b iha ihb =>
    intro n l i cs hcs
    rw [WordBignum.compile_ite]
    have ha := iha n l i cs hcs
    rcases hca : WordBignum.compile n l i cs a with ⟨a', la, ia, ca⟩
    rw [hca] at ha
    dsimp only
    have hb := ihb n la ia ca ha.2.2.2.2
    rcases hcb : WordBignum.compile n la ia ca b with ⟨b', lb, ib, cb⟩
    rw [hcb] at hb
    dsimp only
    obtain ⟨a1, a2, a3, a4, _⟩ := ha
    obtain ⟨b1, b2, b3, b4, b5⟩ := hb
    have := labRange_append n l la lb _ _ a2 a3 b2 b3 a1 b1
    simp only at a1 a4 b1 b4 this
    cases arg <;> simp only [CompOk] <;>
      exact ⟨by omega, by simpa [WordBignum.seqTemp, extractLabels] using this.1,
        by simpa [WordBignum.seqTemp, extractLabels] using this.2,
        by simp_all [WordBignum.seqTemp, noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp],
        b5⟩
  | loopBody body ih =>
    intro n l i cs hcs
    rw [WordBignum.compile_loopBody]
    exact ih n l i cs hcs
  | loop rc live body ih =>
    intro n l i cs hcs
    rw [WordBignum.compile_loop]
    cases hh : WordBignum.hasCompiled body cs with
    | inl k =>
      simp only [CompOk]
      refine ⟨by omega, ?_, ?_, ?_, hcs⟩ <;> stub_simp
    | inr k =>
      have hb := ih k 2 1 (WordBignum.codeAccNext cs) hcs
      rcases hcb : WordBignum.compile k 2 1 (WordBignum.codeAccNext cs) body with
        ⟨b', lb, ib, cb⟩
      rw [hcb] at hb
      simp only [hcb]
      obtain ⟨_, b2, b3, b4, b5⟩ := hb
      simp only [CompOk, extractLabels, WordBignum.install, List.mem_cons]
      refine ⟨by omega, by simp, by simp, by stub_simp, ?_⟩
      intro e he
      rcases he with rfl | he
      · exact ⟨fun q hq => ⟨(b2 q hq).1, (b2 q hq).2.1⟩, b3, b4⟩
      · exact b5 e he
  | recurse save names =>
    intro n l i cs hcs
    rw [WordBignum.compile_recurse]
    have h1 := extractLabels_loadRegs (width := width) save
      (.call (some ([1], (.ls (), sptListInsert (save.map (· + 2)) .ln),
        WordBignum.saveRegs save, n, l)) (some n) [] none)
    have h2 := extractLabels_saveRegs (width := width) save
    simp only [CompOk, h1.1, h1.2]
    simp [extractLabels, h2.1, noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp] at h2 ⊢
    exact ⟨h2, fun _ _ _ h => hcs _ h⟩
  | add _ _ _ r3 r4 =>
    intro n l i cs hcs
    rw [WordBignum.compile_add]
    cases r3 <;> cases r4 <;> stub_simp <;> exact fun _ _ _ h => hcs _ h
  | sub _ _ _ r3 r4 =>
    intro n l i cs hcs
    rw [WordBignum.compile_sub]
    cases r3 <;> cases r4 <;> stub_simp <;> exact fun _ _ _ h => hcs _ h
  | div =>
    intro n l i cs hcs
    rw [WordBignum.compile_div]
    stub_simp
    exact fun _ _ _ h => hcs _ h
  | _ =>
    intro n l i cs hcs
    simp only [WordBignum.compile_skip, WordBignum.compile_continue, WordBignum.compile_assign,
      WordBignum.compile_delete, WordBignum.compile_swap, WordBignum.compile_store,
      WordBignum.compile_load, WordBignum.compile_mul]
    stub_simp
    exact fun _ _ _ h => hcs _ h

/-- The bignum stubs: labels at their own index from 2, distinct, and no
`ShareInst` (Flapjack infrastructure). -/
theorem generatedBignumStubs_good {width : Nat} [NeZero width] (loc : Nat) :
    ∀ e ∈ WordBignum.generatedBignumStubs width loc,
      ((∀ q ∈ extractLabels e.2.2, q.1 = e.1 ∧ q.2 ≠ 0 ∧ q.2 ≠ 1) ∧
        (extractLabels e.2.2).Nodup) ∧ noShareInstSubprogsHOL e.2.2 = true := by
  have h := compile_compOk (WordBignum.mcIopCode width) loc 2 1 (loc + 1, []) (by simp)
  simp only [WordBignum.generatedBignumStubs]
  rcases hc : WordBignum.compile loc 2 1 (loc + 1, []) (WordBignum.mcIopCode width) with
    ⟨body, l', i', n', installed⟩
  rw [hc] at h
  obtain ⟨_, h2, h3, h4, h5⟩ := h
  intro e he
  simp only [List.mem_cons, List.mem_map] at he
  rcases he with rfl | ⟨⟨b, idx, code⟩, hm, rfl⟩
  · simp only [extractLabels, List.append_nil]
    refine ⟨⟨fun q hq => ?_, h3⟩, ?_⟩
    · have := h2 q hq; simp only at this; omega
    · simpa [noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp] using h4
  · obtain ⟨g1, g2, g3⟩ := h5 _ hm
    simp only [extractLabels, List.append_nil]
    refine ⟨⟨fun q hq => ?_, g2⟩, ?_⟩
    · have := g1 q hq; simp only at this; omega
    · simpa [noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp] using g3

section NoShare
variable {width : Nat} [NeZero width]

theorem ns_seq (a b : WordLangProgHOL (BitVec width)) :
    noShareInstSubprogsHOL (.seq a b) = (noShareInstSubprogsHOL a && noShareInstSubprogsHOL b) := by
  simp [noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp]

theorem ns_ite (c : Cmp) (r : Nat) (x : WordRegImm (BitVec width))
    (a b : WordLangProgHOL (BitVec width)) :
    noShareInstSubprogsHOL (.ite c r x a b) =
      (noShareInstSubprogsHOL a && noShareInstSubprogsHOL b) := by
  simp [noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp]

theorem ns_mustTerminate (a : WordLangProgHOL (BitVec width)) :
    noShareInstSubprogsHOL (.mustTerminate a) = noShareInstSubprogsHOL a := by
  simp [noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp]

theorem ns_call_none (d : Option Nat) (args : List Nat) :
    noShareInstSubprogsHOL (width := width) (.call none d args none) = true := by
  simp [noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp]

theorem ns_call_some
    (r : List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat)
    (d : Option Nat) (args : List Nat) :
    noShareInstSubprogsHOL (.call (some r) d args none) = noShareInstSubprogsHOL r.2.2.1 := by
  rcases r with ⟨_, _, _, _, _⟩
  simp [noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp]

theorem byteCopyAdd_facts : extractLabels (byteCopyAddCode (width := width)) = [] ∧
    noShareInstSubprogsHOL (byteCopyAddCode (width := width)) = true := ⟨rfl, rfl⟩

theorem byteCopySub_facts : extractLabels (byteCopySubCode (width := width)) = [] ∧
    noShareInstSubprogsHOL (byteCopySubCode (width := width)) = true := ⟨rfl, rfl⟩

end NoShare

set_option linter.unusedSimpArgs false in
/-- Each fixed stub: labels at its own location from 2, distinct, and no
`ShareInst` (Flapjack infrastructure). -/
theorem fixedStub_good {width : Nat} [NeZero width] (conf : Config) (loc arity : Nat)
    (p : WordLangProgHOL (BitVec width)) (hloc : loc ∈ fixedLocations)
    (h : compileConfiguredStub? conf loc = some (arity, p)) :
    ((∀ q ∈ extractLabels p, q.1 = loc ∧ q.2 ≠ 0 ∧ q.2 ≠ 1) ∧ (extractLabels p).Nodup) ∧
      noShareInstSubprogsHOL p = true := by
  simp only [fixedLocations, fromListLocation, fromList1Location, refByteLocation,
      refArrayLocation, replicateLocation, anyArithLocation, addLocation, subLocation,
      mulLocation, divLocation, modLocation, compare1Location, compareLocation, equal1Location,
      equalLocation, longDiv1Location, longDivLocation, memCopyLocation, byteCopyLocation,
      byteCopyAddLocation, byteCopySubLocation, byteCopyNewLocation, installLocation,
      installCodeLocation, installDataLocation, dummyLocation, appendLocation,
      appendMainLoopLocation, appendLenLoopLocation, xorLoopLocation, unusedLocation,
      stringCmpLoopLocation, wordNumStubs, stackNumStubs, List.mem_cons, List.not_mem_nil,
      or_false] at hloc
  rcases hloc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals simp [compileConfiguredStub?, compileStub?, fromListLocation, fromList1Location,
      refByteLocation,
      refArrayLocation, replicateLocation, anyArithLocation, addLocation, subLocation,
      mulLocation, divLocation, modLocation, compare1Location, compareLocation, equal1Location,
      equalLocation, longDiv1Location, longDivLocation, memCopyLocation, byteCopyLocation,
      byteCopyAddLocation, byteCopySubLocation, byteCopyNewLocation, installLocation,
      installCodeLocation, installDataLocation, dummyLocation, appendLocation,
      appendMainLoopLocation, appendLenLoopLocation, xorLoopLocation, unusedLocation,
      stringCmpLoopLocation, wordNumStubs, stackNumStubs] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  all_goals by_cases hffi : conf.callEmptyFfi = true
  all_goals simp [hffi, byteCopyAdd_facts, byteCopySub_facts, addNumSize, anyHeader, replicateCode,
    arithWrapperCode, addCode, subCode, mulCode, divCode, modCode, compare1Code, equal1Code,
    installCode, xorLoopCode, stringCmpLoopCode, memCopyCode, fromListCode, fromList1Code,
    refByteCode, refArrayCode, anyArithCode, compareCode, equalCode, longDiv1Code, longDivCode,
    installCodeStub, installDataStub, appendCode, appendMainLoopCode, appendLenLoopCode,
    byteCopyCode, allocVar, bignumHalt, makeBytes, makePtrBitsCode, writeLastBytes,
    writeLastByteAux, giveUp, silentFfi, maxoutBitsCode, extractLabels,
    extractLabels_wordListSeq, listSeq_noShareInst, ns_seq, ns_ite, ns_mustTerminate,
    ns_call_none, ns_call_some, apply_ite (extractLabels (width := width)),
    apply_ite (noShareInstSubprogsHOL (width := width))]
  all_goals (try simp [noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp])
  all_goals (try (split <;> simp [extractLabels, extractLabels_wordListSeq, listSeq_noShareInst,
    ns_seq, ns_ite, ns_mustTerminate, ns_call_none, ns_call_some]))
  all_goals (try simp [noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp])
  all_goals rfl

/-- Every stub: labels at its own location other than 0 and 1, distinct, and
no `ShareInst` (Flapjack infrastructure combining both HOL facts). -/
theorem stubs_good {width : Nat} [NeZero width] (conf : Config) :
    ∀ e ∈ stubs (width := width) conf,
      ((∀ q ∈ extractLabels e.2.2, q.1 = e.1 ∧ q.2 ≠ 0 ∧ q.2 ≠ 1) ∧
        (extractLabels e.2.2).Nodup) ∧ noShareInstSubprogsHOL e.2.2 = true := by
  obtain ⟨L, hL, hs⟩ := stubs_eq (width := width) conf
  obtain ⟨hfst, hent⟩ := fixedStubs_keyed conf L hL
  rw [hs]
  intro e he
  rcases List.mem_append.1 he with he | he
  · have hloc : e.1 ∈ fixedLocations := by rw [← hfst]; exact List.mem_map_of_mem he
    exact fixedStub_good conf e.1 e.2.1 e.2.2 hloc (hent e he)
  · exact generatedBignumStubs_good bignumLocation e he

/-- Exact HOL `stub_labels`. `EVERY (λ(n,m,p). ...)` over the stub table and
`EVERY (λ(l1,l2). ...)` over the labels are membership foralls; `ALL_DISTINCT`
is `List.Nodup`; HOL `extract_labels` is the reviewed `extractLabels`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "stub_labels"
  (words_as_type_indexed_bitvec)]
theorem stub_labels {width : Nat} [NeZero width] (dataConf : Config) :
    ∀ e ∈ (stubs dataConf : List (Nat × Nat × WordLangProgHOL (BitVec width))),
      (∀ q ∈ extractLabels e.2.2, q.1 = e.1 ∧ q.2 ≠ 0 ∧ q.2 ≠ 1) ∧
        (extractLabels e.2.2).Nodup :=
  fun e he => (stubs_good dataConf e he).1

/-- Exact HOL `stubs_no_share_inst`. HOL `no_share_inst` is the reviewed
Boolean `noShareInstSubprogsHOL`; `SND $ SND x` is `x.2.2`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "stubs_no_share_inst"
  (words_as_type_indexed_bitvec)]
theorem stubs_noShareInst {width : Nat} [NeZero width] (dataConf : Config) :
    ∀ x ∈ (stubs dataConf : List (Nat × Nat × WordLangProgHOL (BitVec width))),
      noShareInstSubprogsHOL x.2.2 = true :=
  fun e he => (stubs_good dataConf e he).2

end Flapjack.Compiler.Backend.DataToWord.Proofs
