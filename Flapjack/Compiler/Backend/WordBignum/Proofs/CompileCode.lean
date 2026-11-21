module

public import Flapjack.Compiler.Backend.WordBignum.Proofs.CompileLemmas
public import Flapjack.Misc.List.Size
public import Flapjack.Misc.GeneratedSize
public import Flapjack.Pancake.PanLang.Exp

@[expose] public section

/-! The installed-code facts of
`cakeml/compiler/backend/proofs/word_bignumProofScript.sml`
(`compile_LESS_mini_size`, `MEM_compile`, `compile_NIL_IMP`): every program the
compiler installs is a strictly smaller sub-program of the compiled one, and
the installed list stays `good_code`.

## HOL's generated `mini_size`

`compile_LESS_mini_size` is stated over `mini_size (K 0)`, which HOL's
`Datatype` package generates for `word_bignum$mini`; it has no source
declaration, so the transcription below is untagged (as for the panLang and
crepLang size precedents). The equations are pinned in
`scripts/hol-probes/word_bignum_proof_typed_probe.out` (`mini_size_def_typed`,
`wordLang_exp_size_def_typed`, `asm_reg_imm_size_def_typed`,
`stackLang_store_name_size_def_typed`, and the nullary `address`, `cmp`,
`binop` and `shift` sizes, all the constant `0`). HOL's size-function
parameter `f : 'a -> num` sizes the dimension type `'a` and is applied by no
clause (words are sized by `w2n`, `bool_size` and `list_size (λx. x)` size the
other fields), so `mini_size f x` does not depend on `f`; the Lean
transcriptions omit that vacuous parameter, so `miniSizeHOL x` is
`mini_size f x` for every `f`, in particular HOL's `K 0`.
-/

namespace Flapjack.Compiler.Backend.WordBignum

open Flapjack

/-- HOL's generated `store_name_size`: `Temp a` is `1 + w2n a`, every other
store name is nullary and sized `0`. -/
def storeNameSizeHOL : WordStoreHOL → Nat
  | .temp a => 1 + a.toNat
  | _ => 0

mutual
  /-- HOL's generated `wordLang$exp_size`, without its vacuous parameter. -/
  def wordExpSizeHOL {width : Nat} : WordLangExpHOL (BitVec width) → Nat
    | .const a => 1 + a.toNat
    | .var a => 1 + a
    | .lookup a => 1 + storeNameSizeHOL a
    | .load a => 1 + wordExpSizeHOL a
    | .op a0 a1 => 1 + (Pancake.PanLang.binopSizeHOL a0 + wordExp1SizeHOL a1)
    | .shift a0 a1 a2 => 1 + (Pancake.PanLang.shiftSizeHOL a0 + (wordExpSizeHOL a1 + wordExpSizeHOL a2))

  /-- HOL's generated `wordLang$exp1_size` for expression lists. -/
  def wordExp1SizeHOL {width : Nat} : List (WordLangExpHOL (BitVec width)) → Nat
    | [] => 0
    | a0 :: a1 => 1 + (wordExpSizeHOL a0 + wordExp1SizeHOL a1)
end

/-- HOL's generated `asm$reg_imm_size`, without its vacuous parameter. -/
def regImmSizeHOL {width : Nat} : WordRegImm (BitVec width) → Nat
  | .reg a => 1 + a
  | .imm a => 1 + a.toNat

/-- HOL's generated `word_bignum$address_size`: the constant `0`. -/
def addressSizeHOL (_ : Address) : Nat := 0

/-- HOL's generated `word_bignum$mini_size`, without its vacuous parameter;
clause for clause as pinned in `mini_size_def_typed`. -/
def miniSizeHOL {width : Nat} : Mini (BitVec width) → Nat
  | .skip => 0
  | .assign a0 a1 => 1 + (a0 + wordExpSizeHOL a1)
  | .delete a => 1 + listSizeHOL (fun x => x) a
  | .seq a0 a1 => 1 + (miniSizeHOL a0 + miniSizeHOL a1)
  | .load a0 a1 a2 => 1 + (a0 + (a1 + addressSizeHOL a2))
  | .store a0 a1 => 1 + (a0 + a1)
  | .ite a0 a1 a2 a3 a4 =>
      1 + (Pancake.PanLang.cmpSizeHOL a0 + (a1 + (regImmSizeHOL a2 + (miniSizeHOL a3 + miniSizeHOL a4))))
  | .swap => 0
  | .add a0 a1 a2 a3 a4 => 1 + (a0 + (a1 + (a2 + (regImmSizeHOL a3 + regImmSizeHOL a4))))
  | .sub a0 a1 a2 a3 a4 => 1 + (a0 + (a1 + (a2 + (regImmSizeHOL a3 + regImmSizeHOL a4))))
  | .mul a0 a1 a2 a3 => 1 + (a0 + (a1 + (a2 + a3)))
  | .div a0 a1 a2 a3 a4 => 1 + (a0 + (a1 + (a2 + (a3 + a4))))
  | .loop a0 a1 a2 => 1 + (boolSizeHOL a0 + (listSizeHOL (fun x => x) a1 + miniSizeHOL a2))
  | .continue => 0
  | .recurse a0 a1 => 1 + (listSizeHOL (fun x => x) a0 + listSizeHOL (fun x => x) a1)
  | .loopBody a => 1 + miniSizeHOL a

/-- HOL `compile_LESS_mini_size` (`word_bignumProofScript.sml:1260`): every
entry the compiler adds to the installed-code list is a strictly smaller
program than the compiled one. HOL's `mini_size (K 0)` is `miniSizeHOL` (see
the module note on the vacuous size parameter). -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "compile_LESS_mini_size"
  (words_as_type_indexed_bitvec)]
theorem compile_LESS_miniSize {width : Nat} [NeZero width] :
    ∀ (k l1 l2 : Nat) (yy5 : CodeAcc width) (code : Mini (BitVec width))
      (xx1 : WordLangProgHOL (BitVec width)) (xx2 xx3 : Nat) (xx5 : CodeAcc width),
      compile k l1 l2 yy5 code = (xx1, xx2, xx3, xx5) →
        ∀ x : CodeEntry width, x ∈ xx5.2 ∧ x ∉ yy5.2 →
          miniSizeHOL x.1 < miniSizeHOL code := by
  intro k l1 l2 yy5 code
  induction code generalizing k l1 l2 yy5 with
  | skip => intro _ _ _ _ h x hx; rw [compile_skip] at h; cases h; exact absurd hx.1 hx.2
  | «continue» =>
    intro _ _ _ _ h x hx; rw [compile_continue] at h; cases h; exact absurd hx.1 hx.2
  | assign => intro _ _ _ _ h x hx; rw [compile_assign] at h; cases h; exact absurd hx.1 hx.2
  | delete => intro _ _ _ _ h x hx; rw [compile_delete] at h; cases h; exact absurd hx.1 hx.2
  | swap => intro _ _ _ _ h x hx; rw [compile_swap] at h; cases h; exact absurd hx.1 hx.2
  | store => intro _ _ _ _ h x hx; rw [compile_store] at h; cases h; exact absurd hx.1 hx.2
  | load => intro _ _ _ _ h x hx; rw [compile_load] at h; cases h; exact absurd hx.1 hx.2
  | add => intro _ _ _ _ h x hx; rw [compile_add] at h; cases h; exact absurd hx.1 hx.2
  | sub => intro _ _ _ _ h x hx; rw [compile_sub] at h; cases h; exact absurd hx.1 hx.2
  | mul => intro _ _ _ _ h x hx; rw [compile_mul] at h; cases h; exact absurd hx.1 hx.2
  | div => intro _ _ _ _ h x hx; rw [compile_div] at h; cases h; exact absurd hx.1 hx.2
  | recurse => intro _ _ _ _ h x hx; rw [compile_recurse] at h; cases h; exact absurd hx.1 hx.2
  | loopBody body ih =>
    intro _ _ _ _ h x hx
    rw [compile_loopBody] at h
    have := ih k l1 l2 yy5 _ _ _ _ h x hx
    simp only [miniSizeHOL]
    omega
  | seq a b iha ihb =>
    intro xx1 xx2 xx3 xx5 h x hx
    rcases ha : compile k l1 l2 yy5 a with ⟨a', la, ia, ca⟩
    rcases hb : compile k la ia ca b with ⟨b', lb, ib, cb⟩
    rw [compile_seq, ha] at h
    dsimp only at h
    rw [hb] at h
    dsimp only at h
    cases h
    simp only [miniSizeHOL]
    by_cases hca : x ∈ ca.2
    · have := iha _ _ _ _ _ _ _ _ ha x ⟨hca, hx.2⟩
      omega
    · have := ihb _ _ _ _ _ _ _ _ hb x ⟨hx.1, hca⟩
      omega
  | ite op r arg a b iha ihb =>
    intro xx1 xx2 xx3 xx5 h x hx
    rcases ha : compile k l1 l2 yy5 a with ⟨a', la, ia, ca⟩
    rcases hb : compile k la ia ca b with ⟨b', lb, ib, cb⟩
    rw [compile_ite, ha] at h
    dsimp only at h
    rw [hb] at h
    dsimp only at h
    have hcs : xx5 = cb := by cases arg <;> simp only at h <;> cases h <;> rfl
    subst hcs
    simp only [miniSizeHOL]
    by_cases hca : x ∈ ca.2
    · have := iha _ _ _ _ _ _ _ _ ha x ⟨hca, hx.2⟩
      omega
    · have := ihb _ _ _ _ _ _ _ _ hb x ⟨hx.1, hca⟩
      omega
  | loop recs live body ih =>
    intro xx1 xx2 xx3 xx5 h x hx
    rw [compile_loop] at h
    cases hc : hasCompiled body yy5 with
    | inl existing =>
      rw [hc] at h
      cases h
      exact absurd hx.1 hx.2
    | inr index =>
      rcases hb : compile index 2 1 (codeAccNext yy5) body with ⟨body', lb, ib, cb⟩
      rw [hc] at h
      dsimp only at h
      rw [hb] at h
      dsimp only at h
      cases h
      simp only [miniSizeHOL]
      rcases List.mem_cons.mp hx.1 with hxe | hxc
      · subst hxe
        simp only
        omega
      · have := ih _ _ _ _ _ _ _ _ hb x ⟨hxc, hx.2⟩
        omega

/-- Flapjack-only helper: a successful association-list lookup comes from a
list entry with that key. -/
theorem holAlookup_some_mem {α β : Type} [DecidableEq α] :
    ∀ (l : List (α × β)) (k : α) (v : β), holAlookup l k = some v → ∃ e ∈ l, e.1 = k
  | [], _, _, h => by simp [holAlookup] at h
  | (a, b) :: rest, k, v, h => by
    by_cases hk : a = k
    · exact ⟨(a, b), List.mem_cons_self, hk⟩
    · rw [holAlookup, if_neg hk] at h
      obtain ⟨e, he, hek⟩ := holAlookup_some_mem rest k v h
      exact ⟨e, List.mem_cons_of_mem _ he, hek⟩

/-- Flapjack-only helper: a failed association-list lookup has no entry with
that key. -/
theorem holAlookup_none_not_mem {α β : Type} [DecidableEq α] :
    ∀ (l : List (α × β)) (k : α), holAlookup l k = none → ∀ e ∈ l, e.1 ≠ k
  | [], _, _, _, he => by simp at he
  | (a, b) :: rest, k, h, e, he => by
    by_cases hk : a = k
    · rw [holAlookup, if_pos hk] at h
      cases h
    · rw [holAlookup, if_neg hk] at h
      rcases List.mem_cons.mp he with heq | hmem
      · subst heq
        exact hk
      · exact holAlookup_none_not_mem rest k h e hmem

/-- Flapjack-only helper: `good_code` ignores the accumulator's next index. -/
theorem goodCode_codeAccNext {width : Nat} [NeZero width] (cs : CodeAcc width) :
    goodCode cs → goodCode (codeAccNext cs) := by
  intro h prog n p2 hm
  obtain ⟨cs1, l2', i2, cs2, hc, hs⟩ := h prog n p2 hm
  exact ⟨cs1, l2', i2, cs2, hc, hs⟩

/-- HOL `MEM_compile` (`word_bignumProofScript.sml:1281`): compiling from a
`good_code` accumulator yields a `good_code` accumulator. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "MEM_compile"
  (words_as_type_indexed_bitvec)]
theorem MEM_compile {width : Nat} [NeZero width] :
    ∀ (k l1 l2 : Nat) (yy5 : CodeAcc width) (code : Mini (BitVec width))
      (xx1 : WordLangProgHOL (BitVec width)) (xx2 xx3 : Nat) (xx5 : CodeAcc width),
      goodCode yy5 ∧ compile k l1 l2 yy5 code = (xx1, xx2, xx3, xx5) → goodCode xx5 := by
  intro k l1 l2 yy5 code
  induction code generalizing k l1 l2 yy5 with
  | skip => intro _ _ _ _ ⟨hg, h⟩; rw [compile_skip] at h; cases h; exact hg
  | «continue» => intro _ _ _ _ ⟨hg, h⟩; rw [compile_continue] at h; cases h; exact hg
  | assign => intro _ _ _ _ ⟨hg, h⟩; rw [compile_assign] at h; cases h; exact hg
  | delete => intro _ _ _ _ ⟨hg, h⟩; rw [compile_delete] at h; cases h; exact hg
  | swap => intro _ _ _ _ ⟨hg, h⟩; rw [compile_swap] at h; cases h; exact hg
  | store => intro _ _ _ _ ⟨hg, h⟩; rw [compile_store] at h; cases h; exact hg
  | load => intro _ _ _ _ ⟨hg, h⟩; rw [compile_load] at h; cases h; exact hg
  | add => intro _ _ _ _ ⟨hg, h⟩; rw [compile_add] at h; cases h; exact hg
  | sub => intro _ _ _ _ ⟨hg, h⟩; rw [compile_sub] at h; cases h; exact hg
  | mul => intro _ _ _ _ ⟨hg, h⟩; rw [compile_mul] at h; cases h; exact hg
  | div => intro _ _ _ _ ⟨hg, h⟩; rw [compile_div] at h; cases h; exact hg
  | recurse => intro _ _ _ _ ⟨hg, h⟩; rw [compile_recurse] at h; cases h; exact hg
  | loopBody body ih =>
    intro _ _ _ _ ⟨hg, h⟩
    rw [compile_loopBody] at h
    exact ih k l1 l2 yy5 _ _ _ _ ⟨hg, h⟩
  | seq a b iha ihb =>
    intro xx1 xx2 xx3 xx5 ⟨hg, h⟩
    rcases ha : compile k l1 l2 yy5 a with ⟨a', la, ia, ca⟩
    rcases hb : compile k la ia ca b with ⟨b', lb, ib, cb⟩
    rw [compile_seq, ha] at h
    dsimp only at h
    rw [hb] at h
    dsimp only at h
    cases h
    exact ihb _ _ _ _ _ _ _ _ ⟨iha _ _ _ _ _ _ _ _ ⟨hg, ha⟩, hb⟩
  | ite op r arg a b iha ihb =>
    intro xx1 xx2 xx3 xx5 ⟨hg, h⟩
    rcases ha : compile k l1 l2 yy5 a with ⟨a', la, ia, ca⟩
    rcases hb : compile k la ia ca b with ⟨b', lb, ib, cb⟩
    rw [compile_ite, ha] at h
    dsimp only at h
    rw [hb] at h
    dsimp only at h
    have hcs : xx5 = cb := by cases arg <;> simp only at h <;> cases h <;> rfl
    subst hcs
    exact ihb _ _ _ _ _ _ _ _ ⟨iha _ _ _ _ _ _ _ _ ⟨hg, ha⟩, hb⟩
  | loop recs live body ih =>
    intro xx1 xx2 xx3 xx5 ⟨hg, h⟩
    rw [compile_loop] at h
    cases hc : hasCompiled body yy5 with
    | inl existing =>
      rw [hc] at h
      cases h
      exact hg
    | inr index =>
      rcases hb : compile index 2 1 (codeAccNext yy5) body with ⟨body', lb, ib, cb⟩
      rw [hc] at h
      dsimp only at h
      rw [hb] at h
      dsimp only at h
      cases h
      have hgcb := ih _ _ _ _ _ _ _ _ ⟨goodCode_codeAccNext yy5 hg, hb⟩
      have hnone0 := (hasCompiled_inr_lookup body yy5 index hc).1
      -- The new body is not a key of the extended accumulator.
      have hnone : holAlookup cb.2 body = none := by
        cases hl : holAlookup cb.2 body with
        | none => rfl
        | some v =>
          exfalso
          obtain ⟨e, he, hek⟩ := holAlookup_some_mem cb.2 body v hl
          by_cases hey : e ∈ yy5.2
          · exact holAlookup_none_not_mem yy5.2 body hnone0 e hey hek
          · have := compile_LESS_miniSize _ _ _ _ _ _ _ _ _ hb e ⟨he, hey⟩
            rw [hek] at this
            omega
      have hsub : codeSubset cb (install (body, index, body') cb) := by
        intro key v hv
        simp only [holAlookup]
        by_cases hk : body = key
        · subst hk
          rw [hnone] at hv
          cases hv
        · rw [if_neg hk]
          exact hv
      intro prog n p2 hm
      rcases List.mem_cons.mp hm with he | hm'
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        exact ⟨codeAccNext yy5, lb, ib, cb, hb, hsub⟩
      · obtain ⟨cs1, l2', i2, cs2, hcomp, hs⟩ := hgcb prog n p2 hm'
        exact ⟨cs1, l2', i2, cs2, hcomp, codeSubset_trans _ _ _ ⟨hs, hsub⟩⟩

/-- HOL `compile_NIL_IMP` (`word_bignumProofScript.sml:1327`): every entry
installed when compiling from an empty installed-code list is a recorded
compilation. HOL's free variables `k l1 l2 l` are explicit parameters. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "compile_NIL_IMP"
  (words_as_type_indexed_bitvec)]
theorem compile_NIL_IMP {width : Nat} [NeZero width] (k l1 l2 l : Nat) :
    ∀ (code : Mini (BitVec width)) (xx1 : WordLangProgHOL (BitVec width)) (xx2 xx3 : Nat)
      (xx5 : CodeAcc width),
      compile k l1 l2 (l, []) code = (xx1, xx2, xx3, xx5) →
        ∀ (prog : Mini (BitVec width)) (n : Nat) (p2 : WordLangProgHOL (BitVec width)),
          (prog, n, p2) ∈ xx5.2 →
            ∃ (cs1 : CodeAcc width) (l2' i2 : Nat) (cs2 : CodeAcc width),
              compile n 2 1 cs1 prog = (p2, l2', i2, cs2) ∧ codeSubset cs2 xx5 := by
  intro code xx1 xx2 xx3 xx5 h
  have hg : goodCode ((l, []) : CodeAcc width) := by
    intro prog n p2 hm
    simp at hm
  exact MEM_compile k l1 l2 (l, []) code xx1 xx2 xx3 xx5 ⟨hg, h⟩

end Flapjack.Compiler.Backend.WordBignum
