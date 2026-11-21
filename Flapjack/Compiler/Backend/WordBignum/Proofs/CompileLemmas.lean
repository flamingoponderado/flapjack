module

public import Flapjack.Compiler.Backend.WordBignum.Proofs.StateRel
public import Flapjack.Compiler.Backend.WordBignum.Proofs.CompileEquations
public import Flapjack.Compiler.Backend.WordBignum.Proofs.Lookup
public import Flapjack.Misc.GoodDimindex

@[expose] public section

/-! Facts about the mini-language compiler of
`cakeml/compiler/backend/proofs/word_bignumProofScript.sml`: expression
compilation, the growth of the installed-code accumulator, and cached
compilations. -/

namespace Flapjack.Compiler.Backend.WordBignum

open Flapjack

namespace CompileLemmasSupport

/-- Same-module canonical roundtrip witness for the mini-language state
carrier, required by the relation qualifiers in this module. -/
theorem holFmapAsFiniteSupportRelationWitness_MiniState {width : Nat} [NeZero width] :
    (∀ s : MiniStateBroad width, (MiniState.ofBroad s).toBroad = s) ∧
      (∀ s : MiniState width, MiniState.ofBroad s.toBroad = s) :=
  Flapjack.Compiler.Backend.WordBignum.holFmapAsFiniteSupportWitness

/-- Same-module canonical roundtrip witness for the `wordSem` state carrier,
required by the relation qualifiers in this module. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact {width : Nat}
    [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CompileLemmasSupport

/-- HOL `compile_exp_thm` (`word_bignumProofScript.sml:429`): under the state
relation, a well-formed mini-language expression compiles to a word expression
that evaluates to the same word. HOL's premise is one conjunction. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "compile_exp_thm"
  (fmap_as_finite_support_relation := [MiniState.regs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compileExp_thm {width : Nat} [NeZero width] {β : Type} {C F : Type}
    (s1 : MiniState width) (t1 : WordSemStateFiniteExact width C F)
    (cs2 : β × List (Mini (BitVec width) × Nat × WordLangProgHOL (BitVec width)))
    (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (x : WordLangExpHOL (BitVec width)) :
    stateRel s1 t1 cs2 t0 frame ∧ evalExpPre s1 x ∧ goodDimindex width →
      WordSemStateFiniteExact.wordExp t1 (compileExp x) = some (.word (evalExp s1 x)) :=
  match x with
  | .const w => fun _ => by simp [compileExp, evalExp, WordSemStateFiniteExact.wordExp]
  | .var v => fun ⟨hrel, hpre, hgood⟩ => by
    obtain ⟨_, _, hr, _⟩ := hrel
    cases hl : s1.regs.lookup v with
    | none => exact absurd hl hpre
    | some w =>
      have := (hr v w hl).2
      simp [compileExp, evalExp, WordSemStateFiniteExact.wordExp,
        WordSemStateFiniteExact.getStore, this, holFapply_of_lookup hl]
  | .op op [a, b] => fun ⟨hrel, hpre, hgood⟩ => by
    have ha := compileExp_thm s1 t1 cs2 t0 frame a ⟨hrel, hpre.1, hgood⟩
    have hb := compileExp_thm s1 t1 cs2 t0 frame b ⟨hrel, hpre.2, hgood⟩
    simp only [compileExp]
    rw [WordSemStateFiniteExact.wordExp]
    simp [ha, hb, theWords]
    cases op <;> simp [wordOpHOL, wordOp, evalExp]
    · show evalExp s1 a &&& (evalExp s1 b &&& BitVec.allOnes width) = _
      simp
    · show evalExp s1 a ||| (evalExp s1 b ||| 0#width) = _
      simp
  | .shift sh a b => fun ⟨hrel, hpre, hgood⟩ => by
    have ha := compileExp_thm s1 t1 cs2 t0 frame a ⟨hrel, hpre.1, hgood⟩
    have hb := compileExp_thm s1 t1 cs2 t0 frame b ⟨hrel, hpre.2.1, hgood⟩
    have hlt := hpre.2.2
    simp only [compileExp]
    rw [WordSemStateFiniteExact.wordExp]
    simp only [ha, hb]
    have hw : ¬ ((evalExp s1 b).toNat ≠ 0 ∧ width ≤ (evalExp s1 b).toNat) := by
      rcases hgood with h | h <;> omega
    cases sh <;> simp [wordShiftHOL, hw, evalExp]
  | .lookup _ => fun ⟨_, hpre, _⟩ => by simp [evalExpPre] at hpre
  | .load _ => fun ⟨_, hpre, _⟩ => by simp [evalExpPre] at hpre
  | .op _ [] => fun ⟨_, hpre, _⟩ => by simp [evalExpPre] at hpre
  | .op _ [_] => fun ⟨_, hpre, _⟩ => by simp [evalExpPre] at hpre
  | .op _ (_ :: _ :: _ :: _) => fun ⟨_, hpre, _⟩ => by simp [evalExpPre] at hpre
termination_by sizeOf x

/-- Flapjack-only helper: `hasCompiled` answers `inr` only when the program is
not cached. -/
theorem hasCompiled_inr_lookup {width : Nat} [NeZero width] (body : Mini (BitVec width))
    (cs : CodeAcc width) (index : Nat) (h : hasCompiled body cs = .inr index) :
    holAlookup cs.2 body = none ∧ index = cs.1 := by
  obtain ⟨n, l⟩ := cs
  simp only [hasCompiled] at h
  induction l with
  | nil => simp_all [holAlookup]
  | cons e rest ih =>
    obtain ⟨k, v⟩ := e
    by_cases hk : k = body
    · subst hk
      simp [List.lookup] at h
    · have hne : decide (body = k) = false := by simp [Ne.symm hk]
      simp only [List.lookup, hne] at h
      obtain ⟨h1, h2⟩ := ih h
      exact ⟨by simpa [holAlookup, hk] using h1, h2⟩

/-- HOL `compile_IMP_code_subset` (`word_bignumProofScript.sml:380`):
compilation only extends the installed-code accumulator and never decreases
the next temporary. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "compile_IMP_code_subset"
  (words_as_type_indexed_bitvec)]
theorem compile_IMP_codeSubset {width : Nat} [NeZero width] (prog : Mini (BitVec width)) :
    ∀ (n l i : Nat) (cs : CodeAcc width) (p1 : WordLangProgHOL (BitVec width)) (l1 i1 : Nat)
      (cs1 : CodeAcc width),
      compile n l i cs prog = (p1, l1, i1, cs1) → codeSubset cs cs1 ∧ i ≤ i1 := by
  induction prog with
  | skip => intro n l i cs p1 l1 i1 cs1 h; rw [compile_skip] at h; cases h; exact ⟨codeSubset_refl _, le_rfl⟩
  | «continue» => intro n l i cs p1 l1 i1 cs1 h; rw [compile_continue] at h; cases h; exact ⟨codeSubset_refl _, le_rfl⟩
  | assign => intro n l i cs p1 l1 i1 cs1 h; rw [compile_assign] at h; cases h; exact ⟨codeSubset_refl _, by omega⟩
  | delete => intro n l i cs p1 l1 i1 cs1 h; rw [compile_delete] at h; cases h; exact ⟨codeSubset_refl _, le_rfl⟩
  | swap => intro n l i cs p1 l1 i1 cs1 h; rw [compile_swap] at h; cases h; exact ⟨codeSubset_refl _, by omega⟩
  | store => intro n l i cs p1 l1 i1 cs1 h; rw [compile_store] at h; cases h; exact ⟨codeSubset_refl _, by omega⟩
  | load => intro n l i cs p1 l1 i1 cs1 h; rw [compile_load] at h; cases h; exact ⟨codeSubset_refl _, by omega⟩
  | add => intro n l i cs p1 l1 i1 cs1 h; rw [compile_add] at h; cases h; exact ⟨codeSubset_refl _, by omega⟩
  | sub => intro n l i cs p1 l1 i1 cs1 h; rw [compile_sub] at h; cases h; exact ⟨codeSubset_refl _, by omega⟩
  | mul => intro n l i cs p1 l1 i1 cs1 h; rw [compile_mul] at h; cases h; exact ⟨codeSubset_refl _, by omega⟩
  | div => intro n l i cs p1 l1 i1 cs1 h; rw [compile_div] at h; cases h; exact ⟨codeSubset_refl _, by omega⟩
  | recurse => intro n l i cs p1 l1 i1 cs1 h; rw [compile_recurse] at h; cases h; exact ⟨codeSubset_refl _, le_rfl⟩
  | loopBody body ih => intro n l i cs p1 l1 i1 cs1 h; rw [compile_loopBody] at h; exact ih _ _ _ _ _ _ _ _ h
  | seq a b iha ihb =>
    intro n l i cs p1 l1 i1 cs1 h
    rcases ha : compile n l i cs a with ⟨a', la, ia, ca⟩
    rcases hb : compile n la ia ca b with ⟨b', lb, ib, cb⟩
    rw [compile_seq, ha] at h
    dsimp only at h
    rw [hb] at h
    dsimp only at h
    cases h
    obtain ⟨h1, h2⟩ := iha _ _ _ _ _ _ _ _ ha
    obtain ⟨h3, h4⟩ := ihb _ _ _ _ _ _ _ _ hb
    exact ⟨codeSubset_trans _ _ _ ⟨h1, h3⟩, by omega⟩
  | ite op r arg a b iha ihb =>
    intro n l i cs p1 l1 i1 cs1 h
    rcases ha : compile n l i cs a with ⟨a', la, ia, ca⟩
    rcases hb : compile n la ia ca b with ⟨b', lb, ib, cb⟩
    rw [compile_ite, ha] at h
    dsimp only at h
    rw [hb] at h
    dsimp only at h
    obtain ⟨h1, h2⟩ := iha _ _ _ _ _ _ _ _ ha
    obtain ⟨h3, h4⟩ := ihb _ _ _ _ _ _ _ _ hb
    cases arg <;> simp only at h <;> cases h <;>
      exact ⟨codeSubset_trans _ _ _ ⟨h1, h3⟩, by omega⟩
  | loop recs live body ih =>
    intro n l i cs p1 l1 i1 cs1 h
    rw [compile_loop] at h
    cases hc : hasCompiled body cs with
    | inl existing =>
      rw [hc] at h
      cases h
      exact ⟨codeSubset_refl _, by omega⟩
    | inr index =>
      rcases hb : compile index 2 1 (codeAccNext cs) body with ⟨body', lb, ib, cb⟩
      rw [hc] at h
      dsimp only at h
      rw [hb] at h
      dsimp only at h
      cases h
      obtain ⟨hsub, -⟩ := ih _ _ _ _ _ _ _ _ hb
      refine ⟨?_, by omega⟩
      have hnone := (hasCompiled_inr_lookup body cs index hc).1
      intro key v hv
      simp only [holAlookup]
      by_cases hk : body = key
      · subst hk
        rw [hnone] at hv
        cases hv
      · rw [if_neg hk]
        exact hsub key v hv

/-- Flapjack-only helper: `hasCompiled` answers `inl` with the cached index. -/
theorem hasCompiled_inl_lookup {width : Nat} [NeZero width] (body : Mini (BitVec width))
    (cs : CodeAcc width) (x : Nat) (h : hasCompiled body cs = .inl x) :
    ∃ code, holAlookup cs.2 body = some (x, code) := by
  obtain ⟨n, l⟩ := cs
  simp only [hasCompiled] at h
  induction l with
  | nil => simp_all
  | cons e rest ih =>
    obtain ⟨k, v⟩ := e
    by_cases hk : k = body
    · subst hk
      simp only [List.lookup, decide_true] at h
      obtain ⟨vi, vc⟩ := v
      simp only [Sum.inl.injEq] at h
      subst h
      exact ⟨vc, by simp [holAlookup]⟩
    · have hne : decide (body = k) = false := by simp [Ne.symm hk]
      simp only [List.lookup, hne] at h
      obtain ⟨code, hc⟩ := ih h
      exact ⟨code, by simpa [holAlookup, hk] using hc⟩

/-- HOL `has_compiled_lemma` (`word_bignumProofScript.sml:401`): a cached
program has a recorded compilation, which is installed in the `wordSem` code
store. HOL's existential also binds an unused `cs0` of an independent type
variable; since every HOL type is inhabited, `∃ cs0. P` is `P` there, and the
vacuous binder is omitted rather than requiring an inhabitant in Lean. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "has_compiled_lemma"
  (fmap_as_finite_support_relation := [MiniState.regs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem has_compiled_lemma {width : Nat} [NeZero width] {β : Type} {C F : Type}
    (s1 : MiniState width) (t1 : WordSemStateFiniteExact width C F)
    (cs2 : β × List (Mini (BitVec width) × Nat × WordLangProgHOL (BitVec width)))
    (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (p : Mini (BitVec width)) (cs : CodeAcc width) (x : Nat) :
    stateRel s1 t1 cs2 t0 frame ∧ hasCompiledHOL p cs = .inl x ∧ codeSubset cs cs2 →
      ∃ (p1 : WordLangProgHOL (BitVec width)) (l1 i1 : Nat) (cs' cs1 : CodeAcc width),
        compile x 2 1 cs' p = (p1, l1, i1, cs1) ∧ codeSubset cs1 cs2 ∧
          sptLookup x t1.code = some (1, .seq p1 (.return 0 [0])) := by
  rintro ⟨hrel, hc, hsub⟩
  rw [← hasCompiled_eq_HOL] at hc
  obtain ⟨code, hl⟩ := hasCompiled_inl_lookup p cs x hc
  have hl2 := hsub p (x, code) hl
  obtain ⟨cs1, l2, i2, cs2', hcomp, hlook, hsub2⟩ := hrel.2.2.2.1 p x code hl2
  exact ⟨code, l2, i2, cs1, cs2', hcomp, hsub2, hlook⟩

end Flapjack.Compiler.Backend.WordBignum
