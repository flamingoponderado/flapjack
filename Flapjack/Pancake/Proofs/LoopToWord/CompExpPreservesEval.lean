import Flapjack.Pancake.LoopToWord
import Flapjack.Pancake.LoopToWord.Proofs.RelationsExact
import Flapjack.Pancake.Proofs.LoopToWord.LocalsRel
import Flapjack.Pancake.Proofs.LoopToWord.WordShiftModDimword
import Flapjack.Pancake.Semantics.LoopSemStateExact
import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
import Flapjack.Misc.GoodDimindex

/-!
# Exact port of HOL `comp_exp_preserves_eval`

The HOL source `loop_to_wordProofScript.sml:460-509` states
`!s e v t ctxt. eval s e = SOME v /\ good_dimindex(:'a) /\ state_rel s t /\
locals_rel ctxt s.locals t.locals ==> word_exp t (comp_exp ctxt e) = SOME v`.
This module ports it over the exact `LoopSemStateFiniteExact.eval`,
`compExpHOL`, the tagged `WordSemStateFiniteExact.wordExp`,
`loopToWordStateRelHOLExact` and `localsRelHOL` carriers, using the tagged
`word_sh_SOME_MOD_dimword` lemma for the shift case.
-/

namespace Flapjack.LoopToWord

open Flapjack.WordSemStateFiniteExact

private theorem attach_map_val {α β : Type} (l : List α) (f : α → β) :
    l.attach.map (fun x => f x.val) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => cases l <;> simp_all [List.attach]

private theorem theWords_exists_word {width : Nat} [NeZero width]
    {ws : List (BitVec width)} :
    ∀ {l : List (Option (WordLocW width))}, Flapjack.theWords l = some ws →
      ∀ x ∈ l, ∃ w, x = some (.word w) := by
  intro l
  induction l generalizing ws with
  | nil => intro h x hx; simp at hx
  | cons y ys ih =>
    intro h x hx
    simp only [Flapjack.theWords] at h
    cases hy : y with
    | none => rw [hy] at h; simp at h
    | some v =>
      cases v with
      | word w =>
        cases hys : Flapjack.theWords ys with
        | none => rw [hy, hys] at h; simp at h
        | some ws' =>
          rw [hy, hys] at h
          simp only [Option.some.injEq] at h
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨w, hy⟩
          · exact ih hys x hx
      | loc b o => rw [hy] at h; simp at h

private theorem twoPow_one {width : Nat} : BitVec.twoPow width 1 = (2 : BitVec width) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.twoPow, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mul_mod, Nat.mul_mod]
  simp

private theorem wordShiftHOL_lsl_one {width : Nat} [NeZero width] (v : BitVec width)
    (hgd : goodDimindex width) : wordShiftHOL .lsl v 1 = some (v + v) := by
  unfold wordShiftHOL
  have hw : ¬ (1 ≠ 0 ∧ width ≤ 1) := by
    rintro ⟨_, hle⟩
    rcases hgd with h | h <;> omega
  rw [if_neg hw]
  show some (v <<< (1 : Nat)) = some (v + v)
  rw [BitVec.shiftLeft_eq_mul_twoPow, twoPow_one, BitVec.mul_comm]
  exact congrArg some BitVec.two_mul

private theorem ofNat_one_toNat {width : Nat} [NeZero width] (hgd : goodDimindex width) :
    (BitVec.ofNat width 1).toNat = 1 := by
  rw [BitVec.toNat_ofNat]
  have hw : 1 < 2 ^ width := by
    rcases hgd with h | h <;> (rw [h]; decide)
  exact Nat.mod_eq_of_lt hw

private theorem findVarHOL_of_lookup {context : Spt Nat} {name : Nat} {r : Nat}
    (h : sptLookup name context = some r) : findVarHOL context name = r := by
  unfold findVarHOL; rw [h]; rfl

/-! Fresh-namespace re-exports of the two relation carriers' canonical
finite-support witnesses, so the `fmap_as_finite_support_relation` qualifier on
the tagged theorem resolves them in this module without shadowing the imported
`LoopToWordStateRelWitnesses` declarations (AGENTS precedent). -/
namespace LoopToWordCompExpWitnesses

theorem holFmapAsFiniteSupportRelationWitness_LoopSemStateFiniteExact
    {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopToWordStateRelWitnesses.holFmapAsFiniteSupportRelationWitness_LoopSemStateFiniteExact

theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopToWordStateRelWitnesses.holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact

end LoopToWordCompExpWitnesses

/-- Exact HOL `comp_exp_preserves_eval` (`loop_to_wordProofScript.sml:460-509`):
`eval s e = SOME v` under `good_dimindex(:'a)`, `state_rel s t` and
`locals_rel ctxt s.locals t.locals` implies `word_exp t (comp_exp ctxt e) =
SOME v`. Binder order and hypotheses are exactly HOL's; `word_exp` resolves to
`WordSemStateFiniteExact.wordExp` via the file-level `open`. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "comp_exp_preserves_eval"
  (fmap_as_finite_support_relation := [LoopSemStateFiniteExact.globals, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem loopToWordCompExpPreservesEval {width : Nat} [NeZero width] {F : Type}
    (source : LoopSemStateFiniteExact width F) (expression : HolLoopExp width)
    (value : WordLocW width) (target : WordSemStateFiniteExact width Nat F)
    (context : Spt Nat)
    (heval : LoopSemStateFiniteExact.eval source expression = some value)
    (hgd : Flapjack.goodDimindex width)
    (hstate : loopToWordStateRelHOLExact source target)
    (hlocals : localsRelHOL context source.locals target.locals) :
    wordExp target (compExpHOL context expression) = some value := by
  classical
  revert value target context
  induction expression using LoopSemStateFiniteExact.eval.induct source with
  | case1 w => -- const
    intro value target context heval hstate hlocals
    simp only [LoopSemStateFiniteExact.eval, Option.some.injEq] at heval
    have hv : value = .word w := heval.symm
    subst hv
    simp only [compExpHOL, wordExp]
  | case2 v => -- var
    intro value target context heval hstate hlocals
    simp only [LoopSemStateFiniteExact.eval] at heval
    obtain ⟨r, hctx, hloc⟩ := hlocals.2.2 v value heval
    simp only [compExpHOL, wordExp, WordSemStateFiniteExact.getVar]
    rw [findVarHOL_of_lookup hctx]
    exact hloc
  | case3 name => -- lookup
    intro value target context heval hstate hlocals
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hglob, _⟩ := hstate
    simp only [LoopSemStateFiniteExact.eval] at heval
    simp only [compExpHOL, wordExp, WordSemStateFiniteExact.getStore]
    exact hglob name value heval
  | case4 address w haddr ih => -- load (word address)
    intro value target context heval hstate hlocals
    obtain ⟨len, hmem, hmdom, hshm, hclock, hbe, hffi, hcurr, hhlen, htop, hglob, hcode⟩ := hstate
    have hsrc : LoopSemStateFiniteExact.memLoad w source = some value := by
      simpa only [LoopSemStateFiniteExact.eval, haddr] using heval
    have ihw := ih (.word w) target context haddr
      ⟨len, hmem, hmdom, hshm, hclock, hbe, hffi, hcurr, hhlen, htop, hglob, hcode⟩ hlocals
    have hmemLoad : WordSemStateFiniteExact.memLoad w target =
        LoopSemStateFiniteExact.memLoad w source := by
      unfold WordSemStateFiniteExact.memLoad LoopSemStateFiniteExact.memLoad
      rw [hmdom, hmem]
    simp only [compExpHOL, wordExp, ihw, hmemLoad]
    exact hsrc
  | case5 address hnotword ih => -- load (non-word address): impossible
    intro value target context heval hstate hlocals
    simp only [LoopSemStateFiniteExact.eval] at heval
    cases h : LoopSemStateFiniteExact.eval source address with
    | none => simp at heval
    | some v' =>
      cases v' with
      | word w => exact absurd h (hnotword w)
      | loc b o => simp at heval
  | case6 operator args ws hwords ih => -- op (success)
    intro value target context heval hstate hlocals
    simp only [LoopSemStateFiniteExact.eval, hwords] at heval
    obtain ⟨w, hw, hval⟩ : ∃ w, wordOpHOL operator ws = some w ∧ value = .word w := by
      cases hh : wordOpHOL operator ws with
      | none => simp [hh] at heval
      | some w => exact ⟨w, rfl, by simpa [hh] using heval.symm⟩
    subst hval
    have hwords_map : Flapjack.theWords
        (args.map (fun e => LoopSemStateFiniteExact.eval source e)) = some ws := by
      rw [← attach_map_val args (fun e => LoopSemStateFiniteExact.eval source e)]
      exact hwords
    have hf_eq : args.map (fun e => LoopSemStateFiniteExact.eval source e) =
        args.map (fun e => wordExp target (compExpHOL context e)) := by
      apply List.map_congr_left
      intro e he
      obtain ⟨w', hw'⟩ := theWords_exists_word hwords_map
        (LoopSemStateFiniteExact.eval source e) (List.mem_map.mpr ⟨e, he, rfl⟩)
      have hih := ih e he (.word w') target context hw' hstate hlocals
      rw [hih, hw']
    have hgoal : Flapjack.theWords
        (args.map (fun e => wordExp target (compExpHOL context e))) = some ws := by
      rw [← hf_eq]; exact hwords_map
    have hX : (args.map (compExpHOL context)).attach.map
        (fun item => wordExp target item.val) =
        args.map (fun e => wordExp target (compExpHOL context e)) := by
      rw [← attach_map_val args (fun e => wordExp target (compExpHOL context e))]
      rw [List.attach_map, List.map_map]
      simp only [Function.comp_def]
    simp only [compExpHOL, wordExp, hX, hgoal, hw]
    rfl
  | case7 operator args hwords ih => -- op (failure): impossible
    intro value target context heval hstate hlocals
    simp only [LoopSemStateFiniteExact.eval, hwords] at heval
    exact absurd heval (by simp)
  | case8 sh e1 e2 w1 w2 heval2 heval1 ih1 ih2 => -- shift (success)
    intro value target context heval hstate hlocals
    simp only [LoopSemStateFiniteExact.eval, heval1, heval2] at heval
    simp only [compExpHOL, wordExp]
    rw [ih1 (.word w1) target context heval1 hstate hlocals,
        ih2 (.word w2) target context heval2 hstate hlocals]
    exact heval
  | case9 sh e1 e2 hnot ih1 ih2 => -- shift (failure): impossible
    intro value target context heval hstate hlocals
    simp only [LoopSemStateFiniteExact.eval] at heval
    cases h1 : LoopSemStateFiniteExact.eval source e1 with
    | none => simp at heval
    | some v1 =>
      cases v1 with
      | word w1 =>
        cases h2 : LoopSemStateFiniteExact.eval source e2 with
        | none => simp at heval
        | some v2 =>
          cases v2 with
          | word w2 => exact (hnot w1 w2 h1 h2).elim
          | loc b o => simp at heval
      | loc b o => simp at heval
  | case10 => -- baseAddr
    intro value target context heval hstate hlocals
    obtain ⟨_, _, _, _, _, _, _, hcurr, _, _, _, _⟩ := hstate
    simp only [LoopSemStateFiniteExact.eval, Option.some.injEq] at heval
    subst heval
    simp only [compExpHOL, wordExp, WordSemStateFiniteExact.getStore]
    exact hcurr
  | case11 => -- topAddr
    intro value target context heval hstate hlocals
    obtain ⟨len, hmem, hmdom, hshm, hclock, hbe, hffi, hcurr, hhlen, htop, hglob, hcode⟩ := hstate
    simp only [LoopSemStateFiniteExact.eval, Option.some.injEq] at heval
    subst heval
    simp only [compExpHOL]
    have htop' : source.topAddr = source.baseAddr +
        (BitVec.ofNat width len + BitVec.ofNat width len) := by
      rw [htop]
      exact congrArg (fun x => source.baseAddr + x) BitVec.two_mul
    simp only [wordExp, WordSemStateFiniteExact.getStore, hcurr, hhlen, ofNat_one_toNat hgd,
      wordShiftHOL_lsl_one _ hgd, Flapjack.theWords, wordOpHOL, wordOp, List.attach_cons,
      List.attach_nil, List.map_cons, List.map_nil]
    rw [htop']
    simp

end Flapjack.LoopToWord
