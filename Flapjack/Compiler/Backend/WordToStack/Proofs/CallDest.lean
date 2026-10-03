import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRelGetVar
import Flapjack.Compiler.Backend.WordToStack.NativeCallArgs
import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers
import Flapjack.Compiler.Backend.Semantics.WordSem.Alloc
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef

/-!
# Word-to-Stack `call_dest_lemma`

The call-destination preamble (`word_to_stackProofScript.sml:3315-3415`): the
compiled destination finds the compiled callee of the source destination.
-/

namespace Flapjack.WordToStackProofs.CallDest
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStackRegFormat (wReg2)

/-- Canonical source-state relation codec re-export; no separate HOL original. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Canonical target-state relation codec re-export; no separate HOL original. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- The last argument's value is the last looked-up value. Flapjack helper; no
separate HOL original. -/
theorem getVars_getLast {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) :
    ∀ (args : List Nat) (vals : List (WordLocW width)),
      WordSemStateFiniteExact.getVars args s = some vals → ∀ (h : args ≠ []),
      ∃ (h' : vals ≠ []), WordSemStateFiniteExact.getVar (args.getLast h) s =
        some (vals.getLast h')
  | [], _, _, h => absurd rfl h
  | [a], vals, hv, _ => by
      simp only [WordSemStateFiniteExact.getVars] at hv
      rcases ha : WordSemStateFiniteExact.getVar a s with _ | v
      · simp [ha] at hv
      simp only [ha, Option.some.injEq] at hv
      subst hv
      exact ⟨by simp, by simpa using ha⟩
  | a :: b :: rest, vals, hv, _ => by
      rw [show WordSemStateFiniteExact.getVars (a :: b :: rest) s =
          (match WordSemStateFiniteExact.getVar a s with
            | none => none
            | some x =>
                match WordSemStateFiniteExact.getVars (b :: rest) s with
                | none => none
                | some xs => some (x :: xs)) from rfl] at hv
      rcases ha : WordSemStateFiniteExact.getVar a s with _ | v
      · rw [ha] at hv; cases hv
      rcases hr : WordSemStateFiniteExact.getVars (b :: rest) s with _ | vs
      · rw [ha, hr] at hv; cases hv
      rw [ha, hr] at hv
      simp only [Option.some.injEq] at hv
      subst hv
      obtain ⟨hne, hl⟩ := getVars_getLast s (b :: rest) vs hr (by simp)
      refine ⟨by simp, ?_⟩
      rw [List.getLast_cons (by simp), List.getLast_cons hne]
      exact hl

/-- The compiled code of every source function, read from `state_rel`'s code
conjunct. Flapjack projection helper; no separate HOL original. -/
theorem stateRel_code {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f f' : Nat}
    {s : WordSemStateFiniteExact width (Nat × C) F}
    {t : StackSemStateFiniteExact width C F} {lens : List Nat}
    (h : stateRel ac k f f' s t lens 0) (p arity : Nat) (prog : WordLangProgHOL (BitVec width))
    (hp : sptLookup p s.code = some (arity, prog)) :
    ∃ (bs : AppList (BitVec width)) (i : Nat) (bs2 : AppList (BitVec width)) (i2 fs : Nat)
      (stackProg : HolProg width),
      compileProgNative ac false prog arity k (bs, i) = (stackProg, fs, (bs2, i2)) ∧
      (appListAppend bs).length ≤ i ∧ i - (appListAppend bs).length ≤ t.bitmaps.length ∧
      List.IsPrefix (appListAppend bs2) (t.bitmaps.drop (i - (appListAppend bs).length)) ∧
      (sptLookup p s.stackSize).getD fs = fs ∧ sptLookup p t.code = some stackProg := by
  unfold stateRel at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h25, -⟩ := h
  obtain ⟨-, -, bs, i, bs2, i2, fs, sp, hc, h1, h2, h3, h4, h5⟩ := h25 p prog arity hp
  exact ⟨bs, i, bs2, i2, fs, sp, hc, h1, h2, h3, h5, h4⟩

/-- Writing a target register at or above `k` preserves `state_rel`: source
locals live only in registers below `k`. Flapjack helper generalizing HOL's
`state_rel_set_var_k` (which states the `k` and `k + 1` instances). -/
theorem stateRel_setVar_of_ge {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f f' : Nat}
    {s : WordSemStateFiniteExact width (Nat × C) F}
    {t : StackSemStateFiniteExact width C F} {lens : List Nat} {extra : Nat}
    (r : Nat) (hr : k ≤ r) (v : WordLocW width) (h : stateRel ac k f f' s t lens extra) :
    stateRel ac k f f' s (StackSemStateOps.setVar r v t) lens extra := by
  unfold stateRel at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36,
    h37, h38, hloc⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36,
    h37, h38, ?_⟩
  intro n w hn
  obtain ⟨he, hif⟩ := hloc n w hn
  refine ⟨he, ?_⟩
  by_cases hlt : n / 2 < k
  · rw [if_pos hlt] at hif ⊢
    have hne : n / 2 ≠ r := by omega
    simp [StackSemStateOps.setVar, HolFiniteMapExact.updateEq, FUPDATE_HOL, hne, hif]
  · rw [if_neg hlt] at hif ⊢
    exact hif

/-- Exact HOL `call_dest_lemma` (`word_to_stackProofScript.sml:3315-3415`). HOL's
free `ret`, `ac`, `k`, `f`, `f'` and `lens` are explicit; HOL `the fs ssize` is
`ssize.getD fs`. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "call_dest_lemma"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store,
    StackSemStateFiniteExact.regs, StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem callDestLemma {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f f' : Nat) (dest : Option Nat) (args : List Nat)
    (s : WordSemStateFiniteExact width (Nat × C) F) (t : StackSemStateFiniteExact width C F)
    (lens : List Nat) (q0 : HolProg width) (dest' : Sum Nat Nat)
    (args' : List (WordLocW width))
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    ¬ wordSemBadDestArgs dest args = true ∧ stateRel ac k f f' s t lens 0 ∧
      callDestNative dest args (k, f, f') = (q0, dest') ∧
      WordSemStateFiniteExact.getVars args s = some args' →
    ∃ t4 : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (q0, t) = (none, t4) ∧ stateRel ac k f f' s t4 lens 0 ∧
      t4.stack.length = t.stack.length ∧ t4.stackSpace = t.stackSpace ∧
      ∀ (realArgs : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
        (ssize : Option Nat),
        wordSemFindCode dest (wordSemAddRetLoc ret args') s.code s.stackSize =
          some (realArgs, prog, ssize) →
        ∃ (bs : AppList (BitVec width)) (i : Nat) (bs2 : AppList (BitVec width)) (i2 fs : Nat)
          (stackProg : HolProg width),
          compileProgNative ac false prog realArgs.length k (bs, i) =
            (stackProg, fs, (bs2, i2)) ∧
          (appListAppend bs).length ≤ i ∧ i - (appListAppend bs).length ≤ t.bitmaps.length ∧
          List.IsPrefix (appListAppend bs2) (t.bitmaps.drop (i - (appListAppend bs).length)) ∧
          ssize.getD fs = fs ∧ StackSemControl.findCode dest' t4.regs t4.code = some stackProg := by
  rintro ⟨hbad, hrel, hcall, hvars⟩
  rcases dest with _ | p
  · have hne : args ≠ [] := by
      rintro rfl; simp [wordSemBadDestArgs] at hbad
    obtain ⟨hne', hlast⟩ := getVars_getLast s args args' hvars hne
    have hloc := StateRelGetVar.stateRel_locals hrel _ _ hlast
    have hlen0 : ¬ args.length = 0 := by simpa using hne
    simp only [callDestNative, dif_neg hlen0, Prod.mk.injEq] at hcall
    obtain ⟨rfl, rfl⟩ := hcall
    have hrne : wordSemAddRetLoc ret args' ≠ [] := by
      rcases ret with _ | ⟨_, _, _, _, _⟩ <;> simp [wordSemAddRetLoc, hne']
    have hrlast : (wordSemAddRetLoc ret args').getLast hrne = args'.getLast hne' := by
      rcases ret with _ | ⟨_, _, _, _, _⟩
      · rfl
      · simp only [wordSemAddRetLoc]; exact List.getLast_cons hne'
    have hsrc : ∀ realArgs prog ssize,
        wordSemFindCode none (wordSemAddRetLoc ret args') s.code s.stackSize =
          some (realArgs, prog, ssize) →
        ∃ n arity, args'.getLast hne' = .loc n 0 ∧ sptLookup n s.code = some (arity, prog) ∧
          realArgs.length = arity ∧ ssize = sptLookup n s.stackSize := by
      intro realArgs prog ssize hfind
      simp only [wordSemFindCode, dif_neg hrne, hrlast] at hfind
      rcases hv : args'.getLast hne' with w | ⟨n, off⟩
      · rw [hv] at hfind; cases hfind
      rw [hv] at hfind
      rcases off with _ | off
      · rcases hp : sptLookup n s.code with _ | ⟨arity, body⟩
        · simp only [hp] at hfind; cases hfind
        simp only [hp] at hfind
        split at hfind
        · rename_i hl
          simp only [Option.some.injEq, Prod.mk.injEq] at hfind
          obtain ⟨rfl, rfl, rfl⟩ := hfind
          exact ⟨n, arity, rfl, hp, by simp [List.length_dropLast, hl], rfl⟩
        · cases hfind
      · simp at hfind
    by_cases hlt : args.getLast hne / 2 < k
    · rw [if_pos hlt] at hloc
      have hw : wReg2 (args.getLast hne) (k, f, f') = ([], args.getLast hne / 2) := by
        simp [wReg2, hlt]
      simp only [hw, wStackLoadNative]
      refine ⟨t, StackSemEvaluate.evaluate_skip t, hrel, rfl, rfl, ?_⟩
      intro realArgs prog ssize hfind
      obtain ⟨n, arity, hv, hp, hl, rfl⟩ := hsrc _ _ _ hfind
      obtain ⟨bs, i, bs2, i2, fs, sp, hc, h1, h2, h3, h4, h5⟩ := stateRel_code hrel n arity prog hp
      refine ⟨bs, i, bs2, i2, fs, sp, by rw [hl]; exact hc, h1, h2, h3, h4, ?_⟩
      simp only [StackSemControl.findCode, hloc.2, hv]
      exact h5
    · rw [if_neg hlt] at hloc
      obtain ⟨-, hslot, hbound⟩ := hloc
      have hw : wReg2 (args.getLast hne) (k, f, f') =
          ([(k + 1, f - 1 - (args.getLast hne / 2 - k))], k + 1) := by
        simp [wReg2, hlt]
      simp only [hw, wStackLoadNative]
      have hrel' := hrel
      unfold stateRel at hrel'
      obtain ⟨-, -, -, -, h5, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
        -, -, -, -, h33, -, -, -, -, -, -⟩ := hrel'
      set idx := f - 1 - (args.getLast hne / 2 - k) with hidx
      rw [Nat.add_zero, List.getElem?_take, List.getElem?_drop] at hslot
      split at hslot
      swap
      · cases hslot
      rename_i hif
      have hlt2 : t.stackSpace + idx < t.stack.length :=
        (List.getElem?_eq_some_iff.mp hslot).1
      have hval : t.stack[t.stackSpace + idx] = args'.getLast hne' :=
        (List.getElem?_eq_some_iff.mp hslot).2
      rw [StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_stackLoad,
        if_neg (by simp [h5]), dif_pos hlt2]
      simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
      rw [StackSemEvaluate.evaluate_skip]
      refine ⟨_, rfl, ?_, rfl, rfl, ?_⟩
      · exact stateRel_setVar_of_ge (k + 1) (by omega) _ hrel
      · intro realArgs prog ssize hfind
        obtain ⟨n, arity, hv, hp, hl, rfl⟩ := hsrc _ _ _ hfind
        obtain ⟨bs, i, bs2, i2, fs, sp, hc, h1, h2, h3, h4, h6⟩ :=
          stateRel_code hrel n arity prog hp
        refine ⟨bs, i, bs2, i2, fs, sp, by rw [hl]; exact hc, h1, h2, h3, h4, ?_⟩
        simp only [StackSemControl.findCode, HolFiniteMapExact.updateEq, FUPDATE_HOL, if_true,
          hval, hv]
        exact h6
  · simp only [callDestNative, Prod.mk.injEq] at hcall
    obtain ⟨rfl, rfl⟩ := hcall
    refine ⟨t, StackSemEvaluate.evaluate_skip t, hrel, rfl, rfl, ?_⟩
    intro realArgs prog ssize hfind
    simp only [wordSemFindCode] at hfind
    rcases hp : sptLookup p s.code with _ | ⟨arity, body⟩
    · rw [hp] at hfind; cases hfind
    rw [hp] at hfind
    simp only at hfind
    split at hfind
    · rename_i hlen
      simp only [Option.some.injEq, Prod.mk.injEq] at hfind
      obtain ⟨rfl, rfl, rfl⟩ := hfind
      obtain ⟨bs, i, bs2, i2, fs, sp, hc, h1, h2, h3, h4, h5⟩ :=
        stateRel_code hrel p arity body hp
      exact ⟨bs, i, bs2, i2, fs, sp, by rw [hlen]; exact hc, h1, h2, h3, h4, h5⟩
    · cases hfind

end Flapjack.WordToStackProofs.CallDest
