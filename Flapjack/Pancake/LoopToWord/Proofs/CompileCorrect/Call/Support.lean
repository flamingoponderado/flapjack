import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Property
import Flapjack.Pancake.Proofs.LoopToWord.ContextSupport
import Flapjack.Pancake.Semantics.LoopProps.UnassignedVarsExact

/-!
# Shared support for the `Call` case of `loop_to_word`'s `compile_correct`

This is Flapjack-only proof support for the `Call` resumes of HOL
`compile_correct` (`cakeml/pancake/proofs/loop_to_wordProofScript.sml:1017-1407`,
bead `flapjack-pxn.18.5.9.27.1`).  Nothing here is tagged: HOL proves these
facts inline in the `Call` case.

* `sptLookup_sptDifference` is HOL's `sptree$lookup_difference` for the exact
  `sptDifference`.
* `findCode_rel` is the find-code correspondence that HOL establishes at
  `:1037-1080` and `:1091-1127`.  A source call target found by loopSem
  `find_code` is found by wordSem `find_code` on any extra leading argument
  `x` (the return location).  Its body is `comp_func`, that is, the source
  body compiled under a `make_ctxt` context, which satisfies `locals_rel`
  and the `acc_vars` domain condition.
-/

namespace Flapjack.LoopToWord.CompileCorrect

open Flapjack

/-- HOL `sptree$lookup_difference` for `sptDifference`: a key survives exactly
    when it is absent from the right tree. -/
theorem sptLookup_sptDifference {α β : Type} :
    ∀ (t1 : Spt α) (t2 : Spt β) (k : Nat),
      sptLookup k (sptDifference t1 t2) =
        if (sptLookup k t2).isSome then none else sptLookup k t1
  | .ln, t2, k => by simp [sptDifference, sptLookup]
  | .ls v, t2, k => by
      cases t2 <;> simp only [sptDifference] <;> by_cases hk : k = 0 <;> simp [sptLookup, hk]
  | .bn l r, t2, k => by
      cases t2 with
      | ln => simp [sptDifference, sptLookup]
      | ls _ => simp only [sptDifference]; by_cases hk : k = 0 <;> simp [sptLookup, hk]
      | bn l' r' =>
        simp only [sptDifference, sptLookup_sptMkBN]
        by_cases hk : k = 0
        · simp [sptLookup, hk]
        · by_cases he : k % 2 = 0
          · simp only [sptLookup, hk, he, if_false, if_true, sptLookup_sptDifference l l']
          · simp only [sptLookup, hk, he, if_false, sptLookup_sptDifference r r']
      | bs l' _ r' =>
        simp only [sptDifference, sptLookup_sptMkBN]
        by_cases hk : k = 0
        · simp [sptLookup, hk]
        · by_cases he : k % 2 = 0
          · simp only [sptLookup, hk, he, if_false, if_true, sptLookup_sptDifference l l']
          · simp only [sptLookup, hk, he, if_false, sptLookup_sptDifference r r']
  | .bs l v r, t2, k => by
      cases t2 with
      | ln => simp [sptDifference, sptLookup]
      | ls _ => simp only [sptDifference]; by_cases hk : k = 0 <;> simp [sptLookup, hk]
      | bn l' r' =>
        simp only [sptDifference, sptLookup_sptMkBS]
        by_cases hk : k = 0
        · simp [sptLookup, hk]
        · by_cases he : k % 2 = 0
          · simp only [sptLookup, hk, he, if_false, if_true, sptLookup_sptDifference l l']
          · simp only [sptLookup, hk, he, if_false, sptLookup_sptDifference r r']
      | bs l' _ r' =>
        simp only [sptDifference, sptLookup_sptMkBN]
        by_cases hk : k = 0
        · simp [sptLookup, hk]
        · by_cases he : k % 2 = 0
          · simp only [sptLookup, hk, he, if_false, if_true, sptLookup_sptDifference l l']
          · simp only [sptLookup, hk, he, if_false, sptLookup_sptDifference r r']

theorem sptMem_sptDifference {α β : Type} (t1 : Spt α) (t2 : Spt β) (k : Nat) :
    sptMem k (sptDifference t1 t2) ↔ sptMem k t1 ∧ ¬ sptMem k t2 := by
  simp only [sptMem_iff_lookup, sptLookup_sptDifference]
  cases h2 : sptLookup k t2 <;> cases h1 : sptLookup k t1 <;> simp

/-- The `comp_func` context of a callee, with `locals_rel` and the `acc_vars`
    condition. -/
theorem compFunc_ctxt {width : Nat} [NeZero width] (params : List Nat)
    (body : HolLoopProg width) (values : List (WordLocW width)) (x : WordLocW width)
    (hnd : params.Nodup) (hlen : params.length = values.length) :
    let vs := fromNumSetHOL (sptDifference (accVarsHOL body (.ln : Spt Unit)) (toNumSetHOL params))
    let ctxt1 := Flapjack.makeCtxtHOL 2 (params ++ vs) (.ln : Spt Nat)
    localsRelHOL ctxt1 (sptFromAList (params.zip values)) (sptFromList2 (x :: values)) ∧
      ∀ k, sptMem k (accVarsHOL body .ln) → sptMem k ctxt1 := by
  intro vs ctxt1
  have hvs : ∀ k, k ∈ vs ↔ sptMem k (accVarsHOL body .ln) ∧ ¬ k ∈ params := by
    intro k
    have h1 := congrFun (fromNumSetHOL_set
      (sptDifference (accVarsHOL body (.ln : Spt Unit)) (toNumSetHOL params))) k
    have h2 := congrFun (sptDomain_toNumSetHOL params) k
    rw [show (k ∈ vs) = _ from h1]
    change sptMem k _ ↔ _
    rw [sptMem_sptDifference]
    change _ ∧ ¬ sptDomain _ k ↔ _
    rw [h2]
  refine ⟨localsRelHOLMakeCtxt params vs values x ⟨hnd, ?_, hlen⟩, ?_⟩
  · intro name hp hv
    exact ((hvs name).mp hv).2 hp
  · intro k hk
    have hd := congrFun (sptDomain_makeCtxtHOL 2 (params ++ vs) (.ln : Spt Nat)) k
    change sptDomain _ k
    rw [hd]
    right
    by_cases hp : k ∈ params
    · exact List.mem_append_left _ hp
    · exact List.mem_append_right _ ((hvs k).mpr ⟨hk, hp⟩)

/-- The find-code correspondence of HOL's `Call` case
    (`loop_to_wordProofScript.sml:1037-1080`, `:1091-1127`). -/
theorem findCode_rel {width : Nat} [NeZero width]
    (scode : Spt (List Nat × HolLoopProg width))
    (tcode : Spt (Nat × WordLangProgHOL (BitVec width))) (ssize : Spt Nat)
    (dest : Option Nat) (argvals : List (WordLocW width)) (env : Spt (WordLocW width))
    (prog : HolLoopProg width) (x : WordLocW width)
    (hcode : loopToWordCodeRelHOLExact scode tcode)
    (hf : LoopSemStateFiniteExact.findCode dest argvals scode = some (env, prog)) :
    ∃ args1 ss1 ctxt1 l1,
      wordSemFindCode dest (x :: argvals) tcode ssize =
          some (args1, (compHOL ctxt1 prog l1).1, ss1) ∧
        sptLookup 0 (sptFromList2 args1) = some x ∧
        localsRelHOL ctxt1 env (sptFromList2 args1) ∧
        ∀ k, sptMem k (accVarsHOL prog .ln) → sptMem k ctxt1 := by
  cases dest with
  | some p =>
    simp only [LoopSemStateFiniteExact.findCode] at hf
    split at hf
    · cases hf
    · rename_i params body hlk
      split at hf
      · rename_i hlen
        simp only [Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        obtain ⟨htl, hnd⟩ := hcode p params body hlk
        obtain ⟨hl, hacc⟩ := compFunc_ctxt params body argvals x hnd hlen.symm
        refine ⟨x :: argvals, sptLookup p ssize, _, (p, 2), ?_, ?_, hl, hacc⟩
        · simp [wordSemFindCode, htl, hlen, loopToWordCompFuncHOL]
        · have h := sptLookup_sptFromList2_get (x :: argvals) 0 (by simp)
          simp only [Nat.mul_zero, List.getElem_cons_zero] at h; exact h
      · cases hf
  | none =>
    cases argvals with
    | nil => simp [LoopSemStateFiniteExact.findCode] at hf
    | cons a rest =>
      simp only [LoopSemStateFiniteExact.findCode] at hf
      split at hf
      · rename_i loc hlast
        split at hf
        · cases hf
        · rename_i params body hlk
          split at hf
          · rename_i hlen
            simp only [Option.some.injEq, Prod.mk.injEq] at hf
            obtain ⟨rfl, rfl⟩ := hf
            obtain ⟨htl, hnd⟩ := hcode loc params body hlk
            have hlen' : params.length = (a :: rest).dropLast.length := by
              simp at hlen ⊢; omega
            obtain ⟨hl, hacc⟩ := compFunc_ctxt params body (a :: rest).dropLast x hnd hlen'
            refine ⟨x :: (a :: rest).dropLast, sptLookup loc ssize, _, (loc, 2), ?_, ?_, hl, hacc⟩
            · have hl2 : (x :: a :: rest).getLast (by simp) = .loc loc 0 := by
                rw [List.getLast_cons (by simp)]; exact hlast
              simp only [wordSemFindCode, List.cons_ne_nil, dite_false, hl2, htl]
              rw [if_pos (by simp at hlen ⊢; omega)]
              simp [loopToWordCompFuncHOL, List.dropLast_cons_of_ne_nil]
            · have h := sptLookup_sptFromList2_get (x :: (a :: rest).dropLast) 0 (by simp)
              simp only [Nat.mul_zero, List.getElem_cons_zero] at h; exact h
          · cases hf
      · cases hf

end Flapjack.LoopToWord.CompileCorrect
