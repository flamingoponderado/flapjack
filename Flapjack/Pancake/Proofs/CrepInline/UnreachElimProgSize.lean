import Flapjack.Pancake.Proofs.CrepInline.UnreachElim
import Flapjack.Pancake.CrepLang.GeneratedSize

/-!
# crep_inline: `unreach_elim` size and return lemmas

Counterpart and explicitly untagged support for
`cakeml/pancake/proofs/crep_inlineProofScript.sml:1730-1780`
(`unreach_elim_prog_size`, `not_has_return_imp_unreach_elim`), bead
`flapjack-pxn.18.5.5.46.2`, over the tagged `unreachElimHOLExact`
(`unreach_elim_def`) and `hasReturnHOLExact` (`has_return_def`).
`unreach_elim_prog_size` is stated over HOL's Datatype-generated
`crepLang$prog_size`, transcribed untagged as `crepProgSizeHOL`
(`Flapjack.Pancake.CrepLang.GeneratedSize`, pinned by
`scripts/hol-probes/crep_lang_size_probe.out`).  HOL's size parameter
`f : 'a -> num` shares the program's HOL type index; the untagged size
rendering below has an independent Lean parameter, as its local caveat explains.
-/

namespace Flapjack

open Flapjack.CrepLangGeneratedSize

namespace CrepInlineUnreachElimProgSize

/-- Flapjack rendering of HOL `unreach_elim_prog_size`
    (`crep_inlineProofScript.sml:1730-1733`); NOT an exact tagged port.  HOL's
    elaborated statement (`scripts/hol-probes/crep_inline_prog_size_type_probe.out`)
    is `∀(p q : α prog) (r : early_exit option) (f : α -> num). ...`: the size
    function's domain is the same type variable `α` that indexes `α word`.
    The `words_as_type_indexed_bitvec` translation renders `α word` as
    `BitVec width` but has no Lean type for bare `α`, so this statement's
    independent `{α : Type} (f : α → Nat)` is an extra type quantifier (it
    implies every HOL instance, since `prog_size` never applies `f`).  The
    faithful carrier is tracked by bead `flapjack-pxn.18.5.5.50`. -/
theorem unreachElimProgSize {width : Nat} [NeZero width] {α : Type} :
    ∀ (p q : CrepProgHOL width) (r : Option CrepEarlyExitHOL) (f : α → Nat),
      unreachElimHOLExact p = (q, r) → crepProgSizeHOL f q ≤ crepProgSizeHOL f p := by
  intro p
  fun_induction unreachElimHOLExact p <;> intro q r f h <;>
    obtain ⟨hq, _⟩ := Prod.mk.inj h <;> subst hq
  -- Return, Raise, Break, Continue.
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  -- Seq whose first component reports an exit: the result is that component.
  · rename_i first second first' firstExit hfirst _ ih _
    have := ih first' firstExit f hfirst
    simp only [crepProgSizeHOL]
    omega
  -- Seq without an exit from its first component.
  · rename_i first second first' firstExit hfirst _ second' secondExit hsecond ih1 ih2 _
    have h1 := ih1 first' firstExit f hfirst
    have h2 := ih2 second' secondExit f hsecond
    simp only [crepProgSizeHOL]
    omega
  -- Dec.
  · rename_i name value body body' bodyExit hbody ih _
    have := ih body' bodyExit f hbody
    simp only [crepProgSizeHOL]
    omega
  -- If.
  · rename_i condition thenBranch elseBranch then' thenExit hthen else' elseExit helse ih1 ih2 _
    have h1 := ih1 then' thenExit f hthen
    have h2 := ih2 else' elseExit f helse
    simp only [crepProgSizeHOL]
    omega
  -- While.
  · rename_i condition body body' bodyExit hbody ih _
    have := ih body' bodyExit f hbody
    simp only [crepProgSizeHOL]
    omega
  -- Tail call and returning call without handler: unchanged.
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  -- Returning call with handler: the handler body shrinks.
  · rename_i names handler body name arguments body' bodyExit hbody ih _
    have := ih body' bodyExit f hbody
    simp only [crepProgSizeHOL, crepProg1SizeHOL, crepProg2SizeHOL, crepProg3SizeHOL,
      crepProg4SizeHOL]
    omega
  -- Every other constructor is unchanged.
  · exact Nat.le_refl _

/-- A merged exit is `Ret` only if one of the branch exits is `Ret`.  Local
    support; no separate HOL declaration. -/
private theorem crepMergeExitHOL_eq_return (a b : Option CrepEarlyExitHOL) :
    crepMergeExitHOL a b = some .return → a = some .return ∨ b = some .return := by
  rcases a with _ | a <;> rcases b with _ | b <;> (try cases a) <;> (try cases b) <;>
    simp [crepMergeExitHOL]

/-- Exact HOL `not_has_return_imp_unreach_elim` (`crep_inlineProofScript.sml:1765-1766`).
    HOL's Bool `has_return` used as a proposition is `= true`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "not_has_return_imp_unreach_elim"
  (words_as_type_indexed_bitvec)]
theorem notHasReturnImpUnreachElim {width : Nat} [NeZero width] :
    ∀ (p : CrepProgHOL width) (r : Option CrepEarlyExitHOL),
      ¬ hasReturnHOLExact p = true ∧ unreachElimHOLExact p = (p, r) → r ≠ some .return := by
  intro p
  fun_induction unreachElimHOLExact p <;> intro r ⟨hret, hu⟩ <;>
    obtain ⟨_, hr⟩ := Prod.mk.inj hu <;> subst hr
  -- Return has a return.
  · simp [hasReturnHOLExact] at hret
  · simp
  · simp
  · simp
  -- Seq whose first component reports an exit cannot be a fixed point: the
  -- result is no larger than the first component.
  · rename_i first second first' firstExit hfirst _ _ hp
    exfalso
    have hsize := unreachElimProgSize first first' firstExit (fun (_ : Unit) => 0) hfirst
    rw [hp] at hsize
    simp only [crepProgSizeHOL] at hsize
    omega
  -- Seq without an exit from its first component: the exit is the second's.
  · rename_i first second first' firstExit hfirst _ second' secondExit hsecond _ ih hp
    simp only [CrepProgHOL.seq.injEq] at hp
    obtain ⟨_, rfl⟩ := hp
    simp only [hasReturnHOLExact, Bool.or_eq_true, not_or] at hret
    exact ih secondExit ⟨hret.2, hsecond⟩
  -- Dec.
  · rename_i name value body body' bodyExit hbody ih hp
    simp only [CrepProgHOL.dec.injEq] at hp
    obtain ⟨_, _, rfl⟩ := hp
    exact ih bodyExit ⟨by simpa [hasReturnHOLExact] using hret, hbody⟩
  -- If: a merged Ret needs a Ret from one branch.
  · rename_i condition thenBranch elseBranch then' thenExit hthen else' elseExit helse ih1 ih2 hp
    simp only [CrepProgHOL.ite.injEq] at hp
    obtain ⟨_, rfl, rfl⟩ := hp
    simp only [hasReturnHOLExact, Bool.or_eq_true, not_or] at hret
    intro hmerge
    rcases crepMergeExitHOL_eq_return _ _ hmerge with h | h
    · exact ih1 thenExit ⟨hret.1, hthen⟩ h
    · exact ih2 elseExit ⟨hret.2, helse⟩ h
  -- While, returning calls and every other constructor report no Ret.
  · simp
  · simp [hasReturnHOLExact] at hret
  · simp
  · simp
  · simp

end CrepInlineUnreachElimProgSize

end Flapjack
