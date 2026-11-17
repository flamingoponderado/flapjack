module

public import Flapjack.Compiler.Inference.TypeDCanon.SingleRename

@[expose] public section

/-! Source type-scheme non-instantiation under single identifier renaming. -/
namespace Flapjack.Compiler.Inference.TypeDCanon
open Flapjack.TypeSystemHOL Flapjack.Compiler.Inference.InferProps Flapjack.Compiler.Inference.TypeDCanon

mutual
/-- Flapjack proof helper for the source non-instantiation proof: a changed
constructor identifier cannot be repaired by de Bruijn substitution. -/
private theorem clash (t : SemanticT) (m n : Nat) (present : setTids t m) (different : m ≠ n)
    (skip : Nat) (sub : List SemanticT) :
    deBruijnSubst skip sub t ≠ tsTidRename (singRenum m n) t ∧
    deBruijnSubst skip sub (tsTidRename (singRenum m n) t) ≠ t := by
  cases t with
  | var name => simp [setTids] at present
  | varDb k => simp [setTids] at present
  | app ts id =>
    simp only [setTids] at present
    rcases present with eq | member
    · subst id
      simp [deBruijnSubst, tsTidRename, singRenum, different, Ne.symm different]
    · have ih := clashList ts m n member different skip sub
      constructor
      · intro eq
        apply ih.1
        simp only [deBruijnSubst, tsTidRename, SemanticT.app.injEq] at eq
        exact eq.1
      · intro eq
        apply ih.2
        simp only [deBruijnSubst, tsTidRename, SemanticT.app.injEq] at eq
        exact eq.1
termination_by sizeOf t

/-- List induction for the constructor-position argument. -/
private theorem clashList (ts : List SemanticT) (m n : Nat) (present : setTidsList ts m) (different : m ≠ n)
    (skip : Nat) (sub : List SemanticT) :
    deBruijnSubstList skip sub ts ≠ tsTidRenameList (singRenum m n) ts ∧
    deBruijnSubstList skip sub (tsTidRenameList (singRenum m n) ts) ≠ ts := by
  cases ts with
  | nil => simp [setTidsList] at present
  | cons t ts =>
    simp only [setTidsList] at present
    rcases present with head | tail
    · have ih := clash t m n head different skip sub
      constructor
      · intro eq
        apply ih.1
        simp only [deBruijnSubstList, tsTidRenameList, List.cons.injEq] at eq
        exact eq.1
      · intro eq
        apply ih.2
        simp only [deBruijnSubstList, tsTidRenameList, List.cons.injEq] at eq
        exact eq.1
    · have ih := clashList ts m n tail different skip sub
      constructor
      · intro eq
        apply ih.1
        simp only [deBruijnSubstList, tsTidRenameList, List.cons.injEq] at eq
        exact eq.2
      · intro eq
        apply ih.2
        simp only [deBruijnSubstList, tsTidRenameList, List.cons.injEq] at eq
        exact eq.2
termination_by sizeOf ts
end

/-- Flapjack proof infrastructure for the source declaration-canonicalization
argument: HOL proves this scheme-instance transport inline using the mapped
substitution witness. There is no separate HOL theorem for the helper. -/
theorem tschemeInstRename (f : Nat → Nat) (specCount implCount : Nat) (spec impl : SemanticT) :
    tschemeInst (specCount, spec) (implCount, impl) →
    tschemeInst (specCount, tsTidRename f spec) (implCount, tsTidRename f impl) := by
  rintro ⟨sub, length, freeImpl, freeSub, result⟩
  refine ⟨sub.map (tsTidRename f), ?_, ?_, ?_, ?_⟩
  · simpa using length
  · exact (checkFreevarsTsTidRename implCount [] impl f).2 freeImpl
  · rw [List.all_eq_true] at freeSub ⊢
    intro renamed member
    obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp member
    exact (checkFreevarsTsTidRename specCount [] original f).2 (freeSub original originalMem)
  · rw [← tsTidRenameDeBruijnSubst, result]

/-- Renaming an occurring identifier to a distinct one prevents type-scheme
instantiation in either direction. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "sing_renum_NOT_tscheme_inst"]
theorem singRenumNotTschemeInst (m n : Nat) (t : SemanticT) : setTids t m ∧ m ≠ n →
    tsTidRename (singRenum m n) t ≠ t ∧ ∀ tvs tvs',
      ¬tschemeInst (tvs, tsTidRename (singRenum m n) t) (tvs', t) ∧
      ¬tschemeInst (tvs', t) (tvs, tsTidRename (singRenum m n) t) := by
  rintro ⟨present, different⟩
  refine ⟨singRenumInNotId t m n ⟨present, different⟩, ?_⟩
  intro tvs tvs'
  constructor <;> intro h <;> obtain ⟨sub, _, _, _, eq⟩ := h
  · exact (clash t m n present different 0 sub).1 eq
  · exact (clash t m n present different 0 sub).2 eq

end Flapjack.Compiler.Inference.TypeDCanon
