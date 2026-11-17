module

public import Flapjack.Compiler.Inference.InferProps.NameBounds
public import Flapjack.NamespaceProps.All

@[expose] public section

/-! Identifier bounds for source constructor environments. -/
namespace Flapjack.Compiler.Inference.TypeDCanon
open Flapjack Flapjack.NamespaceHOL Flapjack.TypeSystemHOL Flapjack.AstHOL
  Flapjack.Compiler.Inference.InferProps

noncomputable local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

/-- Constructor environments use only existing or newly allocated type IDs. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "build_ctor_tenv_type_identities"]
theorem buildCtorTenvTypeIdentities {M N P Q : Type}
    (env : TenvAbbrev) (xs : List (P × Q × List (N × List AstT)))
    (ids : List Nat) (tids : Nat → Prop) :
    primTids true tids ∧
      nsAll (fun _ entry => setTidsSubset (fun id => tids id ∨ id ∈ ids) entry.2) env ∧
      xs.length = ids.length →
    nsAll (fun _ entry => (∀ t ∈ entry.2.1, setTidsSubset (fun id => tids id ∨ id ∈ ids) t) ∧
      (tids entry.2.2 ∨ entry.2.2 ∈ ids))
      (buildCtorTenv (α := M) env xs ids) := by
  induction xs generalizing ids tids with
  | nil =>
    intro ⟨prim, envBound, length⟩
    cases ids with
    | nil =>
      intro name value found
      cases name <;> simp [buildCtorTenv, alistToNs, nsLookup] at found
    | cons id ids => simp at length
  | cons x xs ih =>
    rcases x with ⟨params, typeName, ctors⟩
    cases ids with
    | nil => simp
    | cons id ids =>
      intro ⟨prim, envBound, length⟩
      simp only [List.length_cons, Nat.succ.injEq] at length
      simp only [buildCtorTenv]
      apply nsAll_nsAppend
      constructor
      · have prim' : primTids true (fun x => tids x ∨ x = id) := by
          intro x member
          exact ⟨fun _ => rfl, fun _ => Or.inl ((prim x member).2 rfl)⟩
        have envBound' : nsAll (fun _ entry => setTidsSubset
            (fun x => (tids x ∨ x = id) ∨ x ∈ ids) entry.2) env := by
          intro name entry found x member
          have h := envBound name entry found x member
          simpa [List.mem_cons, or_assoc, or_left_comm, or_comm] using h
        have h := ih ids (fun x => tids x ∨ x = id) ⟨prim', envBound', length⟩
        intro name entry found
        have h' := h name entry found
        simpa [List.mem_cons, or_assoc, or_left_comm, or_comm] using h'
      · apply nsAllAlistToNs
        intro entry member
        simp only [List.mem_reverse, List.mem_map] at member
        obtain ⟨⟨cname, args⟩, mem, rfl⟩ := member
        constructor
        · intro typ htyp
          obtain ⟨source, sourceMem, rfl⟩ := List.mem_map.mp htyp
          apply setTidsSubsetTypeNameSubst env source (fun x => tids x ∨ x ∈ id :: ids)
          constructor
          · intro x h
            exact ⟨fun _ => rfl, fun _ => Or.inl ((prim x h).2 rfl)⟩
          · exact envBound
        · exact Or.inr (by simp)

end Flapjack.Compiler.Inference.TypeDCanon
