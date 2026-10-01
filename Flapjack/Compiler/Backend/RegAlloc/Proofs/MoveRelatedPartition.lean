import Flapjack.Compiler.Backend.RegAlloc.Accessors
import Flapjack.Compiler.Backend.RegAlloc.StatePartition
import Flapjack.Compiler.Backend.RegAlloc.Proofs.ArrayRead

/-!
# reg_allocProof `st_ex_PARTITION move_related_sub`

Port of `reg_allocProofScript.sml:2118-2134`: the state-exception partition of
in-range nodes by their `move_related` flag succeeds without changing the
state, and each bucket draws only from its accumulator and the input. HOL
`EVERY P l` is `∀ x ∈ l, P x` and `MEM` is list membership. The proof reads
array elements through Lean's bounds-checked indexing, not the held HOL `EL`
rendering.
-/

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- HOL `st_ex_PARTITION_move_related_sub` (`reg_allocProofScript.sml:2118-2134`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "st_ex_PARTITION_move_related_sub"]
theorem stExPartitionMoveRelatedSub :
    ∀ (atemps lss lss' : List Nat) (s : State),
      (∀ x ∈ atemps, x < s.move_related.length) →
      ∃ ts fs, stExPartition moveRelatedSub atemps lss lss' s = (.success (ts, fs), s) ∧
        (∀ x ∈ ts, x ∈ lss ∨ x ∈ atemps) ∧
        (∀ x ∈ fs, x ∈ lss' ∨ x ∈ atemps) := by
  intro atemps
  induction atemps with
  | nil =>
      intro lss lss' s _
      exact ⟨lss, lss', rfl, fun x hx => Or.inl hx, fun x hx => Or.inl hx⟩
  | cons h atemps ih =>
      intro lss lss' s hb
      have hh : h < s.move_related.length := hb h (by simp)
      have hrest : ∀ x ∈ atemps, x < s.move_related.length :=
        fun x hx => hb x (by simp [hx])
      have hsub : moveRelatedSub h s = (.success s.move_related[h], s) := by
        show (mSub StateException.Subscript h s.move_related, s) = _
        rw [mSub_success_getElem _ _ _ hh]
      cases hflag : s.move_related[h] with
      | true =>
          obtain ⟨ts, fs, heq, hts, hfs⟩ := ih (h :: lss) lss' s hrest
          refine ⟨ts, fs, ?_, ?_, ?_⟩
          · simp only [stExPartition, Translator.Monadic.MonadBase.bind, hsub, hflag, if_true]
            exact heq
          · intro x hx
            rcases hts x hx with hx | hx
            · rcases List.mem_cons.mp hx with rfl | hx
              · exact Or.inr (by simp)
              · exact Or.inl hx
            · exact Or.inr (by simp [hx])
          · intro x hx
            rcases hfs x hx with hx | hx
            · exact Or.inl hx
            · exact Or.inr (by simp [hx])
      | false =>
          obtain ⟨ts, fs, heq, hts, hfs⟩ := ih lss (h :: lss') s hrest
          refine ⟨ts, fs, ?_, ?_, ?_⟩
          · simp only [stExPartition, Translator.Monadic.MonadBase.bind, hsub, hflag, Bool.false_eq_true, if_false]
            exact heq
          · intro x hx
            rcases hts x hx with hx | hx
            · exact Or.inl hx
            · exact Or.inr (by simp [hx])
          · intro x hx
            rcases hfs x hx with hx | hx
            · rcases List.mem_cons.mp hx with rfl | hx
              · exact Or.inr (by simp)
              · exact Or.inl hx
            · exact Or.inr (by simp [hx])

end Flapjack.RegAlloc
