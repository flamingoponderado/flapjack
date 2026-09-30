import Flapjack.Pancake.Proofs.CrepInline.TransformBranch.Loops

/-!
# crep_inline: assembled `transform_branch_correct`

Assembly of HOL `transform_branch_correct` (`cakeml/pancake/proofs/crep_inlineProofScript.sml:2042-2186`)
from its tagged constructor cases (beads `flapjack-pxn.18.5.5.47.3`, `.47.6`).
As for the accepted `evaluate_state_locals_rel_strong` assembly, the
`evaluate_ind` motive is established for every program and state by the
lexicographic (clock, size) induction `evalCrepSemHOLProgExact_inductLex`,
which supplies every tagged case's literal premises, including the Call callee
premise at the decremented clock.  No public induction hypothesis remains.

See `EvaluateLocals/Assembly.lean` ("Induction principle and guard spellings")
for the equations (`callGuard_args_eq`, `callGuard_lookup_eq`,
`callGuard_nodup_iff`) relating the Call premises' guards to `evaluate_ind`'s.
-/

namespace Flapjack

namespace CrepInlineTransformBranch

open HolFiniteMapExact
open CrepInlineExact

namespace AssemblyWitness
/-- Same-module canonical witness for the finite-map qualifier on the
`CrepSemHOLState` fields `locals`, `globals` and `code`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end AssemblyWitness

/-- Local support: the `evaluate_ind` motive of `transform_branch_correct` for
    every program and state, by the lexicographic (clock, size) induction
    `evalCrepSemHOLProgExact_inductLex`.  Each tagged case is applied with
    exactly its `evaluate_ind` premises (including the Call callee premise at
    the decremented clock); every premise's program/state pair is
    lexicographically smaller. -/
private theorem branchMotive {width : Nat} [NeZero width] {σ : Type} :
    ∀ (p : CrepProgHOL width) (s : CrepSemHOLState width σ), transformBranchGoal p s := by
  refine evalCrepSemHOLProgExact_inductLex (motive := transformBranchGoal) ?_
  intro p s ih
  have lower : ∀ (p' : CrepProgHOL width) (s' : CrepSemHOLState width σ),
      s'.clock < s.clock → transformBranchGoal p' s' :=
    fun p' s' hc => ih p' s' (Prod.Lex.left _ _ hc)
  have same : ∀ (p' : CrepProgHOL width) (s' : CrepSemHOLState width σ),
      s'.clock = s.clock → sizeOf p' < sizeOf p → transformBranchGoal p' s' :=
    fun p' s' hc hs => ih p' s' (by rw [hc]; exact Prod.Lex.right _ hs)
  have dec_lt : s.clock ≠ 0 → (decClockCrepSemHOL s).clock < s.clock := by
    intro h; simp only [decClockCrepSemHOL_clock']; omega
  cases p with
  | skip => exact transformBranchCorrect_Leaf _ s (Or.inl rfl)
  | assign n e => exact transformBranchCorrect_Leaf _ s (Or.inr (Or.inl ⟨n, e, rfl⟩))
  | primitive ns op args =>
      exact transformBranchCorrect_Leaf _ s (Or.inr (Or.inr (Or.inl ⟨ns, op, args, rfl⟩)))
  | store a b => exact transformBranchCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, rfl⟩))))
  | store32 a b =>
      exact transformBranchCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, rfl⟩)))))
  | storeByte a b =>
      exact transformBranchCorrect_Leaf _ s
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, rfl⟩))))))
  | storeGlob a b =>
      exact transformBranchCorrect_Leaf _ s
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, rfl⟩)))))))
  | «break» n =>
      exact transformBranchCorrect_Leaf _ s
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))))))))
  | «continue» n =>
      exact transformBranchCorrect_Leaf _ s
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)))))))))
  | raise e =>
      exact transformBranchCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl ⟨e, rfl⟩))))))))))
  | tick =>
      exact transformBranchCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))
  | extCall f a b c d =>
      exact transformBranchCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, a, b, c, d, rfl⟩))))))))))))
  | shMem op n a =>
      exact transformBranchCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨op, n, a, rfl⟩))))))))))))
  | «return» es => exact transformBranchCorrect_Return es s
  | dec v e body =>
      exact transformBranchCorrect_Dec v e body s (fun _ _ =>
        same _ _ rfl (by simp only [CrepProgHOL.dec.sizeOf_spec]; omega))
  | ite c a b =>
      refine transformBranchCorrect_If c a b s (fun _ w _ _ => ?_)
      by_cases hw : w ≠ 0
      · rw [if_pos hw]; exact same _ _ rfl (by simp only [CrepProgHOL.ite.sizeOf_spec]; omega)
      · rw [if_neg hw]; exact same _ _ rfl (by simp only [CrepProgHOL.ite.sizeOf_spec]; omega)
  | seq a b =>
      refine transformBranchCorrect_Seq a b s (fun res s1 hs1 _ => ?_)
        (same _ _ rfl (by simp only [CrepProgHOL.seq.sizeOf_spec]; omega))
      have hle := evalCrepSemHOLProgExact_clock_le s a
      rw [← hs1] at hle
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · exact lower _ _ hlt
      · exact same _ _ heq (by simp only [CrepProgHOL.seq.sizeOf_spec]; omega)
  | «while» e c =>
      have hlt : ∀ res s1, s.clock ≠ 0 →
          (res, s1) = evalCrepSemHOLProgExact (decClockCrepSemHOL s) c → s1.clock < s.clock := by
        intro res s1 hck heq
        have hle := evalCrepSemHOLProgExact_clock_le (decClockCrepSemHOL s) c
        rw [← heq] at hle
        exact Nat.lt_of_le_of_lt hle (dec_lt hck)
      exact transformBranchCorrect_While e c s
        { continueCase := fun _ _ res s1 _ _ _ _ _ hck heq _ _ _ =>
            lower _ s1 (hlt res s1 hck heq)
          normalCase := fun _ _ res s1 _ _ _ hck heq _ => lower _ s1 (hlt res s1 hck heq)
          bodyCase := fun _ _ _ _ _ hck => lower _ _ (dec_lt hck) }
  | call info f args =>
      exact transformBranchCorrect_Call info f args s
        (fun _ _ newlocals _ _ _ hck => lower _ { decClockCrepSemHOL s with locals := newlocals }
          (dec_lt hck))
        (fun _ prog newlocals _ _ _ st _ _ _ hck hb _ => by
          have hle := evalCrepSemHOLProgExact_clock_le
            { decClockCrepSemHOL s with locals := newlocals } prog
          rw [hb] at hle
          exact lower _ { st with locals := s.locals } (Nat.lt_of_le_of_lt hle (dec_lt hck)))

/-- Exact HOL `transform_branch_correct` (`crep_inlineProofScript.sml:2042-2186`),
    assembled from the tagged constructor cases with every `evaluate_ind`
    premise discharged internally. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "transform_branch_correct"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem transformBranchCorrect {width : Nat} [NeZero width] {σ : Type} :
    ∀ (p : CrepProgHOL width) (s : CrepSemHOLState width σ)
      (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
      (ld : Nat) (rts : List Nat),
      evalCrepSemHOLProgExact s (p) = (r, s') ∧
        (∀ retvs, r = some (.return retvs) → rts.length = retvs.length) ∧
        (∀ x, x ∈ rts → x ∉ crepVarProgHOLExact (p)) ∧
        (∃ z, rts.mapM s.locals.lookup = some z) ∧
        rts.Nodup ∧
        r ≠ some .error →
      ∃ r1 s1', evalCrepSemHOLProgExact s (transformBranchHOLExact ld rts (p)) = (r1, s1') ∧
        crepInlineStateRelExact s' s1' ∧
        match r with
        | none => r1 = none ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.break n) => r1 = some (.break n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.continue n) => r1 = some (.continue n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.return retvs) => r1 = some (.break ld) ∧ rts.mapM s1'.locals.lookup = some retvs
        | some .error => False
        | _ => r1 = r :=
  fun p s => branchMotive p s

end CrepInlineTransformBranch

end Flapjack
