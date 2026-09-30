import Flapjack.Pancake.Proofs.CrepInline.TransformBranch.Loops

/-!
# crep_inline: assembled `transform_branch_correct`

Assembly of HOL `transform_branch_correct` (`cakeml/pancake/proofs/crep_inlineProofScript.sml:2042-2186`)
from its constructor calculations. The untagged `handlerOnlyBranchMotive`
establishes the structural calculation, with inner clock induction for While,
and uses the existing untagged handler-only `callGoal`. The complete
`branchMotive` uses lexicographic clock/size induction to supply both original
Call hypotheses to the exact tagged wrapper internally. Its callee clock is
strictly decremented; its matching handler clock is bounded by the callee
poststate clock. The public theorem has no additional induction hypothesis.

The untagged equations `callGuard_args_eq`, `callGuard_lookup_eq` and
`callGuard_nodup_iff` in `EvaluateLocals/Assembly.lean` relate the normalized
argument, lookup and nodup guards to the literal faithful `evaluate_ind` guards.
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

/-- Local support: the While motive for every state, by clock induction. -/
private theorem whileBranchMotive {width : Nat} [NeZero width] {σ : Type}
    (e : CrepExpHOL width) (c : CrepProgHOL width)
    (ihc : ∀ u : CrepSemHOLState width σ, transformBranchGoal c u) :
    ∀ s : CrepSemHOLState width σ, transformBranchGoal (.while e c) s := by
  have step : ∀ s : CrepSemHOLState width σ,
      (∀ s1 : CrepSemHOLState width σ, s1.clock < s.clock → transformBranchGoal (.while e c) s1) →
      transformBranchGoal (.while e c) s := by
    intro s ih
    have hlt : ∀ res s1, s.clock ≠ 0 →
        (res, s1) = evalCrepSemHOLProgExact (decClockCrepSemHOL s) c → s1.clock < s.clock := by
      intro res s1 hck heq
      have hle := evalCrepSemHOLProgExact_clock_le (decClockCrepSemHOL s) c
      rw [← heq] at hle
      simp only [decClockCrepSemHOL_clock'] at hle
      omega
    exact transformBranchCorrect_While e c s
      { continueCase := fun _ _ res s1 _ _ _ _ _ hck heq _ _ _ => ih s1 (hlt res s1 hck heq)
        normalCase := fun _ _ res s1 _ _ _ hck heq _ => ih s1 (hlt res s1 hck heq)
        bodyCase := fun _ _ _ _ _ _ => ihc _ }
  have main : ∀ (n : Nat) (s : CrepSemHOLState width σ), s.clock ≤ n →
      transformBranchGoal (.while e c) s := by
    intro n
    induction n with
    | zero => intro s hs; exact step s (fun s1 h1 => absurd h1 (by omega))
    | succ k ih => intro s hs; exact step s (fun s1 h1 => ih s1 (by omega))
  exact fun s => main s.clock s (Nat.le_refl _)

/-- Local support: the `evaluate_ind` motive of `transform_branch_correct` for
    every program and state. -/
private theorem handlerOnlyBranchMotive {width : Nat} [NeZero width] {σ : Type} :
    ∀ (p : CrepProgHOL width) (s : CrepSemHOLState width σ), transformBranchGoal p s
  | .skip, s => transformBranchCorrect_Leaf _ s (Or.inl rfl)
  | .assign n e, s => transformBranchCorrect_Leaf _ s (Or.inr (Or.inl ⟨n, e, rfl⟩))
  | .primitive ns op args, s =>
      transformBranchCorrect_Leaf _ s (Or.inr (Or.inr (Or.inl ⟨ns, op, args, rfl⟩)))
  | .store a b, s => transformBranchCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, rfl⟩))))
  | .store32 a b, s =>
      transformBranchCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, rfl⟩)))))
  | .storeByte a b, s =>
      transformBranchCorrect_Leaf _ s
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, rfl⟩))))))
  | .storeGlob a b, s =>
      transformBranchCorrect_Leaf _ s
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, rfl⟩)))))))
  | .break n, s =>
      transformBranchCorrect_Leaf _ s
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))))))))
  | .continue n, s =>
      transformBranchCorrect_Leaf _ s
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)))))))))
  | .raise e, s =>
      transformBranchCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl ⟨e, rfl⟩))))))))))
  | .tick, s =>
      transformBranchCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))
  | .extCall f a b c d, s =>
      transformBranchCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, a, b, c, d, rfl⟩))))))))))))
  | .shMem op n a, s =>
      transformBranchCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨op, n, a, rfl⟩))))))))))))
  | .return es, s => transformBranchCorrect_Return es s
  | .dec v e body, s => transformBranchCorrect_Dec v e body s (fun _ _ => handlerOnlyBranchMotive body _)
  | .ite c a b, s => transformBranchCorrect_If c a b s (fun _ w _ _ => by
      by_cases hw : w ≠ 0
      · rw [if_pos hw]; exact handlerOnlyBranchMotive a s
      · rw [if_neg hw]; exact handlerOnlyBranchMotive b s)
  | .seq a b, s => transformBranchCorrect_Seq a b s (fun _ s1 _ _ => handlerOnlyBranchMotive b s1) (handlerOnlyBranchMotive a s)
  | .while e c, s => whileBranchMotive e c (fun u => handlerOnlyBranchMotive c u) s
  | .call none f args, s =>
      callGoal none f args s (fun _ _ _ _ _ _ _ _ _ _ _ _ hinfo => by cases hinfo)
  | .call (some (names, none)) f args, s =>
      callGoal _ f args s (fun _ _ _ _ _ _ _ _ _ _ _ _ hinfo => by simp at hinfo)
  | .call (some (names, some (eid, handler))) f args, s =>
      callGoal _ f args s (fun _ _ _ _ _ handler' st _ _ _ _ _ hinfo => by
        simp only [Option.some.injEq, Prod.mk.injEq] at hinfo
        obtain ⟨_, _, rfl⟩ := hinfo
        exact handlerOnlyBranchMotive handler _)
termination_by p => sizeOf p

/-- Complete motive with both exact Call induction premises supplied internally.
Non-Call constructors reuse the independent structural calculation above. -/
private theorem branchMotive {width : Nat} [NeZero width] {σ : Type} :
    ∀ (p : CrepProgHOL width) (s : CrepSemHOLState width σ), transformBranchGoal p s := by
  refine evalCrepSemHOLProgExact_inductLex (motive := transformBranchGoal) ?_
  intro p s ih
  have lower : ∀ (q : CrepProgHOL width) (u : CrepSemHOLState width σ),
      u.clock < s.clock → transformBranchGoal q u :=
    fun q u hc => ih q u (Prod.Lex.left _ _ hc)
  have dec_lt : s.clock ≠ 0 → (decClockCrepSemHOL s).clock < s.clock := by
    intro h; simp only [decClockCrepSemHOL_clock']; omega
  cases p with
  | call info fname args =>
      exact transformBranchCorrect_Call info fname args s
        (fun _ _ newlocals _ _ _ hck =>
          lower _ {decClockCrepSemHOL s with locals := newlocals} (dec_lt hck))
        (fun _ prog newlocals _ _ _ st _ _ _ hck hb _ => by
          have hle := evalCrepSemHOLProgExact_clock_le
            {decClockCrepSemHOL s with locals := newlocals} prog
          rw [hb] at hle
          exact lower _ {st with locals := s.locals} (Nat.lt_of_le_of_lt hle (dec_lt hck)))
  | _ => exact handlerOnlyBranchMotive _ s

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
