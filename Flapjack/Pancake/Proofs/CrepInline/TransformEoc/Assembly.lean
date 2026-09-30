import Flapjack.Pancake.Proofs.CrepInline.TransformEoc.While
import Flapjack.Pancake.Proofs.CrepInline.TransformEoc.Call

/-!
# crep_inline: assembled `transform_eoc_correct`

Assembly of HOL `transform_eoc_correct` (`cakeml/pancake/proofs/crep_inlineProofScript.sml:1893-2038`)
from its tagged constructor cases (bead `flapjack-pxn.18.5.5.47.2.4`).  As for
the accepted `evaluate_locals_same_fdom` assembly, the `evaluate_ind` motive is
established for every state by structural recursion on the program (the
handler of a call being a structural subterm), with an inner clock induction
supplying exactly the guarded While premises.  No public induction hypothesis
remains.
-/

namespace Flapjack

namespace CrepInlineTransformEoc

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
private theorem whileEocMotive {width : Nat} [NeZero width] {σ : Type}
    (e : CrepExpHOL width) (c : CrepProgHOL width)
    (ihc : ∀ u : CrepSemHOLState width σ, transformEocGoal c u) :
    ∀ s : CrepSemHOLState width σ, transformEocGoal (.while e c) s := by
  have step : ∀ s : CrepSemHOLState width σ,
      (∀ s1 : CrepSemHOLState width σ, s1.clock < s.clock → transformEocGoal (.while e c) s1) →
      transformEocGoal (.while e c) s := by
    intro s ih
    have hlt : ∀ res s1, s.clock ≠ 0 →
        (res, s1) = evalCrepSemHOLProgExact (decClockCrepSemHOL s) c → s1.clock < s.clock := by
      intro res s1 hck heq
      have hle := evalCrepSemHOLProgExact_clock_le (decClockCrepSemHOL s) c
      rw [← heq] at hle
      simp only [decClockCrepSemHOL_clock'] at hle
      omega
    exact transformEocCorrect_While e c s
      { continueCase := fun _ _ res s1 _ _ _ _ _ hck heq _ _ _ => ih s1 (hlt res s1 hck heq)
        normalCase := fun _ _ res s1 _ _ _ hck heq _ => ih s1 (hlt res s1 hck heq)
        bodyCase := fun _ _ _ _ _ _ => ihc _ }
  have main : ∀ (n : Nat) (s : CrepSemHOLState width σ), s.clock ≤ n →
      transformEocGoal (.while e c) s := by
    intro n
    induction n with
    | zero => intro s hs; exact step s (fun s1 h1 => absurd h1 (by omega))
    | succ k ih => intro s hs; exact step s (fun s1 h1 => ih s1 (by omega))
  exact fun s => main s.clock s (Nat.le_refl _)

/-- Local support: the `evaluate_ind` motive of `transform_eoc_correct` for
    every program and state. -/
private theorem eocMotive {width : Nat} [NeZero width] {σ : Type} :
    ∀ (p : CrepProgHOL width) (s : CrepSemHOLState width σ), transformEocGoal p s
  | .skip, s => transformEocCorrect_Leaf _ s (Or.inl rfl)
  | .assign n e, s => transformEocCorrect_Leaf _ s (Or.inr (Or.inl ⟨n, e, rfl⟩))
  | .primitive ns op args, s =>
      transformEocCorrect_Leaf _ s (Or.inr (Or.inr (Or.inl ⟨ns, op, args, rfl⟩)))
  | .store a b, s => transformEocCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, rfl⟩))))
  | .store32 a b, s =>
      transformEocCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, rfl⟩)))))
  | .storeByte a b, s =>
      transformEocCorrect_Leaf _ s
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, rfl⟩))))))
  | .storeGlob a b, s =>
      transformEocCorrect_Leaf _ s
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, rfl⟩)))))))
  | .break n, s =>
      transformEocCorrect_Leaf _ s
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))))))))
  | .continue n, s =>
      transformEocCorrect_Leaf _ s
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)))))))))
  | .raise e, s =>
      transformEocCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl ⟨e, rfl⟩))))))))))
  | .tick, s =>
      transformEocCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))
  | .extCall f a b c d, s =>
      transformEocCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, a, b, c, d, rfl⟩))))))))))))
  | .shMem op n a, s =>
      transformEocCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨op, n, a, rfl⟩))))))))))))
  | .return es, s => transformEocCorrect_Return es s
  | .dec v e body, s => transformEocCorrect_Dec v e body s (fun _ _ => eocMotive body _)
  | .ite c a b, s => transformEocCorrect_If c a b s (fun _ w _ _ => by
      by_cases hw : w ≠ 0
      · rw [if_pos hw]; exact eocMotive a s
      · rw [if_neg hw]; exact eocMotive b s)
  | .seq a b, s => transformEocCorrect_Seq a b s (fun _ s1 _ _ => eocMotive b s1) (eocMotive a s)
  | .while e c, s => whileEocMotive e c (fun u => eocMotive c u) s
  | .call none f args, s =>
      transformEocCorrect_Call none f args s (fun _ _ _ _ _ _ _ _ _ _ _ _ hinfo => by cases hinfo)
  | .call (some (names, none)) f args, s =>
      transformEocCorrect_Call _ f args s (fun _ _ _ _ _ _ _ _ _ _ _ _ hinfo => by simp at hinfo)
  | .call (some (names, some (eid, handler))) f args, s =>
      transformEocCorrect_Call _ f args s (fun _ _ _ _ _ handler' st _ _ _ _ _ hinfo => by
        simp only [Option.some.injEq, Prod.mk.injEq] at hinfo
        obtain ⟨_, _, rfl⟩ := hinfo
        exact eocMotive handler _)
termination_by p => sizeOf p

/-- Exact HOL `transform_eoc_correct` (`crep_inlineProofScript.sml:1893-2038`),
    assembled from the tagged constructor cases with every `evaluate_ind`
    premise discharged internally. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "transform_eoc_correct"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem transformEocCorrect {width : Nat} [NeZero width] {σ : Type} :
    ∀ (p : CrepProgHOL width) (s : CrepSemHOLState width σ)
      (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
      (res : Option CrepEarlyExitHOL) (rts : List Nat),
      evalCrepSemHOLProgExact s p = (r, s') ∧
        unreachElimHOLExact p = (p, res) ∧
        notBranchRetHOLExact p = true ∧
        (∀ retvs, r = some (.return retvs) → rts.length = retvs.length) ∧
        (∀ x, x ∈ rts → x ∉ crepVarProgHOLExact p) ∧
        (∃ z, rts.mapM s.locals.lookup = some z) ∧
        rts.Nodup ∧
        r ≠ some .error →
      ∃ r1 s1', evalCrepSemHOLProgExact s (transformEocHOLExact rts p) = (r1, s1') ∧
        crepInlineStateRelExact s' s1' ∧
        match r with
        | none => r1 = none ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.break n) => r1 = some (.break n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.continue n) => r1 = some (.continue n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.return retvs) => r1 = none ∧ rts.mapM s1'.locals.lookup = some retvs
        | some .error => False
        | _ => r1 = r :=
  fun p s => eocMotive p s

end CrepInlineTransformEoc

end Flapjack
