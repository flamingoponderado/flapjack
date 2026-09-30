import Flapjack.Pancake.Proofs.CrepInline.TransformEoc.While
import Flapjack.Pancake.Proofs.CrepInline.TransformEoc.Call

/-!
# crep_inline: assembled `transform_eoc_correct`

Assembly of HOL `transform_eoc_correct` (`cakeml/pancake/proofs/crep_inlineProofScript.sml:1893-2038`)
from its tagged constructor cases (bead `flapjack-pxn.18.5.5.47.2.4`).  As for
the accepted `evaluate_locals_same_fdom` assembly, the `evaluate_ind` motive is
established by clock/program-size lexicographic induction, with arbitrary
code-map callee bodies reached at a strictly smaller clock. All guarded Call
and While premises are discharged internally. No public induction hypothesis remains.

See `EvaluateLocals/Assembly.lean` ("Induction principle and guard spellings")
for the equivalent well-founded induction underlying this assembly, and for the equations (`callGuard_args_eq`,
`callGuard_lookup_eq`, `callGuard_nodup_iff`) relating the Call handler
premise's guards to `evaluate_ind`'s.
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

/-- Internal well-founded assembly: the exact evaluator's clock/program-size
lexicographic induction discharges callee and handler premises, including
calls into arbitrary code-map bodies. No public IH is assumed. -/
private theorem eocMotive {width : Nat} [NeZero width] {σ : Type} :
    ∀ (p : CrepProgHOL width) (s : CrepSemHOLState width σ), transformEocGoal p s := by
  refine evalCrepSemHOLProgExact_inductLex (motive := transformEocGoal) ?_
  intro p s ih
  have lower : ∀ (p' : CrepProgHOL width) (s' : CrepSemHOLState width σ),
      s'.clock < s.clock → transformEocGoal p' s' :=
    fun p' s' hc => ih p' s' (Prod.Lex.left _ _ hc)
  have same : ∀ (p' : CrepProgHOL width) (s' : CrepSemHOLState width σ),
      s'.clock = s.clock → sizeOf p' < sizeOf p → transformEocGoal p' s' :=
    fun p' s' hc hs => ih p' s' (by rw [hc]; exact Prod.Lex.right _ hs)
  have dec_lt : s.clock ≠ 0 → (decClockCrepSemHOL s).clock < s.clock := by
    intro h; simp only [decClockCrepSemHOL_clock']; omega
  cases p with
  | skip => exact transformEocCorrect_Leaf _ s (Or.inl rfl)
  | assign n e => exact transformEocCorrect_Leaf _ s (Or.inr (Or.inl ⟨n, e, rfl⟩))
  | primitive ns op args =>
      exact transformEocCorrect_Leaf _ s (Or.inr (Or.inr (Or.inl ⟨ns, op, args, rfl⟩)))
  | store a b => exact transformEocCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, rfl⟩))))
  | store32 a b =>
      exact transformEocCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, rfl⟩)))))
  | storeByte a b =>
      exact transformEocCorrect_Leaf _ s
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, rfl⟩))))))
  | storeGlob a b =>
      exact transformEocCorrect_Leaf _ s
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, rfl⟩)))))))
  | «break» n =>
      exact transformEocCorrect_Leaf _ s
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))))))))
  | «continue» n =>
      exact transformEocCorrect_Leaf _ s
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)))))))))
  | raise e =>
      exact transformEocCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl ⟨e, rfl⟩))))))))))
  | tick =>
      exact transformEocCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))
  | extCall f a b c d =>
      exact transformEocCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, a, b, c, d, rfl⟩))))))))))))
  | shMem op n a =>
      exact transformEocCorrect_Leaf _ s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨op, n, a, rfl⟩))))))))))))
  | «return» es => exact transformEocCorrect_Return es s
  | dec v e body =>
      exact transformEocCorrect_Dec v e body s
        (fun _ _ => same _ _ rfl (by simp only [CrepProgHOL.dec.sizeOf_spec]; omega))
  | ite c a b =>
      refine transformEocCorrect_If c a b s (fun _ w _ _ => ?_)
      by_cases hw : w ≠ 0
      · rw [if_pos hw]; exact same _ _ rfl (by simp only [CrepProgHOL.ite.sizeOf_spec]; omega)
      · rw [if_neg hw]; exact same _ _ rfl (by simp only [CrepProgHOL.ite.sizeOf_spec]; omega)
  | seq a b =>
      refine transformEocCorrect_Seq a b s (fun res s1 hs1 _ => ?_)
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
      exact transformEocCorrect_While e c s
        { continueCase := fun _ _ res s1 _ _ _ _ _ hck heq _ _ _ => lower _ s1 (hlt res s1 hck heq)
          normalCase := fun _ _ res s1 _ _ _ hck heq _ => lower _ s1 (hlt res s1 hck heq)
          bodyCase := fun _ _ _ _ _ hck => lower _ _ (dec_lt hck) }
  | call info f args =>
      exact transformEocCorrect_Call info f args s
        (fun _ _ newlocals _ _ _ hck => lower _ { decClockCrepSemHOL s with locals := newlocals }
          (dec_lt hck))
        (fun _ prog newlocals _ _ _ st _ _ _ hck hb _ => by
          have hle := evalCrepSemHOLProgExact_clock_le
            { decClockCrepSemHOL s with locals := newlocals } prog
          rw [hb] at hle
          exact lower _ { st with locals := s.locals } (Nat.lt_of_le_of_lt hle (dec_lt hck)))

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
