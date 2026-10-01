import Flapjack.HolRef
import Flapjack.Pancake.Proofs.CrepInline.CallCase
import Flapjack.Pancake.Proofs.CrepInline.ShMem

/-!
# crep_inline: assembled `inline_prog_correct`

HOL `inline_prog_correct` (`cakeml/pancake/proofs/crep_inlineProofScript.sml:2301-3037`,
bead `flapjack-pxn.18.5.5.51`), assembled from its 19 tagged constructor cases
(`CrepInline.lean`, `CrepInline/ShMem.lean`, `CrepInline/CallCase.lean`).  As
for the accepted `evaluate_state_locals_rel_strong` assembly, the
`evaluate_ind` predicate is established for every program and state by the
lexicographic (clock, size) induction `evalCrepSemHOLProgExact_inductLex`,
which supplies each case's literal premises, including the Call callee and
handler premises and the While body and loop premises at smaller clocks.  No
public induction hypothesis remains.
-/

namespace Flapjack

namespace CrepInlineCallCase

open CrepInlineCanonical CrepInlineExact

/-- Flapjack induction infrastructure: establish the curried `crepInlineGoal`
for every program and state by lexicographic (clock, size) induction. The public
`inline_prog_correct` below instantiates this predicate with the original
arguments and premises. This helper stays visible because
`CrepInline/StateRelImpSemantics.lean` also supplies it as the non-inlined Call
callee motive. It has no separately named HOL declaration, so it is untagged;
the exact HOL result is recorded on `inline_prog_correct`, while the original
HOL `evaluate_ind` port remains a separate obligation. -/
theorem inlineMotive {width : Nat} [NeZero width] {σ : Type} :
    ∀ (p : CrepProgHOL width) (s : CrepSemHOLState width σ), crepInlineGoal p s := by
  refine evalCrepSemHOLProgExact_inductLex (motive := crepInlineGoal) ?_
  intro p s ih
  have lower : ∀ (p' : CrepProgHOL width) (s' : CrepSemHOLState width σ),
      s'.clock < s.clock → crepInlineGoal p' s' :=
    fun p' s' hc => ih p' s' (Prod.Lex.left _ _ hc)
  have same : ∀ (p' : CrepProgHOL width) (s' : CrepSemHOLState width σ),
      s'.clock = s.clock → sizeOf p' < sizeOf p → crepInlineGoal p' s' :=
    fun p' s' hc hs => ih p' s' (by rw [hc]; exact Prod.Lex.right _ hs)
  have dec_lt : s.clock ≠ 0 → (decClockCrepSemHOL s).clock < s.clock := by
    intro h; simp only [decClockCrepSemHOL_clock']; omega
  intro r s' inlFs t inlBag hev hne hsub hbag hsr hls hci
  unfold resultPost
  cases p with
  | skip =>
      rcases r with _ | ⟨_ | _ | _ | _ | _ | _ | _⟩ <;>
        apply inlineProgCorrectSkipCaseExact <;> assumption
  | tick =>
      rcases r with _ | ⟨_ | _ | _ | _ | _ | _ | _⟩ <;>
        apply inlineProgCorrectTickCaseExact <;> assumption
  | «break» n =>
      rcases r with _ | ⟨_ | _ | _ | _ | _ | _ | _⟩ <;>
        apply inlineProgCorrectBreakCaseExact <;> assumption
  | «continue» n =>
      rcases r with _ | ⟨_ | _ | _ | _ | _ | _ | _⟩ <;>
        apply inlineProgCorrectContinueCaseExact <;> assumption
  | assign n e =>
      rcases r with _ | ⟨_ | _ | _ | _ | _ | _ | _⟩ <;>
        apply inlineProgCorrectAssignCaseExact <;> assumption
  | store a b =>
      rcases r with _ | ⟨_ | _ | _ | _ | _ | _ | _⟩ <;>
        apply inlineProgCorrectStoreCaseExact <;> assumption
  | store32 a b =>
      rcases r with _ | ⟨_ | _ | _ | _ | _ | _ | _⟩ <;>
        apply inlineProgCorrectStore32CaseExact <;> assumption
  | storeByte a b =>
      rcases r with _ | ⟨_ | _ | _ | _ | _ | _ | _⟩ <;>
        apply inlineProgCorrectStoreByteCaseExact <;> assumption
  | storeGlob a b =>
      rcases r with _ | ⟨_ | _ | _ | _ | _ | _ | _⟩ <;>
        apply inlineProgCorrectStoreGlobCaseExact <;> assumption
  | raise e =>
      rcases r with _ | ⟨_ | _ | _ | _ | _ | _ | _⟩ <;>
        apply inlineProgCorrectRaiseCaseExact <;> assumption
  | «return» es =>
      rcases r with _ | ⟨_ | _ | _ | _ | _ | _ | _⟩ <;>
        apply inlineProgCorrectReturnCaseExact <;> assumption
  | primitive ns op args =>
      rcases r with _ | ⟨_ | _ | _ | _ | _ | _ | _⟩ <;>
        apply inlineProgCorrectPrimitiveCaseExact <;> assumption
  | extCall f a b c d =>
      rcases r with _ | ⟨_ | _ | _ | _ | _ | _ | _⟩ <;>
        apply inlineProgCorrectExtCallCaseExact <;> assumption
  | shMem op n a =>
      rcases r with _ | ⟨_ | _ | _ | _ | _ | _ | _⟩ <;>
        apply inlineProgCorrectShMemCaseExact <;> assumption
  | dec v e body =>
      have hsz : sizeOf body < sizeOf (CrepProgHOL.dec v e body) := by
        simp only [CrepProgHOL.dec.sizeOf_spec]; omega
      rcases r with _ | ⟨_ | _ | _ | _ | _ | _ | _⟩ <;>
        apply inlineProgCorrectDecCaseExact <;>
        first | assumption | exact fun vr _ => same _ _ rfl hsz
  | seq a b =>
      have hszA : sizeOf a < sizeOf (CrepProgHOL.seq a b) := by
        simp only [CrepProgHOL.seq.sizeOf_spec]; omega
      have hszB : sizeOf b < sizeOf (CrepProgHOL.seq a b) := by
        simp only [CrepProgHOL.seq.sizeOf_spec]; omega
      have ih2 : ∀ (rF : Option (CrepResultHOLExact width)) (sF : CrepSemHOLState width σ),
          (rF, sF) = evalCrepSemHOLProgExact s a → crepInlineGoal b sF := by
        intro rF sF heq
        have hle := evalCrepSemHOLProgExact_clock_le s a
        rw [← heq] at hle
        rcases Nat.lt_or_eq_of_le hle with hlt | heq'
        · exact lower _ _ hlt
        · exact same _ _ heq' hszB
      rcases r with _ | ⟨_ | _ | _ | _ | _ | _ | _⟩ <;>
        apply inlineProgCorrectSeqCaseExact <;>
        first | assumption | exact same _ _ rfl hszA | exact fun rF sF heq _ => ih2 rF sF heq
  | ite c a b =>
      have hsz : ∀ w : BitVec width,
          sizeOf (if w ≠ 0 then a else b) < sizeOf (CrepProgHOL.ite c a b) := by
        intro w
        by_cases hw : w ≠ 0
        · rw [if_pos hw]; simp only [CrepProgHOL.ite.sizeOf_spec]; omega
        · rw [if_neg hw]; simp only [CrepProgHOL.ite.sizeOf_spec]; omega
      rcases r with _ | ⟨_ | _ | _ | _ | _ | _ | _⟩ <;>
        apply inlineProgCorrectIfCaseExact <;>
        first | assumption | exact fun _ w _ _ => same _ _ rfl (hsz w)
  | «while» e c =>
      have hlt : ∀ res s1, s.clock ≠ 0 →
          evalCrepSemHOLProgExact (decClockCrepSemHOL s) c = (res, s1) → s1.clock < s.clock := by
        intro res s1 hck heq
        have hle := evalCrepSemHOLProgExact_clock_le (decClockCrepSemHOL s) c
        rw [heq] at hle
        exact Nat.lt_of_le_of_lt hle (dec_lt hck)
      rcases r with _ | ⟨_ | _ | _ | _ | _ | _ | _⟩ <;>
        apply inlineProgCorrectWhileCaseExact <;>
        first
          | assumption
          | exact fun _ _ _ hck => lower _ _ (dec_lt hck)
          | exact fun _ _ _ hck ls lr hb _ => lower _ _ (hlt lr ls hck hb)
  | call info f args =>
      rcases r with _ | ⟨_ | _ | _ | _ | _ | _ | _⟩ <;>
        apply inlineProgCorrectCallCaseExact <;>
        first
          | assumption
          | exact fun _ _ _ nl _ _ _ _ hck => lower _ _ (dec_lt hck)
          | exact fun _ _ prog nl ev _ st _ _ _ _ _ _ _ _ _ _ _ _ hck hev1 hev2 _ _ _ _ _ _ _ => by
              have hle := evalCrepSemHOLProgExact_clock_le
                { decClockCrepSemHOL s with locals := nl } prog
              rw [← hev1, hev2] at hle
              exact lower _ _ (Nat.lt_of_le_of_lt hle (dec_lt hck))

namespace InlineProgCorrectSupport
/-- Canonical carrier roundtrip re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end InlineProgCorrectSupport

/-- Exact HOL `inline_prog_correct` (`crep_inlineProofScript.sml:2301-2319`):

    ```
    ∀p s r s' inl_fs s1 inl_bag.
      evaluate (p, s) = (r, s') ∧ r ≠ SOME Error ∧ inl_fs SUBMAP s.code ∧
      inl_bag SUBMAP inl_fs ∧ state_rel_code s s1 ∧ locals_strong_rel s s1 ∧
      code_inl_rel inl_fs s s1 ⇒
      ∃s1'. evaluate (inline_prog inl_bag p, s1) = (r, s1') ∧
        state_rel_code s' s1' ∧ code_inl_rel inl_fs s' s1' ∧
        case r of NONE => locals_strong_rel s' s1' | SOME (Break n) => locals_strong_rel s' s1'
        | SOME (Continue n) => locals_strong_rel s' s1' | SOME Error => F | _ => T
    ```

    assembled from the tagged constructor cases with every `evaluate_ind`
    premise discharged internally. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "inline_prog_correct"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals,
      CrepSemHOLState.code, inlFs, inlBag])
  (words_as_type_indexed_bitvec)]
theorem inlineProgCorrectExact {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (inlFs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (s1 : CrepSemHOLState width σ)
    (inlBag : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width)) :
    evalCrepSemHOLProgExact s p = (r, s') ∧ r ≠ some .error ∧
      HolFiniteMapExact.submap inlFs s.code ∧ HolFiniteMapExact.submap inlBag inlFs ∧
      crepInlineStateRelCodeExact s s1 ∧ crepInlineLocalsStrongRelExact s s1 ∧
      crepInlineCodeInlRelExact inlFs s s1 →
    ∃ s1' : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact s1 (CrepInlineCanonical.inlineProgHOLExact inlBag p) = (r, s1') ∧
      crepInlineStateRelCodeExact s' s1' ∧
      crepInlineCodeInlRelExact inlFs s' s1' ∧
      match r with
      | none => crepInlineLocalsStrongRelExact s' s1'
      | some (CrepResultHOLExact.break _) => crepInlineLocalsStrongRelExact s' s1'
      | some (CrepResultHOLExact.continue _) => crepInlineLocalsStrongRelExact s' s1'
      | some .error => False
      | _ => True :=
  fun ⟨h, hne, hsub, hbag, hsr, hls, hci⟩ =>
    inlineMotive p s r s' inlFs s1 inlBag h hne hsub hbag hsr hls hci

end CrepInlineCallCase

end Flapjack
