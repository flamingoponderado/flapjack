import Flapjack.HolRef
import Flapjack.Pancake.Proofs.CrepInline.CallNontail

/-!
# `inline_prog_correct`: the tagged `Call` case

`Resume inline_prog_correct[Call]` with its `Tail` and `Nontail` suspensions
(`cakeml/pancake/proofs/crep_inlineProofScript.sml:2409-3037`, bead
`flapjack-pxn.18.5.5.42.4`).  The case takes exactly the two `evaluate_ind`
Call premises for the theorem predicate, the handler premise `ihExc` and the
callee-body premise `ihBody`, in the spelling of the reviewed `callNonInlined`
with the predicate written out.  The proof splits on HOL's own case analysis
of `inline_prog` (`crep_inlineScript.sml:204-237`): calls left as calls
(`callNonInlined`), inlined tail calls (`callTail`) and inlined assign calls
(`callNontail`).
-/

namespace Flapjack

namespace CrepInlineCallCase

namespace CallCaseSupport
/-- Canonical carrier roundtrip re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end CallCaseSupport

open CrepInlineCanonical CrepInlineExact

/-- `Call` case of HOL `inline_prog_correct` (`crep_inlineProofScript.sml:2301-2319`,
    case `:2409-3037`) for every call shape, with exactly `evaluate_ind`'s two
    guarded Call premises at the theorem predicate. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "inline_prog_correct"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals,
      CrepSemHOLState.code, inlFs, inlBag])
  (words_as_type_indexed_bitvec)]
theorem inlineProgCorrectCallCaseExact {width : Nat} [NeZero width] {σ : Type}
    (caltyp : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fname : Flapjack.Basis.Pure.MlString.MlString) (argexps : List (CrepExpHOL width))
    (s : CrepSemHOLState width σ)
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (inlFs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (inlBag : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (t : CrepSemHOLState width σ)
    (hsource : evalCrepSemHOLProgExact s (.call caltyp fname argexps) = (r, s'))
    (hnotError : r ≠ some .error)
    (hsubmap : HolFiniteMapExact.submap inlFs s.code)
    (hbag : HolFiniteMapExact.submap inlBag inlFs)
    (hstate : crepInlineStateRelCodeExact s t)
    (hlocals : crepInlineLocalsStrongRelExact s t)
    (hcode : crepInlineCodeInlRelExact inlFs s t)
    (ihExc : ∀ (args : List (HolWordLab width))
        (v6 : CrepProgHOL width × HolFiniteMapExact Nat (HolWordLab width))
        (prog : CrepProgHOL width) (newlocals : HolFiniteMapExact Nat (HolWordLab width))
        eval_prog v4 st v7 eid v v1 v2 v3 eid' p,
      argexps.mapM (crepExactEvalExpClassical s) = some args →
      lookupCodeHOLFinite s.code.lookup fname args (List.length args) = some v6 →
      v6 = (prog, newlocals) →
      (¬ (match (generalizing := false) caltyp with
          | none => False
          | some (rts, _) => ¬ rts.Nodup)) →
      s.clock ≠ 0 →
      eval_prog = evalCrepSemHOLProgExact { decClockCrepSemHOL s with locals := newlocals } prog →
      eval_prog = (v4, st) →
      v4 = some v7 → v7 = .exception eid →
      caltyp = some v → v = (v1, v2) → v2 = some v3 → v3 = (eid', p) →
      eid = eid' →
      ∀ (result : Option (CrepResultHOLExact width))
        (source' : CrepSemHOLState width σ)
        (inlFs' : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
        (target : CrepSemHOLState width σ)
        (inlBag' : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width)),
        evalCrepSemHOLProgExact ({ st with locals := s.locals }) p = (result, source') →
        result ≠ some .error →
        HolFiniteMapExact.submap inlFs' ({ st with locals := s.locals }).code →
        HolFiniteMapExact.submap inlBag' inlFs' →
        crepInlineStateRelCodeExact ({ st with locals := s.locals }) target →
        crepInlineLocalsStrongRelExact ({ st with locals := s.locals }) target →
        crepInlineCodeInlRelExact inlFs' ({ st with locals := s.locals }) target →
        ∃ target' : CrepSemHOLState width σ,
          evalCrepSemHOLProgExact target (CrepInlineCanonical.inlineProgHOLExact inlBag' p) =
            (result, target') ∧
          crepInlineStateRelCodeExact source' target' ∧
          crepInlineCodeInlRelExact inlFs' source' target' ∧
          match result with
          | none => crepInlineLocalsStrongRelExact source' target'
          | some (CrepResultHOLExact.break _) => crepInlineLocalsStrongRelExact source' target'
          | some (CrepResultHOLExact.continue _) => crepInlineLocalsStrongRelExact source' target'
          | some .error => False
          | _ => True)
    (ihBody : ∀ (args : List (HolWordLab width))
        (v6 : CrepProgHOL width × HolFiniteMapExact Nat (HolWordLab width))
        (prog : CrepProgHOL width) (newlocals : HolFiniteMapExact Nat (HolWordLab width)),
      argexps.mapM (crepExactEvalExpClassical s) = some args →
      lookupCodeHOLFinite s.code.lookup fname args (List.length args) = some v6 →
      v6 = (prog, newlocals) →
      (¬ (match (generalizing := false) caltyp with
          | none => False
          | some (rts, _) => ¬ rts.Nodup)) →
      s.clock ≠ 0 →
      ∀ (result : Option (CrepResultHOLExact width))
        (source' : CrepSemHOLState width σ)
        (inlFs' : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
        (target : CrepSemHOLState width σ)
        (inlBag' : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width)),
        evalCrepSemHOLProgExact ({ decClockCrepSemHOL s with locals := newlocals }) prog = (result, source') →
        result ≠ some .error →
        HolFiniteMapExact.submap inlFs' ({ decClockCrepSemHOL s with locals := newlocals }).code →
        HolFiniteMapExact.submap inlBag' inlFs' →
        crepInlineStateRelCodeExact ({ decClockCrepSemHOL s with locals := newlocals }) target →
        crepInlineLocalsStrongRelExact ({ decClockCrepSemHOL s with locals := newlocals }) target →
        crepInlineCodeInlRelExact inlFs' ({ decClockCrepSemHOL s with locals := newlocals }) target →
        ∃ target' : CrepSemHOLState width σ,
          evalCrepSemHOLProgExact target (CrepInlineCanonical.inlineProgHOLExact inlBag' prog) =
            (result, target') ∧
          crepInlineStateRelCodeExact source' target' ∧
          crepInlineCodeInlRelExact inlFs' source' target' ∧
          match result with
          | none => crepInlineLocalsStrongRelExact source' target'
          | some (CrepResultHOLExact.break _) => crepInlineLocalsStrongRelExact source' target'
          | some (CrepResultHOLExact.continue _) => crepInlineLocalsStrongRelExact source' target'
          | some .error => False
          | _ => True) :
    ∃ t' : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact t (CrepInlineCanonical.inlineProgHOLExact inlBag
          (.call caltyp fname argexps)) = (r, t') ∧
      crepInlineStateRelCodeExact s' t' ∧
      crepInlineCodeInlRelExact inlFs s' t' ∧
      match r with
      | none => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.break _) => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.continue _) => crepInlineLocalsStrongRelExact s' t'
      | some .error => False
      | _ => True := by
  by_cases hpath : inlinedPath inlBag caltyp fname
  · obtain ⟨hsome, hcal⟩ := hpath
    rcases hlk : inlBag.lookup fname with _ | ⟨ns, body⟩
    · rw [hlk] at hsome; cases hsome
    rcases hcal with rfl | ⟨rts, rfl, hd⟩
    · exact callTail fname argexps s ihBody r s' inlFs t inlBag ns body hlk hsource hnotError
        hsubmap hbag hstate hlocals hcode
    · have hnd : rts.Nodup := crepAllDistinct_nodup rts hd
      exact callNontail fname argexps rts s
        (fun args v6 prog nl h1 h2 h3 _ h5 => ihBody args v6 prog nl h1 h2 h3 (by simp [hnd]) h5)
        r s' inlFs t inlBag ns body hd hlk hsource hnotError hsubmap hbag hstate hlocals hcode
  · refine callNonInlined caltyp fname argexps s
      (fun args v6 prog nl ev v4 st v7 eid v v1 v2 v3 eid' p h1 h2 h3 hg h5 =>
        ihExc args v6 prog nl ev v4 st v7 eid v v1 v2 v3 eid' p h1 h2 h3
          (by rcases caltyp with _ | ⟨rts, _⟩ <;> exact hg) h5)
      (fun args v6 prog nl h1 h2 h3 hg h5 =>
        ihBody args v6 prog nl h1 h2 h3 (by rcases caltyp with _ | ⟨rts, _⟩ <;> exact hg) h5)
      r s' inlFs t inlBag hpath hsource hnotError hsubmap hbag hstate hlocals hcode

end CrepInlineCallCase

end Flapjack
