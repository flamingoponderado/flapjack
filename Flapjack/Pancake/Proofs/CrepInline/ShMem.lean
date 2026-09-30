import Flapjack.Pancake.Proofs.CrepInline

namespace Flapjack.CrepInlineExact
namespace ShMemSupport

/-- Flapjack-specific same-module canonical state carrier witness re-export. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

/-- Flapjack-specific code-field preservation for the exact shared load.
No separate HOL declaration is claimed; this discharges the case proof's
post-state code relation from the reviewed transition definition. -/
theorem load_code {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (addr : BitVec width) (nb : Nat) (s : CrepSemHOLState width σ) :
    (@crepShMemLoadExactHOL width _ σ name addr nb s
      (fun a => Classical.propDecidable (s.shMemaddrs a))).2.code = s.code := by
  classical
  simp only [crepShMemLoadExactHOL]
  split <;> (try split) <;> (try split) <;> rfl

/-- Flapjack-specific code-field preservation, including store errors/final FFI. -/
theorem store_code {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (addr : BitVec width) (nb : Nat) (s : CrepSemHOLState width σ) :
    (@crepShMemStoreExactHOL width _ σ name addr nb s
      (fun a => Classical.propDecidable (s.shMemaddrs a))).2.code = s.code := by
  classical
  simp only [crepShMemStoreExactHOL]
  split <;> (try split) <;> (try split) <;> (try split) <;> rfl

/-- Flapjack-specific dispatch of code-field preservation for all eight operators. -/
theorem op_code {width : Nat} [NeZero width] {σ : Type}
    (op : WordMemOp) (name : Nat) (addr : BitVec width) (s : CrepSemHOLState width σ) :
    (@crepShMemOpExactHOL width _ σ op name addr s
      (fun a => Classical.propDecidable (s.shMemaddrs a))).2.code = s.code := by
  cases op <;> simp only [crepShMemOpExactHOL] <;>
    first | exact load_code _ _ _ _ | exact store_code _ _ _ _

end ShMemSupport

/-- The complete nonrecursive ShMem case of HOL inline_prog_correct (:2405-2406).
The theorem retains the original seven premises and existential target result,
including post-state code relation and result-dependent locals relation. Exact
shared-memory helpers cover all widths, domain errors, returned/final FFI states.
No helper simulation or successful target evaluation is assumed. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "inline_prog_correct"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals,
      CrepSemHOLState.code, inlFs, inlBag])
  (words_as_type_indexed_bitvec)]
theorem inlineProgCorrectShMemCaseExact {width : Nat} [NeZero width] {σ : Type}
    (operator : WordMemOp) (name : Nat) (address : CrepExpHOL width)
    (s : CrepSemHOLState width σ)
    (inlFs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (inlBag : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (t : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width))
    (s' : CrepSemHOLState width σ)
    (hsource : evalCrepSemHOLProgExact s (.shMem operator name address) = (r,s'))
    (hnotError : r ≠ some .error)
    (_hsubmap : HolFiniteMapExact.submap inlFs s.code)
    (_hbag : HolFiniteMapExact.submap inlBag inlFs)
    (hstate : crepInlineStateRelCodeExact s t)
    (hlocals : crepInlineLocalsStrongRelExact s t)
    (hcode : crepInlineCodeInlRelExact inlFs s t) :
    ∃ t' : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact t
        (CrepInlineCanonical.inlineProgHOLExact inlBag (.shMem operator name address)) = (r,t') ∧
      crepInlineStateRelCodeExact s' t' ∧
      crepInlineCodeInlRelExact inlFs s' t' ∧
      match (generalizing := false) r with
      | none => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.break _) => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.continue _) => crepInlineLocalsStrongRelExact s' t'
      | some .error => False
      | _ => True := by
  classical
  have hinline : CrepInlineCanonical.inlineProgHOLExact inlBag (.shMem operator name address) =
      .shMem operator name address := by
    unfold CrepInlineCanonical.inlineProgHOLExact
    simp only [CrepInlineCanonical.inlineProgHOLCoreExact]
  have hlocalEq : s.locals = t.locals := hlocals
  have finish (addr : BitVec width)
      (hsop : crepShMemOpExactHOL operator name addr s = (r,s'))
      (htop : evalCrepSemHOLProgExact t (.shMem operator name address) =
        crepShMemOpExactHOL operator name addr t) :
      ∃ t' : CrepSemHOLState width σ,
        evalCrepSemHOLProgExact t
          (CrepInlineCanonical.inlineProgHOLExact inlBag (.shMem operator name address)) = (r,t') ∧
        crepInlineStateRelCodeExact s' t' ∧ crepInlineCodeInlRelExact inlFs s' t' ∧
        match (generalizing := false) r with
        | none => crepInlineLocalsStrongRelExact s' t'
        | some (CrepResultHOLExact.break _) => crepInlineLocalsStrongRelExact s' t'
        | some (CrepResultHOLExact.continue _) => crepInlineLocalsStrongRelExact s' t'
        | some .error => False
        | _ => True := by
    obtain ⟨hresult, hpost⟩ := crepShMemOpExactHOL_same operator name addr s t ⟨hstate,hlocals⟩
    have hsfirst : (crepShMemOpExactHOL operator name addr s).1 = r := congrArg Prod.fst hsop
    have hssecond : (crepShMemOpExactHOL operator name addr s).2 = s' := congrArg Prod.snd hsop
    rw [hssecond] at hpost
    have hsc : s'.code = s.code := by
      rw [← hssecond]
      exact ShMemSupport.op_code _ _ _ _
    have htc := ShMemSupport.op_code operator name addr t
    refine ⟨(crepShMemOpExactHOL operator name addr t).2, ?_, hpost.1, ?_, ?_⟩
    · rw [hinline,htop]
      exact Prod.ext (hresult.symm.trans hsfirst) rfl
    · simpa only [crepInlineCodeInlRelExact,hsc,htc] using hcode
    · have hp : crepInlineLocalsStrongRelExact s' (crepShMemOpExactHOL operator name addr t).2 := hpost.2
      split <;> first | exact hp | trivial | contradiction
  rw [evalCrepSemHOLProgExact_shMem_holShape] at hsource
  cases heval : evalCrepSemHOLExp s address with
  | none =>
      simp only [heval] at hsource
      exact False.elim (hnotError (congrArg Prod.fst hsource).symm)
  | some value =>
      cases value with
      | word addr =>
          have htarget := evalCodeInlExact s address (.word addr) t inlFs ⟨heval,hstate,hlocals,hcode⟩
          cases hop : crepIsLoadMemOp operator with
          | true =>
              cases hlookup : s.locals.lookup name with
              | none =>
                  simp only [heval,hop,if_true,hlookup] at hsource
                  exact False.elim (hnotError (congrArg Prod.fst hsource).symm)
              | some localValue =>
                  simp only [heval,hop,if_true,hlookup] at hsource
                  apply finish addr hsource
                  rw [evalCrepSemHOLProgExact_shMem_holShape,htarget,hop]
                  simp only [if_true,← hlocalEq,hlookup]
          | false =>
              cases hlookup : s.locals.lookup name with
              | none =>
                  simp only [heval,hop,Bool.false_eq_true,if_false,hlookup] at hsource
                  exact False.elim (hnotError (congrArg Prod.fst hsource).symm)
              | some localValue =>
                  cases localValue with
                  | word localWord =>
                      simp only [heval,hop,Bool.false_eq_true,if_false,hlookup] at hsource
                      apply finish addr hsource
                      rw [evalCrepSemHOLProgExact_shMem_holShape,htarget,hop]
                      simp only [Bool.false_eq_true,if_false,← hlocalEq,hlookup]

end Flapjack.CrepInlineExact
