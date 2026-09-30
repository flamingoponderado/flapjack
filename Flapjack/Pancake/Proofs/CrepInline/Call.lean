import Flapjack.Pancake.Proofs.CrepInline
import Flapjack.Pancake.Semantics.CrepSem.EvaluateInd
import Flapjack.Pancake.Semantics.CrepProps

/-!
# `inline_prog_correct`: the `Call` case

Counterpart of the `Call` case of HOL `inline_prog_correct`
(`cakeml/pancake/proofs/crep_inlineProofScript.sml:2409-3038`, bead
`flapjack-pxn.18.5.5.42`).  HOL splits the case with `suspend`s:
* `Call` proper (`:2409-2534`) covers every call that `inline_prog` leaves as
  a `Call`: non-distinct return names, a callee absent from `inl_bag`, and a
  call with an exception handler.  This is `callNonInlined` below (bead
  `.42.1`).
* `Tail` (`:2536`) and `Nontail` (`:2719`) cover the inlined callee (beads
  `.42.2`/`.42.3`).

`crepInlineGoal` is HOL's theorem predicate at one `(prog, s)` pair.  It is
Flapjack-specific organization and untagged; the tagged Call case states the
goal written out.
-/

namespace Flapjack

namespace CrepInlineCallCase

open CrepInlineCanonical CrepInlineExact

variable {width : Nat} [NeZero width] {σ : Type}

/-- The finite maps `inl_fs`/`inl_bag` of `inline_prog_correct`. -/
abbrev InlMap (width : Nat) [NeZero width] :=
  HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width)

/-- The result-indexed postcondition of HOL `inline_prog_correct`. -/
def resultPost (r : Option (CrepResultHOLExact width)) (s' t' : CrepSemHOLState width σ) :
    Prop :=
  match r with
  | none => crepInlineLocalsStrongRelExact s' t'
  | some (.break _) => crepInlineLocalsStrongRelExact s' t'
  | some (.continue _) => crepInlineLocalsStrongRelExact s' t'
  | some .error => False
  | _ => True

/-- HOL `inline_prog_correct`'s predicate at one `(prog, s)` pair. -/
def crepInlineGoal (p : CrepProgHOL width) (s : CrepSemHOLState width σ) : Prop :=
  ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (inlFs : InlMap width) (t : CrepSemHOLState width σ) (inlBag : InlMap width),
    evalCrepSemHOLProgExact s p = (r, s') → r ≠ some .error →
    HolFiniteMapExact.submap inlFs s.code → HolFiniteMapExact.submap inlBag inlFs →
    crepInlineStateRelCodeExact s t → crepInlineLocalsStrongRelExact s t →
    crepInlineCodeInlRelExact inlFs s t →
    ∃ t' : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact t (inlineProgHOLExact inlBag p) = (r, t') ∧
      crepInlineStateRelCodeExact s' t' ∧ crepInlineCodeInlRelExact inlFs s' t' ∧
      resultPost r s' t'

/-- The calls that `inline_prog` expands: a callee in `inl_bag` called as a
    tail call, or as an assignment to distinct return names without handler. -/
def inlinedPath (inlBag : InlMap width)
    (caltyp : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fname : CrepInlineMapHOLName) : Prop :=
  (inlBag.lookup fname).isSome = true ∧
    (caltyp = none ∨ ∃ rts, caltyp = some (rts, none) ∧ crepAllDistinct rts = true)

/-- `inline_prog` on a call it does not expand: only the handler body is
    inlined. -/
noncomputable def inlineCaltyp (inlBag : InlMap width) :
    Option (List Nat × Option (BitVec width × CrepProgHOL width)) →
      Option (List Nat × Option (BitVec width × CrepProgHOL width))
  | none => none
  | some (rts, none) => some (rts, none)
  | some (rts, some (e, p)) => some (rts, some (e, inlineProgHOLExact inlBag p))

theorem inlineProgHOLExact_call_nonInlined (inlBag : InlMap width)
    (caltyp : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fname : CrepInlineMapHOLName) (args : List (CrepExpHOL width))
    (h : ¬ inlinedPath inlBag caltyp fname) :
    inlineProgHOLExact inlBag (.call caltyp fname args) =
      .call (inlineCaltyp inlBag caltyp) fname args := by
  unfold inlinedPath at h
  unfold inlineProgHOLExact
  rcases caltyp with _ | ⟨rts, _ | ⟨e, p⟩⟩
  · simp only [inlineProgHOLCoreExact, inlineCaltyp]
    split
    · rfl
    · rename_i _ heq
      simp [heq] at h
  · simp only [inlineProgHOLCoreExact, inlineCaltyp]
    by_cases hd : crepAllDistinct rts = true
    · simp only [hd, Bool.not_true, Bool.false_eq_true, if_false]
      split
      · rfl
      · rename_i _ heq
        simp [heq, hd] at h
    · simp [hd]
  · simp only [inlineProgHOLCoreExact, inlineCaltyp]
    rfl

/-- `code_inl_rel` reads only the two code maps. -/
theorem codeInl_of_code_eq {inlFs : InlMap width} {s1 t1 s2 t2 : CrepSemHOLState width σ}
    (hs : s2.code = s1.code) (ht : t2.code = t1.code)
    (h : crepInlineCodeInlRelExact inlFs s1 t1) : crepInlineCodeInlRelExact inlFs s2 t2 := by
  intro fname args prog hlk
  rw [hs] at hlk
  obtain ⟨bag, hsub, hlkT⟩ := h fname args prog hlk
  exact ⟨bag, hsub, by rw [ht]; exact hlkT⟩

theorem nodupError_inlineCaltyp (inlBag : InlMap width)
    (caltyp : Option (List Nat × Option (BitVec width × CrepProgHOL width))) :
    crepReturnInfoNodupError (inlineCaltyp inlBag caltyp) ↔ crepReturnInfoNodupError caltyp := by
  rcases caltyp with _ | ⟨rts, _ | ⟨e, p⟩⟩ <;> rfl

/-- The finite code lookup of the HOL-shaped Call clause and the
    `lookupCodeHOLFinite` wrapper of `evaluate_ind` agree. -/
theorem lookupCodeFiniteHOL_eq_holFinite
    (code : HolFiniteMapExact Flapjack.Basis.Pure.MlString.MlString
      (List Nat × CrepProgHOL width))
    (fname : Flapjack.Basis.Pure.MlString.MlString) (args : List (HolWordLab width)) (len : Nat)
    (prog : CrepProgHOL width) (newlocals : HolFiniteMapExact Nat (HolWordLab width))
    (h : lookupCodeFiniteHOL code fname args len = some (prog, newlocals)) :
    lookupCodeHOLFinite code.lookup fname args len = some (prog, newlocals) := by
  rw [lookupCodeHOLFinite_eq_some_iff, ← lookupCodeFiniteHOL_lookup, h]
  rfl

/-- The paths of HOL `inline_prog_correct`'s `Call` case
    (`crep_inlineProofScript.sml:2409-2534`) where `inline_prog` leaves a
    `Call`: non-distinct return names, a callee outside `inl_bag`, and a
    call with an exception handler.  The two induction hypotheses are the
    `evaluate_ind` `Call` premises with `P := crepInlineGoal`.  Flapjack
    helper of the tagged Call case, which adds the inlined paths. -/
theorem callNonInlined
    (caltyp : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fname : Flapjack.Basis.Pure.MlString.MlString) (argexps : List (CrepExpHOL width))
    (s : CrepSemHOLState width σ)
    (ihExc : ∀ (args : List (HolWordLab width))
        (v6 : CrepProgHOL width × HolFiniteMapExact Nat (HolWordLab width))
        (prog : CrepProgHOL width) (newlocals : HolFiniteMapExact Nat (HolWordLab width))
        eval_prog v4 st v7 eid v v1 v2 v3 eid' p,
      argexps.mapM (crepExactEvalExpClassical s) = some args →
      lookupCodeHOLFinite s.code.lookup fname args (List.length args) = some v6 →
      v6 = (prog, newlocals) →
      (¬ (match caltyp with
          | none => False
          | some (rts, _) => ¬ rts.Nodup)) →
      s.clock ≠ 0 →
      eval_prog = evalCrepSemHOLProgExact { decClockCrepSemHOL s with locals := newlocals } prog →
      eval_prog = (v4, st) →
      v4 = some v7 → v7 = .exception eid →
      caltyp = some v → v = (v1, v2) → v2 = some v3 → v3 = (eid', p) →
      eid = eid' →
      crepInlineGoal p { st with locals := s.locals })
    (ihBody : ∀ (args : List (HolWordLab width))
        (v6 : CrepProgHOL width × HolFiniteMapExact Nat (HolWordLab width))
        (prog : CrepProgHOL width) (newlocals : HolFiniteMapExact Nat (HolWordLab width)),
      argexps.mapM (crepExactEvalExpClassical s) = some args →
      lookupCodeHOLFinite s.code.lookup fname args (List.length args) = some v6 →
      v6 = (prog, newlocals) →
      (¬ (match caltyp with
          | none => False
          | some (rts, _) => ¬ rts.Nodup)) →
      s.clock ≠ 0 →
      crepInlineGoal prog { decClockCrepSemHOL s with locals := newlocals }) :
    ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
      (inlFs : InlMap width) (t : CrepSemHOLState width σ) (inlBag : InlMap width),
      ¬ inlinedPath inlBag caltyp fname →
      evalCrepSemHOLProgExact s (.call caltyp fname argexps) = (r, s') → r ≠ some .error →
      HolFiniteMapExact.submap inlFs s.code → HolFiniteMapExact.submap inlBag inlFs →
      crepInlineStateRelCodeExact s t → crepInlineLocalsStrongRelExact s t →
      crepInlineCodeInlRelExact inlFs s t →
      ∃ t' : CrepSemHOLState width σ,
        evalCrepSemHOLProgExact t (inlineProgHOLExact inlBag (.call caltyp fname argexps)) =
          (r, t') ∧
        crepInlineStateRelCodeExact s' t' ∧ crepInlineCodeInlRelExact inlFs s' t' ∧
        resultPost r s' t' := by
  intro r s' inlFs t inlBag hpath hev hne hsub hbag hsr hls hci
  rw [inlineProgHOLExact_call_nonInlined _ _ _ _ hpath]
  rw [evalCrepSemHOLProgExact_call_holShape] at hev ⊢
  rcases hargs : argexps.mapM (evalCrepSemHOLExp s) with _ | vs
  · simp only [hargs, Prod.mk.injEq] at hev
    exact absurd hev.1.symm hne
  have hargsT := optMmapEvalCodeInlExact s argexps vs t inlFs ⟨hargs, hsr, hls, hci⟩
  simp only [hargs] at hev
  simp only [hargsT]
  rcases hlk : lookupCodeFiniteHOL s.code fname vs vs.length with _ | ⟨prog, newlocals⟩
  · simp only [hlk, Prod.mk.injEq] at hev
    exact absurd hev.1.symm hne
  simp only [hlk] at hev
  have hlk' := hlk
  unfold lookupCodeFiniteHOL at hlk'
  rcases hcs : s.code.lookup fname with _ | ⟨params, body⟩
  · simp [hcs] at hlk'
  simp only [hcs] at hlk'
  have hcond : params.length = vs.length ∧ params.Nodup := by
    by_cases hc : params.length = vs.length ∧ params.Nodup
    · exact hc
    · rw [if_neg hc] at hlk'
      cases hlk'
  rw [if_pos hcond] at hlk'
  simp only [Option.some.injEq, Prod.mk.injEq] at hlk'
  obtain ⟨rfl, rfl⟩ := hlk'
  obtain ⟨bag', hbag', hct⟩ := hci fname params body hcs
  have hlkT : lookupCodeFiniteHOL t.code fname vs vs.length =
      some (inlineProgHOLExact bag' body, HolFiniteMapExact.empty.updateList (params.zip vs)) := by
    unfold lookupCodeFiniteHOL
    rw [hct]
    simp [hcond]
  simp only [hlkT]
  by_cases hnd : crepReturnInfoNodupError caltyp
  · rw [if_pos hnd] at hev
    simp only [Prod.mk.injEq] at hev
    exact absurd hev.1.symm hne
  rw [if_neg hnd] at hev
  rw [if_neg (fun h => hnd ((nodupError_inlineCaltyp inlBag caltyp).mp h))]
  have hclk : s.clock = t.clock := hsr.2.2.2.2.1
  by_cases hz : s.clock = 0
  · rw [if_pos hz] at hev
    rw [if_pos (hclk ▸ hz)]
    simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    exact ⟨t.emptyLocals, rfl, hsr, codeInl_of_code_eq rfl rfl hci, trivial⟩
  rw [if_neg hz] at hev
  rw [if_neg (fun h => hz (hclk ▸ h))]
  have ihB := ihBody vs (body, HolFiniteMapExact.empty.updateList (params.zip vs)) body
    (HolFiniteMapExact.empty.updateList (params.zip vs))
    (by rw [show crepExactEvalExpClassical s = evalCrepSemHOLExp s from
          funext (crepExactEvalExpClassical_eq s)]; exact hargs)
    (lookupCodeFiniteHOL_eq_holFinite _ _ _ _ _ _ hlk) rfl
    (by rcases caltyp with _ | ⟨rts, _⟩ <;> simp_all [crepReturnInfoNodupError]) hz
  rcases hb : evalCrepSemHOLProgExact
      { decClockCrepSemHOL s with locals := HolFiniteMapExact.empty.updateList (params.zip vs) }
      body with ⟨res, st⟩
  rw [hb] at hev
  have hres : res ≠ some .error := by
    intro h
    subst h
    simp only [Prod.mk.injEq] at hev
    exact hne hev.1.symm
  have hsrD : crepInlineStateRelCodeExact
      ({ decClockCrepSemHOL s with locals := HolFiniteMapExact.empty.updateList (params.zip vs) } :
        CrepSemHOLState width σ)
      ({ decClockCrepSemHOL t with locals := HolFiniteMapExact.empty.updateList (params.zip vs) } :
        CrepSemHOLState width σ) := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hsr
    exact ⟨h1, h2, h3, h4, by simp [decClockCrepSemHOL, h5], h6, h7, h8, h9⟩
  obtain ⟨st', hbT, hsr1, hci1, _⟩ := ihB res st inlFs
    { decClockCrepSemHOL t with locals := HolFiniteMapExact.empty.updateList (params.zip vs) }
    bag' hb hres hsub hbag' hsrD rfl (codeInl_of_code_eq rfl rfl hci)
  rw [hbT]
  have hloc : t.locals = s.locals := hls.symm
  rcases res with _ | (_ | _ | l | l | retvs | eid | f)
  · simp only [Prod.mk.injEq] at hev
    exact absurd hev.1.symm hne
  · exact absurd rfl hres
  · simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    exact ⟨st'.emptyLocals, rfl, hsr1, codeInl_of_code_eq rfl rfl hci1, trivial⟩
  · simp only [Prod.mk.injEq] at hev
    exact absurd hev.1.symm hne
  · simp only [Prod.mk.injEq] at hev
    exact absurd hev.1.symm hne
  · rcases caltyp with _ | ⟨rts, h⟩
    · simp only [Prod.mk.injEq] at hev
      obtain ⟨rfl, rfl⟩ := hev
      exact ⟨st'.emptyLocals, by simp [inlineCaltyp], hsr1, codeInl_of_code_eq rfl rfl hci1, trivial⟩
    · have hic : inlineCaltyp inlBag (some (rts, h)) =
          some (rts, match h with
            | none => none
            | some (e, p) => some (e, inlineProgHOLExact inlBag p)) := by
        rcases h with _ | ⟨e, p⟩ <;> rfl
      rw [hic]
      simp only at hev ⊢
      by_cases hlen : retvs.length ≠ rts.length
      · rw [if_pos hlen] at hev
        simp only [Prod.mk.injEq] at hev
        exact absurd hev.1.symm hne
      rw [if_neg hlen] at hev
      rw [if_neg hlen, hloc]
      rcases hm : rts.mapM s.locals.lookup with _ | vals
      · simp only [hm, Prod.mk.injEq] at hev
        exact absurd hev.1.symm hne
      simp only [hm, Prod.mk.injEq] at hev
      obtain ⟨rfl, rfl⟩ := hev
      exact ⟨_, rfl, hsr1, codeInl_of_code_eq rfl rfl hci1, rfl⟩
  · rcases caltyp with _ | ⟨rts, _ | ⟨eid', p⟩⟩
    · simp only [Prod.mk.injEq] at hev
      obtain ⟨rfl, rfl⟩ := hev
      exact ⟨st'.emptyLocals, rfl, hsr1, codeInl_of_code_eq rfl rfl hci1, trivial⟩
    · simp only [Prod.mk.injEq] at hev
      obtain ⟨rfl, rfl⟩ := hev
      exact ⟨st'.emptyLocals, rfl, hsr1, codeInl_of_code_eq rfl rfl hci1, trivial⟩
    · simp only [inlineCaltyp] at hev ⊢
      by_cases heq : eid = eid'
      · rw [if_pos heq] at hev
        rw [if_pos heq]
        have ihH := ihExc vs (body, HolFiniteMapExact.empty.updateList (params.zip vs)) body
          (HolFiniteMapExact.empty.updateList (params.zip vs)) _ (some (.exception eid)) st
          (.exception eid) eid (rts, some (eid', p)) rts (some (eid', p)) (eid', p) eid' p
          (by rw [show crepExactEvalExpClassical s = evalCrepSemHOLExp s from
                funext (crepExactEvalExpClassical_eq s)]; exact hargs)
          (lookupCodeFiniteHOL_eq_holFinite _ _ _ _ _ _ hlk) rfl
          (by simpa [crepReturnInfoNodupError] using hnd) hz rfl hb rfl rfl rfl rfl rfl rfl heq
        have hcodeSt := evaluateCodeInvariantHOL body _ _ st hb
        obtain ⟨t'', hT, hsr2, hci2, hpost2⟩ := ihH r s' inlFs
          { st' with locals := t.locals } inlBag hev hne
          (by show HolFiniteMapExact.submap inlFs st.code; rw [hcodeSt]; exact hsub)
          hbag hsr1 hls (codeInl_of_code_eq rfl rfl hci1)
        exact ⟨t'', hT, hsr2, hci2, hpost2⟩
      · rw [if_neg heq] at hev
        rw [if_neg heq]
        simp only [Prod.mk.injEq] at hev
        obtain ⟨rfl, rfl⟩ := hev
        exact ⟨st'.emptyLocals, rfl, hsr1, codeInl_of_code_eq rfl rfl hci1, trivial⟩
  · simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    exact ⟨st'.emptyLocals, rfl, hsr1, codeInl_of_code_eq rfl rfl hci1, trivial⟩

end CrepInlineCallCase

end Flapjack
