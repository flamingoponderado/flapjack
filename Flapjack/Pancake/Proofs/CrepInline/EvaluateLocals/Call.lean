import Flapjack.Pancake.Proofs.CrepInline.EvaluateLocals.Primitive
import Flapjack.Pancake.Proofs.CrepInline.EvaluateLocals.While

namespace Flapjack.CrepInlineExact

/-- Flapjack-specific mapM infrastructure: a successful list of lookups
means every requested key is in the map domain. No separate HOL port claim. -/
theorem lookupMapMSomeIsSome {α β : Type} (lookup : α → Option β)
    (keys : List α) (values : List β) (h : keys.mapM lookup = some values) :
    ∀ key ∈ keys, (lookup key).isSome = true := by
  induction keys generalizing values with
  | nil => simp
  | cons key keys ih =>
    cases hk : lookup key with
    | none => simp [List.mapM_cons, hk] at h
    | some value =>
      cases ht : keys.mapM lookup with
      | none => simp [List.mapM_cons, hk, ht] at h
      | some tail =>
        intro query hquery
        rcases List.mem_cons.mp hquery with rfl | hmem
        · simp [hk]
        · exact ih tail ht query hmem

/-- Flapjack-specific canonical map update infrastructure used by the HOL
Call return case. All returned destinations are checked by the original
mapM lookup guard; zip updates therefore preserve the caller domain. -/
theorem callReturnUpdateDomain {α β : Type} [DecidableEq α]
    (locals : HolFiniteMapExact α β) (keys : List α) (oldValues retValues : List β)
    (hlookup : keys.mapM locals.lookup = some oldValues) :
    crepHolFdom locals.lookup = crepHolFdom (locals.updateListEq (keys.zip retValues)).lookup := by
  funext key
  apply Eq.symm
  apply updateListEqIsSomeOfPresent
  intro entry hentry
  exact lookupMapMSomeIsSome locals.lookup keys oldValues hlookup entry.1
    (List.of_mem_zip hentry).1

namespace CallLocalsSupport
/-- Flapjack-specific canonical state roundtrip re-export. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end CallLocalsSupport

/-- Call constructor domain case, using only the guarded handler recursion
hypothesis. The callee domain IH is unused because caller locals are restored. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_locals_same_fdom"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateLocalsSameFdomCallExact {width : Nat} [NeZero width] {σ : Type}
    (s s' : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width))
    (info : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fname : Flapjack.Basis.Pure.MlString.MlString) (args : List (CrepExpHOL width))
    (ihHandler : ∀ values prog newlocals rts eid handler st,
      args.mapM (evalCrepSemHOLExp s) = some values →
      lookupCodeFiniteHOL s.code fname values values.length = some (prog,newlocals) →
      ¬ crepReturnInfoNodupError info → s.clock ≠ 0 →
      evalCrepSemHOLProgExact {decClockCrepSemHOL s with locals := newlocals} prog =
        (some (.exception eid),st) →
      info = some (rts,some (eid,handler)) →
      localsDomainMotive handler {st with locals := s.locals})
    (heval : evalCrepSemHOLProgExact s (.call info fname args) = (r,s'))
    (hresult : match (generalizing := false) r with
      | none => True | some (.continue _) => True | some (.break _) => True
      | _ => False) :
    crepHolFdom s.locals.lookup = crepHolFdom s'.locals.lookup := by
  classical
  rw [evalCrepSemHOLProgExact_call_holShape] at heval
  repeat' (first | dsimp at heval | split at heval)
  all_goals try
    solve |
      obtain ⟨hr,ht⟩ := Prod.ext_iff.mp heval
      simp only at hr ht
      subst r
      exact False.elim hresult
  all_goals try
    solve |
      have ht := congrArg Prod.snd heval
      simp only at ht
      subst s'
      apply callReturnUpdateDomain
      assumption
  all_goals try
    solve |
      obtain ⟨hr,ht⟩ := Prod.ext_iff.mp heval
      simp only at hr ht
      subst r
      clear ihHandler
      split at hresult <;> (first | contradiction | (subst_vars; contradiction))
  case h_3.isTrue =>
    rename_i xargs values hargs xcode prog newlocals hcode hc xrun eid st hbody
      xinfo rts eid' handler hn heid
    subst eid'
    exact ihHandler values prog newlocals rts eid handler st hargs hcode hn hc hbody rfl
      r s' heval hresult
  case h_6 =>
    rename_i res st hnone hbreak hcontinue hreturn hexception hbody
    have hr := congrArg Prod.fst heval
    simp only at hr
    subst r
    cases res with
    | none => exact False.elim (hnone rfl)
    | some result =>
      cases result <;> first
        | exact False.elim hresult
        | exact False.elim (hbreak _ rfl)
        | exact False.elim (hcontinue _ rfl)

end Flapjack.CrepInlineExact
