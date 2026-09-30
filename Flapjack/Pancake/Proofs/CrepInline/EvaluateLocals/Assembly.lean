import Flapjack.Pancake.Proofs.CrepInline.EvaluateLocals.While
import Flapjack.Pancake.Proofs.CrepInline.EvaluateLocals.Call
import Flapjack.Pancake.Proofs.CrepInline.EvaluateLocals.ExtCall
import Flapjack.Pancake.Proofs.CrepInline.EvaluateLocals.Primitive
import Flapjack.Pancake.Proofs.CrepInline.EvaluateLocals.ShMem

/-!
# crep_inline: assembled `evaluate_locals_same_fdom`

Assembly of HOL `evaluate_locals_same_fdom` (`cakeml/pancake/proofs/crep_inlineProofScript.sml:181-260`)
from its reviewed constructor cases, and the corollary
`evaluate_locals_same_fdom'` (`:262-270`); bead `flapjack-pxn.18.5.5.43.7`.
HOL proves the theorem by `recInduct evaluate_ind`.  Here the motive
`localsDomainMotive p s` is established for every state by structural recursion
on the program; the `While` case adds an inner induction on the clock, whose
recursive premises are exactly the guarded `WhileDomainIH` of `evaluate_ind`.
`FDOM` is rendered by `crepHolFdom` of the finite-support lookup, as in the
case theorems.

## Induction principle and guard spellings (review item 4, PR #1182)

The crep_inline assemblies in this directory (`evaluate_locals_same_fdom`
here, `transform_eoc_correct` in `TransformEoc/Assembly.lean` and
`transform_branch_correct` in `TransformBranch/Assembly.lean`) do not apply the
tagged Crep `evaluate_ind` (`evalCrepSemHOLProgExact_induct`,
`Semantics/CrepSem/EvaluateInd.lean`).  Each proves its motive for every
program and state by structural recursion on the program (a `Call` handler is
a structural subterm of the call), plus, in the `While` case, an inner
induction on `s.clock` using `evalCrepSemHOLProgExact_clock_le`.  Every tagged
case theorem is applied with exactly its own premise, which is `evaluate_ind`'s
premise for that constructor, so the public statements are unchanged: this is
a different proof of the same induction step, not a stronger or weaker
theorem.  None of these cases uses `evaluate_ind`'s callee premise.

The Call handler premises (`ihHandler` here, `TransformEocCallHandlerIH`,
`TransformBranchCallHandlerIH`) state their guards with `args.mapM
(evalCrepSemHOLExp s)`, `lookupCodeFiniteHOL s.code` and
`crepReturnInfoNodupError`, while `evaluate_ind` uses
`args.mapM (crepExactEvalExpClassical s)`, `lookupCodeHOLFinite s.code.lookup`
and the inline `match caltyp` selector.  The three untagged equations below
(`callGuard_args_eq`, `callGuard_lookup_eq`, `callGuard_nodup_iff`) show that
the two spellings are the same propositions.  They are Lean equalities
between Lean definitions; they make no cross-prover claim.
-/

namespace Flapjack.CrepInlineExact

namespace LocalsAssemblySupport
/-- Canonical carrier roundtrip re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end LocalsAssemblySupport

/-- Guard equivalence (review item 4): the argument evaluation of the Call
    handler premises equals `evaluate_ind`'s classical spelling.  Untagged. -/
theorem callGuard_args_eq {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (args : List (CrepExpHOL width)) :
    args.mapM (evalCrepSemHOLExp s) = args.mapM (crepExactEvalExpClassical s) := by
  congr 1
  funext e
  exact (crepExactEvalExpClassical_eq s e).symm

/-- Guard equivalence (review item 4): the finite code lookup of the Call
    handler premises equals `evaluate_ind`'s `lookupCodeHOLFinite`.  Untagged. -/
theorem callGuard_lookup_eq {width : Nat} [NeZero width]
    (c : HolFiniteMapExact Flapjack.Basis.Pure.MlString.MlString (List Nat × CrepProgHOL width))
    (f : Flapjack.Basis.Pure.MlString.MlString) (args : List (HolWordLab width)) (len : Nat) :
    lookupCodeFiniteHOL c f args len = lookupCodeHOLFinite c.lookup f args len := by
  have h1 := lookupCodeFiniteHOL_lookup c f args len
  unfold lookupCodeHOLFinite
  split
  · rename_i hn
    rw [hn] at h1
    cases hF : lookupCodeFiniteHOL c f args len with
    | none => rfl
    | some val => rw [hF] at h1; simp at h1
  · rename_i body cl hs
    rw [hs] at h1
    cases hF : lookupCodeFiniteHOL c f args len with
    | none => rw [hF] at h1; simp at h1
    | some val =>
        obtain ⟨b, m⟩ := val
        rw [hF] at h1
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, hm⟩ := h1
        congr 2
        exact holFiniteMapExact_eq_of_lookup_eq hm

/-- Guard equivalence (review item 4): `crepReturnInfoNodupError` is
    `evaluate_ind`'s inline `ALL_DISTINCT` selector.  Untagged. -/
theorem callGuard_nodup_iff {width : Nat} [NeZero width]
    (info : Option (List Nat × Option (BitVec width × CrepProgHOL width))) :
    crepReturnInfoNodupError info ↔
      (match info with | none => False | some (rts, _) => ¬ rts.Nodup) := Iff.rfl

/-- Local support: the `FDOM` rendering of the atom cases gives the
    `crepHolFdom` rendering. -/
private theorem crepHolFdom_of_FDOM {κ β : Type} {f g : κ → Option β}
    (h : FDOM f = FDOM g) : crepHolFdom f = crepHolFdom g := by
  funext n
  have hn := congrFun h n
  simp only [FDOM] at hn
  unfold crepHolFdom
  cases hf : f n <;> cases hg : g n <;> simp_all

/-- Local support: the `While` case of the motive for every state, by
    induction on the clock, given the motive for the body at every state. -/
private theorem whileMotive {width : Nat} [NeZero width] {σ : Type}
    (e : CrepExpHOL width) (c : CrepProgHOL width)
    (ihc : ∀ u : CrepSemHOLState width σ, localsDomainMotive c u) :
    ∀ s : CrepSemHOLState width σ, localsDomainMotive (.while e c) s := by
  have step : ∀ s : CrepSemHOLState width σ,
      (∀ s1 : CrepSemHOLState width σ, s1.clock < s.clock →
        localsDomainMotive (.while e c) s1) →
      localsDomainMotive (.while e c) s := by
    intro s ih r s' h hc
    have hlt : ∀ res s1, s.clock ≠ 0 →
        (res, s1) = evalCrepSemHOLProgExact (decClockCrepSemHOL s) c → s1.clock < s.clock := by
      intro res s1 hck heq
      have hle := evalCrepSemHOLProgExact_clock_le (decClockCrepSemHOL s) c
      rw [← heq] at hle
      simp only [decClockCrepSemHOL_clock'] at hle
      omega
    exact evaluateLocalsSameFdomWhileExact s s' r e c
      { continueCase := fun _ _ res s1 _ _ _ _ _ hck heq _ _ _ => ih s1 (hlt res s1 hck heq)
        normalCase := fun _ _ res s1 _ _ _ hck heq _ => ih s1 (hlt res s1 hck heq)
        bodyCase := fun _ _ _ _ _ _ => ihc _ }
      h hc
  have main : ∀ (n : Nat) (s : CrepSemHOLState width σ), s.clock ≤ n →
      localsDomainMotive (.while e c) s := by
    intro n
    induction n with
    | zero => intro s hs; exact step s (fun s1 h1 => absurd h1 (by omega))
    | succ k ih => intro s hs; exact step s (fun s1 h1 => ih s1 (by omega))
  exact fun s => main s.clock s (Nat.le_refl _)

-- Local support tactic: convert between the argument orders and dependent
-- forms of the "result is `NONE`/`Break`/`Continue`" condition used by the
-- case theorems, for the result `r`, evaluation `h` and condition `hc` in scope.
set_option hygiene false in
local macro "conv_cond" : tactic =>
  `(tactic| (clear localsMotive; revert hc h; cases r with
      | none => simp
      | some x => cases x <;> simp))

/-- Local support: the `evaluate_ind` motive of `evaluate_locals_same_fdom`
    for every program and state. -/
private theorem localsMotive {width : Nat} [NeZero width] {σ : Type} :
    ∀ (p : CrepProgHOL width) (s : CrepSemHOLState width σ), localsDomainMotive p s
  | .skip, s => fun r s' h hc =>
      crepHolFdom_of_FDOM (evaluateLocalsSameFdomTrivialAtomsExact s r s' _ (Or.inl rfl) h (by conv_cond))
  | .break n, s => fun r s' h hc =>
      crepHolFdom_of_FDOM (evaluateLocalsSameFdomTrivialAtomsExact s r s' _
        (Or.inr (Or.inl ⟨n, rfl⟩)) h (by conv_cond))
  | .continue n, s => fun r s' h hc =>
      crepHolFdom_of_FDOM (evaluateLocalsSameFdomTrivialAtomsExact s r s' _
        (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))) h (by conv_cond))
  | .tick, s => fun r s' h hc =>
      crepHolFdom_of_FDOM (evaluateLocalsSameFdomTrivialAtomsExact s r s' _
        (Or.inr (Or.inr (Or.inr rfl))) h (by conv_cond))
  | .store a b, s => fun r s' h hc =>
      crepHolFdom_of_FDOM (evaluateLocalsSameFdomMemoryGlobalsAtomsExact s r s' _
        (Or.inl ⟨a, b, rfl⟩) h (by conv_cond))
  | .store32 a b, s => fun r s' h hc =>
      crepHolFdom_of_FDOM (evaluateLocalsSameFdomMemoryGlobalsAtomsExact s r s' _
        (Or.inr (Or.inl ⟨a, b, rfl⟩)) h (by conv_cond))
  | .storeByte a b, s => fun r s' h hc =>
      crepHolFdom_of_FDOM (evaluateLocalsSameFdomMemoryGlobalsAtomsExact s r s' _
        (Or.inr (Or.inr (Or.inl ⟨a, b, rfl⟩))) h (by conv_cond))
  | .storeGlob a b, s => fun r s' h hc =>
      crepHolFdom_of_FDOM (evaluateLocalsSameFdomMemoryGlobalsAtomsExact s r s' _
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, rfl⟩)))) h (by conv_cond))
  | .raise e, s => fun r s' h hc =>
      crepHolFdom_of_FDOM (evaluateLocalsSameFdomMemoryGlobalsAtomsExact s r s' _
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨e, rfl⟩)))) h (by conv_cond))
  | .assign n e, s => fun r s' h hc =>
      crepHolFdom_of_FDOM (evaluateLocalsSameFdomAssignCaseExact s r s' _ ⟨n, e, rfl⟩ h (by conv_cond))
  | .primitive names op args, s => fun r s' h hc =>
      evaluateLocalsSameFdomPrimitiveExact s s' r names args op h (by conv_cond)
  | .extCall f a b c d, s => fun r s' h hc =>
      evaluateLocalsSameFdomExtCallExact s s' r f a b c d h (by conv_cond)
  | .shMem op n a, s => fun r s' h hc =>
      evaluateLocalsSameFdomShMemExact s s' r op n a h (by conv_cond)
  | .return values, s => fun r s' h hc => by
      rw [evalCrepSemHOLProgExact_return] at h
      split at h <;> (obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hc.elim)
  | .seq a b, s => fun r s' h hc =>
      evaluateLocalsSameFdomSeqExact s s' r a b
        (fun u t r h hc => localsMotive a u r t h (by conv_cond))
        (fun u t r h hc => localsMotive b u r t h (by conv_cond)) h (by conv_cond)
  | .ite cond a b, s => fun r s' h hc =>
      evaluateLocalsSameFdomIfExact s s' r cond a b
        (fun u t r h hc => localsMotive a u r t h (by conv_cond))
        (fun u t r h hc => localsMotive b u r t h (by conv_cond)) h (by conv_cond)
  | .dec n e body, s => fun r s' h hc =>
      evaluateLocalsSameFdomDecExact s s' r n e body
        (fun u t r h hc => localsMotive body u r t h (by conv_cond)) h (by conv_cond)
  | .while e c, s => whileMotive e c (fun u => localsMotive c u) s
  | .call none f args, s => fun r s' h hc =>
      evaluateLocalsSameFdomCallExact s s' r none f args
        (fun _ _ _ _ _ _ _ _ _ _ _ _ hinfo => by cases hinfo) h (by conv_cond)
  | .call (some (rts, none)) f args, s => fun r s' h hc =>
      evaluateLocalsSameFdomCallExact s s' r (some (rts, none)) f args
        (fun _ _ _ _ _ _ _ _ _ _ _ _ hinfo => by simp at hinfo) h (by conv_cond)
  | .call (some (rts, some (eid, handler))) f args, s => fun r s' h hc =>
      evaluateLocalsSameFdomCallExact s s' r (some (rts, some (eid, handler))) f args
        (fun _ _ _ _ _ handler' st _ _ _ _ _ hinfo => by
          simp only [Option.some.injEq, Prod.mk.injEq] at hinfo
          obtain ⟨_, _, rfl⟩ := hinfo
          exact localsMotive handler _) h (by conv_cond)
termination_by p => sizeOf p

/-- Exact HOL `evaluate_locals_same_fdom` (`crep_inlineProofScript.sml:181-260`),
    assembled from the reviewed constructor cases.  HOL's `(case r of ...) = T`
    is the displayed `match` proposition, and `FDOM` equality is equality of
    `crepHolFdom` on the finite-support lookups. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_locals_same_fdom"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateLocalsSameFdomExact {width : Nat} [NeZero width] {σ : Type} :
    ∀ (p : CrepProgHOL width) (s : CrepSemHOLState width σ)
      (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact s p = (r, s') ∧
        (match (generalizing := false) r with
         | none => True
         | some (.continue _) => True
         | some (.break _) => True
         | _ => False) →
      crepHolFdom s.locals.lookup = crepHolFdom s'.locals.lookup :=
  fun p s r s' ⟨h, hc⟩ => localsMotive p s r s' h hc

/-- Exact HOL `evaluate_locals_same_fdom'` (`crep_inlineProofScript.sml:262-270`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_locals_same_fdom'"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateLocalsSameFdom'Exact {width : Nat} [NeZero width] {σ : Type} :
    ∀ (p : CrepProgHOL width) (s : CrepSemHOLState width σ)
      (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact s p = (r, s') ∧
        (r = none ∨ (∃ n, r = some (.break n)) ∨ (∃ n, r = some (.continue n))) →
      crepHolFdom s.locals.lookup = crepHolFdom s'.locals.lookup := by
  intro p s r s' ⟨h, hr⟩
  refine evaluateLocalsSameFdomExact p s r s' ⟨h, ?_⟩
  rcases hr with rfl | ⟨n, rfl⟩ | ⟨n, rfl⟩ <;> trivial

end Flapjack.CrepInlineExact
