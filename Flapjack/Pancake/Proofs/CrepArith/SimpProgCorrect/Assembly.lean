import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect.Assign
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect.Call
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect.Dec
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect.If
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect.Return
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect.Seq
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect.Store
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect.While
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrectPrimitiveRaise
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrectShMem
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrectStore32
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrectStoreByte
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrectStoreGlob
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrectExtCall
import Flapjack.Pancake.Semantics.CrepSem.EvaluateInd

/-!
# Assembly of HOL `crep_arith$simp_prog_correct`

HOL proves `simp_prog_correct` (`crep_arithProofScript.sml:186-212`) by
`ho_match_mp_tac (name_ind_cases [] ind_thm)`, with `ind_thm` the Crep
`evaluate_ind`.  This module wires the tagged per-constructor cases into the
tagged Crep `evaluate_ind` port `evalCrepSemHOLProgExact_induct`, with the
per-program predicate `simpProgCorrectAt`.

`simpProgCorrectOfExtCall` assembles all cases except `ExtCall`, which it
takes as a hypothesis; `crepArithSimpProgCorrect` discharges that hypothesis
with the tagged `simpProgCorrectExtCallCase` and states HOL's
`simp_prog_correct` (bead `flapjack-pxn.18.5.4.26`).
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

namespace SimpProgCorrectAssemblySupport

/-- Same-module canonical finite-support witness for the named state fields
    used by the tagged `simp_prog_correct` theorem below. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end SimpProgCorrectAssemblySupport

/-- The evaluator's `lookupCodeFiniteHOL` and the induction principle's
    `lookupCodeHOLFinite` agree on a finite-support code map. -/
private theorem simpProgLookupCodeFinite_eq_HOLFinite {width : Nat} [NeZero width]
    (c : HolFiniteMapExact MlString (List Nat × CrepProgHOL width))
    (f : MlString) (args : List (HolWordLab width)) (len : Nat) :
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

/-- Flapjack-only preparation (no HOL declaration, untagged): given the
    `ExtCall` case, every program and state satisfy the `simp_prog_correct`
    predicate, by the tagged Crep `evaluate_ind` over the eighteen tagged
    constructor cases.  The Call IHs are bridged from the induction principle's
    un-normalized form to the one-point-normalized form of
    `simpProgCorrectCallCase`, as in the ncompile assembly. -/
theorem simpProgCorrectOfExtCall {width : Nat} [NeZero width] {σ : Type}
    (hext : ∀ (f : MlString) (p1 l1 p2 l2 : Nat) (s : CrepSemHOLState width σ),
      simpProgCorrectAt (.extCall f p1 l1 p2 l2) s) :
    ∀ (p : CrepProgHOL width) (s : CrepSemHOLState width σ), simpProgCorrectAt p s := by
  intro p s
  apply evalCrepSemHOLProgExact_induct (P := fun x => simpProgCorrectAt x.1 x.2)
  · intro s
    exact simpProgCorrectSkipCase s
  · intro v e prog s ih
    exact simpProgCorrectDecCase v e prog s ih
  · intro lhss pop rhss s
    exact simpProgCorrectPrimitiveCase s lhss pop rhss
  · intro v src s
    exact simpProgCorrectAssignCase s v src
  · intro dst src s
    exact simpProgCorrectStoreCase s dst src
  · intro dst src s
    exact simpProgCorrectStore32Case s dst src
  · intro dst src s
    exact simpProgCorrectStoreByteCase s dst src
  · intro dst src s
    exact simpProgCorrectStoreGlobCase s dst src
  · intro op v ad s
    exact simpProgCorrectShMemCase s op v ad
  · intro c1 c2 s ih2 ih1
    exact simpProgCorrectSeqCase s c1 c2 ih2 ih1
  · intro e c1 c2 s ih
    exact simpProgCorrectIfCase e c1 c2 s ih
  · intro n s
    exact simpProgCorrectBreakCase s n
  · intro n s
    exact simpProgCorrectContinueCase s n
  · intro e c s ih1 ih2 ih3
    exact simpProgCorrectWhileCase e c s ih1 ih2 ih3
  · intro es s
    exact simpProgCorrectReturnCase s es
  · intro eid s
    exact simpProgCorrectRaiseCase s eid
  · intro s
    exact simpProgCorrectTickCase s
  · intro caltyp fname argexps s ihh ihb
    have hfun : crepExactEvalExpClassical s = evalCrepSemHOLExp s :=
      funext (crepExactEvalExpClassical_eq s)
    exact simpProgCorrectCallCase caltyp fname argexps s
      (fun args prog newlocals st eid rts p ⟨h1, h2, h3, h4, h5, h6⟩ =>
        ihh args (prog, newlocals) prog newlocals _ _ st _ eid _ _ _ _ eid p
          (by rw [hfun]; exact h1)
          (by rw [← simpProgLookupCodeFinite_eq_HOLFinite]; exact h2) rfl
          (by subst h6; simpa using h3) h4 h5.symm rfl rfl rfl h6 rfl rfl rfl rfl)
      (fun args prog newlocals ⟨h1, h2, h3, h4⟩ =>
        ihb args (prog, newlocals) prog newlocals (by rw [hfun]; exact h1)
          (by rw [← simpProgLookupCodeFinite_eq_HOLFinite]; exact h2) rfl
          (by cases caltyp with
              | none => simp
              | some x => obtain ⟨rts, y⟩ := x; simpa using h3) h4)
  · intro f p1 l1 p2 l2 s
    exact hext f p1 l1 p2 l2 s


/-- Exact HOL `simp_prog_correct` (`crep_arithProofScript.sml:186-190`):
    `∀p s r s'. crepSem$evaluate (p, s) = (r, s') ⇒ r ≠ SOME Error ⇒
      evaluate (simp_prog p, mapcs s) = (r, mapcs s')`, over the tagged native
    Crep evaluator `evalCrepSemHOLProgExact`, the tagged `crepSimpProgHOL`, and
    the proof script's `mapcs` rendered by `crepSimpMapcsHOL`
    (`crepSimpMapcsHOL_eq_mapc`).  Same binders, premises and conclusion; no
    other premise.  Proved as HOL does, by `evaluate_ind`
    (`evalCrepSemHOLProgExact_induct`) over the nineteen tagged constructor
    cases. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_prog_correct"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem crepArithSimpProgCorrect {width : Nat} [NeZero width] {σ : Type} :
    ∀ (p : CrepProgHOL width) (s : CrepSemHOLState width σ)
      (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact s p = (r, s') →
      r ≠ some .error →
      evalCrepSemHOLProgExact (crepSimpMapcsHOL s) (crepSimpProgHOL p) =
        (r, crepSimpMapcsHOL s') :=
  fun p s => simpProgCorrectOfExtCall
    (fun f p1 l1 p2 l2 s => simpProgCorrectExtCallCase s f p1 l1 p2 l2) p s

end Flapjack
