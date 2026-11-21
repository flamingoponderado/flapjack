import Flapjack.Compiler.Backend.ClosToBvl.Common
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ChainSyntactic
import Flapjack.Compiler.Backend.ClosNumber.Proofs.NoLabels
import Flapjack.Compiler.Backend.ClosNumber.Proofs.ObeysMaxApp
import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationInvariants
import Flapjack.Compiler.Backend.ClosMti.Proofs.NoLabels
import Flapjack.Compiler.Backend.ClosMti.Proofs.Arity
import Flapjack.Compiler.Backend.ClosKnown.Proofs.CompileLabels
import Flapjack.Compiler.Backend.ClosKnown.Proofs.CompileArity
import Flapjack.Compiler.Backend.ClosKnown.Proofs.TraversalLocationsTotal
import Flapjack.Compiler.Backend.ClosFvs.Proofs.Syntax
import Flapjack.Compiler.Backend.ClosTicks.Proofs.Syntax
import Flapjack.Compiler.Backend.ClosLetop.Proofs.Syntax
import Flapjack.Compiler.Backend.ClosCall.Proofs.SyntaxPreservation
import Flapjack.Compiler.Backend.ClosCall.Proofs.ArityPreservation
import Flapjack.Compiler.Backend.ClosCall.Proofs.LocationMembership
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.NoLabels
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.FreeMaxApp
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.AnnotationInvariants.Original
import Flapjack.Compiler.Backend.BackendProof.NoMti

/-! backendProofScript.sml 219-298: `compile_common_syntax`, the syntactic
invariants of the closure preprocessing passes run by
`clos_to_bvl$compile_common`. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack.Compiler.Backend.ClosLang Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.ClosToBvl

/-- Flapjack helper: membership in the bodies of an appended program. -/
private theorem mem_map_append_bodies {α : Type} (P : Exp → Prop)
    (xs ys : List (α × Nat × Exp))
    (hx : ∀ e ∈ xs.map (fun entry => entry.2.2), P e)
    (hy : ∀ entry ∈ ys, P entry.2.2) :
    ∀ e ∈ (xs ++ ys).map (fun entry => entry.2.2), P e := by
  intro e he
  rw [List.map_append, List.mem_append] at he
  rcases he with h | h
  · exact hx e h
  · obtain ⟨entry, mem, rfl⟩ := List.mem_map.mp h
    exact hy entry mem

/-- Exact HOL `compile_common_syntax` (`backendProofScript.sml:219-298`). HOL
`EVERY P l` is membership quantification and `MAP (SND o SND)` maps each
`(name, arity, body)` entry to its body. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "compile_common_syntax"]
theorem compileCommon_syntax :
    ∀ (cf : ClosToBvl.Config) (e3 : List Exp) (cf1 : ClosToBvl.Config)
      (e4 : List (Nat × Nat × Exp)),
      compileCommon cf e3 = (cf1, e4) →
      ((∀ e ∈ e3, noLabels e) → ∀ e ∈ e4.map (Prod.snd ∘ Prod.snd), noLabels e) ∧
      (0 < cf.maxApp ∧ (∀ e ∈ e3, noMti e) →
        ∀ e ∈ e4.map (Prod.snd ∘ Prod.snd), obeysMaxApp cf.maxApp e) ∧
      everyFnLocationSome (e4.map (Prod.snd ∘ Prod.snd)) := by
  intro cf e3 cf1 e4 run
  simp only [compileCommon] at run
  generalize hes1 : ClosMti.compile cf.doMti cf.maxApp e3 = es1 at run
  generalize hloc : (if (cf.nextLoc + max 1 es1.length) % 2 = 0 then cf.nextLoc + max 1 es1.length
    else cf.nextLoc + max 1 es1.length + 1) = loc at run
  rcases hr : ClosNumber.renumberList loc es1 with ⟨n, es2⟩
  rw [hr] at run
  rcases hk : ClosKnown.compileSource cf.knownConf es2 with ⟨kc, es3⟩
  rw [hk] at run
  rcases hc : ClosCall.compile cf.doCall es3 with ⟨es4, st⟩
  rw [hc] at run
  simp only [Prod.mk.injEq] at run
  obtain ⟨-, rfl⟩ := run
  have bodies : (Prod.snd ∘ Prod.snd : Nat × Nat × Exp → Exp) = fun entry => entry.2.2 := rfl
  rw [bodies]
  refine ⟨?_, ?_, ?_⟩
  · -- no_Labels
    intro input
    have h1 : ∀ e ∈ es1, noLabels e := by
      rw [← hes1]
      cases cf.doMti with
      | true => exact ClosMti.intro_multi_noLabels cf.maxApp e3 input
      | false => exact input
    have h2 : ∀ e ∈ es2, noLabels e :=
      ClosNumber.renumberCodeLocs_noLabels.1 loc es1 n es2 ⟨hr, h1⟩
    have h3 : ∀ e ∈ es3, noLabels e := by
      cases hkc : cf.knownConf with
      | none =>
          rw [hkc] at hk
          simp only [ClosKnown.compileSource, Prod.mk.injEq] at hk
          rw [← hk.2]
          exact h2
      | some c =>
          rw [hkc] at hk
          obtain ⟨_, _, safe, _⟩ := ClosKnown.compileNoLabels c es2 kc es3 ⟨hk, h2⟩
          exact safe
    have h4 : (∀ e ∈ es4, noLabels e) ∧ ClosCall.stateSyntax noLabels st := by
      cases hcall : cf.doCall with
      | true =>
          rw [hcall] at hc
          exact ClosCall.callsNoLabels es3 (.ln, []) es4 st hc (by simp [ClosCall.stateSyntax]) h3
      | false =>
          rw [hcall] at hc
          simp only [ClosCall.compile, Bool.false_eq_true, if_false, Prod.mk.injEq] at hc
          rw [← hc.1, ← hc.2]
          exact ⟨h3, by simp [ClosCall.stateSyntax]⟩
    apply ClosAnnotate.compileSource_noLabels
    exact mem_map_append_bodies noLabels _ _
      (ClosToBvl.chainExps_noLabels es4 cf.nextLoc h4.1) h4.2
  · -- obeys_max_app
    intro ⟨positive, input⟩
    have h1 : ∀ e ∈ es1, obeysMaxApp cf.maxApp e := by
      rw [← hes1]
      cases cf.doMti with
      | true => exact ClosMti.intro_multi_obeys_max_app cf.maxApp e3 ⟨by omega, input⟩
      | false => exact every_noMti_imp_obeysMaxApp cf.maxApp e3 ⟨positive, input⟩
    have h2 : ∀ e ∈ es2, obeysMaxApp cf.maxApp e :=
      (ClosNumber.renumberCodeLocs_obeysMaxApp cf.maxApp).1 loc es1 n es2 ⟨hr, h1⟩
    have h3 : ∀ e ∈ es3, obeysMaxApp cf.maxApp e := by
      cases hkc : cf.knownConf with
      | none =>
          rw [hkc] at hk
          simp only [ClosKnown.compileSource, Prod.mk.injEq] at hk
          rw [← hk.2]
          exact h2
      | some c =>
          rw [hkc] at hk
          obtain ⟨_, _, safe, _⟩ := ClosKnown.compileObeysMaxApp cf.maxApp c es2 kc es3 ⟨hk, h2⟩
          exact safe
    have h4 : (∀ e ∈ es4, obeysMaxApp cf.maxApp e) ∧
        ClosCall.stateSyntax (obeysMaxApp cf.maxApp) st := by
      cases hcall : cf.doCall with
      | true =>
          rw [hcall] at hc
          exact ClosCall.callsObeysMaxApp cf.maxApp es3 (.ln, []) es4 st hc
            (by simp [ClosCall.stateSyntax]) h3
      | false =>
          rw [hcall] at hc
          simp only [ClosCall.compile, Bool.false_eq_true, if_false, Prod.mk.injEq] at hc
          rw [← hc.1, ← hc.2]
          exact ⟨h3, by simp [ClosCall.stateSyntax]⟩
    apply ClosAnnotate.compileSource_obeysMaxApp
    exact mem_map_append_bodies (obeysMaxApp cf.maxApp) _ _
      (ClosToBvl.chainExps_obeysMaxApp cf.maxApp es4 cf.nextLoc h4.1) h4.2
  · -- every_Fn_SOME
    have h2 : everyFnLocationSome es2 := by
      have h := ClosNumber.renumberCodeLocs_everyFnSome.1 loc es1
      rw [hr] at h
      exact h
    have h3 : everyFnLocationSome es3 := by
      cases hkc : cf.knownConf with
      | none =>
          rw [hkc] at hk
          simp only [ClosKnown.compileSource, Prod.mk.injEq] at hk
          rw [← hk.2]
          exact h2
      | some c =>
          rw [hkc] at hk
          simp only [ClosKnown.compileSource, Prod.mk.injEq] at hk
          rw [← hk.2]
          have known := ClosKnown.TraversalLocations.knownEveryFnLocations c
            (ClosFvs.compileSource es2) [] .ln
            ⟨(ClosFvs.removeSource_locations 0 es2).mpr h2, by simp,
              by simp [ClosKnown.globalsApproxLocations, Flapjack.sptLookup]⟩
          rw [ClosLetop.compileSource_locations, ClosTicks.removeSource_locations]
          exact known.1
    have h4 : everyFnLocationSome es4 ∧ everyFnLocationSome (st.2.map (fun p => p.2.2)) := by
      cases hcall : cf.doCall with
      | true =>
          rw [hcall] at hc
          exact ClosCall.calls_preserves_everyFnLocationSome es3 (.ln, []) es4 st hc
            ⟨h3, by simp [everyFnLocationSome]⟩
      | false =>
          rw [hcall] at hc
          simp only [ClosCall.compile, Bool.false_eq_true, if_false, Prod.mk.injEq] at hc
          rw [← hc.1, ← hc.2]
          exact ⟨h3, by simp [everyFnLocationSome]⟩
    apply ClosAnnotate.everyFnSome_ann
    rw [List.map_append, everyFnLocationSome_append]
    exact ⟨ClosToBvl.chainExps_everyFnSome es4 cf.nextLoc h4.1, h4.2⟩

end Flapjack.Compiler.Backend.BackendProof
