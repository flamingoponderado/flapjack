import Flapjack.Pancake.Proofs.PanGlobals.CompileExpCorrect
import Flapjack.Pancake.Proofs.PanGlobals.ReadBytearray
import Flapjack.Pancake.Proofs.PanGlobals.WriteBytearray
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationFfi
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationLocals
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Base

/-!
# pan_globals `compile_correct`: the `ExtCall` case

`Resume compile_correct[ExtCall]` (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1595-1613`,
bead `flapjack-pxn.18.5.2.35`).  The case uses the established theorem
`compile_exp_correct` for the four compiled arguments, the byte-array
read transport `state_rel_read_bytearray`, the `call_FFI` split with
`state_rel_change_ffi` and `state_rel_write_bytearray`, and the empty-locals
transport `state_rel_empty_locals`. These are established support theorems,
not additional `evaluate_ind` hypotheses. The return-length step uses
tagged `StackRemove.callFFILengthHOL` (`call_FFI_LENGTH`), whose proof uses
the shared `callFFIHOL_ret_length` helper. Its dependency direction is helper
to tagged wrapper; the case consumes the tagged theorem directly.
Source evaluator is the tagged
`evaluateHOLFiniteState` (`panSem$evaluate_def`), the compiler the tagged
`compileProgExactHOL` (`pan_globals$compile_def`) and the relation the tagged
`panGlobalsStateRelHOLExact` (`state_rel_def`).
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open PanSemStateFiniteExact

namespace PanGlobalsCompileCorrectExtCall

/-- Canonical state roundtrip, re-exported for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Canonical context roundtrip, re-exported for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_PanGlobalsContextExact
    {width : Nat} [NeZero width] (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad (PanGlobalsContextExact.toBroad context) = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context

/-- Original `ExtCall` compiler-correctness case, HOL1595-1613.  The original
state relation, source run and non-Error premises suffice: the four compiled
argument evaluations follow from `compile_exp_correct`, the two reads from
`state_rel_read_bytearray`, and the FFI transitions from the `call_FFI` split
with `state_rel_change_ffi`/`state_rel_write_bytearray`; no extra hypothesis. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_ExtCall {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (function : MlS)
    (configuration configurationLength array arrayLength : ExpHOL width) :
    ∀ (res : Option (PanSemResultExact width)) (context : PanGlobalsContextExact width)
      (target post : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true context source target ∧
        evaluateHOLFiniteState source
          (.extCall function configuration configurationLength array arrayLength) = (res, post) ∧
        res ≠ some .error →
      ∃ targetPost,
        evaluateHOLFiniteState target
          (compileProgExactHOL context
            (.extCall function configuration configurationLength array arrayLength)) =
              (res, targetPost) ∧
        panGlobalsStateRelHOLExact (goodResHOL res) context post targetPost := by
  classical
  intro res context target post ⟨hrel, hev, hne⟩
  have hffi : source.ffi = target.ffi := by
    have hrel' := hrel
    rcases hrel' with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hffi,_,_⟩
    exact hffi
  have hcompile : compileProgExactHOL context
      (.extCall function configuration configurationLength array arrayLength) =
        .extCall function (compileExpExactHOL context configuration)
          (compileExpExactHOL context configurationLength)
          (compileExpExactHOL context array) (compileExpExactHOL context arrayLength) := by
    simp [compileProgExactHOL]
  rw [hcompile]
  rw [evaluateHOLFiniteState_extCall_source] at hev
  rw [evaluateHOLFiniteState_extCall_source]
  cases hc : @evalHOLFinite width σ _ source
      (fun a => Classical.propDecidable (source.memaddrs a)) configuration with
  | none =>
      simp only [hc] at hev
      exact False.elim (hne (Prod.mk.inj hev).1.symm)
  | some vc =>
      cases vc with
      | val wc =>
          cases wc with
          | word a1 =>
              cases hcl : @evalHOLFinite width σ _ source
                  (fun a => Classical.propDecidable (source.memaddrs a)) configurationLength with
              | none =>
                  simp only [hc, hcl] at hev
                  exact False.elim (hne (Prod.mk.inj hev).1.symm)
              | some vcl =>
                  cases vcl with
                  | val wcl =>
                      cases wcl with
                      | word l1 =>
                          cases ha : @evalHOLFinite width σ _ source
                              (fun a => Classical.propDecidable (source.memaddrs a)) array with
                          | none =>
                              simp only [hc, hcl, ha] at hev
                              exact False.elim (hne (Prod.mk.inj hev).1.symm)
                          | some va =>
                              cases va with
                              | val wa =>
                                  cases wa with
                                  | word a2 =>
                                      cases hal : @evalHOLFinite width σ _ source
                                          (fun a => Classical.propDecidable (source.memaddrs a)) arrayLength with
                                      | none =>
                                          simp only [hc, hcl, ha, hal] at hev
                                          exact False.elim (hne (Prod.mk.inj hev).1.symm)
                                      | some val_ =>
                                          cases val_ with
                                          | val wal =>
                                              cases wal with
                                              | word l2 =>
                                                  cases hr1 : readBytearrayWordHOL (byteWidth := 8) a1
                                                      l1.toNat
                                                      (@panMemLoadByteWord8HOL width _ source.memory
                                                        source.memaddrs
                                                        (fun a => Classical.propDecidable (source.memaddrs a))
                                                        source.be) with
                                                  | none =>
                                                      simp only [hc, hcl, ha, hal, hr1] at hev
                                                      exact False.elim (hne (Prod.mk.inj hev).1.symm)
                                                  | some bytes1 =>
                                                      cases hr2 : readBytearrayWordHOL (byteWidth := 8) a2
                                                          l2.toNat
                                                          (@panMemLoadByteWord8HOL width _ source.memory
                                                            source.memaddrs
                                                            (fun a => Classical.propDecidable (source.memaddrs a))
                                                            source.be) with
                                                      | none =>
                                                          simp only [hc, hcl, ha, hal, hr1, hr2] at hev
                                                          exact False.elim (hne (Prod.mk.inj hev).1.symm)
                                                      | some bytes2 =>
                                                          have ht_c := PanGlobalsCompileExpCorrect.compileExpCorrectHOL
                                                            source configuration (.val (.word a1)) context target ⟨hrel, hc⟩
                                                          have ht_cl := PanGlobalsCompileExpCorrect.compileExpCorrectHOL
                                                            source configurationLength (.val (.word l1)) context target ⟨hrel, hcl⟩
                                                          have ht_a := PanGlobalsCompileExpCorrect.compileExpCorrectHOL
                                                            source array (.val (.word a2)) context target ⟨hrel, ha⟩
                                                          have ht_al := PanGlobalsCompileExpCorrect.compileExpCorrectHOL
                                                            source arrayLength (.val (.word l2)) context target ⟨hrel, hal⟩
                                                          have ht_r1 := PanGlobalsReadBytearray.stateRelReadBytearray
                                                            true context source target bytes1 a1 l1.toNat ⟨hrel, hr1⟩
                                                          have ht_r2 := PanGlobalsReadBytearray.stateRelReadBytearray
                                                            true context source target bytes2 a2 l2.toNat ⟨hrel, hr2⟩
                                                          simp only [hc, hcl, ha, hal, hr1, hr2] at hev
                                                          simp only [ht_c, ht_cl, ht_a, ht_al, ht_r1, ht_r2]
                                                          rw [hffi] at hev
                                                          cases hcall : callFFIHOL target.ffi (.extCall function) bytes1 bytes2 with
                                                          | final event =>
                                                              simp only [hcall] at hev
                                                              obtain ⟨hr, hpost⟩ := Prod.mk.inj hev
                                                              have hr' : res = some (.finalFfi event) := hr.symm
                                                              subst hr'
                                                              refine ⟨emptyLocalsHOLFinite target, ?_, ?_⟩
                                                              · rfl
                                                              · rw [hpost.symm]
                                                                simp [goodResHOL]
                                                                exact (PanGlobalsStateRelationLocals.stateRelEmptyLocalsHOL
                                                                  context source target false).1 hrel
                                                          | ret newFfi newBytes =>
                                                              simp only [hcall] at hev
                                                              obtain ⟨hr, hpost⟩ := Prod.mk.inj hev
                                                              have hr' : res = none := hr.symm
                                                              subst hr'
                                                              have hlen : newBytes.length = l2.toNat :=
                                                                (Flapjack.Compiler.Backend.StackRemove.callFFILengthHOL target.ffi (.extCall function)
                                                                  bytes1 bytes2 newBytes newFfi hcall).trans
                                                                  (readBytearrayWordHOL_length a2 l2.toNat
                                                                    (@panMemLoadByteWord8HOL width _ source.memory
                                                                      source.memaddrs
                                                                      (fun a => Classical.propDecidable (source.memaddrs a))
                                                                      source.be) bytes2 hr2)
                                                              have hreadSrc : readBytearrayWordHOL (byteWidth := 8)
                                                                  a2 newBytes.length
                                                                  (@panMemLoadByteWord8HOL width _ source.memory
                                                                    source.memaddrs
                                                                    (fun a => Classical.propDecidable (source.memaddrs a))
                                                                    source.be) = some bytes2 := by
                                                                rw [hlen]; exact hr2
                                                              have hw := PanGlobalsWriteBytearray.stateRelWriteBytearrayHOL
                                                                true context source target a2 newBytes bytes2
                                                                ⟨hrel, hreadSrc⟩
                                                              have hw2 := PanGlobalsStateRelationFfi.stateRelChangeFfiHOL
                                                                context _ _ true newFfi hw
                                                              refine ⟨PanSemStateFiniteExact.ofExact
                                                                { target.toExact with
                                                                  memory := @panWriteBytearrayWord8HOL width _
                                                                    a2 newBytes target.memory target.memaddrs
                                                                    (fun a => Classical.propDecidable
                                                                      (target.memaddrs a)) target.be
                                                                  ffi := newFfi }
                                                                (by
                                                                  change ({ target.toExact with
                                                                      memory := @panWriteBytearrayWord8HOL width _
                                                                        a2 newBytes target.memory target.memaddrs
                                                                        (fun a => Classical.propDecidable
                                                                          (target.memaddrs a)) target.be
                                                                      ffi := newFfi } :
                                                                        PanSemStateExact width σ).FiniteSupport
                                                                  simpa [PanSemStateExact.FiniteSupport] using target.toExact_finiteSupport),
                                                                ?_, ?_⟩
                                                              · rfl
                                                              · simp [goodResHOL]
                                                                rw [hpost.symm,
                                                                  PanSemStateFiniteExact.ofExact_update_memory_ffi,
                                                                  PanSemStateFiniteExact.ofExact_update_memory_ffi]
                                                                exact hw2
                                          | rStruct fl =>
                                              simp only [hc, hcl, ha, hal] at hev
                                              exact False.elim (hne (Prod.mk.inj hev).1.symm)
                                          | nStruct nm fl =>
                                              simp only [hc, hcl, ha, hal] at hev
                                              exact False.elim (hne (Prod.mk.inj hev).1.symm)
                              | rStruct fl =>
                                  simp only [hc, hcl, ha] at hev
                                  exact False.elim (hne (Prod.mk.inj hev).1.symm)
                              | nStruct nm fl =>
                                  simp only [hc, hcl, ha] at hev
                                  exact False.elim (hne (Prod.mk.inj hev).1.symm)
                  | rStruct fl =>
                      simp only [hc, hcl] at hev
                      exact False.elim (hne (Prod.mk.inj hev).1.symm)
                  | nStruct nm fl =>
                      simp only [hc, hcl] at hev
                      exact False.elim (hne (Prod.mk.inj hev).1.symm)
      | rStruct fl =>
          simp only [hc] at hev
          exact False.elim (hne (Prod.mk.inj hev).1.symm)
      | nStruct nm fl =>
          simp only [hc] at hev
          exact False.elim (hne (Prod.mk.inj hev).1.symm)

end PanGlobalsCompileCorrectExtCall

end Flapjack
