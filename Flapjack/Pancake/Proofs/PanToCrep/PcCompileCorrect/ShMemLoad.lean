import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Call
import Flapjack.Pancake.Semantics.ShMemBytesBridge

/-!
# `pc_compile_correct` ShMemLoad case over the exact carriers

The `ShMemLoad` constructor conjunct of HOL `pc_compile_correct`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, resumed at
`:1912-1958`). The source and target shared-memory load primitives are related
by the control/byte bridge in `ShMemBytesBridge` and the successful-return
relation bridge `shMemLoadHOLFiniteExact_ret_corresponds`. Decoding the
FFI-returned bytes uses the Pan/Crep decoded-word equality, which holds whenever
the word has at least one whole byte (`8 ≤ width`; RISC-V 32/64). Unlike the
store case the compiler writes the loaded word straight into the destination
slot of `name`, so no fresh temporary is needed.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ProgHOL ExpHOL sizeOfShapeHOL)
open Flapjack.PanSemStateFiniteExact

/-- HOL `pc_compile_correct`, `ShMemLoad` constructor case
    (`pan_to_crepProofScript.sml:1912-1958`, under the `evaluate_ind` conjunct
    from `:442-468`). Its binders are `op vk name e`; there is no induction
    hypothesis because the address uses `eval`, not recursive `evaluate`. The
    side condition `8 ≤ width` is exactly HOL's implicit `8 ≤ dimindex`
    requirement of `word_of_bytes` (automatic for RISC-V 32/64). -/
theorem pcCompileCorrectAt_shMemLoad {width : Nat} {σ : Type} [NeZero width]
    (h8 : 8 ≤ width) (operator : OpSize) (kind : VarKind) (name : MlS)
    (address : ExpHOL width) (s : PanSemStateFiniteExact width σ) :
    pcCompileCorrectAt (.shMemLoad operator kind name address : ProgHOL width) s := by
  classical
  intro res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  cases kind
  · -- `.local`
    have hlocExp : localisedExpHOL address = true := by simpa [localisedProgHOL] using hloc
    rw [PanSemStateFiniteExact.evaluateHOLFiniteState_shMemLoad_source] at hrun
    cases haddress : @evalHOLFinite width σ _ s
        (fun key => Classical.propDecidable (s.memaddrs key)) address with
    | none =>
        simp only [haddress] at hrun
        exact absurd (Prod.mk.inj hrun).1.symm hres
    | some addressValue =>
        cases addressValue with
        | rStruct fields =>
            simp only [haddress] at hrun
            exact absurd (Prod.mk.inj hrun).1.symm hres
        | nStruct structName fields =>
            simp only [haddress] at hrun
            exact absurd (Prod.mk.inj hrun).1.symm hres
        | val addressPayload =>
            cases addressPayload with
            | word addr =>
                cases hlookup : lookupKvarHOLFinite VarKind.local name s with
                | none =>
                    simp only [haddress, hlookup] at hrun
                    exact absurd (Prod.mk.inj hrun).1.symm hres
                | some destinationValue =>
                    cases destinationValue with
                    | rStruct fields =>
                        simp only [haddress, hlookup] at hrun
                        exact absurd (Prod.mk.inj hrun).1.symm hres
                    | nStruct structName fields =>
                        simp only [haddress, hlookup] at hrun
                        exact absurd (Prod.mk.inj hrun).1.symm hres
                    | val destinationPayload =>
                        cases destinationPayload with
                        | word w =>
                            have hlookup' : s.locals.lookup name = some (.val (.word w)) := by
                              simpa only [lookupKvarHOLFinite] using hlookup
                            obtain ⟨slots, words, hvar, hmapSlots, hflatten, _⟩ :=
                              hlocals.2.2 name (.val (.word w)) hlookup'
                            have hvarOne : ctxt.vars.lookup name =
                                some (ShapeHOL.one, slots) := by
                              rw [hvar, shapeOfHOLExact_val]
                            have hwords : words = [HolWordLab.word w] := by
                              rw [← hflatten]; simp [flattenHOL]
                            have hmapSlots' : slots.mapM t.locals.lookup =
                                some [HolWordLab.word w] := by
                              rw [← hwords]; exact hmapSlots
                            obtain ⟨destination, hdestEq, hdestLookup⟩ :
                                ∃ d, slots = [d] ∧
                                  t.locals.lookup d = some (HolWordLab.word w) := by
                              cases slots with
                              | nil => simp at hmapSlots'
                              | cons d rest =>
                                  rw [List.mapM_cons] at hmapSlots'
                                  rcases Option.bind_eq_some_iff.mp hmapSlots' with
                                    ⟨y, hy, hrest⟩
                                  cases rest with
                                  | nil =>
                                      simp only [List.mapM_nil] at hrest
                                      rcases Option.bind_eq_some_iff.mp hrest with
                                        ⟨ys, _, hnil⟩
                                      have hcons : y :: ys = [HolWordLab.word w] :=
                                        Option.some.inj hnil
                                      refine ⟨d, rfl, ?_⟩
                                      rw [hy, (List.cons.inj hcons).1]
                                  | cons d2 rest2 =>
                                      rcases Option.bind_eq_some_iff.mp hrest with
                                        ⟨ys, hys, hnil⟩
                                      have hcons : y :: ys = [HolWordLab.word w] :=
                                        Option.some.inj hnil
                                      have hysnil : ys = [] := (List.cons.inj hcons).2
                                      rw [hysnil] at hys
                                      rw [List.mapM_cons] at hys
                                      rcases Option.bind_eq_some_iff.mp hys with
                                        ⟨z, _, hz⟩
                                      rcases Option.bind_eq_some_iff.mp hz with
                                        ⟨zs, _, hzzs⟩
                                      simp at hzzs
                            have hvarDest : ctxt.vars.lookup name =
                                some (ShapeHOL.one, [destination]) := by
                              rw [hvarOne, hdestEq]
                            rcases hcAddress : compileExpExactHOLW ctxt address with
                              ⟨esAddress, shAddress⟩
                            obtain ⟨hmapAddress, _, _, _⟩ :=
                              @compileExpValRelHOL width σ _ s
                                (fun key => Classical.propDecidable (s.memaddrs key)) ctxt t
                                (fun key => Classical.propDecidable (t.memaddrs key))
                                address (.val (.word addr)) esAddress shAddress
                                haddress
                                hstate hcode hlocals hlocExp hcAddress
                            obtain ⟨ceAddress, hceAddress⟩ : ∃ ce, esAddress = [ce] := by
                              rcases esAddress with _ | ⟨ce, _ | ⟨_, _⟩⟩
                              · simp [flattenHOL] at hmapAddress
                              · exact ⟨ce, rfl⟩
                              · simp [flattenHOL] at hmapAddress
                            subst hceAddress
                            have hceAddressEval :
                                evalCrepSemHOLExp t ceAddress = some (.word addr) := by
                              simpa [flattenHOL] using hmapAddress
                            have hcomp : compileProgExactHOLW ctxt
                                  (.shMemLoad operator VarKind.local name address :
                                    ProgHOL width) =
                                .shMem (loadMemOpHOL operator) destination ceAddress := by
                              simp [compileProgExactHOLW, compileShMemLoadExactHOLW,
                                hcAddress, hvarDest]
                            have hbody : evalCrepSemHOLProgExact t
                                  (.shMem (loadMemOpHOL operator) destination ceAddress) =
                                crepShMemLoadExactHOL destination addr (nbOpHOL operator) t := by
                              rw [evalCrepSemHOLProgExact_shMem_holShape, hceAddressEval,
                                hdestLookup]
                              cases operator <;>
                                simp [crepIsLoadMemOp, loadMemOpHOL, crepShMemOpExactHOL,
                                  nbOpHOL]
                            have hstateKeep := hstate
                            obtain ⟨_, _, hshmema, _, _, _, _, hffi, _, _⟩ := hstateKeep
                            by_cases hnb : nbOpHOL operator = 0
                            · by_cases hdom : s.shMemaddrs addr
                              · have hdomT : t.shMemaddrs addr := by
                                  rw [← congrFun hshmema addr]; exact hdom
                                cases hcall : callFFIHOL s.ffi (.sharedMem .mappedRead)
                                    [BitVec.ofNat 8 (nbOpHOL operator)]
                                    (panWordToBytesHOL addr false) with
                                | final event =>
                                    have hcallT : callFFIHOL t.ffi (.sharedMem .mappedRead)
                                        [BitVec.ofNat 8 (nbOpHOL operator)]
                                        ((crepClockWordToBytes addr).map UInt8.toBitVec) =
                                        .final event := by
                                      rw [← hffi,
                                        (panWordToBytesHOL_eq_map_crepClockWordToBytes
                                          addr).symm]
                                      exact hcall
                                    have hred : (some (.finalFfi event),
                                          PanSemStateFiniteExact.emptyLocalsHOLFinite s) =
                                        (res, s1) := by
                                      have h := hrun
                                      simp only [haddress, hlookup] at h
                                      unfold shMemLoadHOLFiniteExact at h
                                      rw [if_pos hnb, if_pos hdom, hcall] at h
                                      try simp only [] at h
                                      exact h
                                    have hs1 : s1 =
                                        PanSemStateFiniteExact.emptyLocalsHOLFinite s :=
                                      (Prod.mk.inj hred).2.symm
                                    have hresF : res = some (.finalFfi event) :=
                                      (Prod.mk.inj hred).1.symm
                                    have htargetF : crepShMemLoadExactHOL destination addr
                                        (nbOpHOL operator) t =
                                        (some (.finalFfi event),
                                          CrepSemHOLState.emptyLocals t) := by
                                      unfold crepShMemLoadExactHOL
                                      rw [if_pos hnb, if_pos hdomT, hcallT]
                                    refine ⟨some (.finalFfi event),
                                      CrepSemHOLState.emptyLocals t, ?_, ?_, ?_, ?_, ?_⟩
                                    · rw [hcomp, hbody, htargetF]
                                    · rw [hs1]
                                      simpa only [panToCrepStateRelFiniteExact,
                                        PanSemStateFiniteExact.emptyLocalsHOLFinite,
                                        CrepSemHOLState.emptyLocals] using hstate
                                    · rw [hs1]
                                      simpa only [PanSemStateFiniteExact.emptyLocalsHOLFinite,
                                        CrepSemHOLState.emptyLocals] using hcode
                                    · rw [hs1]
                                      simpa only [PanSemStateFiniteExact.emptyLocalsHOLFinite]
                                        using hexcp
                                    · unfold pcCompileCorrectResultRel
                                      rw [hresF]
                                | ret newFfi newBytes =>
                                    have hcallT : callFFIHOL t.ffi (.sharedMem .mappedRead)
                                        [BitVec.ofNat 8 (nbOpHOL operator)]
                                        ((crepClockWordToBytes addr).map UInt8.toBitVec) =
                                        .ret newFfi newBytes := by
                                      rw [← hffi,
                                        (panWordToBytesHOL_eq_map_crepClockWordToBytes
                                          addr).symm]
                                      exact hcall
                                    have hred : (none, setKvarFfiHOLFinite VarKind.local name
                                        (.val (.word (panWordOfBytesHOL false 0 newBytes)))
                                        s newFfi) = (res, s1) := by
                                      have h := hrun
                                      simp only [haddress, hlookup] at h
                                      unfold shMemLoadHOLFiniteExact at h
                                      rw [if_pos hnb, if_pos hdom, hcall] at h
                                      try simp only [] at h
                                      exact h
                                    have hs1 : s1 = setKvarFfiHOLFinite VarKind.local name
                                        (.val (.word (panWordOfBytesHOL false 0 newBytes)))
                                        s newFfi := (Prod.mk.inj hred).2.symm
                                    have hresN : res = none := (Prod.mk.inj hred).1.symm
                                    have htargetR : crepShMemLoadExactHOL destination addr
                                        (nbOpHOL operator) t =
                                        (none, { CrepSemHOLState.setVar destination
                                          (.word (crepClockWordOfBytes
                                            (newBytes.map UInt8.ofBitVec))) t with
                                          ffi := newFfi }) := by
                                      unfold crepShMemLoadExactHOL
                                      rw [if_pos hnb, if_pos hdomT, hcallT]
                                    have hsource' : shMemLoadHOLFiniteExact s VarKind.local
                                        name addr (nbOpHOL operator) = (none, s1) := by
                                      unfold shMemLoadHOLFiniteExact
                                      rw [if_pos hnb, if_pos hdom, hcall]
                                      rw [hs1]
                                    obtain ⟨hst1, hloc1⟩ :=
                                      shMemLoadHOLFiniteExact_ret_corresponds (source := s)
                                        (target := t) (ctxt := ctxt) (destination := destination)
                                        (name := name) (address := addr) (nb := nbOpHOL operator)
                                        h8 hstate hlocals hvarDest hsource' htargetR
                                    refine ⟨none, { CrepSemHOLState.setVar destination
                                        (.word (crepClockWordOfBytes
                                          (newBytes.map UInt8.ofBitVec))) t with
                                      ffi := newFfi }, ?_, hst1, ?_, ?_, ?_⟩
                                    · rw [hcomp, hbody, htargetR]
                                    · rw [hs1]
                                      simpa only [setKvarFfiHOLFinite, setKvarHOLFinite,
                                        setVarHOLFinite, CrepSemHOLState.setVar] using hcode
                                    · rw [hs1]
                                      simpa only [setKvarFfiHOLFinite, setKvarHOLFinite,
                                        setVarHOLFinite, CrepSemHOLState.setVar] using hexcp
                                    · unfold pcCompileCorrectResultRel
                                      rw [hresN]
                                      exact ⟨rfl, hloc1⟩
                              · have hsrc : res = some .error := by
                                  have h := hrun
                                  simp only [haddress, hlookup] at h
                                  unfold shMemLoadHOLFiniteExact at h
                                  rw [if_pos hnb, if_neg hdom] at h
                                  try simp only [] at h
                                  exact (Prod.mk.inj h).1.symm
                                exact absurd hsrc hres
                            · by_cases hdom : s.shMemaddrs (panByteAlignHOL addr)
                              · have hdomT : t.shMemaddrs (panByteAlignHOL addr) := by
                                  rw [← congrFun hshmema (panByteAlignHOL addr)]; exact hdom
                                cases hcall : callFFIHOL s.ffi (.sharedMem .mappedRead)
                                    [BitVec.ofNat 8 (nbOpHOL operator)]
                                    (panWordToBytesHOL addr false) with
                                | final event =>
                                    have hcallT : callFFIHOL t.ffi (.sharedMem .mappedRead)
                                        [BitVec.ofNat 8 (nbOpHOL operator)]
                                        ((crepClockWordToBytes addr).map UInt8.toBitVec) =
                                        .final event := by
                                      rw [← hffi,
                                        (panWordToBytesHOL_eq_map_crepClockWordToBytes
                                          addr).symm]
                                      exact hcall
                                    have hred : (some (.finalFfi event),
                                          PanSemStateFiniteExact.emptyLocalsHOLFinite s) =
                                        (res, s1) := by
                                      have h := hrun
                                      simp only [haddress, hlookup] at h
                                      unfold shMemLoadHOLFiniteExact at h
                                      rw [if_neg hnb, if_pos hdom, hcall] at h
                                      try simp only [] at h
                                      exact h
                                    have hs1 : s1 =
                                        PanSemStateFiniteExact.emptyLocalsHOLFinite s :=
                                      (Prod.mk.inj hred).2.symm
                                    have hresF : res = some (.finalFfi event) :=
                                      (Prod.mk.inj hred).1.symm
                                    have htargetF : crepShMemLoadExactHOL destination addr
                                        (nbOpHOL operator) t =
                                        (some (.finalFfi event),
                                          CrepSemHOLState.emptyLocals t) := by
                                      unfold crepShMemLoadExactHOL
                                      rw [if_neg hnb, if_pos hdomT, hcallT]
                                    refine ⟨some (.finalFfi event),
                                      CrepSemHOLState.emptyLocals t, ?_, ?_, ?_, ?_, ?_⟩
                                    · rw [hcomp, hbody, htargetF]
                                    · rw [hs1]
                                      simpa only [panToCrepStateRelFiniteExact,
                                        PanSemStateFiniteExact.emptyLocalsHOLFinite,
                                        CrepSemHOLState.emptyLocals] using hstate
                                    · rw [hs1]
                                      simpa only [PanSemStateFiniteExact.emptyLocalsHOLFinite,
                                        CrepSemHOLState.emptyLocals] using hcode
                                    · rw [hs1]
                                      simpa only [PanSemStateFiniteExact.emptyLocalsHOLFinite]
                                        using hexcp
                                    · unfold pcCompileCorrectResultRel
                                      rw [hresF]
                                | ret newFfi newBytes =>
                                    have hcallT : callFFIHOL t.ffi (.sharedMem .mappedRead)
                                        [BitVec.ofNat 8 (nbOpHOL operator)]
                                        ((crepClockWordToBytes addr).map UInt8.toBitVec) =
                                        .ret newFfi newBytes := by
                                      rw [← hffi,
                                        (panWordToBytesHOL_eq_map_crepClockWordToBytes
                                          addr).symm]
                                      exact hcall
                                    have hred : (none, setKvarFfiHOLFinite VarKind.local name
                                        (.val (.word (panWordOfBytesHOL false 0 newBytes)))
                                        s newFfi) = (res, s1) := by
                                      have h := hrun
                                      simp only [haddress, hlookup] at h
                                      unfold shMemLoadHOLFiniteExact at h
                                      rw [if_neg hnb, if_pos hdom, hcall] at h
                                      try simp only [] at h
                                      exact h
                                    have hs1 : s1 = setKvarFfiHOLFinite VarKind.local name
                                        (.val (.word (panWordOfBytesHOL false 0 newBytes)))
                                        s newFfi := (Prod.mk.inj hred).2.symm
                                    have hresN : res = none := (Prod.mk.inj hred).1.symm
                                    have htargetR : crepShMemLoadExactHOL destination addr
                                        (nbOpHOL operator) t =
                                        (none, { CrepSemHOLState.setVar destination
                                          (.word (crepClockWordOfBytes
                                            (newBytes.map UInt8.ofBitVec))) t with
                                          ffi := newFfi }) := by
                                      unfold crepShMemLoadExactHOL
                                      rw [if_neg hnb, if_pos hdomT, hcallT]
                                    have hsource' : shMemLoadHOLFiniteExact s VarKind.local
                                        name addr (nbOpHOL operator) = (none, s1) := by
                                      unfold shMemLoadHOLFiniteExact
                                      rw [if_neg hnb, if_pos hdom, hcall]
                                      rw [hs1]
                                    obtain ⟨hst1, hloc1⟩ :=
                                      shMemLoadHOLFiniteExact_ret_corresponds (source := s)
                                        (target := t) (ctxt := ctxt) (destination := destination)
                                        (name := name) (address := addr) (nb := nbOpHOL operator)
                                        h8 hstate hlocals hvarDest hsource' htargetR
                                    refine ⟨none, { CrepSemHOLState.setVar destination
                                        (.word (crepClockWordOfBytes
                                          (newBytes.map UInt8.ofBitVec))) t with
                                      ffi := newFfi }, ?_, hst1, ?_, ?_, ?_⟩
                                    · rw [hcomp, hbody, htargetR]
                                    · rw [hs1]
                                      simpa only [setKvarFfiHOLFinite, setKvarHOLFinite,
                                        setVarHOLFinite, CrepSemHOLState.setVar] using hcode
                                    · rw [hs1]
                                      simpa only [setKvarFfiHOLFinite, setKvarHOLFinite,
                                        setVarHOLFinite, CrepSemHOLState.setVar] using hexcp
                                    · unfold pcCompileCorrectResultRel
                                      rw [hresN]
                                      exact ⟨rfl, hloc1⟩
                              · have hsrc : res = some .error := by
                                  have h := hrun
                                  simp only [haddress, hlookup] at h
                                  unfold shMemLoadHOLFiniteExact at h
                                  rw [if_neg hnb, if_neg hdom] at h
                                  try simp only [] at h
                                  exact (Prod.mk.inj h).1.symm
                                exact absurd hsrc hres
  · -- `.global`
    simp [localisedProgHOL] at hloc

end Flapjack
