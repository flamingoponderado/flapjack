import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Call
import Flapjack.Pancake.Semantics.ShMemBytesBridge

/-!
# `pc_compile_correct` ShMemStore case over the exact carriers

The `ShMemStore` constructor conjunct of HOL `pc_compile_correct`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, resumed at
`:1960-2011`). The source and target shared-memory primitives are related by
the byte-list/control bridge in `ShMemBytesBridge`; the compiler's temporary
is greater than every variable in the address expression, as in HOL's
`compile_def` at `pan_to_crepScript.sml:291-297`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ProgHOL ExpHOL sizeOfShapeHOL)

private theorem mem_lt_succ_foldr_max (xs : List Nat) (x : Nat) (h : x ∈ xs) :
    x < xs.foldr max 0 + 1 := by
  induction xs with
  | nil => simp at h
  | cons head tail ih =>
      rw [List.foldr_cons]
      rcases List.mem_cons.mp h with rfl | htail
      · exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
      · have ht := ih htail
        exact Nat.lt_of_lt_of_le ht (Nat.add_le_add_right (Nat.le_max_right _ _) 1)

/-- HOL `pc_compile_correct`, `ShMemStore` constructor case
    (`pan_to_crepProofScript.sml:1960-2011`, under the `evaluate_ind`
    conjunct from `:442-468`). Its binders are `op ad e s`; there is no
    induction hypothesis because the two operands use `eval`, not recursive
    `evaluate`. The source evaluator's explicit total branches, exact compiler,
    and exact target evaluator are used below. -/
theorem pcCompileCorrectAt_shMemStore {width : Nat} {σ : Type} [NeZero width]
    (operator : OpSize) (address value : ExpHOL width)
    (s : PanSemStateFiniteExact width σ) :
    pcCompileCorrectAt (.shMemStore operator address value : ProgHOL width) s := by
  classical
  intro res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  have hlocs : localisedExpHOL address = true ∧ localisedExpHOL value = true := by
    simpa [localisedProgHOL] using hloc
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_shMemStore_total] at hrun
  let evalAddress := @evalHOLExact width σ _ s.toExact
    (fun key => Classical.propDecidable (s.memaddrs key)) address
  let evalValue := @evalHOLExact width σ _ s.toExact
    (fun key => Classical.propDecidable (s.memaddrs key)) value
  cases haddress : evalAddress with
  | none =>
      simp only [evalAddress, haddress] at hrun
      exact absurd (Prod.mk.inj hrun).1.symm hres
  | some addressValue =>
      cases addressValue with
      | rStruct fields =>
          simp only [evalAddress, haddress] at hrun
          exact absurd (Prod.mk.inj hrun).1.symm hres
      | nStruct name fields =>
          simp only [evalAddress, haddress] at hrun
          exact absurd (Prod.mk.inj hrun).1.symm hres
      | val addressPayload =>
          cases addressPayload with
          | word addr =>
              cases hvalue : evalValue with
              | none =>
                  simp only [evalAddress, evalValue, haddress, hvalue] at hrun
                  exact absurd (Prod.mk.inj hrun).1.symm hres
              | some valueResult =>
                  cases valueResult with
                  | rStruct fields =>
                      simp only [evalAddress, evalValue, haddress, hvalue] at hrun
                      exact absurd (Prod.mk.inj hrun).1.symm hres
                  | nStruct name fields =>
                      simp only [evalAddress, evalValue, haddress, hvalue] at hrun
                      exact absurd (Prod.mk.inj hrun).1.symm hres
                  | val valuePayload =>
                      cases valuePayload with
                      | word bytes =>
                          let sourceOutput := shMemStoreHOLExact s.toExact bytes addr
                            (nbOpHOL operator)
                          cases hsource : sourceOutput with
                          | mk sourceResult sourcePost =>
                              simp only [evalAddress, evalValue, haddress, hvalue,
                                sourceOutput, hsource] at hrun
                              rcases Prod.mk.inj hrun with ⟨hrunResult, hrunState⟩
                              subst res
                              rcases hcAddress : compileExpExactHOLW ctxt address with
                                ⟨esAddress, shAddress⟩
                              obtain ⟨hmapAddress, _, _, _⟩ :=
                                @compileExpValRelHOL width σ _ s
                                  (fun key => Classical.propDecidable (s.memaddrs key)) ctxt t
                                  (fun key => Classical.propDecidable (t.memaddrs key))
                                  address (.val (.word addr)) esAddress shAddress haddress
                                  hstate hcode hlocals hlocs.1 hcAddress
                              obtain ⟨ceAddress, hceAddress⟩ : ∃ ce, esAddress = [ce] := by
                                rcases esAddress with _ | ⟨ce, _ | ⟨_, _⟩⟩
                                · simp [flattenHOL] at hmapAddress
                                · exact ⟨ce, rfl⟩
                                · simp [flattenHOL] at hmapAddress
                              subst hceAddress
                              have hceAddressEval :
                                  evalCrepSemHOLExp t ceAddress = some (.word addr) := by
                                simpa [flattenHOL] using hmapAddress
                              rcases hcValue : compileExpExactHOLW ctxt value with
                                ⟨esValue, shValue⟩
                              obtain ⟨hmapValue, _, _, _⟩ :=
                                @compileExpValRelHOL width σ _ s
                                  (fun key => Classical.propDecidable (s.memaddrs key)) ctxt t
                                  (fun key => Classical.propDecidable (t.memaddrs key))
                                  value (.val (.word bytes)) esValue shValue hvalue
                                  hstate hcode hlocals hlocs.2 hcValue
                              obtain ⟨ceValue, hceValue⟩ : ∃ ce, esValue = [ce] := by
                                rcases esValue with _ | ⟨ce, _ | ⟨_, _⟩⟩
                                · simp [flattenHOL] at hmapValue
                                · exact ⟨ce, rfl⟩
                                · simp [flattenHOL] at hmapValue
                              subst hceValue
                              have hceValueEval :
                                  evalCrepSemHOLExp t ceValue = some (.word bytes) := by
                                simpa [flattenHOL] using hmapValue
                              let index := (crepExpVarsW (crepExpOfHOL ceAddress)).foldr max 0
                              let temporary := index + 1
                              have hcomp :
                                  compileProgExactHOLW ctxt
                                      (.shMemStore operator address value : ProgHOL width) =
                                    .dec temporary ceValue
                                      (.shMem (storeMemOpHOL operator) temporary ceAddress) := by
                                simp [compileProgExactHOLW, compileShMemStoreExactHOLW,
                                  hcAddress, hcValue, index, temporary]
                              have hvars : crepExpVarsW (crepExpOfHOL ceAddress) =
                                  crepExpVarsHOL ceAddress := by
                                rw [crepExpVarsW_eq_crepExpVarsHOL_crepExpToHOL,
                                  crepExpToHOL_crepExpOfHOL]
                              have hfresh : temporary ∉ crepExpVarsHOL ceAddress := by
                                intro hmem
                                have hmem' : temporary ∈ crepExpVarsW (crepExpOfHOL ceAddress) :=
                                  hvars ▸ hmem
                                have hlt := mem_lt_succ_foldr_max
                                  (crepExpVarsW (crepExpOfHOL ceAddress)) temporary hmem'
                                dsimp [temporary, index] at hlt
                                omega
                              let boundState : CrepSemHOLState width σ :=
                                { t with locals := t.locals.updateEq (temporary, .word bytes) }
                              have hlocal : boundState.locals.lookup temporary = some (.word bytes) := by
                                simp [boundState, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
                              have haddrBound :
                                  evalCrepSemHOLExp boundState ceAddress = some (.word addr) := by
                                rw [evalCrepSemHOLExp_updateLocals_eq_of_not_vars
                                  t ceAddress temporary (.word bytes) hfresh]
                                exact hceAddressEval
                              let targetOutput := crepShMemStoreExactHOL temporary addr
                                (nbOpHOL operator) boundState
                              have hbody : evalCrepSemHOLProgExact boundState
                                  (.shMem (storeMemOpHOL operator) temporary ceAddress) =
                                  targetOutput := by
                                rw [evalCrepSemHOLProgExact_shMem_holShape, haddrBound]
                                rw [hlocal]
                                cases operator <;>
                                  simp [crepIsLoadMemOp, storeMemOpHOL, crepShMemOpExactHOL,
                                    nbOpHOL, targetOutput, boundState,
                                    crepShMemStoreExactHOL]
                              have htarget : evalCrepSemHOLProgExact t
                                  (compileProgExactHOLW ctxt
                                    (.shMemStore operator address value : ProgHOL width)) =
                                  (targetOutput.1,
                                    { targetOutput.2 with
                                      locals := targetOutput.2.locals.resVarEq
                                        (temporary, t.locals.lookup temporary) }) := by
                                rw [hcomp, evalCrepSemHOLProgExact_dec_holShape]
                                simp only [hceValueEval]
                                rw [hbody]
                              have hsourceLocals : sourcePost.locals = s.locals.lookup := by
                                calc
                                  sourcePost.locals = sourceOutput.2.locals := by rw [hsource]
                                  _ = s.locals.lookup := by
                                    have hlocalOut :
                                      (shMemStoreHOLExact s.toExact bytes addr
                                          (nbOpHOL operator)).2.locals = s.locals.lookup := by
                                      unfold shMemStoreHOLExact
                                      split <;> split <;> (try split) <;> rfl
                                    simpa [sourceOutput] using hlocalOut
                              have htargetLocals :
                                  (targetOutput.2.locals.resVarEq
                                    (temporary, t.locals.lookup temporary)).lookup = t.locals.lookup := by
                                have hout : targetOutput.2.locals = boundState.locals := by
                                  have hlocalOut :
                                      (crepShMemStoreExactHOL temporary addr
                                        (nbOpHOL operator) boundState).2.locals = boundState.locals := by
                                    unfold crepShMemStoreExactHOL
                                    rw [hlocal]
                                    split <;> split <;> (try split) <;> (try split) <;> rfl
                                  simpa [targetOutput] using hlocalOut
                                funext key
                                rw [hout]
                                by_cases hkey : key = temporary
                                · subst key
                                  cases hOld : t.locals.lookup temporary <;>
                                    simp [boundState, HolFiniteMapExact.resVarEq,
                                      HolFiniteMapExact.updateEq, FUPDATE_HOL, FDOMSUB_HOL]
                                · cases hOld : t.locals.lookup temporary <;>
                                    simp [boundState, HolFiniteMapExact.resVarEq,
                                      HolFiniteMapExact.updateEq, FUPDATE_HOL, FDOMSUB_HOL,
                                      hkey]
                              have hffiBefore : s.toExact.ffi = boundState.ffi := by
                                exact hstate.2.2.2.2.2.2.2.1
                              have hdom : ∀ a, s.toExact.shMemaddrs a = boundState.shMemaddrs a := by
                                intro a
                                change s.shMemaddrs a = t.shMemaddrs a
                                exact propext (Iff.of_eq (congrFun hstate.2.2.1 a))
                              have hdomEq : s.toExact.shMemaddrs = boundState.shMemaddrs := by
                                change s.shMemaddrs = t.shMemaddrs
                                exact hstate.2.2.1
                              have hffiStep :
                                  (shMemStoreHOLExact s.toExact bytes addr (nbOpHOL operator)).2.ffi =
                                    (crepShMemStoreExactHOL temporary addr (nbOpHOL operator)
                                      boundState).2.ffi := by
                                unfold shMemStoreHOLExact crepShMemStoreExactHOL
                                rw [hffiBefore,
                                  hdomEq,
                                  panWordToBytesHOL_eq_map_crepClockWordToBytes bytes,
                                  panWordToBytesHOL_eq_map_crepClockWordToBytes addr]
                                simp only [List.map_append, ← List.map_take]
                                simp only [boundState]
                                split <;> split <;> split <;>
                                  all_goals (simp_all [boundState] <;> rfl)
                              have hsourceState : sourcePost = sourceOutput.2 := by
                                have h := (Prod.mk.inj hsource).2
                                exact h.symm
                              have hffiAfter : sourcePost.ffi = targetOutput.2.ffi := by
                                calc
                                  sourcePost.ffi = sourceOutput.2.ffi := by rw [hsourceState]
                                  _ = targetOutput.2.ffi := by
                                    simpa [sourceOutput, targetOutput] using hffiStep
                              have hs1Locals : s1.locals.lookup = s.locals.lookup := by
                                rw [← hrunState]
                                simp [PanSemStateFiniteExact.ofExact, hsourceLocals]
                              have hlocalsAfter : panToCrepLocalsRelFiniteExact ctxt s1.locals
                                  (targetOutput.2.locals.resVarEq
                                    (temporary, t.locals.lookup temporary)) := by
                                simpa [panToCrepLocalsRelFiniteExact, hs1Locals,
                                  htargetLocals] using hlocals
                              have hsourceCode : sourcePost.code = s.code.lookup := by
                                rw [hsourceState]
                                unfold sourceOutput shMemStoreHOLExact
                                split <;> split <;> (try split) <;> rfl
                              have hsourceEshapes : sourcePost.eshapes = s.eshapes.lookup := by
                                rw [hsourceState]
                                unfold sourceOutput shMemStoreHOLExact
                                split <;> split <;> (try split) <;> rfl
                              have htargetCode : targetOutput.2.code = t.code := by
                                unfold targetOutput crepShMemStoreExactHOL
                                rw [hlocal]
                                split <;> split <;> (try split) <;> (try split) <;> rfl
                              have hstateAfter : panToCrepStateRelFiniteExact s1
                                  { targetOutput.2 with locals :=
                                      (targetOutput.2.locals.resVarEq
                                        (temporary, t.locals.lookup temporary)) } := by
                                rw [← hrunState]
                                rcases hstate with ⟨hmemory, hmemaddrs, hshmemaddrs, hstructs,
                                  hglobals, hclock, hbe, hffi, hbaseAddr, htopAddr⟩
                                have hsourceMemory : sourcePost.memory = s.memory := by
                                  rw [hsourceState]
                                  unfold sourceOutput shMemStoreHOLExact
                                  split <;> split <;> (try split) <;> rfl
                                have hsourceMemaddrs : sourcePost.memaddrs = s.memaddrs := by
                                  rw [hsourceState]
                                  unfold sourceOutput shMemStoreHOLExact
                                  split <;> split <;> (try split) <;> rfl
                                have hsourceShmem : sourcePost.shMemaddrs = s.shMemaddrs := by
                                  rw [hsourceState]
                                  unfold sourceOutput shMemStoreHOLExact
                                  split <;> split <;> (try split) <;> rfl
                                have hsourceStructs : sourcePost.structs = s.structs := by
                                  rw [hsourceState]
                                  unfold sourceOutput shMemStoreHOLExact
                                  split <;> split <;> (try split) <;> rfl
                                have hsourceGlobals : sourcePost.globals = s.globals.lookup := by
                                  rw [hsourceState]
                                  unfold sourceOutput shMemStoreHOLExact
                                  split <;> split <;> (try split) <;> rfl
                                have hsourceClock : sourcePost.clock = s.clock := by
                                  rw [hsourceState]
                                  unfold sourceOutput shMemStoreHOLExact
                                  split <;> split <;> (try split) <;> rfl
                                have hsourceBe : sourcePost.be = s.be := by
                                  rw [hsourceState]
                                  unfold sourceOutput shMemStoreHOLExact
                                  split <;> split <;> (try split) <;> rfl
                                have hsourceBase : sourcePost.baseAddr = s.baseAddr := by
                                  rw [hsourceState]
                                  unfold sourceOutput shMemStoreHOLExact
                                  split <;> split <;> (try split) <;> rfl
                                have hsourceTop : sourcePost.topAddr = s.topAddr := by
                                  rw [hsourceState]
                                  unfold sourceOutput shMemStoreHOLExact
                                  split <;> split <;> (try split) <;> rfl
                                have htargetMemory : targetOutput.2.memory = t.memory := by
                                  unfold targetOutput crepShMemStoreExactHOL
                                  rw [hlocal]
                                  split <;> split <;> (try split) <;> (try split) <;> rfl
                                have htargetMemaddrs : targetOutput.2.memaddrs = t.memaddrs := by
                                  unfold targetOutput crepShMemStoreExactHOL
                                  rw [hlocal]
                                  split <;> split <;> (try split) <;> (try split) <;> rfl
                                have htargetShmem : targetOutput.2.shMemaddrs = t.shMemaddrs := by
                                  unfold targetOutput crepShMemStoreExactHOL
                                  rw [hlocal]
                                  split <;> split <;> (try split) <;> (try split) <;> rfl
                                have htargetGlobals : targetOutput.2.globals = t.globals := by
                                  unfold targetOutput crepShMemStoreExactHOL
                                  rw [hlocal]
                                  split <;> split <;> (try split) <;> (try split) <;> rfl
                                have htargetClock : targetOutput.2.clock = t.clock := by
                                  unfold targetOutput crepShMemStoreExactHOL
                                  rw [hlocal]
                                  split <;> split <;> (try split) <;> (try split) <;> rfl
                                have htargetBe : targetOutput.2.be = t.be := by
                                  unfold targetOutput crepShMemStoreExactHOL
                                  rw [hlocal]
                                  split <;> split <;> (try split) <;> (try split) <;> rfl
                                have htargetBase : targetOutput.2.baseAddr = t.baseAddr := by
                                  unfold targetOutput crepShMemStoreExactHOL
                                  rw [hlocal]
                                  split <;> split <;> (try split) <;> (try split) <;> rfl
                                have htargetTop : targetOutput.2.topAddr = t.topAddr := by
                                  unfold targetOutput crepShMemStoreExactHOL
                                  rw [hlocal]
                                  split <;> split <;> (try split) <;> (try split) <;> rfl
                                change sourcePost.memory = targetOutput.2.memory ∧
                                  sourcePost.memaddrs = targetOutput.2.memaddrs ∧
                                  sourcePost.shMemaddrs = targetOutput.2.shMemaddrs ∧
                                  sourcePost.structs = [] ∧ sourcePost.globals = (fun _ => none) ∧
                                  sourcePost.clock = targetOutput.2.clock ∧ sourcePost.be = targetOutput.2.be ∧
                                  sourcePost.ffi = targetOutput.2.ffi ∧
                                  sourcePost.baseAddr = targetOutput.2.baseAddr ∧
                                  sourcePost.topAddr = targetOutput.2.topAddr
                                exact ⟨hsourceMemory.trans (hmemory.trans htargetMemory.symm),
                                  hsourceMemaddrs.trans (hmemaddrs.trans htargetMemaddrs.symm),
                                  hsourceShmem.trans (hshmemaddrs.trans htargetShmem.symm),
                                  hsourceStructs.trans hstructs,
                                  hsourceGlobals.trans hglobals,
                                  hsourceClock.trans (hclock.trans htargetClock.symm),
                                  hsourceBe.trans (hbe.trans htargetBe.symm), hffiAfter,
                                  hsourceBase.trans (hbaseAddr.trans htargetBase.symm),
                                  hsourceTop.trans (htopAddr.trans htargetTop.symm)⟩
                              have hcodeAfter : codeRelExactHOLW ctxt s1.code
                                  ({ targetOutput.2 with locals :=
                                    (targetOutput.2.locals.resVarEq
                                      (temporary, t.locals.lookup temporary)) }).code := by
                                have hsourceCodeLookup : s1.code.lookup = s.code.lookup := by
                                  rw [← hrunState]
                                  simpa [PanSemStateFiniteExact.ofExact] using hsourceCode
                                have htargetCodeLookup :
                                    ({ targetOutput.2 with locals :=
                                      (targetOutput.2.locals.resVarEq
                                        (temporary, t.locals.lookup temporary)) }).code.lookup =
                                      t.code.lookup := by
                                  change targetOutput.2.code.lookup = t.code.lookup
                                  rw [htargetCode]
                                unfold codeRelExactHOLW at *
                                rw [hsourceCodeLookup, htargetCodeLookup]
                                exact hcode
                              have hexcpAfter : panToCrepExcpRelFiniteExact ctxt.eids s1.eshapes := by
                                rw [← hrunState]
                                simp only [panToCrepExcpRelFiniteExact,
                                  PanSemStateFiniteExact.ofExact]
                                rw [hsourceEshapes]
                                exact hexcp
                              have hcontrol := shMemStoreHOLExact_control_corresponds
                                s.toExact boundState bytes temporary addr (nbOpHOL operator)
                                hffiBefore hdom hlocal
                              let targetPost : CrepSemHOLState width σ :=
                                { targetOutput.2 with locals :=
                                  (HolFiniteMapExact.resVarEq targetOutput.2.locals
                                    (temporary, t.locals.lookup temporary)) }
                              have htargetPost : evalCrepSemHOLProgExact t
                                  (compileProgExactHOLW ctxt
                                    (.shMemStore operator address value : ProgHOL width)) =
                                  (targetOutput.1, targetPost) := by
                                simpa [targetPost] using htarget
                              have hsourceFst : sourceOutput.1 = sourceResult :=
                                (Prod.mk.inj hsource).1
                              have hsourceResult : ∀ result,
                                  (shMemStoreHOLExact s.toExact bytes addr
                                    (nbOpHOL operator)).1 = result → sourceResult = result := by
                                intro result hresult
                                have hresult' : sourceOutput.1 = result := by
                                  simpa [sourceOutput] using hresult
                                exact hsourceFst.symm.trans hresult'
                              have htargetResult : ∀ result,
                                  (crepShMemStoreExactHOL temporary addr
                                    (nbOpHOL operator) boundState).1 = result →
                                      targetOutput.1 = result := by
                                intro result hresult
                                simpa [targetOutput] using hresult
                              rcases hcontrol with ⟨event, hsourceFinal, htargetFinal⟩ |
                                ⟨hsourceError, _⟩ | ⟨hsourceNone, htargetNone⟩
                              · have hresFinal := hsourceResult _ hsourceFinal
                                have htFinal := htargetResult _ htargetFinal
                                refine ⟨some (.finalFfi event), targetPost, ?_, ?_, ?_, ?_, ?_⟩
                                · simpa [targetPost, htFinal] using htargetPost
                                · simpa [targetPost] using hstateAfter
                                · simpa [targetPost] using hcodeAfter
                                · exact hexcpAfter
                                · simp [pcCompileCorrectResultRel, hresFinal]
                              · have hresError := hsourceResult _ hsourceError
                                exact False.elim (hres hresError)
                              · have hresNone := hsourceResult _ hsourceNone
                                have htNone := htargetResult _ htargetNone
                                refine ⟨none, targetPost, ?_, ?_, ?_, ?_, ?_⟩
                                · simpa [targetPost, htNone] using htargetPost
                                · simpa [targetPost] using hstateAfter
                                · simpa [targetPost] using hcodeAfter
                                · exact hexcpAfter
                                · rw [hresNone]
                                  change none = none ∧
                                  panToCrepLocalsRelFiniteExact ctxt s1.locals targetPost.locals
                                  exact ⟨rfl, by simpa [targetPost] using hlocalsAfter⟩

namespace PcCompileCorrectShMemStoreWitnesses

/-! Same-module canonical relation witnesses for the carriers qualified by the
tagged ShMemStore case. -/

theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  CallPreservationFiniteMapWitnesses.holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact

theorem holFmapAsFiniteSupportRelationWitness_PanToCrepContextExact
    {width : Nat} [NeZero width] (context : PanToCrepContextExact width) :
    PanToCrepContextExact.ofBroad (PanToCrepContextExact.toBroad context) = context :=
  CallPreservationFiniteMapWitnesses.holFmapAsFiniteSupportRelationWitness_PanToCrepContextExact
    context

theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state :=
  CallPreservationFiniteMapWitnesses.holFmapAsFiniteSupportRelationWitness_CrepSemHOLState state

end PcCompileCorrectShMemStoreWitnesses

/-- Exact HOL `pc_compile_correct[ShMemStore]` case, resumed at
    `pan_to_crepProofScript.sml:1960-1989`. HOL's `ShMemStore op ad e`
    evaluator evaluates `ad` as the address and `e` as the stored word; the
    compiler stores the compiled `e` in a fresh local above every variable in
    the compiled `ad`, then executes `ShMem (store_op op) temp ad`. The exact
    source and target definitions used by the proof above follow these clauses.
    The carrier qualifiers are the same finite-map and positive-word
    translations reviewed for the exact `Store` case, with local canonical
    witnesses above. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pc_compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, PanToCrepContextExact.vars, PanToCrepContextExact.funcs,
    PanToCrepContextExact.eids])
  (words_as_type_indexed_bitvec)]
theorem pcCompileCorrect_ShMemStore {width : Nat} {σ : Type} [NeZero width] :
    ∀ (operator : OpSize) (address value : ExpHOL width)
      (s : PanSemStateFiniteExact width σ)
      (res : Option (PanSemResultExact width))
      (s1 : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
      (ctxt : PanToCrepContextExact width),
      s.evaluateHOLFiniteState (.shMemStore operator address value : ProgHOL width) = (res, s1) ∧
        res ≠ some .error ∧ panToCrepStateRelFiniteExact s t ∧
        codeRelExactHOLW ctxt s.code t.code ∧
        panToCrepExcpRelFiniteExact ctxt.eids s.eshapes ∧
        panToCrepLocalsRelFiniteExact ctxt s.locals t.locals ∧
        localisedProgHOL (.shMemStore operator address value : ProgHOL width) = true →
      ∃ (res1 : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ),
        evalCrepSemHOLProgExact t
            (compileProgExactHOLW ctxt (.shMemStore operator address value : ProgHOL width)) =
          (res1, t1) ∧
        panToCrepStateRelFiniteExact s1 t1 ∧ codeRelExactHOLW ctxt s1.code t1.code ∧
        panToCrepExcpRelFiniteExact ctxt.eids s1.eshapes ∧
        match res with
        | none => res1 = none ∧ panToCrepLocalsRelFiniteExact ctxt s1.locals t1.locals
        | some .error => False
        | some .timeOut => res1 = some .timeOut
        | some .break =>
            res1 = some (.break 0) ∧ panToCrepLocalsRelFiniteExact ctxt s1.locals t1.locals
        | some .continue =>
            res1 = some (.continue 0) ∧ panToCrepLocalsRelFiniteExact ctxt s1.locals t1.locals
        | some (.returned rv) => res1 = some (.return (flattenHOL rv))
        | some (.exception eid v') =>
            (match ctxt.eids.lookup eid with
             | none => False
             | some n =>
                 res1 = some (.exception n) ∧
                 (1 ≤ sizeOfShapeHOL (shapeOfHOLExact v') →
                   globalsLookupHOL t1 v' = some (flattenHOL v') ∧
                     sizeOfShapeHOL (shapeOfHOLExact v') ≤ 32))
        | some (.finalFfi f) => res1 = some (.finalFfi f) := by
  intro operator address value s res s1 t ctxt
    ⟨hrun, hres, hstate, hcode, hexcp, hlocals, hloc⟩
  obtain ⟨res1, t1, h1, h2, h3, h4, h5⟩ :=
    pcCompileCorrectAt_shMemStore operator address value s res s1 t ctxt
      hrun hres hstate hcode hexcp hlocals hloc
  refine ⟨res1, t1, h1, h2, h3, h4, ?_⟩
  rcases res with _ | r
  · exact h5
  · cases r <;> exact h5

end Flapjack
