import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.ShMem
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace Flapjack

open Flapjack.Pancake.PanLang
open PanSemStateFiniteExact

namespace PanGlobalsCompileCorrectShMemGlobalWitnesses

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

end PanGlobalsCompileCorrectShMemGlobalWitnesses

namespace PanGlobalsCompileCorrect

open Flapjack.PanGlobalsMemStores
open Flapjack.Compiler.Backend.StackRemove (addresses)
open Flapjack.Basis.Pure.MlString (ofString)

/-- Flapjack-only support: applying a singleton `mem_stores` update. -/
theorem panMemStoresHOL_singleton_apply {width : Nat} [NeZero width]
    (addr : RiscV.Word width) (v : HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (memory : RiscV.Word width → HolWordLab width) (m : RiscV.Word width → HolWordLab width)
    (h : panMemStoresHOL addr [v] domain memory = some m) :
    ∀ x, m x = if x = addr then v else memory x := by
  classical
  rw [panMemStoresHOL] at h
  split at h
  · rename_i updated hupd
    rw [panMemStoresHOL_nil] at h
    have hu : updated = fun x => if x = addr then v else memory x := by
      rw [panMemStoreHOL] at hupd
      split at hupd
      · exact (Option.some.inj hupd).symm
      · exact absurd hupd (by simp)
    have hm : updated = m := Option.some.inj h
    intro x
    rw [← hm]
    exact congrFun hu x
  · exact absurd h (by simp)

/-- Flapjack-only support: the two canonical update interfaces agree at the
    executable (Boolean `BEq`) and HOL-equality (`DecidableEq`) renderings. -/
private theorem updateEq_eq_update {width : Nat} [NeZero width]
    (m : HolFiniteMapExact MlS (ValueHOL width)) (e : MlS × ValueHOL width) :
    m.updateEq e = m.update e := by
  apply HolFiniteMapExact.ext
  funext key
  simp only [HolFiniteMapExact.lookup_updateEq, HolFiniteMapExact.lookup_update,
    FUPDATE_HOL_eq_FUPDATE]

/-- Flapjack-only support: `setVarHOLFinite` in the HOL-equality update form. -/
private theorem setVarEq {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (name : MlS) (value : ValueHOL width) :
    setVarHOLFinite name value state =
      {state with locals := state.locals.updateEq (name, value)} := by
  simp only [setVarHOLFinite, updateEq_eq_update]

/-- Flapjack-only support: a later update shadows an earlier one at the same
    key. -/
private theorem updateSameEq {width : Nat} [NeZero width]
    (m : HolFiniteMapExact MlS (ValueHOL width)) (name : MlS)
    (first second : ValueHOL width) :
    (m.updateEq (name, first)).updateEq (name, second) = m.updateEq (name, second) := by
  apply HolFiniteMapExact.ext
  funext key
  by_cases h : key = name <;>
    simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, h]

/-- Flapjack-only support: restoring the original binding after an update at the
    same key. -/
private theorem resVarEq_updateEq {width : Nat} [NeZero width]
    (m : HolFiniteMapExact MlS (ValueHOL width)) (k : MlS) (v : ValueHOL width)
    (old : Option (ValueHOL width)) :
    HolFiniteMapExact.resVarEq (m.updateEq (k, v)) (k, old) =
      match old with
      | some x => m.updateEq (k, x)
      | none => m.eraseEq k := by
  cases old with
  | none =>
      simp only [HolFiniteMapExact.resVarEq, HolFiniteMapExact.eraseEq]
      apply HolFiniteMapExact.ext
      funext key
      by_cases h : key = k <;>
        simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, FDOMSUB_HOL, h]
  | some x =>
      simp only [HolFiniteMapExact.resVarEq, updateSameEq]

/-- Flapjack-only support: updating a key with the value it already holds is the
    identity. -/
private theorem updateEq_self {width : Nat} [NeZero width]
    (m : HolFiniteMapExact MlS (ValueHOL width)) (k : MlS) (v : ValueHOL width)
    (h : m.lookup k = some v) : m.updateEq (k, v) = m := by
  apply HolFiniteMapExact.ext
  funext key
  by_cases hk : key = k
  · subst hk; simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, h]
  · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hk]

/-- Flapjack-only support: erasing an absent key is the identity. -/
private theorem eraseEq_self {width : Nat} [NeZero width]
    (m : HolFiniteMapExact MlS (ValueHOL width)) (k : MlS)
    (h : m.lookup k = none) : m.eraseEq k = m := by
  apply HolFiniteMapExact.ext
  funext key
  by_cases hk : key = k
  · subst hk; simp [HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL, h]
  · simp [HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL, hk]

/-- Flapjack-only support: a successful `ShMemLoad` global-write updates the
    source `globals` map (`set_global name loaded`) and the target `memory` at
    `top_addr - gaddr`, preserving the pan_globals relation.  HOL inlines this
    argument in `Resume compile_correct[ShMemLoad]`; no separate HOL
    declaration exists. -/
theorem stateRelGlobalWriteHOL {width : Nat} {σ : Type} [NeZero width]
    (ctxt : PanGlobalsContextExact width)
    (s t : PanSemStateFiniteExact width σ)
    (hrel : panGlobalsStateRelHOLExact true ctxt s t)
    (name : MlS) (w : BitVec width) (gaddr : BitVec width)
    (hctxt : ctxt.globals.lookup name = some (.one, gaddr))
    (hsrc : s.globals.lookup name ≠ none)
    (newMemory : RiscV.Word width → HolWordLab width)
    (hmem : @panMemStoresHOL width _ (t.topAddr - gaddr) [HolWordLab.word w] t.memaddrs
      (fun a => Classical.propDecidable (t.memaddrs a)) t.memory = some newMemory) :
    panGlobalsStateRelHOLExact true ctxt
      (setGlobalHOLFinite name (.val (.word w)) s)
      {t with memory := newMemory} := by
  classical
  obtain ⟨htop, hloc, hbase, hbe, hesh, hclock, hstructS, hstructT, hglob, hwf, hsub,
    hshmem, hmemAgree, hffi, hcode, hdisj, htopmem, halign, hgood⟩ := hrel
  have hunfold : ∀ n, (setGlobalHOLFinite name (.val (.word w)) s).globals.lookup n =
      (if n = name then some (.val (.word w)) else s.globals.lookup n) := by
    intro n
    simp only [setGlobalHOLFinite]
    show (s.globals.update (name, .val (.word w))).lookup n = _
    rw [HolFiniteMapExact.lookup_update]
    rw [show FUPDATE s.globals.lookup (name, .val (.word w)) n =
        FUPDATE_HOL s.globals.lookup (name, .val (.word w)) n from
          (congrFun (FUPDATE_HOL_eq_FUPDATE _ _) n).symm]
    rfl
  obtain ⟨oldValue, hsold⟩ : ∃ v, s.globals.lookup name = some v := by
    cases h : s.globals.lookup name with
    | none => exact absurd h hsrc
    | some v => exact ⟨v, rfl⟩
  obtain ⟨a0, hctx0, _hwf0, _hload0, hdis0, halign0⟩ := hglob name oldValue hsold
  have hpair : (shapeOfHOLExact oldValue, a0) = (.one, gaddr) :=
    Option.some.inj (hctx0.symm.trans hctxt)
  have hshape0 : shapeOfHOLExact oldValue = .one := (Prod.mk.inj hpair).1
  have ha0 : a0 = gaddr := (Prod.mk.inj hpair).2
  have hstoreApply := panMemStoresHOL_singleton_apply (t.topAddr - gaddr) (HolWordLab.word w)
    t.memaddrs t.memory newMemory hmem
  have hstoreDisj : ∀ slot, s.memaddrs slot → ¬ addresses (t.topAddr - gaddr) 1 slot := by
    intro slot hslot
    have := hdis0 slot hslot
    simpa [ha0, hshape0] using this
  have hflat : flattenHOL (.val (.word w) : ValueHOL width) = [HolWordLab.word w] := by
    simp [flattenHOL]
  have hbound : (flattenHOL (.val (.word w) : ValueHOL width)).length *
      (panBytesInWord width).toNat < 2 ^ width := by
    rw [hflat]
    simp only [List.length_singleton, Nat.one_mul]
    unfold panBytesInWord
    rcases hgood with rfl | rfl <;> decide
  have hwfOne : isWfShapeExactHOL ([] : StructContextExact)
      (shapeOfHOLExact (.val (.word w) : ValueHOL width)) = true := by
    simp [shapeOfHOLExact]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show s.topAddr = t.topAddr - ctxt.maxGlobalsSize
    exact htop
  · intro _
    show s.locals = t.locals
    exact hloc rfl
  · show s.baseAddr = t.baseAddr
    exact hbase
  · show s.be = t.be
    exact hbe
  · show s.eshapes = t.eshapes
    exact hesh
  · show s.clock = t.clock
    exact hclock
  · show s.structs = ([] : StructContextExact)
    exact hstructS
  · show t.structs = ([] : StructContextExact)
    exact hstructT
  · intro nm value hlookup
    rw [hunfold nm] at hlookup
    by_cases hnm : nm = name
    · subst hnm
      rw [if_pos rfl] at hlookup
      obtain rfl : value = .val (.word w) := (Option.some.inj hlookup).symm
      refine ⟨gaddr, by simpa only [shapeOfHOLExact] using hctxt, hwfOne, ?_, ?_, ?_⟩
      · exact (memStoresMemLoadBackHOL.1 (.val (.word w)) (t.topAddr - gaddr) t.memaddrs
          t.memory newMemory [] ⟨by rw [hflat]; exact hmem, hbound, hwfOne, rfl, hgood⟩)
      · intro slot hslot
        simpa only [shapeOfHOLExact, sizeOfShapeHOL_one] using hstoreDisj slot hslot
      · exact ha0 ▸ halign0
    · rw [if_neg hnm] at hlookup
      obtain ⟨addr', hctx', hwf', hload', hdis', halign'⟩ := hglob nm value hlookup
      have hnme : name ≠ nm := fun h => hnm h.symm
      have hnmnone : s.globals.lookup nm ≠ none := by rw [hlookup]; exact Option.some_ne_none _
      have hdisjoint : ∀ x, addresses (t.topAddr - addr')
          (sizeOfShapeHOL (shapeOfHOLExact value)) x →
          ¬ addresses (t.topAddr - gaddr)
            ([HolWordLab.word w] : List (HolWordLab width)).length x := by
        intro x hx hstore
        exact hdisj name nm .one gaddr (shapeOfHOLExact value) addr' hnme hsrc hnmnone
          hctxt hctx' x ⟨by simpa [List.length_singleton, sizeOfShapeHOL_one] using hstore, hx⟩
      refine ⟨addr', hctx', hwf', ?_, hdis', halign'⟩
      rw [memStoresLoadDisjointHOL.1 (shapeOfHOLExact value) (t.topAddr - gaddr)
        [HolWordLab.word w] t.memaddrs t.memory newMemory [] (t.topAddr - addr')
        ⟨hmem, rfl, hwf', hdisjoint⟩]
      exact hload'
  · exact hwf
  · intro a ha
    exact hsub a ha
  · show s.shMemaddrs = t.shMemaddrs
    exact hshmem
  · intro a ha
    change s.memory a = newMemory a
    rw [hstoreApply a]
    by_cases hlt : a = t.topAddr - gaddr
    · have hmem : addresses (t.topAddr - gaddr) 1 a := by rw [hlt]; exact Or.inl rfl
      exact absurd hmem (hstoreDisj a ha)
    · rw [if_neg hlt]
      exact hmemAgree a ha
  · show s.ffi = t.ffi
    exact hffi
  · intro function parameters program returnShape hcode'
    exact hcode function parameters program returnShape hcode'
  · intro n1 n2 sh1 ad1 sh2 ad2 hne hn1 hn2 hc1 hc2 slot
    rw [hunfold n1] at hn1
    rw [hunfold n2] at hn2
    by_cases h1 : n1 = name
    · rw [h1] at hn1 hne hc1
      rw [if_pos rfl] at hn1
      have h2 : ¬ (n2 = name) := fun h => hne h.symm
      rw [if_neg h2] at hn2
      have hp1 : (sh1, ad1) = (.one, gaddr) := Option.some.inj (hc1.symm.trans hctxt)
      rw [(Prod.mk.inj hp1).1, (Prod.mk.inj hp1).2]
      exact hdisj name n2 .one gaddr sh2 ad2 hne hsrc hn2 hctxt hc2 slot
    · by_cases h2 : n2 = name
      · rw [h2] at hn2 hne hc2
        rw [if_pos rfl] at hn2
        rw [if_neg h1] at hn1
        have hp2 : (sh2, ad2) = (.one, gaddr) := Option.some.inj (hc2.symm.trans hctxt)
        rw [(Prod.mk.inj hp2).1, (Prod.mk.inj hp2).2]
        exact hdisj n1 name sh1 ad1 .one gaddr hne hn1 hsrc hc1 hctxt slot
      · rw [if_neg h1] at hn1
        rw [if_neg h2] at hn2
        exact hdisj n1 n2 sh1 ad1 sh2 ad2 hne hn1 hn2 hc1 hc2 slot
  · show ¬ t.memaddrs t.topAddr
    exact htopmem
  · show panGlobalsByteAlignedHOL t.topAddr
    exact halign
  · exact hgood

/-- Flapjack-only support: restoring after an update at the same key when the
    saved binding is exactly the original lookup. -/
private theorem resVarEq_updateEq_of_lookup {width : Nat} [NeZero width]
    (m : HolFiniteMapExact MlS (ValueHOL width)) (k : MlS) (v : ValueHOL width)
    (old : Option (ValueHOL width)) (h : m.lookup k = old) :
    HolFiniteMapExact.resVarEq (m.updateEq (k, v)) (k, old) = m := by
  rw [resVarEq_updateEq]
  cases old with
  | none => exact eraseEq_self m k h
  | some x => exact updateEq_self m k x h

/-- Flapjack-only support: the `BEq` update form of
    `resVarEq_updateEq_of_lookup`. -/
private theorem resVarEq_update_of_lookup {width : Nat} [NeZero width]
    (m : HolFiniteMapExact MlS (ValueHOL width)) (k : MlS) (v : ValueHOL width)
    (old : Option (ValueHOL width)) (h : m.lookup k = old) :
    HolFiniteMapExact.resVarEq (m.update (k, v)) (k, old) = m := by
  rw [← updateEq_eq_update]
  exact resVarEq_updateEq_of_lookup m k v old h

/-- Flapjack-only support: the lookup of `setVarHOLFinite`. -/
private theorem lookup_setVarHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (name : MlS) (value : ValueHOL width)
    (key : MlS) :
    (setVarHOLFinite name value state).locals.lookup key =
      if key = name then some value else state.locals.lookup key := by
  by_cases h : key = name
  · subst h
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · have hne : (name == key) = false := by
      rw [Bool.eq_false_iff]
      intro hb
      exact h (beq_iff_eq.mp hb).symm
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, h]

/-- Flapjack-only support: the relation at flag `false` ignores both `locals`
    fields, so it is invariant under replacing them. -/
theorem stateRelFlagFalse_changeLocals {width : Nat} {σ : Type} [NeZero width]
    (ctxt : PanGlobalsContextExact width) (s t : PanSemStateFiniteExact width σ)
    (sLocals tLocals : HolFiniteMapExact MlS (ValueHOL width)) :
    panGlobalsStateRelHOLExact false ctxt s t →
    panGlobalsStateRelHOLExact false ctxt
      {s with locals := sLocals} {t with locals := tLocals} := by
  intro hrel
  obtain ⟨h1, _, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19⟩ := hrel
  exact ⟨h1, (fun hf => absurd hf (by simp)), h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19⟩

/-- Flapjack-only support: the exact evaluation of `TopAddr - gaddr`. -/
private theorem evalHOLExact_sub_topAddr {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (gaddr : RiscV.Word width) :
    @evalHOLExact width σ _ state _
      (.op .sub [.topAddr, .const gaddr]) = some (.val (.word (state.topAddr - gaddr))) := rfl

/-- Flapjack-only support: the compiled global `ShMemLoad` store step, on the
    return branch of the internal shared-memory load. -/
private theorem evalStore_globalRet {width : Nat} {σ : Type} [NeZero width]
    (t : PanSemStateFiniteExact width σ) (name : MlS) (addr gaddr wL : RiscV.Word width)
    (newFfi : HolFfiState σ) (newMemory : RiscV.Word width → HolWordLab width)
    (hmem : @panMemStoresHOL width _ (t.topAddr - gaddr) [HolWordLab.word wL] t.memaddrs
      (fun a => Classical.propDecidable (t.memaddrs a)) t.memory = some newMemory) :
    evaluateHOLFiniteState
        (setKvarFfiHOLFinite .local (mlstrAppend name (ofString "'")) (.val (.word wL))
          (setVarHOLFinite (mlstrAppend name (ofString "'")) (.val (.word (BitVec.ofNat width 0)))
            (setVarHOLFinite name (.val (.word addr)) t)) newFfi)
        (.store (.op .sub [.topAddr, .const gaddr])
          (.var .local (mlstrAppend name (ofString "'")))) =
      (none,
        {setKvarFfiHOLFinite .local (mlstrAppend name (ofString "'")) (.val (.word wL))
          (setVarHOLFinite (mlstrAppend name (ofString "'")) (.val (.word (BitVec.ofNat width 0)))
            (setVarHOLFinite name (.val (.word addr)) t)) newFfi with memory := newMemory}) := by
  classical
  rw [evaluateHOLFiniteState_store]
  dsimp only
  have hdst : @evalHOLExact width σ _
      (setKvarFfiHOLFinite .local (mlstrAppend name (ofString "'")) (.val (.word wL))
        (setVarHOLFinite (mlstrAppend name (ofString "'")) (.val (.word (BitVec.ofNat width 0)))
          (setVarHOLFinite name (.val (.word addr)) t)) newFfi).toExact
      (fun a => Classical.propDecidable
        ((setKvarFfiHOLFinite .local (mlstrAppend name (ofString "'")) (.val (.word wL))
          (setVarHOLFinite (mlstrAppend name (ofString "'")) (.val (.word (BitVec.ofNat width 0)))
            (setVarHOLFinite name (.val (.word addr)) t)) newFfi).memaddrs a))
      (.op .sub [.topAddr, .const gaddr]) =
      some (.val (.word (t.topAddr - gaddr))) := by
    rw [evalHOLExact_sub_topAddr]
    rfl
  have hsrc : @evalHOLExact width σ _
      (setKvarFfiHOLFinite .local (mlstrAppend name (ofString "'")) (.val (.word wL))
        (setVarHOLFinite (mlstrAppend name (ofString "'")) (.val (.word (BitVec.ofNat width 0)))
          (setVarHOLFinite name (.val (.word addr)) t)) newFfi).toExact
      (fun a => Classical.propDecidable
        ((setKvarFfiHOLFinite .local (mlstrAppend name (ofString "'")) (.val (.word wL))
          (setVarHOLFinite (mlstrAppend name (ofString "'")) (.val (.word (BitVec.ofNat width 0)))
            (setVarHOLFinite name (.val (.word addr)) t)) newFfi).memaddrs a))
      (.var .local (mlstrAppend name (ofString "'"))) = some (.val (.word wL)) := by
    show (setKvarFfiHOLFinite .local (mlstrAppend name (ofString "'")) (.val (.word wL))
        (setVarHOLFinite (mlstrAppend name (ofString "'")) (.val (.word (BitVec.ofNat width 0)))
          (setVarHOLFinite name (.val (.word addr)) t)) newFfi).locals.lookup
        (mlstrAppend name (ofString "'")) = some (.val (.word wL))
    simp only [setKvarFfiHOLFinite, setKvarHOLFinite, lookup_setVarHOLFinite, if_true]
  rw [hdst, hsrc]
  simp only [setKvarFfiHOLFinite, setKvarHOLFinite, setVarHOLFinite, flattenHOL]
  rw [hmem]

/-- Flapjack-only support: the two `Dec`-restores of the compiled global
    `ShMemLoad` return `locals` to the original map. -/
private theorem localsRestoreGlobal {width : Nat} {σ : Type} [NeZero width]
    (t : PanSemStateFiniteExact width σ) (name name' : MlS)
    (vaddr w0 wL : ValueHOL width) :
    HolFiniteMapExact.resVarEq
      (HolFiniteMapExact.resVarEq
        (((t.locals.updateEq (name, vaddr)).updateEq (name', w0)).updateEq (name', wL))
        (name', (t.locals.updateEq (name, vaddr)).lookup name'))
      (name, t.locals.lookup name) = t.locals := by
  rw [updateSameEq]
  rw [resVarEq_updateEq_of_lookup _ name' wL _ rfl]
  rw [resVarEq_updateEq_of_lookup _ name vaddr _ rfl]

/-- Flapjack-only support: the compiled global `ShMemLoad` target post-state on
    the return branch is the original target with only `memory` and `ffi`
    updated. -/
private theorem globalRetTarget_eq {width : Nat} {σ : Type} [NeZero width]
    (t : PanSemStateFiniteExact width σ) (name : MlS) (addr : RiscV.Word width)
    (wL : RiscV.Word width) (newFfi : HolFfiState σ)
    (newMemory : RiscV.Word width → HolWordLab width) :
    ({setKvarFfiHOLFinite .local (mlstrAppend name (ofString "'")) (.val (.word wL))
        (setVarHOLFinite (mlstrAppend name (ofString "'")) (.val (.word (BitVec.ofNat width 0)))
          (setVarHOLFinite name (.val (.word addr)) t)) newFfi with
      memory := newMemory,
      locals := HolFiniteMapExact.resVarEq
        (HolFiniteMapExact.resVarEq
          (setKvarFfiHOLFinite .local (mlstrAppend name (ofString "'")) (.val (.word wL))
            (setVarHOLFinite (mlstrAppend name (ofString "'")) (.val (.word (BitVec.ofNat width 0)))
              (setVarHOLFinite name (.val (.word addr)) t)) newFfi).locals
          (mlstrAppend name (ofString "'"),
            (setVarHOLFinite name (.val (.word addr)) t).locals.lookup
              (mlstrAppend name (ofString "'"))))
        (name, t.locals.lookup name)}) =
    {t with memory := newMemory, ffi := newFfi} := by
  have hl := localsRestoreGlobal t name (mlstrAppend name (ofString "'"))
    (.val (.word addr)) (.val (.word (BitVec.ofNat width 0))) (.val (.word wL))
  simp only [setKvarFfiHOLFinite, setKvarHOLFinite, setVarEq] at hl ⊢
  rw [hl]

/-- Target-evaluation computation for the compiled global `ShMemLoad`: the
    nested `Dec`/`Dec`/`Seq`/`ShMemLoad`/`Store` lowering.  The outer `Dec`
    binds the compiled address to `name`, the inner binds a zero to the generated
    temporary `name'`, the local load reads shared memory and the store writes
    the loaded word to the global's memory block, and the two `Dec`-restores
    return the temporary locals to their saved bindings. -/
theorem evaluateHOLFiniteState_compile_shMemLoad_global {width : Nat} {σ : Type}
    [NeZero width] (ctxt : PanGlobalsContextExact width)
    (t : PanSemStateFiniteExact width σ) (op : OpSize) (name : MlS)
    (address : ExpHOL width) (addr gaddr : RiscV.Word width)
    (haddrT : @PanSemStateFiniteExact.evalHOLFinite width σ _ t
      (fun a => Classical.propDecidable (t.memaddrs a))
      (compileExpExactHOL ctxt address) = some (.val (.word addr)))
    (hctxt : ctxt.globals.lookup name = some (.one, gaddr)) :
    evaluateHOLFiniteState t
        (compileProgExactHOL ctxt (.shMemLoad op .global name address)) =
      (let name' := mlstrAppend name (ofString "'")
       let t2 := setVarHOLFinite name' (.val (.word (BitVec.ofNat width 0)))
          (setVarHOLFinite name (.val (.word addr)) t)
       let loaded := @shMemLoadHOLFiniteExact width σ _ t2
          (fun a => Classical.propDecidable (t2.shMemaddrs a)) .local name' addr (nbOpHOL op)
       let wrapLocals := fun (st : PanSemStateFiniteExact width σ) =>
          {st with
            locals := HolFiniteMapExact.resVarEq
              (HolFiniteMapExact.resVarEq st.locals
                (name', (setVarHOLFinite name (.val (.word addr)) t).locals.lookup name'))
              (name, t.locals.lookup name)}
       match loaded.1 with
       | none =>
           (let storeOutput := evaluateHOLFiniteState loaded.2
              (.store (.op .sub [.topAddr, .const gaddr]) (.var .local name'))
            (storeOutput.1, wrapLocals storeOutput.2))
       | some r => (some r, wrapLocals loaded.2)) := by
  classical
  simp only [compileProgExactHOL, hctxt]
  have haddrExact : @evalHOLExact width σ _ t.toExact
      (fun a => Classical.propDecidable (t.memaddrs a))
      (compileExpExactHOL ctxt address) = some (.val (.word addr)) := haddrT
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [haddrExact]
  simp only [shapeOfHOLExact, shapeEqHOL, if_true]
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  simp only [evalHOLExact]
  simp only [shapeOfHOLExact, shapeEqHOL, if_true]
  rw [evaluateHOLFiniteState_seq_line780]
  rw [evaluateHOLFiniteState_shMemLoad_source]
  dsimp only
  simp only [PanSemStateFiniteExact.evalHOLFinite_var_local, lookupKvarHOLFinite,
    lookup_setVarHOLFinite, Flapjack.PanGlobalsShMemLoadLemmas.vNeqV' name, if_false, if_true]
  cases hload : @shMemLoadHOLFiniteExact width σ _
      (setVarHOLFinite (mlstrAppend name (ofString "'")) (ValueHOL.val (HolWordLab.word 0#width))
        (setVarHOLFinite name (ValueHOL.val (HolWordLab.word addr)) t))
      (fun a => Classical.propDecidable
        ((setVarHOLFinite (mlstrAppend name (ofString "'")) (ValueHOL.val (HolWordLab.word 0#width))
          (setVarHOLFinite name (ValueHOL.val (HolWordLab.word addr)) t)).shMemaddrs a))
      .local (mlstrAppend name (ofString "'")) addr (nbOpHOL op) with
  | mk r st => cases r <;> rfl

/-- `ShMemLoad` Global sub-case of HOL `compile_correct`.  HOL resumes the
    `ShMemLoad` case with a `Cases` on the `varkind` constructor
    (`pan_globalsProofScript.sml:757-838`); this piece fixes `vk = Global`, where
    the compiler lowers the load to a nested `Dec`/`Dec`/`Seq`/`Store` and the
    source writes the loaded word to the global variable while the target writes
    it to the global's memory block. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_ShMemLoad_global {width : Nat} {σ : Type} [NeZero width]
    (operator : OpSize) (name : MlS) (address : ExpHOL width)
    (s : PanSemStateFiniteExact width σ) :
    ∀ (res : Option (PanSemResultExact width)) (ctxt : PanGlobalsContextExact width)
      (t s' : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true ctxt s t ∧
        evaluateHOLFiniteState s (.shMemLoad operator .global name address) = (res, s') ∧
        res ≠ some .error →
      ∃ t', evaluateHOLFiniteState t
          (compileProgExactHOL ctxt (.shMemLoad operator .global name address)) = (res, t') ∧
        panGlobalsStateRelHOLExact (goodResHOL res) ctxt s' t' := by
  intro res ctxt t s' ⟨hrel, hev, hne⟩
  classical
  rw [evaluateHOLFiniteState_shMemLoad_source] at hev
  cases haddrS : @PanSemStateFiniteExact.evalHOLFinite width σ _ s
      (fun a => Classical.propDecidable (s.memaddrs a)) address with
  | none =>
      simp only [haddrS] at hev
      exact absurd (Prod.mk.inj hev).1.symm hne
  | some av =>
      cases av with
      | rStruct fields =>
          simp only [haddrS] at hev
          exact absurd (Prod.mk.inj hev).1.symm hne
      | nStruct structName fields =>
          simp only [haddrS] at hev
          exact absurd (Prod.mk.inj hev).1.symm hne
      | val avp =>
          cases avp with
          | word addr =>
              cases hlookS : lookupKvarHOLFinite .global name s with
              | none =>
                  simp only [haddrS, hlookS] at hev
                  exact absurd (Prod.mk.inj hev).1.symm hne
              | some lv =>
                  cases lv with
                  | rStruct fields =>
                      simp only [haddrS, hlookS] at hev
                      exact absurd (Prod.mk.inj hev).1.symm hne
                  | nStruct structName fields =>
                      simp only [haddrS, hlookS] at hev
                      exact absurd (Prod.mk.inj hev).1.symm hne
                  | val lvp =>
                      cases lvp with
                      | word w0 =>
                          have hglobS : s.globals.lookup name = some (.val (.word w0)) := by
                            simpa only [lookupKvarHOLFinite] using hlookS
                          obtain ⟨gaddr, _hctx, _hwf, hmemload, _hdisjoint, _halign⟩ :=
                            hrel.2.2.2.2.2.2.2.2.1 name (.val (.word w0)) hglobS
                          have hctxt : ctxt.globals.lookup name = some (.one, gaddr) := by
                            simpa only [shapeOfHOLExact] using _hctx
                          have haddrT : @PanSemStateFiniteExact.evalHOLFinite width σ _ t
                              (fun a => Classical.propDecidable (t.memaddrs a))
                              (compileExpExactHOL ctxt address) = some (.val (.word addr)) :=
                            Flapjack.PanGlobalsCompileExpCorrect.compileExpCorrectHOL s address
                              (.val (.word addr)) ctxt t ⟨hrel, haddrS⟩
                          rw [evaluateHOLFiniteState_compile_shMemLoad_global ctxt t operator
                            name address addr gaddr haddrT hctxt]
                          dsimp only
                          simp only [haddrS, hlookS] at hev
                          have hffi : s.ffi = t.ffi :=
                            hrel.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                          have hshmem : s.shMemaddrs = t.shMemaddrs :=
                            hrel.2.2.2.2.2.2.2.2.2.2.2.1
                          have ht2ffi : (setVarHOLFinite (mlstrAppend name (ofString "'"))
                              (ValueHOL.val (HolWordLab.word 0#width))
                              (setVarHOLFinite name (ValueHOL.val (HolWordLab.word addr))
                                t)).ffi = s.ffi := by
                            simp only [setVarHOLFinite]; exact hffi.symm
                          have ht2sh : (setVarHOLFinite (mlstrAppend name (ofString "'"))
                              (ValueHOL.val (HolWordLab.word 0#width))
                              (setVarHOLFinite name (ValueHOL.val (HolWordLab.word addr))
                                t)).shMemaddrs = s.shMemaddrs := by
                            simp only [setVarHOLFinite]; exact hshmem.symm
                          simp only [shMemLoadHOLFiniteExact] at hev ⊢
                          rw [ht2ffi, ht2sh] at ⊢
                          have hdomT : t.memaddrs (t.topAddr - gaddr) := by
                            by_cases ht : t.memaddrs (t.topAddr - gaddr)
                            · exact ht
                            · exfalso
                              have h := hmemload
                              simp only [memLoadHOLExact, shapeOfHOLExact, if_neg ht] at h
                              exact absurd h (by simp)
                          by_cases hnb : nbOpHOL operator = 0
                          · simp only [if_pos hnb] at hev ⊢
                            by_cases hmem0 : s.shMemaddrs addr
                            · simp only [if_pos hmem0] at hev ⊢
                              cases hcall : callFFIHOL s.ffi (.sharedMem .mappedRead)
                                  [BitVec.ofNat 8 (nbOpHOL operator)]
                                  (panWordToBytesHOL addr false) with
                              | final event =>
                                  simp only [hcall] at hev ⊢
                                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                                  refine ⟨_, rfl, ?_⟩
                                  exact stateRelFlagFalse_changeLocals ctxt s t _ _
                                    (stateRelFlagFalseHOL ctxt s t hrel)
                              | ret newFfi newBytes =>
                                  simp only [hcall] at hev ⊢
                                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                                  let newMemory : RiscV.Word width → HolWordLab width :=
                                    fun current => if current = t.topAddr - gaddr
                                      then HolWordLab.word (panWordOfBytesHOL false 0 newBytes)
                                      else t.memory current
                                  have hmem : @panMemStoresHOL width _ (t.topAddr - gaddr)
                                      [HolWordLab.word (panWordOfBytesHOL false 0 newBytes)]
                                      t.memaddrs (fun a => Classical.propDecidable (t.memaddrs a))
                                      t.memory = some newMemory := by
                                    simp only [newMemory, panMemStoresHOL, panMemStoreHOL,
                                      if_pos hdomT]
                                  rw [evalStore_globalRet t name addr gaddr
                                    (panWordOfBytesHOL false 0 newBytes) newFfi newMemory hmem]
                                  refine ⟨_, rfl, ?_⟩
                                  dsimp only
                                  rw [globalRetTarget_eq t name addr
                                    (panWordOfBytesHOL false 0 newBytes) newFfi newMemory]
                                  simpa only [setKvarFfiHOLFinite, setKvarHOLFinite, goodResHOL] using
                                    stateRelFfiUpdateHOL true ctxt
                                      (setGlobalHOLFinite name
                                        (.val (.word (panWordOfBytesHOL false 0 newBytes))) s)
                                      {t with memory := newMemory} newFfi
                                      (stateRelGlobalWriteHOL ctxt s t hrel name
                                        (panWordOfBytesHOL false 0 newBytes) gaddr hctxt
                                        (by simp [hglobS]) newMemory hmem)
                            · simp only [if_neg hmem0] at hev ⊢
                              exact absurd (Prod.mk.inj hev).1.symm hne
                          · simp only [if_neg hnb] at hev ⊢
                            by_cases hmem1 : s.shMemaddrs (panByteAlignHOL addr)
                            · simp only [if_pos hmem1] at hev ⊢
                              cases hcall : callFFIHOL s.ffi (.sharedMem .mappedRead)
                                  [BitVec.ofNat 8 (nbOpHOL operator)]
                                  (panWordToBytesHOL addr false) with
                              | final event =>
                                  simp only [hcall] at hev ⊢
                                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                                  refine ⟨_, rfl, ?_⟩
                                  exact stateRelFlagFalse_changeLocals ctxt s t _ _
                                    (stateRelFlagFalseHOL ctxt s t hrel)
                              | ret newFfi newBytes =>
                                  simp only [hcall] at hev ⊢
                                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                                  let newMemory : RiscV.Word width → HolWordLab width :=
                                    fun current => if current = t.topAddr - gaddr
                                      then HolWordLab.word (panWordOfBytesHOL false 0 newBytes)
                                      else t.memory current
                                  have hmem : @panMemStoresHOL width _ (t.topAddr - gaddr)
                                      [HolWordLab.word (panWordOfBytesHOL false 0 newBytes)]
                                      t.memaddrs (fun a => Classical.propDecidable (t.memaddrs a))
                                      t.memory = some newMemory := by
                                    simp only [newMemory, panMemStoresHOL, panMemStoreHOL,
                                      if_pos hdomT]
                                  rw [evalStore_globalRet t name addr gaddr
                                    (panWordOfBytesHOL false 0 newBytes) newFfi newMemory hmem]
                                  refine ⟨_, rfl, ?_⟩
                                  dsimp only
                                  rw [globalRetTarget_eq t name addr
                                    (panWordOfBytesHOL false 0 newBytes) newFfi newMemory]
                                  simpa only [setKvarFfiHOLFinite, setKvarHOLFinite, goodResHOL] using
                                    stateRelFfiUpdateHOL true ctxt
                                      (setGlobalHOLFinite name
                                        (.val (.word (panWordOfBytesHOL false 0 newBytes))) s)
                                      {t with memory := newMemory} newFfi
                                      (stateRelGlobalWriteHOL ctxt s t hrel name
                                        (panWordOfBytesHOL false 0 newBytes) gaddr hctxt
                                        (by simp [hglobS]) newMemory hmem)
                            · simp only [if_neg hmem1] at hev ⊢
                              exact absurd (Prod.mk.inj hev).1.symm hne

/-- Complete HOL ShMemLoad constructor case, assembled by the original Local/Global
case split from the accepted subcases. No induction hypothesis is needed for this
nonrecursive constructor; all original compile_correct guards remain unchanged. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_ShMemLoad {width : Nat} {σ : Type} [NeZero width]
    (operator : OpSize) (vk : VarKind) (name : MlS) (address : ExpHOL width)
    (s : PanSemStateFiniteExact width σ) :
    ∀ (res : Option (PanSemResultExact width)) (ctxt : PanGlobalsContextExact width)
      (t s' : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true ctxt s t ∧
        evaluateHOLFiniteState s (.shMemLoad operator vk name address) = (res, s') ∧
        res ≠ some .error →
      ∃ t', evaluateHOLFiniteState t
          (compileProgExactHOL ctxt (.shMemLoad operator vk name address)) = (res, t') ∧
        panGlobalsStateRelHOLExact (goodResHOL res) ctxt s' t' := by
  cases vk with
  | «local» => exact compileCorrect_ShMemLoad_local operator name address s
  | «global» => exact compileCorrect_ShMemLoad_global operator name address s

end PanGlobalsCompileCorrect

end Flapjack
