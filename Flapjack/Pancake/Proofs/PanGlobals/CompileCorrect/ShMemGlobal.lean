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

end PanGlobalsCompileCorrect

end Flapjack
