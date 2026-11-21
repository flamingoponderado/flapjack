module

public import Flapjack.HolRef
public import Flapjack.Misc.ListEl
public import Flapjack.Pancake.PanLang.Decl
public import Flapjack.Pancake.Semantics.CrepSem.HOLState
public import Flapjack.Pancake.Semantics.PanSem.MemLoadHOL
public import Flapjack.Pancake.Semantics.PanSem.ValueHOL
public import Flapjack.Pancake.Semantics.PanProps

@[expose] public section

/-! Exact port support for `crepPropsScript.sml` memory-load relations. -/

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- The exact `crepSem$mem_load_def` body at one address (`crepSemScript.sml:48-51`);
this helper removes only the surrounding target-state record. -/
private def memLoadFlatTargetHOL {width : Nat} [NeZero width]
    (domain : BitVec width → Prop) [DecidablePred domain]
    (memory : BitVec width → HolWordLab width) (address : BitVec width) :
    Option (HolWordLab width) :=
  if domain address then some (memory address) else none

/- Mutual strided-read analogue of HOL `mem_loads_flat_rel`
   (`crepPropsScript.sml:66-99`), using the shape clause of
   `mem_load_flat_rel` (`:102-109`). It follows the HOL list induction: the
   append split uses the imported length theorem to establish the tail stride.
   This helper is intentionally untagged: it is over Lean's exact indexed
   carriers and exact evaluator, but is not itself the source theorem's shared
   Pan/Crep state statement. -/
private theorem memLoadHOLExact_flatRead_mutual {width : Nat} [NeZero width]
    (domain : BitVec width → Prop) [DecidablePred domain]
    (memory : BitVec width → HolWordLab width) :
    ∀ (shape : ShapeHOL) (address : BitVec width) (context : StructContextHOLM),
      isWfShapeExactHOL ([] : StructContextExact) shape = true →
      ∀ value, memLoadHOLExact shape address domain memory context = some value →
      ∀ (n : Nat) (hn : n < (flattenHOL value).length),
        memLoadFlatTargetHOL domain memory
          (address + bytesInWordHOL width * BitVec.ofNat width n) =
            some ((flattenHOL value)[n]'hn) := by
  apply memLoadHOLExact.induct (domain := domain) (memory := memory)
    (motive1 := fun shape address context =>
      isWfShapeExactHOL ([] : StructContextExact) shape = true →
      ∀ value, memLoadHOLExact shape address domain memory context = some value →
      ∀ (n : Nat) (hn : n < (flattenHOL value).length),
        memLoadFlatTargetHOL domain memory
          (address + bytesInWordHOL width * BitVec.ofNat width n) =
            some ((flattenHOL value)[n]'hn))
    (motive2 := fun _ _ _ => True)
    (motive3 := fun shapes address context =>
      isWfShapesExactHOL ([] : StructContextExact) shapes = true →
      ∀ values, memLoadsHOLExact shapes address domain memory context = some values →
      ∀ (n : Nat) (hn : n < ((values.map flattenHOL).flatten).length),
        memLoadFlatTargetHOL domain memory
          (address + bytesInWordHOL width * BitVec.ofNat width n) =
            some (((values.map flattenHOL).flatten)[n]'hn))
  case case1 =>
    intro address context hdom _hwf value hload n hn
    simp only [memLoadHOLExact, if_pos hdom] at hload
    injection hload with hvalue
    subst value
    have hn0 : n = 0 := by simpa [flattenHOL] using hn
    subst n
    simp [memLoadFlatTargetHOL, flattenHOL, hdom]
  case case2 =>
    intro address context hndom _hwf value hload n hn
    simp only [memLoadHOLExact, if_neg hndom] at hload
    contradiction
  case case3 =>
    intro address context shapes values hloads ihShapes hwf value hload n hn
    rw [memLoadHOLExact.eq_2, hloads] at hload
    injection hload with hvalue
    subst value
    have hwfShapes : isWfShapesExactHOL ([] : StructContextExact) shapes = true := by
      simpa only [isWfShapeExactHOL_comb] using hwf
    have hread := ihShapes hwfShapes values hloads n (by simpa [flattenHOL] using hn)
    simpa [flattenHOL] using hread
  case case4 =>
    intro address context shapes hfail ihShapes _hwf value hload n hn
    rw [memLoadHOLExact.eq_2, hfail] at hload
    simp at hload
  case case5 =>
    intro address name hwf value hload n hn
    simp [isWfShapeExactHOL] at hwf
  case case6 =>
    intro address candidate info rest fields hfields _ihFields hwf value hload n hn
    simp [isWfShapeExactHOL] at hwf
  case case7 =>
    intro address candidate info rest _hfields _ihFields hwf value hload n hn
    simp [isWfShapeExactHOL] at hwf
  case case8 =>
    intro address name candidate info rest hne ihShape hwf value hload n hn
    simp [isWfShapeExactHOL] at hwf
  case case9 =>
    intro address context
    trivial
  case case10 =>
    intro address context field shape rest value values htail hhead ihHead ihTail
    trivial
  case case11 =>
    intro address context field shape rest hfail ihHead ihTail
    trivial
  case case12 =>
    intro address context hwf values hloads n hn
    simp only [memLoadsHOLExact] at hloads
    injection hloads with hvalues
    subst values
    simp at hn
  case case13 =>
    intro address context shape rest headValue tailValues htail hhead
      ihHead ihTail hwfList values hload n hn
    rw [memLoadsHOLExact.eq_2, hhead, htail] at hload
    injection hload with hvalues
    subst values
    have hwfParts :
        isWfShapeExactHOL ([] : StructContextExact) shape = true ∧
          isWfShapesExactHOL ([] : StructContextExact) rest = true := by
      simpa only [isWfShapesExactHOL_cons, Bool.and_eq_true] using hwfList
    have hheadLength := memLoadHOLExact_length_flatten_context
      domain memory shape address context hwfParts.1 headValue hhead
    let headFlat := flattenHOL headValue
    let tailFlat := (tailValues.map flattenHOL).flatten
    let tailAddress := address + bytesInWordHOL width *
      BitVec.ofNat width (sizeOfShapeWithContextHOL context shape)
    have happend : ((headValue :: tailValues).map flattenHOL).flatten =
        headFlat ++ tailFlat := by simp [headFlat, tailFlat]
    have hflatLen : ((headValue :: tailValues).map flattenHOL).flatten.length =
        headFlat.length + tailFlat.length := by
      simp [headFlat, tailFlat]
    have hnAppend : n < headFlat.length + tailFlat.length := by
      rw [← hflatLen]
      exact hn
    have hidx : n < (headFlat ++ tailFlat).length := by
      simpa [List.length_append] using hnAppend
    by_cases hnHead : n < headFlat.length
    · have hread := ihHead hwfParts.1 headValue hhead n hnHead
      have hget : (headFlat ++ tailFlat)[n]'hidx = headFlat[n]'hnHead := by
        exact List.getElem_append_left hnHead
      simpa [memLoadFlatTargetHOL, headFlat, tailFlat, flattenHOL, hget] using hread
    · have hlarge : headFlat.length ≤ n := Nat.le_of_not_lt hnHead
      let nTail := n - headFlat.length
      have hnTail : nTail < tailFlat.length := by omega
      have hsplit : n = headFlat.length + nTail := by omega
      have hsize : sizeOfShapeWithContextHOL context shape = headFlat.length :=
        hheadLength.symm
      have haddress :
          address + bytesInWordHOL width * BitVec.ofNat width n =
            tailAddress + bytesInWordHOL width * BitVec.ofNat width nTail := by
        simp only [tailAddress, hsize, hsplit, BitVec.ofNat_add,
          BitVec.mul_add, BitVec.add_assoc]
      have hread := ihTail hwfParts.2 tailValues htail nTail hnTail
      have hget : (headFlat ++ tailFlat)[n]'hidx = tailFlat[nTail]'hnTail := by
        rw [List.getElem_append_right hlarge]
      simpa [memLoadFlatTargetHOL, headFlat, tailFlat, flattenHOL,
        haddress, hget] using hread
  case case14 =>
    intro address context shape rest hfail _ihHead _ihTail _hwfList values hload n hn
    rw [memLoadsHOLExact.eq_2] at hload
    cases hhead : memLoadHOLExact shape address domain memory context with
    | none => simp [hhead] at hload
    | some headValue =>
      let tailAddress := address + bytesInWordHOL width *
        BitVec.ofNat width (sizeOfShapeWithContextHOL context shape)
      cases htail : memLoadsHOLExact rest tailAddress domain memory context with
      | none =>
        have htail' := htail
        dsimp [tailAddress] at htail'
        simp [hhead, htail'] at hload
      | some tailValues => exact (hfail headValue tailValues hhead htail).elim

/- Shapes-level strided read (`crepPropsScript.sml:75-87`): the list analogue of
   `memLoadHOLExact_flatRead_mutual`, proved by list induction on the shape list
   with the single-shape mutual lemma supplying the head step. -/
private theorem memLoadsHOLExact_flatRead_shapes {width : Nat} [NeZero width]
    (domain : BitVec width → Prop) [DecidablePred domain]
    (memory : BitVec width → HolWordLab width) :
    ∀ (shapes : List ShapeHOL) (address : BitVec width) (context : StructContextHOLM),
      isWfShapesExactHOL ([] : StructContextExact) shapes = true →
      ∀ values, memLoadsHOLExact shapes address domain memory context = some values →
      ∀ (n : Nat) (hn : n < ((values.map flattenHOL).flatten).length),
        memLoadFlatTargetHOL domain memory
          (address + bytesInWordHOL width * BitVec.ofNat width n) =
            some (((values.map flattenHOL).flatten)[n]'hn) := by
  intro shapes
  induction shapes with
  | nil =>
      intro address context _hwf values hload n hn
      rw [memLoadsHOLExact.eq_1] at hload
      injection hload with hvalues
      subst hvalues
      simp at hn
  | cons shape rest ih =>
      intro address context hwf values hload n hn
      rw [memLoadsHOLExact.eq_2] at hload
      cases hhead : memLoadHOLExact shape address domain memory context with
      | none => simp [hhead] at hload
      | some headValue =>
        let tailAddress := address + bytesInWordHOL width *
          BitVec.ofNat width (sizeOfShapeWithContextHOL context shape)
        cases htail : memLoadsHOLExact rest tailAddress domain memory context with
        | none =>
          have htail' := htail
          dsimp [tailAddress] at htail'
          simp [hhead, htail'] at hload
        | some tailValues =>
          have hload' := hload
          rw [hhead, htail] at hload'
          injection hload' with hvalues
          subst hvalues
          have hwfParts :
              isWfShapeExactHOL ([] : StructContextExact) shape = true ∧
                isWfShapesExactHOL ([] : StructContextExact) rest = true := by
            simpa only [isWfShapesExactHOL_cons, Bool.and_eq_true] using hwf
          have hheadLength := memLoadHOLExact_length_flatten_context
            domain memory shape address context hwfParts.1 headValue hhead
          let headFlat := flattenHOL headValue
          let tailFlat := (tailValues.map flattenHOL).flatten
          have happend : ((headValue :: tailValues).map flattenHOL).flatten =
              headFlat ++ tailFlat := by simp [headFlat, tailFlat]
          have hflatLen : ((headValue :: tailValues).map flattenHOL).flatten.length =
              headFlat.length + tailFlat.length := by
            simp [headFlat, tailFlat]
          have hnAppend : n < headFlat.length + tailFlat.length := by
            rw [← hflatLen]
            exact hn
          have hidx : n < (headFlat ++ tailFlat).length := by
            simpa [List.length_append] using hnAppend
          by_cases hnHead : n < headFlat.length
          · have hread := memLoadHOLExact_flatRead_mutual domain memory shape
              address context hwfParts.1 headValue hhead n hnHead
            have hget : (headFlat ++ tailFlat)[n]'hidx = headFlat[n]'hnHead := by
              exact List.getElem_append_left hnHead
            simpa [memLoadFlatTargetHOL, headFlat, tailFlat, flattenHOL, hget]
              using hread
          · have hlarge : headFlat.length ≤ n := Nat.le_of_not_lt hnHead
            let nTail := n - headFlat.length
            have hnTail : nTail < tailFlat.length := by omega
            have hsplit : n = headFlat.length + nTail := by omega
            have hsize : sizeOfShapeWithContextHOL context shape = headFlat.length :=
              hheadLength.symm
            have haddress :
                address + bytesInWordHOL width * BitVec.ofNat width n =
                  tailAddress + bytesInWordHOL width * BitVec.ofNat width nTail := by
              simp only [tailAddress, hsize, hsplit, BitVec.ofNat_add,
                BitVec.mul_add, BitVec.add_assoc]
            have hread := ih tailAddress context hwfParts.2 tailValues htail
              nTail hnTail
            have hget : (headFlat ++ tailFlat)[n]'hidx = tailFlat[nTail]'hnTail := by
              rw [List.getElem_append_right hlarge]
            simpa [memLoadFlatTargetHOL, headFlat, tailFlat, flattenHOL,
              haddress, hget] using hread

namespace CrepPropsMemLoadFlatRelFiniteSupport

/-- Local same-module witness for the canonical finite-support `CrepSemHOLState`
carrier used by the qualified `mem_load_flat_rel` port below. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end CrepPropsMemLoadFlatRelFiniteSupport

/- Exact-carrier port of HOL `mem_load_flat_rel`
   (`cakeml/pancake/semantics/crepPropsScript.sml:102-109`). The same target
   state supplies both Pan `mem_load`'s domain/memory arguments and Crep
   `mem_load`; there are no split domain/memory equality premises. The positive
   BitVec dimension and finite-support target maps are recorded by the two
   representation qualifiers. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "mem_load_flat_rel"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem memLoadFlatRelHOLExact {width : Nat} {σ : Type} [NeZero width]
    (target : CrepSemHOLState width σ) [ht : DecidablePred target.memaddrs]
    (shape : ShapeHOL) (address : BitVec width) (context : StructContextHOLM)
    (value : ValueHOL width) (n : Nat)
    (hload : memLoadHOLExact shape address target.memaddrs target.memory context = some value)
    (hn : n < (flattenHOL value).length)
    (hwf : isWfShapeExactHOL ([] : StructContextExact) shape = true) :
    memLoadCrepSemHOL
        (address + bytesInWordHOL width * BitVec.ofNat width
          ((flattenHOL value).take n).length) target =
      some ((flattenHOL value)[n]'hn) := by
  have hread := memLoadHOLExact_flatRead_mutual
    target.memaddrs target.memory shape address context hwf value hload n hn
  have htake : ((flattenHOL value).take n).length = n :=
    List.length_take_of_le (Nat.le_of_lt hn)
  rw [htake]
  simpa [memLoadCrepSemHOL, memLoadFlatTargetHOL] using hread

/-- Flapjack infrastructure: the exact word-lab carrier is inhabited (every HOL
    type is), so the total `holEl` rendering applies to `flattenHOL` lists. -/
instance holWordLabNonempty {width : Nat} [NeZero width] : Nonempty (HolWordLab width) :=
  ⟨HolWordLab.word (BitVec.ofNat width 0)⟩

/- Exact-carrier port of HOL `mem_loads_flat_rel`
   (`cakeml/pancake/semantics/crepPropsScript.sml:61-99`).  The three conjuncts
   keep HOL's own shape: the single-shape and shapes-level strided reads (each
   over Pan `mem_load`/`mem_loads` with explicit domain and memory equal to the
   Crep state's fields) and the vacuous `mem_load_flds` clause.  Each strided
   read has ONE conjoined premise (`mem_load ... = SOME v ∧ is_wf_shape_nil sh`,
   `mem_loads ... = SOME v ∧ EVERY is_wf_shape_nil shs`), `EVERY is_wf_shape_nil
   shs` is `∀ sh ∈ shapes, isWfShapeExactHOL ([] : StructContextExact) sh = true`,
   and HOL's `n < LENGTH (...) ⇒ ... SOME (EL n (...))` is an ordinary premise
   plus the total `holEl` rendering of `EL`.  The positive BitVec dimension and
   the finite-support target maps are recorded by the two representation
   qualifiers. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "mem_loads_flat_rel"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem memLoadsFlatRelHOLExact {width : Nat} {σ : Type} [NeZero width] :
    (∀ (sh : ShapeHOL) (adr : BitVec width) (dm : BitVec width → Prop) [DecidablePred dm]
      (m : BitVec width → HolWordLab width) (context : StructContextHOLM)
      (v : ValueHOL width),
      memLoadHOLExact sh adr dm m context = some v ∧
        isWfShapeExactHOL ([] : StructContextExact) sh = true →
      ∀ (s : CrepSemHOLState width σ) [DecidablePred s.memaddrs] (n : Nat),
        n < (flattenHOL v).length → dm = s.memaddrs → m = s.memory →
        memLoadCrepSemHOL (adr + bytesInWordHOL width * BitVec.ofNat width n) s =
          some (holEl n (flattenHOL v))) ∧
    (∀ (shapes : List ShapeHOL) (adr : BitVec width) (dm : BitVec width → Prop)
      [DecidablePred dm] (m : BitVec width → HolWordLab width)
      (context : StructContextHOLM) (values : List (ValueHOL width)),
      memLoadsHOLExact shapes adr dm m context = some values ∧
        (∀ sh ∈ shapes, isWfShapeExactHOL ([] : StructContextExact) sh = true) →
      ∀ (s : CrepSemHOLState width σ) [DecidablePred s.memaddrs] (n : Nat),
        n < ((values.map flattenHOL).flatten).length → dm = s.memaddrs → m = s.memory →
        memLoadCrepSemHOL (adr + bytesInWordHOL width * BitVec.ofNat width n) s =
          some (holEl n ((values.map flattenHOL).flatten))) ∧
    (∀ (flds : List (MlStringHOLM × ShapeHOL)) (adr : BitVec width)
      (dm : BitVec width → Prop) [DecidablePred dm]
      (m : BitVec width → HolWordLab width) (context : StructContextHOLM)
      (vs : List (MlStringHOLM × ValueHOL width)),
      memLoadFldsHOLExact flds adr dm m context = some vs → True) := by
  refine ⟨?_, ?_, ?_⟩
  · intro sh adr dm inst m context v h s inst2 n hn hdm hmem
    obtain ⟨hload, hwf⟩ := h
    subst hdm hmem
    have hread := memLoadHOLExact_flatRead_mutual s.memaddrs s.memory sh adr context
      hwf v hload n hn
    rw [holEl_eq_getElem n (flattenHOL v) hn]
    simpa [memLoadCrepSemHOL, memLoadFlatTargetHOL] using hread
  · intro shapes adr dm inst m context values h s inst2 n hn hdm hmem
    obtain ⟨hload, hwf⟩ := h
    have hall : ∀ (shapes : List ShapeHOL),
        isWfShapesExactHOL ([] : StructContextExact) shapes =
          shapes.all (fun sh => isWfShapeExactHOL ([] : StructContextExact) sh) := by
      intro shapes
      induction shapes with
      | nil => rfl
      | cons sh rest ih => simp [isWfShapesExactHOL, ih]
    have hwfList : isWfShapesExactHOL ([] : StructContextExact) shapes = true := by
      rw [hall shapes]
      exact List.all_eq_true.mpr hwf
    subst hdm hmem
    have hread := memLoadsHOLExact_flatRead_shapes s.memaddrs s.memory shapes adr context
      hwfList values hload n hn
    rw [holEl_eq_getElem n ((values.map flattenHOL).flatten) hn]
    simpa [memLoadCrepSemHOL, memLoadFlatTargetHOL] using hread
  · intro flds adr dm inst m context vs hload
    trivial

end Flapjack
