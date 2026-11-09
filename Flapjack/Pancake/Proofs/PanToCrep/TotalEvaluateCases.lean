import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.Semantics.CrepSem.TotalEval
import Flapjack.Pancake.Semantics.PanSem.EvaluateFinite
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.PanToCrep.CompileProg
import Flapjack.Pancake.Semantics.PanSem.DecCallExact
import Flapjack.Pancake.Proofs.PanToCrep.CodeRelExact
import Flapjack.Pancake.Proofs.PanToCrep.StateRelFiniteSupport
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
import Flapjack.Pancake.Proofs.PanToCrep.CompileExactVarSupport

/-!
# Total evaluator cases for Pan-to-Crep correctness

Support lemmas for the call-context and expression cases of
`pc_compile_correct`, along with source-reviewed HOL expression lemmas.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
  (MlS ShapeHOL ProgHOL shapeOfHOL sizeOfShapeHOL sizeOfShapeHOL_comb
    sizeOfShapesHOL sizeOfShapesHOL_cons withShapeHOL isWfShapeExactHOL
    StructContextExact)

private theorem shapeSizeShapeOfHOLExact (shape : ShapeHOL) :
    Shape.shapeSize (shapeOfHOL shape) = sizeOfShapeHOL shape := by
  have h := sizeOfShapeHOL_shapeToHOL (shapeOfHOL shape)
  simpa [Flapjack.Pancake.PanLang.shapeToHOL_shapeOfHOL] using h.symm

private theorem shapeSizeCombShapeOfHOLExact (shapes : List ShapeHOL) :
    Shape.shapeSize (.comb (shapes.map shapeOfHOL)) =
      sizeOfShapeHOL (.comb shapes) := by
  have h := sizeOfShapesHOL_shapeToHOL (shapes.map shapeOfHOL)
  rw [List.map_map, Function.comp_def,
    List.map_congr_left (fun shape _ =>
      Flapjack.Pancake.PanLang.shapeToHOL_shapeOfHOL shape)] at h
  simpa [Shape.shapeSize] using h.symm

private theorem withShapeHOL_eq_withShapeShapeOfHOL
    {α : Type} (shapes : List ShapeHOL) (values : List α) :
    withShapeHOL shapes values = withShape (shapes.map shapeOfHOL) values := by
  induction shapes generalizing values with
  | nil => simp [withShapeHOL, withShape]
  | cons shape shapes ih =>
      have hsize : sizeOfShapeHOL shape = Shape.shapeSize (shapeOfHOL shape) :=
        (shapeSizeShapeOfHOLExact shape).symm
      simp [withShapeHOL, withShape, hsize, ih]

private theorem shapeSizeCombHOL_eq_flattenHOL_length
    {width : Nat} [NeZero width]
    (shapes : List ShapeHOL) (arguments : List (ValueHOL width))
    (hlen : shapes.length = arguments.length)
    (hshape : ∀ i (hsi : i < shapes.length) (hai : i < arguments.length),
      (shapes[i]'hsi) = shapeOfHOLExact (arguments[i]'hai))
    (hwf : ∀ value, value ∈ arguments →
      isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true) :
    sizeOfShapeHOL (.comb shapes) = (arguments.map flattenHOL).flatten.length := by
  induction arguments generalizing shapes with
  | nil =>
      cases shapes with
      | nil => simp [sizeOfShapeHOL]
      | cons shape shapes => simp at hlen
  | cons value arguments ih =>
      cases shapes with
      | nil => simp at hlen
      | cons shape shapes =>
          have hhead : shape = shapeOfHOLExact value := by
            have h := hshape 0 (by simp) (by simp)
            simpa using h
          have htailLength : shapes.length = arguments.length := by simpa using hlen
          have htailShape : ∀ i (hsi : i < shapes.length) (hai : i < arguments.length),
              (shapes[i]'hsi) = shapeOfHOLExact (arguments[i]'hai) := by
            intro i hsi hai
            have h := hshape (i + 1) (by simp [hsi]) (by simp [hai])
            simpa [List.getElem_cons_succ] using h
          have htailWf : ∀ other, other ∈ arguments →
              isWfShapeExactHOL ([] : StructContextExact)
                (shapeOfHOLExact other) = true := by
            intro other hmem
            exact hwf other (by simp [hmem])
          simp only [List.map_cons, List.flatten_cons, List.length_append,
            sizeOfShapeHOL_comb, sizeOfShapesHOL_cons]
          rw [hhead, flattenHOL_length_eq_sizeOfShapeHOL value (hwf value (by simp)),
            ← sizeOfShapeHOL_comb shapes]
          exact congrArg (fun n => sizeOfShapeHOL (shapeOfHOLExact value) + n)
            (ih shapes htailLength htailShape htailWf)

private theorem withShapeHOL_getElem_length_exact
    {width : Nat} [NeZero width]
    (shapes : List ShapeHOL) (slots : List Nat)
    (arguments : List (ValueHOL width)) (i : Nat)
    (hslots : slots.length = (arguments.map flattenHOL).flatten.length)
    (hsize : sizeOfShapeHOL (.comb shapes) =
      (arguments.map flattenHOL).flatten.length)
    (hiShape : i < shapes.length) (hiArg : i < arguments.length)
    (hshape : ∀ i (hsi : i < shapes.length) (hai : i < arguments.length),
      (shapes[i]'hsi) = shapeOfHOLExact (arguments[i]'hai))
    (hwf : ∀ value, value ∈ arguments →
      isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true) :
    ((withShapeHOL shapes slots)[i]'(by
      rw [withShapeHOL_eq_withShapeShapeOfHOL, withShape_length]
      simpa only [List.length_map] using hiShape)).length =
        (flattenHOL (arguments[i]'hiArg)).length := by
  have hgroups := withShapeHOL_eq_withShapeShapeOfHOL shapes slots
  have hprodSize : slots.length = Shape.shapeSize (.comb (shapes.map shapeOfHOL)) := by
    rw [shapeSizeCombShapeOfHOLExact]
    exact hslots.trans hsize.symm
  have hgroupLen := withShape_getElem_length (shapes.map shapeOfHOL) slots i
    hprodSize (by simpa only [List.length_map] using hiShape)
  have hgroupsAt := congrArg
    (fun groups : List (List Nat) => groups[i]?) hgroups
  have hholBound : i < (withShapeHOL shapes slots).length := by
    rw [hgroups, withShape_length]
    simpa only [List.length_map] using hiShape
  have hprodBound : i < (withShape (shapes.map shapeOfHOL) slots).length := by
    rw [withShape_length]
    simpa only [List.length_map] using hiShape
  have hlengthEq :
      ((withShapeHOL shapes slots)[i]'hholBound).length =
      ((withShape (shapes.map shapeOfHOL) slots)[i]'hprodBound).length := by
    have h := congrArg (Option.map List.length) hgroupsAt
    have hsome :
        some ((withShapeHOL shapes slots)[i]'hholBound).length =
          some ((withShape (shapes.map shapeOfHOL) slots)[i]'hprodBound).length := by
      simpa [List.getElem?_eq_getElem, hholBound, hprodBound] using h
    exact Option.some.inj hsome
  have hgroupLen' :
      ((withShape (shapes.map shapeOfHOL) slots)[i]'hprodBound).length =
        Shape.shapeSize (shapeOfHOL (shapes[i]'hiShape)) := by
    simpa only [List.getElem_map] using hgroupLen
  calc
    ((withShapeHOL shapes slots)[i]'hholBound).length =
        ((withShape (shapes.map shapeOfHOL) slots)[i]'hprodBound).length := hlengthEq
    _ = Shape.shapeSize (shapeOfHOL (shapes[i]'hiShape)) := hgroupLen'
    _ = sizeOfShapeHOL (shapes[i]'hiShape) :=
      shapeSizeShapeOfHOLExact (shapes[i]'hiShape)
    _ = sizeOfShapeHOL (shapeOfHOLExact (arguments[i]'hiArg)) := by
      rw [hshape i hiShape hiArg]
    _ = (flattenHOL (arguments[i]'hiArg)).length :=
      (flattenHOL_length_eq_sizeOfShapeHOL (arguments[i]'hiArg)
        (hwf (arguments[i]'hiArg) (List.getElem_mem hiArg))).symm

private theorem withShapeHOL_getElem_eq_take_drop
    {α : Type} (shapes : List ShapeHOL) (values : List α) (i : Nat)
    (hvalues : values.length = sizeOfShapeHOL (.comb shapes))
    (hi : i < shapes.length) :
    (withShapeHOL shapes values)[i]'(by
      rw [withShapeHOL_eq_withShapeShapeOfHOL, withShape_length]
      simpa only [List.length_map] using hi) =
      (values.drop (sizeOfShapeHOL (.comb (shapes.take i)))).take
        (sizeOfShapeHOL (shapes[i]'hi)) := by
  have hgroups := withShapeHOL_eq_withShapeShapeOfHOL shapes values
  have hprodValues : values.length = Shape.shapeSize (.comb (shapes.map shapeOfHOL)) := by
    rw [shapeSizeCombShapeOfHOLExact]
    exact hvalues
  have hprodBound : i < (withShape (shapes.map shapeOfHOL) values).length := by
    rw [withShape_length]
    simpa only [List.length_map] using hi
  have hholBound : i < (withShapeHOL shapes values).length := by
    rw [hgroups, withShape_length]
    simpa only [List.length_map] using hi
  have hgroupsAt := congrArg
    (fun groups : List (List α) => groups[i]?) hgroups
  have hgroupEq :
      (withShapeHOL shapes values)[i]'hholBound =
        (withShape (shapes.map shapeOfHOL) values)[i]'hprodBound := by
    have hsome :
        some ((withShapeHOL shapes values)[i]'hholBound) =
          some ((withShape (shapes.map shapeOfHOL) values)[i]'hprodBound) := by
      simpa [List.getElem?_eq_getElem, hholBound, hprodBound] using hgroupsAt
    exact Option.some.inj hsome
  calc
    (withShapeHOL shapes values)[i]'hholBound =
        (withShape (shapes.map shapeOfHOL) values)[i]'hprodBound := hgroupEq
    _ = (values.drop (Shape.shapeSize
          (.comb ((shapes.map shapeOfHOL).take i)))).take
          (Shape.shapeSize ((shapes.map shapeOfHOL)[i]'(by
            simpa only [List.length_map] using hi))) :=
      withShape_getElem_eq_take_drop (shapes.map shapeOfHOL) values i
        hprodValues (by simpa only [List.length_map] using hi)
    _ = (values.drop (sizeOfShapeHOL (.comb (shapes.take i)))).take
          (sizeOfShapeHOL (shapes[i]'hi)) := by
      have hprefix : Shape.shapeSize
          (.comb ((shapes.map shapeOfHOL).take i)) =
            sizeOfShapeHOL (.comb (shapes.take i)) := by
        rw [← List.map_take]
        exact shapeSizeCombShapeOfHOLExact (shapes.take i)
      have hcurrent : Shape.shapeSize
          ((shapes.map shapeOfHOL)[i]'(by
            simpa only [List.length_map] using hi)) =
            sizeOfShapeHOL (shapes[i]'hi) := by
        rw [List.getElem_map]
        exact shapeSizeShapeOfHOLExact (shapes[i]'hi)
      rw [hprefix, hcurrent]

private theorem withShapeHOL_mapFlatten
    {width : Nat} [NeZero width]
    (shapes : List ShapeHOL) (arguments : List (ValueHOL width))
    (hlen : shapes.length = arguments.length)
    (hshape : ∀ i (hsi : i < shapes.length) (hai : i < arguments.length),
      shapes[i]'hsi = shapeOfHOLExact (arguments[i]'hai))
    (hwf : ∀ value, value ∈ arguments →
      isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true) :
    withShapeHOL shapes ((arguments.map flattenHOL).flatten) =
      arguments.map flattenHOL := by
  induction arguments generalizing shapes with
  | nil =>
      cases shapes with
      | nil => simp [withShapeHOL]
      | cons shape shapes => simp at hlen
  | cons value arguments ih =>
      cases shapes with
      | nil => simp at hlen
      | cons shape shapes =>
          have hhead : shape = shapeOfHOLExact value := by
            have h := hshape 0 (by simp) (by simp)
            simpa using h
          have htailLength : shapes.length = arguments.length := by simpa using hlen
          have htailShape : ∀ i (hsi : i < shapes.length) (hai : i < arguments.length),
              shapes[i]'hsi = shapeOfHOLExact (arguments[i]'hai) := by
            intro i hsi hai
            have h := hshape (i + 1) (by simp [hsi]) (by simp [hai])
            simpa [List.getElem_cons_succ] using h
          have htailWf : ∀ other, other ∈ arguments →
              isWfShapeExactHOL ([] : StructContextExact)
                (shapeOfHOLExact other) = true := by
            intro other hmem
            exact hwf other (by simp [hmem])
          have hvalueWf := hwf value (by simp)
          have hvalueLength : (flattenHOL value).length =
              sizeOfShapeHOL (shapeOfHOLExact value) :=
            flattenHOL_length_eq_sizeOfShapeHOL value hvalueWf
          simp only [List.map_cons, List.flatten_cons]
          rw [withShapeHOL, hhead, ← hvalueLength]
          have htake :
              ((flattenHOL value) ++ (arguments.map flattenHOL).flatten).take
                  (flattenHOL value).length = flattenHOL value := by
            rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
          have hdrop :
              ((flattenHOL value) ++ (arguments.map flattenHOL).flatten).drop
                  (flattenHOL value).length = (arguments.map flattenHOL).flatten := by
            simp
          rw [htake, hdrop, ih shapes htailLength htailShape htailWf]

private theorem tlcHOL_lookup_getElem
    {width : Nat} [NeZero width]
    (slots : List Nat) (arguments : List (ValueHOL width)) (i : Nat)
    (hdistinct : slots.Nodup)
    (hlen : slots.length = (arguments.map flattenHOL).flatten.length)
    (hi : i < slots.length) :
    (tlcHOL slots arguments).lookup (slots[i]'hi) =
      some ((arguments.map flattenHOL).flatten[i]'(by omega)) := by
  rw [holFmapAsFiniteSupportResultWitness_tlcHOL]
  have hlookup := FLOOKUP_FUPDATE_LIST_zip_getElem slots
    ((arguments.map flattenHOL).flatten) FEMPTY i hdistinct hlen hi
  change FLOOKUP
    (FUPDATE_LIST_HOL (FEMPTY : FiniteMap Nat (HolWordLab width))
      (slots.zip ((arguments.map flattenHOL).flatten)))
    (slots[i]'hi) = _
  rw [FUPDATE_LIST_HOL_eq_FUPDATE_LIST]
  exact hlookup

private theorem tlcHOLWithShapeMapM
    {width : Nat} [NeZero width]
    (shapes : List ShapeHOL) (arguments : List (ValueHOL width))
    (slots : List Nat) (i : Nat)
    (hslotsNodup : slots.Nodup)
    (hslotsLength : slots.length = (arguments.map flattenHOL).flatten.length)
    (hshapeSize : sizeOfShapeHOL (.comb shapes) =
      (arguments.map flattenHOL).flatten.length)
    (hlen : shapes.length = arguments.length)
    (hshape : ∀ i (hsi : i < shapes.length) (hai : i < arguments.length),
      shapes[i]'hsi = shapeOfHOLExact (arguments[i]'hai))
    (hwf : ∀ value, value ∈ arguments →
      isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true)
    (hiShape : i < shapes.length) (hiArgument : i < arguments.length) :
    ((withShapeHOL shapes slots)[i]'(by
      rw [withShapeHOL_eq_withShapeShapeOfHOL, withShape_length]
      simpa only [List.length_map] using hiShape)).mapM
        (tlcHOL slots arguments).lookup = some (flattenHOL (arguments[i]'hiArgument)) := by
  let words := (arguments.map flattenHOL).flatten
  let shape := shapes[i]'hiShape
  let value := arguments[i]'hiArgument
  have hslotsShape : slots.length = sizeOfShapeHOL (.comb shapes) :=
    hslotsLength.trans hshapeSize.symm
  have hgroupLength :
      ((withShapeHOL shapes slots)[i]'(by
        rw [withShapeHOL_eq_withShapeShapeOfHOL, withShape_length]
        simpa only [List.length_map] using hiShape)).length =
        (flattenHOL value).length := by
    exact withShapeHOL_getElem_length_exact shapes slots arguments i
      hslotsLength hshapeSize hiShape hiArgument hshape hwf
  have hwhole : slots.mapM (tlcHOL slots arguments).lookup = some words := by
    apply (list_mapM_eq_some_iff (tlcHOL slots arguments).lookup slots words).2
    refine ⟨?_, ?_⟩
    · simpa [words] using hslotsLength
    · intro j hj
      have hjSlots : j < slots.length := by simpa [words] using hslotsLength ▸ hj
      have hjWords : j < words.length := by simpa [words] using hj
      calc
        (slots[j]?).bind (tlcHOL slots arguments).lookup =
            some (words[j]'hjWords) := by
          rw [List.getElem?_eq_getElem hjSlots]
          simpa [words] using tlcHOL_lookup_getElem slots arguments j
            hslotsNodup hslotsLength hjSlots
        _ = words[j]? := by rw [List.getElem?_eq_getElem hjWords]
  have hgroupInput := withShapeHOL_getElem_eq_take_drop shapes slots i
    hslotsShape hiShape
  have hgroupWords := withShapeHOL_getElem_eq_take_drop shapes words i
    hshapeSize.symm hiShape
  have hpartition := withShapeHOL_mapFlatten shapes arguments hlen hshape hwf
  have hgroupWordsEq :
      (withShapeHOL shapes words)[i]'(by
        rw [withShapeHOL_eq_withShapeShapeOfHOL, withShape_length]
        simpa only [List.length_map] using hiShape) =
        flattenHOL value := by
    have hpartitionAt := congrArg
      (fun groups : List (List (HolWordLab width)) => groups[i]?) hpartition
    have hgroupBound : i < (withShapeHOL shapes words).length := by
      rw [withShapeHOL_eq_withShapeShapeOfHOL, withShape_length]
      simpa only [List.length_map] using hiShape
    have hvalueBound : i < (arguments.map flattenHOL).length := by
      simpa using hiArgument
    have hleft : (withShapeHOL shapes words)[i]? =
        some ((withShapeHOL shapes words)[i]'hgroupBound) :=
      List.getElem?_eq_getElem hgroupBound
    have hright : (arguments.map flattenHOL)[i]? =
        some ((arguments.map flattenHOL)[i]'hvalueBound) :=
      List.getElem?_eq_getElem hvalueBound
    rw [hleft, hright] at hpartitionAt
    simpa [words, value, List.getElem_map] using Option.some.inj hpartitionAt
  have hwindow := list_mapM_takeDrop_of_success
    (tlcHOL slots arguments).lookup slots words
    (sizeOfShapeHOL (.comb (shapes.take i))) (sizeOfShapeHOL shape) hwhole
  rw [← hgroupInput, ← hgroupWords] at hwindow
  rw [hgroupWordsEq] at hwindow
  exact hwindow

/-! Exact call-context invariant slice for HOL `locals_rel_def`. The first two
conjuncts are independent of the values being bound: distinct formal names,
distinct flat target slots, and the matching total shape size make the
`ctxt_fc`-generated slot groups non-overlapping and bounded by its `MAX_LIST`
value. -/
theorem panToCrepCallContextNoOverlapMaxExact
    {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (names : List MlS) (shapes : List ShapeHOL) (slots : List Nat)
    (_hnames : names.Nodup) (hnamesLength : names.length = shapes.length)
    (hslots : slots.Nodup)
    (hsize : slots.length = sizeOfShapeHOL (.comb shapes)) :
    noOverlapFiniteExact
        (ctxtFcExactHOL context.funcs context.eids names shapes slots).vars ∧
      ctxtMaxFiniteExact
        (ctxtFcExactHOL context.funcs context.eids names shapes slots).vmax
        (ctxtFcExactHOL context.funcs context.eids names shapes slots).vars := by
  let groups := withShapeHOL shapes slots
  let entries := names.zip (shapes.zip groups)
  have hvars :
      (ctxtFcExactHOL context.funcs context.eids names shapes slots).vars.lookup =
        FUPDATE_LIST FEMPTY entries := by
    rfl
  have hshapeSize :
      slots.length = Shape.shapeSize (.comb (shapes.map shapeOfHOL)) := by
    rw [shapeSizeCombShapeOfHOLExact]
    exact hsize
  have hgroups : groups = withShape (shapes.map shapeOfHOL) slots :=
    withShapeHOL_eq_withShapeShapeOfHOL shapes slots
  have hgroupsLength : groups.length = shapes.length := by
    rw [hgroups]
    simp [withShape_length]
  have hnamesGroups : names.length = groups.length := hnamesLength.trans hgroupsLength.symm
  have hshapeGroups : shapes.length = groups.length := hgroupsLength.symm
  have hentries := entries
  constructor
  · unfold noOverlapFiniteExact
    constructor
    · intro name shape namesForValue hlookup
      rw [hvars] at hlookup
      rcases flookupFupdateList_mem_or_base FEMPTY entries name
          (shape, namesForValue) hlookup with hmem | hbase
      · rcases hmem with ⟨entry, hentry, hname, hvalue⟩
        rcases entry with ⟨entryName, entryValue⟩
        rcases entryValue with ⟨entryShape, entrySlots⟩
        have hentryEq :
            (entryName, (entryShape, entrySlots)) = (name, (shape, namesForValue)) := by
          cases hname
          cases hvalue
          rfl
        rw [hentryEq] at hentry
        have hzipMem : (name, (shape, namesForValue)) ∈ entries := by
          simpa [entries] using hentry
        obtain ⟨index, hindexName, hindexPair, hnameAt, hpairAt⟩ :=
          mem_zip_getElem names (shapes.zip groups)
            (name, (shape, namesForValue)) hzipMem
        have hpairBound : index < min shapes.length groups.length := by
          simpa [List.length_zip] using hindexPair
        have hindexShape : index < shapes.length :=
          Nat.lt_of_lt_of_le hpairBound (Nat.min_le_left ..)
        have hindexProdShape : index < (shapes.map shapeOfHOL).length := by
          simpa using hindexShape
        have hindexGroup : index < groups.length :=
          Nat.lt_of_lt_of_le hpairBound (Nat.min_le_right ..)
        have hpairAt' :
            (shapes[index]'hindexShape, groups[index]'hindexGroup) =
              (shape, namesForValue) := by
          simpa using hpairAt
        have hslotsAt : groups[index]'hindexGroup = namesForValue :=
          congrArg Prod.snd hpairAt'
        have hprodGroupAt :
            (withShape (shapes.map shapeOfHOL) slots)[index]'(by
              rw [withShape_length]
              exact hindexProdShape) = namesForValue := by
          simpa [hgroups] using hslotsAt
        rw [← hprodGroupAt]
        exact withShapeGetElemNodupOfSlotsNodup
          (shapes.map shapeOfHOL) slots index hslots hshapeSize hindexProdShape
      · simp at hbase
    · intro name other shape otherShape namesForValue otherNames
        hnameLookup hotherLookup ⟨slot, hslot, hotherSlot⟩
      by_cases hnamesEq : name = other
      · exact hnamesEq
      rw [hvars] at hnameLookup hotherLookup
      have hiLookup := flookupFupdateList_mem_or_base FEMPTY entries name
        (shape, namesForValue) hnameLookup
      have hjLookup := flookupFupdateList_mem_or_base FEMPTY entries other
        (otherShape, otherNames) hotherLookup
      rcases hiLookup with ⟨iEntry, hiEntry, hiName, hiValue⟩ | hiBase
      · rcases hjLookup with ⟨jEntry, hjEntry, hjName, hjValue⟩ | hjBase
        · rcases iEntry with ⟨iName, iPair⟩
          rcases iPair with ⟨iShape, iSlots⟩
          rcases jEntry with ⟨jName, jPair⟩
          rcases jPair with ⟨jShape, jSlots⟩
          have hiEntryEq :
              (iName, (iShape, iSlots)) = (name, (shape, namesForValue)) := by
            cases hiName
            cases hiValue
            rfl
          have hjEntryEq :
              (jName, (jShape, jSlots)) = (other, (otherShape, otherNames)) := by
            cases hjName
            cases hjValue
            rfl
          rw [hiEntryEq] at hiEntry
          rw [hjEntryEq] at hjEntry
          have hiZipMem : (name, (shape, namesForValue)) ∈ entries := by
            simpa [entries] using hiEntry
          have hjZipMem : (other, (otherShape, otherNames)) ∈ entries := by
            simpa [entries] using hjEntry
          obtain ⟨i, hiNameBound, hiPairBound, hiNameAt, hiPairAt⟩ :=
            mem_zip_getElem names (shapes.zip groups)
              (name, (shape, namesForValue)) hiZipMem
          obtain ⟨j, hjNameBound, hjPairBound, hjNameAt, hjPairAt⟩ :=
            mem_zip_getElem names (shapes.zip groups)
              (other, (otherShape, otherNames)) hjZipMem
          have hiPairBound' : i < min shapes.length groups.length := by
            simpa [List.length_zip] using hiPairBound
          have hjPairBound' : j < min shapes.length groups.length := by
            simpa [List.length_zip] using hjPairBound
          have hiShape : i < shapes.length :=
            Nat.lt_of_lt_of_le hiPairBound' (Nat.min_le_left ..)
          have hjShape : j < shapes.length :=
            Nat.lt_of_lt_of_le hjPairBound' (Nat.min_le_left ..)
          have hiProdShape : i < (shapes.map shapeOfHOL).length := by simpa using hiShape
          have hjProdShape : j < (shapes.map shapeOfHOL).length := by simpa using hjShape
          have hiGroup : i < groups.length :=
            Nat.lt_of_lt_of_le hiPairBound' (Nat.min_le_right ..)
          have hjGroup : j < groups.length :=
            Nat.lt_of_lt_of_le hjPairBound' (Nat.min_le_right ..)
          have hiPairAt' :
              (shapes[i]'hiShape, groups[i]'hiGroup) = (shape, namesForValue) := by
            simpa using hiPairAt
          have hjPairAt' :
              (shapes[j]'hjShape, groups[j]'hjGroup) = (otherShape, otherNames) := by
            simpa using hjPairAt
          have hiSlots : groups[i]'hiGroup = namesForValue := congrArg Prod.snd hiPairAt'
          have hjSlots : groups[j]'hjGroup = otherNames := congrArg Prod.snd hjPairAt'
          have hindexNe : i ≠ j := by
            intro heq
            subst j
            exact hnamesEq (calc
              name = names[i]'hiNameBound := hiNameAt.symm
              _ = other := hjNameAt)
          have hdisjoint := listDisjoint_withShape_getElem
            (shapes.map shapeOfHOL) slots i j hslots hiProdShape hjProdShape
            hindexNe hshapeSize
          have hslotLeft :
              slot ∈ (withShape (shapes.map shapeOfHOL) slots)[i]'(by
                rw [withShape_length]
                exact hiProdShape) := by
            have hgroupMem : slot ∈ groups[i]'hiGroup := hiSlots.symm ▸ hslot
            simpa [hgroups] using hgroupMem
          have hslotRight :
              slot ∈ (withShape (shapes.map shapeOfHOL) slots)[j]'(by
                rw [withShape_length]
                exact hjProdShape) := by
            have hgroupMem : slot ∈ groups[j]'hjGroup := hjSlots.symm ▸ hotherSlot
            simpa [hgroups] using hgroupMem
          exact False.elim (hdisjoint slot hslotLeft hslotRight)
        · simp at hjBase
      · simp at hiBase
  · unfold ctxtMaxFiniteExact
    refine ⟨Nat.zero_le _, ?_⟩
    intro name shape namesForValue hlookup slot hslot
    rw [hvars] at hlookup
    rcases flookupFupdateList_mem_or_base FEMPTY entries name
        (shape, namesForValue) hlookup with hmem | hbase
    · rcases hmem with ⟨entry, hentry, hname, hvalue⟩
      rcases entry with ⟨entryName, entryValue⟩
      rcases entryValue with ⟨entryShape, entrySlots⟩
      have hentryEq :
          (entryName, (entryShape, entrySlots)) = (name, (shape, namesForValue)) := by
        cases hname
        cases hvalue
        rfl
      rw [hentryEq] at hentry
      have hzipMem : (name, (shape, namesForValue)) ∈ entries := by
        simpa [entries] using hentry
      obtain ⟨index, hindexName, hindexPair, hnameAt, hpairAt⟩ :=
        mem_zip_getElem names (shapes.zip groups)
          (name, (shape, namesForValue)) hzipMem
      have hpairBound : index < min shapes.length groups.length := by
        simpa [List.length_zip] using hindexPair
      have hindexShape : index < shapes.length :=
        Nat.lt_of_lt_of_le hpairBound (Nat.min_le_left ..)
      have hindexProdShape : index < (shapes.map shapeOfHOL).length := by
        simpa using hindexShape
      have hindexGroup : index < groups.length :=
        Nat.lt_of_lt_of_le hpairBound (Nat.min_le_right ..)
      have hpairAt' :
          (shapes[index]'hindexShape, groups[index]'hindexGroup) =
            (shape, namesForValue) := by
        simpa using hpairAt
      have hslotsAt : groups[index]'hindexGroup = namesForValue :=
        congrArg Prod.snd hpairAt'
      have hslotGroup : slot ∈ groups[index]'hindexGroup := hslotsAt.symm ▸ hslot
      have hslotFlat : slot ∈ slots := by
        have hslotGroupProd :
            slot ∈ (withShape (shapes.map shapeOfHOL) slots)[index]'(by
              rw [withShape_length]
              exact hindexProdShape) := by
          simpa [hgroups] using hslotGroup
        exact withShapeGetElemMemOfSlotsMem
          (shapes.map shapeOfHOL) slots index slot hshapeSize hindexProdShape hslotGroupProd
      have hmax := maxList_ge_of_mem slots slot hslotFlat
      simpa [ctxtFcExactHOL, maxList] using hmax
    · simp at hbase

/-! The third conjunct of HOL `locals_rel` for Call binds a Pan source
argument to its `ctxt_fc` slot group, then obtains that argument's exact
`flatten` from the HOL `tlc` map. This helper uses the exact `slcHOL`,
`tlcHOL`, `ShapeHOL`, and `ValueHOL` carriers; it is a projection, not the
full HOL Call theorem. -/
theorem panToCrepCallLocalsRelArgumentBindingsExact
    {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (variableShapes : List (MlS × ShapeHOL))
    (arguments : List (ValueHOL width)) (slots : List Nat)
    (hnames : (variableShapes.map Prod.fst).Nodup)
    (hlen : variableShapes.length = arguments.length)
    (hshape : ∀ i (hvar : i < variableShapes.length)
      (harg : i < arguments.length),
      (variableShapes[i]'hvar).2 = shapeOfHOLExact (arguments[i]'harg))
    (hslots : slots.Nodup)
    (hslotsLength : slots.length = (arguments.map flattenHOL).flatten.length)
    (hwf : ∀ value, value ∈ arguments →
      isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true) :
    panToCrepLocalsRelFiniteExact
      (ctxtFcExactHOL context.funcs context.eids
        (variableShapes.map Prod.fst) (variableShapes.map Prod.snd) slots)
      (slcHOL variableShapes arguments) (tlcHOL slots arguments) := by
  classical
  let names := variableShapes.map Prod.fst
  let shapes := variableShapes.map Prod.snd
  let groups := withShapeHOL shapes slots
  let words := (arguments.map flattenHOL).flatten
  have hnamesLength : names.length = shapes.length := by simp [names, shapes]
  have hgroupsLength : groups.length = shapes.length := by
    unfold groups
    rw [withShapeHOL_eq_withShapeShapeOfHOL, withShape_length]
    simp only [List.length_map]
  have hshapeList : shapes.length = arguments.length := by
    simpa [shapes] using hlen
  have hshapeAt : ∀ i (hsh : i < shapes.length) (harg : i < arguments.length),
      shapes[i]'hsh = shapeOfHOLExact (arguments[i]'harg) := by
    intro i hsh harg
    simpa [shapes, List.getElem_map] using hshape i
      (by simpa [names, shapes] using hsh) harg
  have hshapeSize : sizeOfShapeHOL (.comb shapes) = words.length := by
    simpa [words] using shapeSizeCombHOL_eq_flattenHOL_length shapes arguments
      hshapeList hshapeAt hwf
  have hslotsShape : slots.length = sizeOfShapeHOL (.comb shapes) := by
    simpa [words] using hslotsLength.trans hshapeSize.symm
  have hcontextInvariants := panToCrepCallContextNoOverlapMaxExact
    context names shapes slots hnames hnamesLength hslots hslotsShape
  unfold panToCrepLocalsRelFiniteExact
  refine ⟨hcontextInvariants.1, hcontextInvariants.2, ?_⟩
  intro name value hsourceLookup
  have hsourceLookupFinite :
      FLOOKUP (FUPDATE_LIST FEMPTY (names.zip arguments)) name = some value := by
    have hmapEq := FUPDATE_LIST_HOL_eq_FUPDATE_LIST
      (FEMPTY : FiniteMap MlS (ValueHOL width)) (names.zip arguments)
    rw [← hmapEq]
    simpa [FLOOKUP] using
      (holFmapAsFiniteSupportResultWitness_slcHOL variableShapes arguments name ▸
        hsourceLookup)
  rcases flookupFupdateList_mem_or_base (FEMPTY : FiniteMap MlS (ValueHOL width))
      (names.zip arguments) name value hsourceLookupFinite with hentry | hbase
  · obtain ⟨entry, hmem, hentryName, hentryValue⟩ := hentry
    obtain ⟨i, hiName, hiArgument, hnameAt, hargumentAt⟩ :=
      mem_zip_getElem names arguments entry hmem
    have hiVariable : i < variableShapes.length := by
      simpa [names] using hiName
    have hnameIs : names[i]'hiName = name := by simpa [hentryName] using hnameAt
    have hvalueIs : arguments[i]'hiArgument = value := by
      simpa [hentryValue] using hargumentAt
    have hshapeIndex : i < shapes.length := by simpa [shapes] using hiVariable
    have hgroupIndex : i < groups.length := by
      rw [hgroupsLength]
      exact hshapeIndex
    have hgroupShape : shapes[i]'hshapeIndex = shapeOfHOLExact value := by
      rw [hshapeAt i hshapeIndex hiArgument, hvalueIs]
    have hcontextLength : names.length = (shapes.zip groups).length := by
      simp [List.length_zip, hnamesLength, hgroupsLength]
    have hcontextLookup := FLOOKUP_FUPDATE_LIST_zip_getElem
      names (shapes.zip groups) FEMPTY i hnames hcontextLength hiName
    have hzipIndex : i < (shapes.zip groups).length := by
      rw [← hcontextLength]
      exact hiName
    have hgroupBound : i < (withShapeHOL shapes slots).length := by
      rw [withShapeHOL_eq_withShapeShapeOfHOL, withShape_length]
      simpa only [List.length_map] using hshapeIndex
    have hcontextValue :
        ((shapes.zip groups)[i]'hzipIndex) =
          (shapeOfHOLExact value, groups[i]'hgroupBound) := by
      simp only [List.getElem_zip]
      exact congrArg (fun shape => (shape, groups[i]'hgroupBound)) hgroupShape
    have hcontextLookup' :
        (ctxtFcExactHOL context.funcs context.eids names shapes slots).vars.lookup name =
          some (shapeOfHOLExact value, groups[i]'hgroupBound) := by
      simpa [ctxtFcExactHOL, names, shapes, groups, FLOOKUP] using
        (hnameIs ▸ hcontextLookup.trans (congrArg some hcontextValue))
    have hargumentWf :
        isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true := by
      rw [← hvalueIs]
      exact hwf (arguments[i]'hiArgument) (List.getElem_mem hiArgument)
    have hmapGroups := tlcHOLWithShapeMapM shapes arguments slots i hslots
      hslotsLength hshapeSize hshapeList hshapeAt hwf hshapeIndex hiArgument
    rw [hvalueIs] at hmapGroups
    refine ⟨groups[i]'hgroupBound, flattenHOL value, hcontextLookup', ?_, rfl,
      hargumentWf⟩
    simpa [groups] using hmapGroups
  · simp at hbase

/-! The three owning carriers used by the exact Call theorem's finite-map
relations. These same-module witnesses make the named carrier translations
visible to the HOL-reference checker. -/
namespace CallPreservationFiniteMapWitnesses

theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  ⟨fun state h => PanSemStateFiniteExact.toExact_ofExact state h,
    fun state => PanSemStateFiniteExact.ofExact_toExact state⟩

theorem holFmapAsFiniteSupportRelationWitness_PanToCrepContextExact
    {width : Nat} [NeZero width] (context : PanToCrepContextExact width) :
    PanToCrepContextExact.ofBroad (PanToCrepContextExact.toBroad context) = context := by
  cases context
  rfl

theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state :=
  CrepSemBroadState.ofBroad_toBroad state

end CallPreservationFiniteMapWitnesses

private theorem listRelGetElemExact {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : ListRel R xs ys) :
    ∀ i (hxs : i < xs.length) (hys : i < ys.length),
      R (xs[i]'hxs) (ys[i]'hys) := by
  induction h with
  | nil =>
      intro i hxs _
      simp at hxs
  | cons head tail ih =>
      intro i hxs hys
      cases i with
      | zero => simpa using head
      | succ i =>
          exact ih i (by simpa using hxs) (by simpa using hys)

/-! Exact port of HOL `call_preserve_state_code_locals_rel`
(`pan_to_crepProofScript.sml:2355-2458`). The premise `hpreLocals` is the
pre-call relation `locals_rel ctxt s.locals t.locals` at source lines
2355-2364. The final conjunct instead relates the newly installed callee
locals under `ctxt_fc` at lines 2374-2378; these are distinct contexts and
maps. The statement keeps all HOL premises and all four conclusions in their
source order. Its only carrier translation is the listed canonical
finite-support representation of the named Pan and Crep maps. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml"
  "call_preserve_state_code_locals_rel"
  (fmap_as_finite_support_relation := [
    PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals,
    PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes,
    PanToCrepContextExact.vars, PanToCrepContextExact.funcs,
    PanToCrepContextExact.eids, CrepSemHOLState.locals, CrepSemHOLState.code])]
theorem panToCrepCallPreserveStateCodeLocalsRelExact
    {width : Nat} {σ : Type} [NeZero width]
    (returnShape : ShapeHOL)
    (context : PanToCrepContextExact width)
    (source : PanSemStateFiniteExact width σ)
    (target : CrepSemHOLState width σ)
    (functionName : MlS)
    (variableShapes : List (MlS × ShapeHOL))
    (program : ProgHOL width)
    (arguments : List (ValueHOL width)) (names : List Nat)
    (hDistinctVariables : (variableShapes.map Prod.fst).Nodup)
    (hArgumentShapes : ListRel
      (fun variableShape argument =>
        variableShape.2 = shapeOfHOLExact argument) variableShapes arguments)
    (hstate : panToCrepStateRelFiniteExact source target)
    (hcode : codeRelExactHOLW context source.code target.code)
    (hexcp : panToCrepExcpRelFiniteExact context.eids source.eshapes)
    (hpreLocals : panToCrepLocalsRelFiniteExact
      context source.locals target.locals)
    (_hsourceCodeLookup : source.code.lookup functionName =
      some (variableShapes, program, returnShape))
    (_hcontextFunctionLookup : context.funcs.lookup functionName =
      some (variableShapes, returnShape))
    (hDistinctNames : names.Nodup)
    (_hShapeSize : sizeOfShapeHOL (.comb (variableShapes.map Prod.snd)) =
      (arguments.map flattenHOL).flatten.length)
    (_htargetCodeLookup : target.code.lookup functionName =
      some (names, compileProgExactHOLW
        (ctxtFcExactHOL context.funcs context.eids
          (variableShapes.map Prod.fst) (variableShapes.map Prod.snd) names)
        program))
    (hNamesLength : names.length = (arguments.map flattenHOL).flatten.length)
    (hArgumentsWellFormed : ∀ argument, argument ∈ arguments →
        isWfShapeExactHOL ([] : StructContextExact)
        (shapeOfHOLExact argument) = true) :
    panToCrepStateRelFiniteExact
        ({source.decClockHOLFinite with
          locals := slcHOL variableShapes arguments})
        ({decClockCrepSemHOL target with
          locals := tlcHOL names arguments}) ∧
    codeRelExactHOLW
        (ctxtFcExactHOL context.funcs context.eids
          (variableShapes.map Prod.fst) (variableShapes.map Prod.snd) names)
        source.decClockHOLFinite.code (decClockCrepSemHOL target).code ∧
    panToCrepExcpRelFiniteExact
        (ctxtFcExactHOL context.funcs context.eids
          (variableShapes.map Prod.fst) (variableShapes.map Prod.snd) names).eids
        source.decClockHOLFinite.eshapes ∧
    panToCrepLocalsRelFiniteExact
        (ctxtFcExactHOL context.funcs context.eids
          (variableShapes.map Prod.fst) (variableShapes.map Prod.snd) names)
        (slcHOL variableShapes arguments) (tlcHOL names arguments) := by
  have _preCallLocalsWasAssumed := hpreLocals
  have hlengthAndShapes :=
    vshapesArgsRel_imp_eq_len_MAP variableShapes arguments hArgumentShapes
  have hlength : variableShapes.length = arguments.length := hlengthAndShapes.1
  have hshapeAt : ∀ i (hvariable : i < variableShapes.length)
      (hargument : i < arguments.length),
      (variableShapes[i]'hvariable).2 =
        shapeOfHOLExact (arguments[i]'hargument) := by
    intro i hvariable hargument
    exact listRelGetElemExact hArgumentShapes i hvariable hargument
  have hstatePost := panToCrepCallStateRelFiniteExactLocalUpdate
    source target (slcHOL variableShapes arguments) (tlcHOL names arguments) hstate
  have hcodePost :
      codeRelExactHOLW
        (ctxtFcExactHOL context.funcs context.eids
          (variableShapes.map Prod.fst) (variableShapes.map Prod.snd) names)
        source.decClockHOLFinite.code (decClockCrepSemHOL target).code := by
    simpa [codeRelExactHOLW, ctxtFcExactHOL,
      PanSemStateFiniteExact.decClockHOLFinite, decClockCrepSemHOL] using hcode
  have hexcpPost :
      panToCrepExcpRelFiniteExact
        (ctxtFcExactHOL context.funcs context.eids
          (variableShapes.map Prod.fst) (variableShapes.map Prod.snd) names).eids
        source.decClockHOLFinite.eshapes := by
    simpa [ctxtFcExactHOL, PanSemStateFiniteExact.decClockHOLFinite] using hexcp
  have hlocalsPost := panToCrepCallLocalsRelArgumentBindingsExact
    context variableShapes arguments names hDistinctVariables hlength hshapeAt
    hDistinctNames hNamesLength hArgumentsWellFormed
  refine ⟨?_, hcodePost, hexcpPost, hlocalsPost⟩
  simpa [PanSemStateFiniteExact.decClockHOLFinite, decClockCrepSemHOL] using hstatePost

/-! Source review of HOL `eval_var_cexp_present_ctxt`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:693-748`). It quantifies
    over source state, expression, evaluated value, target state, context,
    compiled expression list, and shape. Its six premises are, in order,
    `state_rel`, successful source `eval`, `code_rel`, `locals_rel`,
    `localised_exp`, and `compile_exp`; its conclusion universally says every
    `var_cexp` name in the compiled list occurs in some `ct.vars` slot list.
    The theorem below preserves those binders, hypotheses, and conclusion.

    The source state, target state, and context use the exact finite-support
    carriers of the state, evaluator, and relation ports. The qualifier names
    source `locals`/`globals`/`code`, target `locals`/`code`, and context
    `vars`/`funcs`/`eids`, the finite-map fields used by the source evaluator
    and the exact relation premises. The source syntax is constructor-for-
    constructor `ExpHOL`, `MlS` is HOL `mlstring`, and `localisedExpHOL` is its
    exact predicate port. No target evaluation or result assumption is added.
    `words_as_type_indexed_bitvec` records HOL's positive type-indexed word
    dimension as `BitVec width` under `[NeZero width]`.

    The conclusion follows from the stronger exact compiler-only provenance
    theorem `compileExpExactHOLW_vars_from_context`; evaluator and relation
    premises remain present to match HOL even though this compiler fact does
    not need them. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "eval_var_cexp_present_ctxt"
  (fmap_as_finite_support_relation := [
    PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals,
    PanSemStateFiniteExact.code, CrepSemHOLState.locals, CrepSemHOLState.code,
    PanToCrepContextExact.vars, PanToCrepContextExact.funcs,
    PanToCrepContextExact.eids])
  (words_as_type_indexed_bitvec)]
theorem evalVarCexpPresentContextExactHOL
    {width : Nat} {ffiState : Type} [NeZero width]
    (source : PanSemStateFiniteExact width ffiState)
    (expression : Flapjack.Pancake.PanLang.ExpHOL width)
    (value : ValueHOL width)
    (target : CrepSemHOLState width ffiState)
    (context : PanToCrepContextExact width)
    (expressions : List (CrepExpHOL width))
    (shape : ShapeHOL)
    (_hstate : panToCrepStateRelFiniteExact source target)
    (_heval : letI : DecidablePred source.memaddrs :=
      fun address => Classical.propDecidable (source.memaddrs address)
      source.evalHOLFinite expression = some value)
    (_hcode : codeRelExactHOLW context source.code target.code)
    (_hlocals : panToCrepLocalsRelFiniteExact context source.locals target.locals)
    (_hlocalized : localisedExpHOL expression = true)
    (hcompile : compileExpExactHOLW context expression = (expressions, shape)) :
    ∀ name, name ∈ expressions.flatMap crepExpVarsHOL →
      ∃ sourceName sourceShape slots,
        context.vars.lookup sourceName = some (sourceShape, slots) ∧
        name ∈ slots := by
  intro name hname
  have hSupport := compileExpExactHOLW_vars_from_context context
  have hcompiledName : name ∈
      (compileExpExactHOLW context expression).1.flatMap crepExpVarsHOL := by
    simpa [hcompile] using hname
  exact hSupport.1 expression name hcompiledName

/-- Exact port of HOL `eval_map_var_cexp_present_ctxt`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:1077`). The five
    universally quantified inputs are the expression list, values, source
    state, target state, and Pan-to-Crep context. Its premises preserve HOL's
    successful `MAP (eval s) es`, `state_rel`, `code_rel`, `locals_rel`, and
    `EVERY localised_exp` conjuncts. The conclusion is the exact nested
    `FLAT`/`MAP` variable-name membership from each compiled expression to a
    slot list in `ctxt.vars`. `compileExpExactHOLWList` and
    `crepExpVarsHOL` preserve HOL's `compile_exp` and `var_cexp` structure;
    source/target/context carriers and cross-pass relations use the exact
    finite-support ports. The relation qualifier lists the map fields read by
    the three relation premises and context conclusion. The evaluator premise
    supplies classical decidability locally for the HOL memory-set predicate;
    it introduces no premise. The proof uses the stronger exact compiler-only
    provenance lemma, while retaining the evaluator and relation hypotheses to
    match HOL's statement. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "eval_map_var_cexp_present_ctxt"
  (fmap_as_finite_support_relation := [
    PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals,
    PanSemStateFiniteExact.code, CrepSemHOLState.locals, CrepSemHOLState.code,
    PanToCrepContextExact.vars, PanToCrepContextExact.funcs,
    PanToCrepContextExact.eids])
  (words_as_type_indexed_bitvec)]
theorem evalMapVarCexpPresentContextExactHOL
    {width : Nat} {ffiState : Type} [NeZero width]
    (expressions : List (Flapjack.Pancake.PanLang.ExpHOL width))
    (values : List (ValueHOL width))
    (source : PanSemStateFiniteExact width ffiState)
    (target : CrepSemHOLState width ffiState)
    (context : PanToCrepContextExact width)
    (_heval : letI : DecidablePred source.memaddrs :=
      fun address => Classical.propDecidable (source.memaddrs address)
      expressions.map source.evalHOLFinite = values.map some)
    (_hstate : panToCrepStateRelFiniteExact source target)
    (_hcode : codeRelExactHOLW context source.code target.code)
    (_hlocals : panToCrepLocalsRelFiniteExact context source.locals target.locals)
    (_hlocalized : expressions.all localisedExpHOL = true) :
    ∀ name, name ∈
        ((compileExpExactHOLWList context expressions).flatMap Prod.fst).flatMap
          crepExpVarsHOL →
      ∃ sourceName shape slots,
        context.vars.lookup sourceName = some (shape, slots) ∧ name ∈ slots := by
  intro name hname
  exact (compileExpExactHOLW_vars_from_context context).2 expressions name hname

end Flapjack
