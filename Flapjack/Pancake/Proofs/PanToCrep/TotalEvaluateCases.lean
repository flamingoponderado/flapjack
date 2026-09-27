import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.Semantics.PanSem.TotalMeasureIf
import Flapjack.Pancake.Semantics.CrepSem.TotalEval
import Flapjack.Pancake.Semantics.PanSem.EvaluateFinite
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.PanToCrep.CompileProg
import Flapjack.Pancake.Proofs.PanToCrep.CodeRelExact
import Flapjack.Pancake.Proofs.PanToCrep.StateRelFiniteSupport
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

/-!
# Total evaluator cases for Pan-to-Crep correctness

The declarations here assemble selected constructor cases from the total,
HOL-result-shaped source and target evaluator clauses. They are induction-case
support for `pc_compile_correct`; they do not claim the complete evaluator
induction or receive a standalone `@[hol]` reference.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
  (MlS ShapeHOL shapeOfHOL sizeOfShapeHOL sizeOfShapesHOL withShapeHOL)

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

/-! The exception-relation conjunct of HOL
`call_preserve_state_code_locals_rel` (`pan_to_crepProofScript.sml:2355`) is
stable across the exact call-context and source clock updates. HOL
`ctxt_fc_def` keeps `ctxt.eids`, and Pan `dec_clock_def` keeps `s.eshapes`;
the exact carriers expose those equations directly. This is only a projected
conjunct helper, not a tagged port of the full Call theorem. -/
theorem panToCrepCallExcpRelFiniteExactContextUpdate
    {width : Nat} {σ : Type} [NeZero width]
    (context : PanToCrepContextExact width)
    (source : PanSemStateFiniteExact width σ)
    (variableShapes : List (MlS × ShapeHOL))
    (names : List Nat)
    (hrel : panToCrepExcpRelFiniteExact context.eids source.eshapes) :
    panToCrepExcpRelFiniteExact
      (ctxtFcExactHOL context.funcs context.eids
        (variableShapes.map Prod.fst) (variableShapes.map Prod.snd) names).eids
      source.decClockHOLFinite.eshapes := by
  simpa [ctxtFcExactHOL, PanSemStateFiniteExact.decClockHOLFinite] using hrel

/-! The code-relation conjunct of the HOL Call-preservation theorem is also
stable under this context/state update. `code_rel_def` reads `ctxt.funcs` and
`ctxt.eids`, which `ctxt_fc_def` preserves, and it reads both code maps, which
`dec_clock_def` leaves unchanged. Its compiled function entries therefore
remain the exact `compile_def` entries. This is only an untagged projected
conjunct helper. -/
theorem panToCrepCallCodeRelExactContextUpdate
    {width : Nat} {σ : Type} [NeZero width]
    (context : PanToCrepContextExact width)
    (source : PanSemStateFiniteExact width σ)
    (target : CrepSemHOLState width σ)
    (variableShapes : List (MlS × ShapeHOL))
    (names : List Nat)
    (hcode : codeRelExactHOLW context source.code target.code) :
    codeRelExactHOLW
      (ctxtFcExactHOL context.funcs context.eids
        (variableShapes.map Prod.fst) (variableShapes.map Prod.snd) names)
      source.decClockHOLFinite.code
      (decClockCrepSemHOL target).code := by
  simpa [codeRelExactHOLW, ctxtFcExactHOL,
    PanSemStateFiniteExact.decClockHOLFinite, decClockCrepSemHOL] using hcode

/-! The `Skip` constructor case uses the total result×state clauses on both
  sides. The source evaluator uses the production `PanSemState`, and the target
  evaluator uses the code-bearing runtime state converted by `toHolState`. The
  compiled target syntax is exactly `Skip`. The returned runtime post-state is
  the original target state, so all four state/code/exception/local relations
  are established at the post-state boundary without a target-run premise. -/
theorem panToCrepTotalSkipStateCase
    {σ : Type _}
    (context : PanToCrepProofContext (RiscV.Word 64))
    (sourceState : PanSemState (RiscV.Word 64) (FfiState σ))
    (targetState : CrepRuntimeState (RiscV.Word 64) σ)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code)
      targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (hlocals : localsRel context sourceState.locals targetState.locals) :
    panSemEvaluateExprIfFragmentRiscV64ByMeasure (.leaf .skip) sourceState =
        (none, sourceState) ∧
    compileCodeRelProg context (.skip : Prog (RiscV.Word 64)) =
        (CrepProg.skip : CrepProg (BitVec 64)) ∧
    ∃ targetPost : CrepRuntimeState (RiscV.Word 64) σ,
      evalCrepClockLeaf .skip targetState.toHolState =
          (none, targetPost.toHolState) ∧
      stateRel sourceState targetPost ∧
      codeRel context (panSemCodeAsLookup sourceState.code) targetPost.code ∧
      excpRel context.eids sourceState.exceptionShapes ∧
      localsRel context sourceState.locals targetPost.locals := by
  refine ⟨by simp [panSemEvaluateExprIfFragmentRiscV64ByMeasure], rfl, ?_⟩
  refine ⟨targetState, by simp, hstate, ?_, hexcp, hlocals⟩
  exact hcode

/-! Source-reviewed prerequisite for HOL `pc_compile_correct[Skip]`.
The proof resumes this leaf case at `pan_to_crepProofScript.sml:493-496`;
the source evaluator clause is `panSemScript.sml:557`, the exact compiler
clause is `pan_to_crepScript.sml:140`, and the target evaluator clause is
`crepSemScript.sml:241`. Over `ProgHOL` and `CrepProgHOL`, source `Skip`
evaluates to normal completion without changing the source state, compiles to
target `Skip`, and the total Crep evaluator returns normal completion with the
same target state. This exact-carrier helper carries state/code/local/exception
relations unchanged and assumes no target run or result. It is distinct from
`panToCrepTotalSkipStateCase`, which uses production Pan/Crep carriers. This is
not the full `pc_compile_correct` theorem and carries no `@[hol]` tag. -/
theorem panToCrepExactSkipTransition
    {width : Nat} {σ : Type} [NeZero width]
    (sourceContext : PanSemStateFiniteExact.FiniteEvalContext width σ)
    (targetState : CrepSemHOLState width σ)
    (compileContext : PanToCrepContextExact width)
    (memDec : (a : BitVec width) → Decidable (targetState.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (targetState.shMemaddrs a))
    (hstate : panToCrepStateRelFiniteExact sourceContext.state targetState)
    (hlocals : panToCrepLocalsRelFiniteExact compileContext
      sourceContext.state.locals targetState.locals)
    (hcode : codeRelExactHOLW compileContext sourceContext.state.code
      targetState.code)
    (hexcp : panToCrepExcpRelFiniteExact compileContext.eids
      sourceContext.state.eshapes) :
    PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
        (.skip : Flapjack.Pancake.PanLang.ProgHOL width) sourceContext =
      some (none, sourceContext) ∧
    compileProgExactHOLW compileContext
        (.skip : Flapjack.Pancake.PanLang.ProgHOL width) =
      (.skip : CrepProgHOL width) ∧
    evalCrepSemHOLProg targetState memDec shMemDec
        (compileProgExactHOLW compileContext
          (.skip : Flapjack.Pancake.PanLang.ProgHOL width)) =
      (none, targetState) ∧
    panToCrepStateRelFiniteExact sourceContext.state targetState ∧
    panToCrepLocalsRelFiniteExact compileContext
      sourceContext.state.locals targetState.locals ∧
    codeRelExactHOLW compileContext sourceContext.state.code targetState.code ∧
    panToCrepExcpRelFiniteExact compileContext.eids
      sourceContext.state.eshapes := by
  refine ⟨?_, ?_, ?_, hstate, hlocals, hcode, hexcp⟩
  · simp [PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext]
  · simp [compileProgExactHOLW]
  · rw [show compileProgExactHOLW compileContext
      (.skip : Flapjack.Pancake.PanLang.ProgHOL width) =
        (.skip : CrepProgHOL width) by simp [compileProgExactHOLW]]
    exact evalCrepSemHOLProg_skip targetState memDec shMemDec

/-! Source-reviewed prerequisite for HOL `pc_compile_correct[Break]`.
The HOL proof resumes this nonrecursive case at
`pan_to_crepProofScript.sml:499-503`; the source evaluator equation is
`panSemScript.sml:623`, the compiler equation is `pan_to_crepScript.sml:219`,
and the target evaluator equation is `crepSemScript.sml:309`. They give source
`Break`, compiled `Break 0`, and target `Break 0`, all with unchanged states.
This helper checks those equations over the finite-support HOL-shaped carriers
and records preservation of the exact state/local/code/exception relations.
It is still a Flapjack-specific case helper rather than the assembled theorem,
so it carries no `@[hol]` tag. -/
theorem panToCrepExactBreakTransition
    {width : Nat} {σ : Type} [NeZero width]
    (sourceContext : PanSemStateFiniteExact.FiniteEvalContext width σ)
    (targetState : CrepSemHOLState width σ)
    (compileContext : PanToCrepContextExact width)
    (memDec : (a : BitVec width) → Decidable (targetState.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (targetState.shMemaddrs a))
    (hstate : panToCrepStateRelFiniteExact sourceContext.state targetState)
    (hlocals : panToCrepLocalsRelFiniteExact compileContext
      sourceContext.state.locals targetState.locals)
    (hcode : codeRelExactHOLW compileContext sourceContext.state.code targetState.code)
    (hexcp : panToCrepExcpRelFiniteExact compileContext.eids
      sourceContext.state.eshapes) :
    PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
        (.break : Flapjack.Pancake.PanLang.ProgHOL width) sourceContext =
      some (some .break, sourceContext) ∧
    compileProgExactHOLW compileContext
        (.break : Flapjack.Pancake.PanLang.ProgHOL width) =
      (.break 0 : CrepProgHOL width) ∧
    evalCrepSemHOLProg targetState memDec shMemDec
        (compileProgExactHOLW compileContext
          (.break : Flapjack.Pancake.PanLang.ProgHOL width)) =
      (some (.break 0), targetState) ∧
    panToCrepStateRelFiniteExact sourceContext.state targetState ∧
    panToCrepLocalsRelFiniteExact compileContext
      sourceContext.state.locals targetState.locals ∧
    codeRelExactHOLW compileContext sourceContext.state.code targetState.code ∧
    panToCrepExcpRelFiniteExact compileContext.eids
      sourceContext.state.eshapes := by
  refine ⟨?_, ?_, ?_, hstate, hlocals, hcode, hexcp⟩
  · simp [PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext]
  · simp [compileProgExactHOLW]
  · rw [show compileProgExactHOLW compileContext
      (.break : Flapjack.Pancake.PanLang.ProgHOL width) =
        (.break 0 : CrepProgHOL width) by simp [compileProgExactHOLW]]
    exact evalCrepSemHOLProg_break targetState memDec shMemDec 0

/-! Source-reviewed prerequisite for HOL `pc_compile_correct[Continue]`.
The proof resumes the nonrecursive constructor at
`pan_to_crepProofScript.sml:505-509`; the source evaluator equation is
`panSemScript.sml:624`, the exact compiler clause is
`pan_to_crepScript.sml:220`, and the target evaluator equation is
`crepSemScript.sml:313`. This slice establishes source `Continue`, compiled
`Continue 0`, and target `Continue 0`, preserving the exact source/target
state and local/code/exception relations. It remains a Flapjack-specific case
helper rather than the full `pc_compile_correct` theorem, so it carries no
`@[hol]` tag. The production-codec bridge
`compileProgExactHOLW_continue_bridge` is a distinct theorem and is not
duplicated here. -/
theorem panToCrepExactContinueTransition
    {width : Nat} {σ : Type} [NeZero width]
    (sourceContext : PanSemStateFiniteExact.FiniteEvalContext width σ)
    (targetState : CrepSemHOLState width σ)
    (compileContext : PanToCrepContextExact width)
    (memDec : (a : BitVec width) → Decidable (targetState.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (targetState.shMemaddrs a))
    (hstate : panToCrepStateRelFiniteExact sourceContext.state targetState)
    (hlocals : panToCrepLocalsRelFiniteExact compileContext
      sourceContext.state.locals targetState.locals)
    (hcode : codeRelExactHOLW compileContext sourceContext.state.code targetState.code)
    (hexcp : panToCrepExcpRelFiniteExact compileContext.eids
      sourceContext.state.eshapes) :
    PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
        (.continue : Flapjack.Pancake.PanLang.ProgHOL width) sourceContext =
      some (some .continue, sourceContext) ∧
    compileProgExactHOLW compileContext
        (.continue : Flapjack.Pancake.PanLang.ProgHOL width) =
      (.continue 0 : CrepProgHOL width) ∧
    evalCrepSemHOLProg targetState memDec shMemDec
        (compileProgExactHOLW compileContext
          (.continue : Flapjack.Pancake.PanLang.ProgHOL width)) =
      (some (.continue 0), targetState) ∧
    panToCrepStateRelFiniteExact sourceContext.state targetState ∧
    panToCrepLocalsRelFiniteExact compileContext
      sourceContext.state.locals targetState.locals ∧
    codeRelExactHOLW compileContext sourceContext.state.code targetState.code ∧
    panToCrepExcpRelFiniteExact compileContext.eids
      sourceContext.state.eshapes := by
  refine ⟨?_, ?_, ?_, hstate, hlocals, hcode, hexcp⟩
  · simp [PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext]
  · simp [compileProgExactHOLW]
  · rw [show compileProgExactHOLW compileContext
      (.continue : Flapjack.Pancake.PanLang.ProgHOL width) =
        (.continue 0 : CrepProgHOL width) by simp [compileProgExactHOLW]]
    exact evalCrepSemHOLProg_continue targetState memDec shMemDec 0

/-! Source-reviewed prerequisite for HOL `pc_compile_correct[Annot]`.
The proof resumes this no-op constructor at
`pan_to_crepProofScript.sml:511-515`; the source evaluator clause is
`panSemScript.sml:656`, the exact compiler erasure is
`pan_to_crepScript.sml:307`, and the target `Skip` evaluator clause is
`crepSemScript.sml:241`. The exact source carrier uses `MlS` tag/text values;
the compiler erases both and produces `Skip`, so both evaluators preserve their
states. This helper proves that target transition directly and preserves the
finite-exact state/code/local/exception relations without assuming a target
run. `code_rel_def` is represented by `codeRelExactHOLW`; this no-op case
carries it unchanged. This remains a Flapjack-specific prerequisite rather
than the full `pc_compile_correct` case, so no `@[hol]` tag is claimed. The
generic String-based `panToCrepPcCompileCorrectAnnotCodeState` does not
establish this exact-carrier result. -/
theorem panToCrepExactAnnotTransition
    {width : Nat} {σ : Type} [NeZero width]
    (sourceContext : PanSemStateFiniteExact.FiniteEvalContext width σ)
    (targetState : CrepSemHOLState width σ)
    (compileContext : PanToCrepContextExact width)
    (memDec : (a : BitVec width) → Decidable (targetState.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (targetState.shMemaddrs a))
    (tag text : Flapjack.Pancake.PanLang.MlS)
    (hstate : panToCrepStateRelFiniteExact sourceContext.state targetState)
    (hlocals : panToCrepLocalsRelFiniteExact compileContext
      sourceContext.state.locals targetState.locals)
    (hcode : codeRelExactHOLW compileContext sourceContext.state.code
      targetState.code)
    (hexcp : panToCrepExcpRelFiniteExact compileContext.eids
      sourceContext.state.eshapes) :
    PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
        (.annot tag text : Flapjack.Pancake.PanLang.ProgHOL width) sourceContext =
      some (none, sourceContext) ∧
    compileProgExactHOLW compileContext
        (.annot tag text : Flapjack.Pancake.PanLang.ProgHOL width) =
      (.skip : CrepProgHOL width) ∧
    evalCrepSemHOLProg targetState memDec shMemDec
        (compileProgExactHOLW compileContext
          (.annot tag text : Flapjack.Pancake.PanLang.ProgHOL width)) =
      (none, targetState) ∧
    panToCrepStateRelFiniteExact sourceContext.state targetState ∧
    panToCrepLocalsRelFiniteExact compileContext
      sourceContext.state.locals targetState.locals ∧
    codeRelExactHOLW compileContext sourceContext.state.code targetState.code ∧
    panToCrepExcpRelFiniteExact compileContext.eids
      sourceContext.state.eshapes := by
  refine ⟨?_, ?_, ?_, hstate, hlocals, hcode, hexcp⟩
  · simp [PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext]
  · simp [compileProgExactHOLW]
  · rw [show compileProgExactHOLW compileContext
      (.annot tag text : Flapjack.Pancake.PanLang.ProgHOL width) =
        (.skip : CrepProgHOL width) by simp [compileProgExactHOLW]]
    exact evalCrepSemHOLProg_skip targetState memDec shMemDec

/-! Source-reviewed prerequisite for HOL `pc_compile_correct[Tick]`.
The HOL proof resumes this clock-sensitive case at
`pan_to_crepProofScript.sml:517-524`; its exact transition clauses are
`panSemScript.sml:653`, `pan_to_crepScript.sml:306`, and
`crepSemScript.sml:332`. The helper gives both clock branches: at zero both
evaluators time out and clear locals; above zero both complete normally and
decrement the clock. It proves the target evaluation directly and preserves
the exact state/local/code/exception relations. This remains a
Flapjack-specific slice, not the full `pc_compile_correct` case; no `@[hol]`
tag is claimed. The existing
`evalPanSemRecursiveCallFiniteContext_tick_projection` relates the finite and
broad exact Pan clause, while `compileProgExactHOLW_tick_bridge` only compares
the exact compiler's Tick output after its output codec with production
`compileProgRiscV`; neither theorem is a production evaluator equivalence. -/
theorem panToCrepExactTickTransition
    {width : Nat} {σ : Type} [NeZero width]
    (sourceContext : PanSemStateFiniteExact.FiniteEvalContext width σ)
    (targetState : CrepSemHOLState width σ)
    (compileContext : PanToCrepContextExact width)
    (memDec : (a : BitVec width) → Decidable (targetState.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (targetState.shMemaddrs a))
    (hstate : panToCrepStateRelFiniteExact sourceContext.state targetState)
    (hlocals : panToCrepLocalsRelFiniteExact compileContext
      sourceContext.state.locals targetState.locals)
    (hcode : codeRelExactHOLW compileContext sourceContext.state.code targetState.code)
    (hexcp : panToCrepExcpRelFiniteExact compileContext.eids
      sourceContext.state.eshapes) :
    let sourcePost :=
      if sourceContext.state.clock = 0 then
        PanSemStateFiniteExact.emptyLocalsHOLFinite sourceContext.state
      else PanSemStateFiniteExact.decClockHOLFinite sourceContext.state
    let targetPost :=
      if targetState.clock = 0 then
        CrepSemHOLState.emptyLocals targetState
      else decClockCrepSemHOL targetState
    PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
        (.tick : Flapjack.Pancake.PanLang.ProgHOL width) sourceContext =
      some (if sourceContext.state.clock = 0 then some .timeOut else none,
        sourceContext.withState sourcePost
          (by by_cases hzero : sourceContext.state.clock = 0 <;>
            simp [sourcePost, PanSemStateFiniteExact.emptyLocalsHOLFinite,
              PanSemStateFiniteExact.decClockHOLFinite, hzero])
          (by by_cases hzero : sourceContext.state.clock = 0 <;>
            simp [sourcePost, PanSemStateFiniteExact.emptyLocalsHOLFinite,
              PanSemStateFiniteExact.decClockHOLFinite, hzero])) ∧
    compileProgExactHOLW compileContext
        (.tick : Flapjack.Pancake.PanLang.ProgHOL width) =
      (.tick : CrepProgHOL width) ∧
    evalCrepSemHOLProg targetState memDec shMemDec
        (compileProgExactHOLW compileContext
          (.tick : Flapjack.Pancake.PanLang.ProgHOL width)) =
      (if targetState.clock = 0 then
        (some .timeOut, CrepSemHOLState.emptyLocals targetState)
      else (none, decClockCrepSemHOL targetState)) ∧
    panToCrepStateRelFiniteExact sourcePost targetPost ∧
    panToCrepLocalsRelFiniteExact compileContext sourcePost.locals targetPost.locals ∧
    codeRelExactHOLW compileContext sourcePost.code targetPost.code ∧
    panToCrepExcpRelFiniteExact compileContext.eids sourcePost.eshapes := by
  let sourcePost : PanSemStateFiniteExact width σ :=
    if sourceContext.state.clock = 0 then
      PanSemStateFiniteExact.emptyLocalsHOLFinite sourceContext.state
    else PanSemStateFiniteExact.decClockHOLFinite sourceContext.state
  let targetPost : CrepSemHOLState width σ :=
    if targetState.clock = 0 then
      CrepSemHOLState.emptyLocals targetState
    else decClockCrepSemHOL targetState
  have hcodePost : codeRelExactHOLW compileContext sourcePost.code targetPost.code := by
    by_cases hsourceZero : sourceContext.state.clock = 0 <;>
      by_cases htargetZero : targetState.clock = 0 <;>
      simpa [sourcePost, targetPost, hsourceZero, htargetZero,
        PanSemStateFiniteExact.emptyLocalsHOLFinite,
        PanSemStateFiniteExact.decClockHOLFinite, CrepSemHOLState.emptyLocals,
        decClockCrepSemHOL] using hcode
  have hexcpPost : panToCrepExcpRelFiniteExact compileContext.eids sourcePost.eshapes := by
    by_cases hsourceZero : sourceContext.state.clock = 0 <;>
      by_cases htargetZero : targetState.clock = 0 <;>
      simpa [sourcePost, targetPost, hsourceZero, htargetZero,
        PanSemStateFiniteExact.emptyLocalsHOLFinite,
        PanSemStateFiniteExact.decClockHOLFinite, CrepSemHOLState.emptyLocals,
        decClockCrepSemHOL] using hexcp
  rcases hstate with ⟨hmem, hmemaddrs, hshmem, hstructs, hglobals,
    hclock, hbe, hffi, hbase, htop⟩
  have hsource :
      PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
        (.tick : Flapjack.Pancake.PanLang.ProgHOL width) sourceContext =
        some (if sourceContext.state.clock = 0 then some .timeOut else none,
          sourceContext.withState sourcePost
            (by by_cases hz : sourceContext.state.clock = 0 <;>
              simp [sourcePost, PanSemStateFiniteExact.emptyLocalsHOLFinite,
                PanSemStateFiniteExact.decClockHOLFinite, hz])
            (by by_cases hz : sourceContext.state.clock = 0 <;>
              simp [sourcePost, PanSemStateFiniteExact.emptyLocalsHOLFinite,
                PanSemStateFiniteExact.decClockHOLFinite, hz])) := by
    by_cases hzero : sourceContext.state.clock = 0
    · simp [PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext,
        sourcePost, hzero]
    · simp [PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext,
        sourcePost, hzero]
  have hcompile : compileProgExactHOLW compileContext
      (.tick : Flapjack.Pancake.PanLang.ProgHOL width) =
        (.tick : CrepProgHOL width) := by
    simp [compileProgExactHOLW]
  refine ⟨hsource, hcompile, ?_, ?_, ?_, hcodePost, hexcpPost⟩
  · rw [hcompile]
    exact evalCrepSemHOLProg_tick targetState memDec shMemDec
  · by_cases hzero : sourceContext.state.clock = 0
    · have htargetZero : targetState.clock = 0 := by rw [← hclock, hzero]
      simpa [panToCrepStateRelFiniteExact, sourcePost, targetPost, hzero,
        htargetZero, PanSemStateFiniteExact.emptyLocalsHOLFinite,
        CrepSemHOLState.emptyLocals] using
        (show panToCrepStateRelFiniteExact sourceContext.state targetState from
          ⟨hmem, hmemaddrs, hshmem, hstructs, hglobals, hclock, hbe, hffi,
            hbase, htop⟩)
    · have htargetNonzero : targetState.clock ≠ 0 := by
        intro hz
        exact hzero (hclock.trans hz)
      simpa [panToCrepStateRelFiniteExact, sourcePost, targetPost, hzero,
        htargetNonzero, PanSemStateFiniteExact.decClockHOLFinite,
        decClockCrepSemHOL, hclock] using
        (show panToCrepStateRelFiniteExact sourceContext.state targetState from
          ⟨hmem, hmemaddrs, hshmem, hstructs, hglobals, hclock, hbe, hffi,
            hbase, htop⟩)
  · by_cases hzero : sourceContext.state.clock = 0
    · rcases hlocals with ⟨hnoOverlap, hctxtMax, _hlocals⟩
      refine ⟨hnoOverlap, hctxtMax, ?_⟩
      intro name value hlookup
      simp [hzero, PanSemStateFiniteExact.emptyLocalsHOLFinite] at hlookup
    · have htargetNonzero : targetState.clock ≠ 0 := by
        intro hz
        exact hzero (hclock.trans hz)
      simpa [sourcePost, targetPost, hzero, htargetNonzero,
        PanSemStateFiniteExact.decClockHOLFinite, decClockCrepSemHOL] using hlocals

end Flapjack
