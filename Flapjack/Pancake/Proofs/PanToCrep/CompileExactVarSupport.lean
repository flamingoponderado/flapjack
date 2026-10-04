import Flapjack.Pancake.PanToCrep.CompileExact

/-!
Compiler-only support facts for the exact Pan-to-Crep expression compiler.
These Flapjack lemmas use the exact `ExpHOL`/`CrepExpHOL` syntax and
`PanToCrepContextExact` finite-map carrier.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- Exact variable clause of `compileExpExactHOLW`: a local variable emits
    precisely the slots stored in its context binding, while a missing local
    binding emits no variable names. This is Flapjack-specific infrastructure,
    not a port of HOL `eval_var_cexp_present_ctxt`; it isolates the compiler
    lookup step used when proving that theorem over exact carriers. -/
@[simp] theorem compileExpExactHOLW_localVar_vars {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (sourceName : MlS) :
    (compileExpExactHOLW (width := width) context (.var .local sourceName)).1.flatMap
      crepExpVarsHOL =
      match context.vars.lookup sourceName with
      | some (_, slots) => slots
      | none => [] := by
  cases hlookup : context.vars.lookup sourceName <;>
    simp [compileExpExactHOLW, hlookup, crepExpVarsHOL, List.flatMap_map]

private theorem crepVars_flatMap_take_subset {width : Nat} [NeZero width]
    (expressions : List (CrepExpHOL width)) (count name : Nat)
    (hname : ∃ expression, expression ∈ expressions.take count ∧
      name ∈ crepExpVarsHOL expression) :
    ∃ expression, expression ∈ expressions ∧ name ∈ crepExpVarsHOL expression := by
  rcases hname with ⟨expression, htake, hvar⟩
  exact ⟨expression, List.mem_of_mem_take htake, hvar⟩

private theorem crepVars_flatMap_drop_subset {width : Nat} [NeZero width]
    (expressions : List (CrepExpHOL width)) (count name : Nat)
    (hname : ∃ expression, expression ∈ expressions.drop count ∧
      name ∈ crepExpVarsHOL expression) :
    ∃ expression, expression ∈ expressions ∧ name ∈ crepExpVarsHOL expression := by
  rcases hname with ⟨expression, hdrop, hvar⟩
  exact ⟨expression, List.mem_of_mem_drop hdrop, hvar⟩

/-- `comp_field` selects or drops a sublist of compiled expressions, so it
    cannot introduce a variable name. This is Flapjack support for recursive
    exact expression variable provenance, not a separate HOL theorem. -/
private theorem compFieldHOL_vars_subset {width : Nat} [NeZero width]
    (index : Nat) (shapes : List ShapeHOL)
    (expressions : List (CrepExpHOL width)) :
    ∀ name, name ∈ (compFieldHOL index shapes expressions).1.flatMap crepExpVarsHOL →
      name ∈ expressions.flatMap crepExpVarsHOL := by
  induction shapes generalizing index expressions with
  | nil =>
      intro name hname
      simp [compFieldHOL, crepExpVarsHOL] at hname
  | cons shape shapes ih =>
      intro name hname
      by_cases hindex : index = 0
      · simp [compFieldHOL, hindex] at hname
        rcases crepVars_flatMap_take_subset expressions
            (Flapjack.Pancake.PanLang.sizeOfShapeHOL shape) name hname with
          ⟨expression, hmember, hvar⟩
        exact List.mem_flatMap.mpr ⟨expression, hmember, hvar⟩
      · simp [compFieldHOL, hindex] at hname
        have hrecursive : name ∈
            ((compFieldHOL (index - 1) shapes
              (expressions.drop (Flapjack.Pancake.PanLang.sizeOfShapeHOL shape))).1).flatMap
              crepExpVarsHOL := List.mem_flatMap.mpr hname
        have hsource := ih (index - 1) _ name hrecursive
        exact List.mem_flatMap.mpr
          (crepVars_flatMap_drop_subset expressions
            (Flapjack.Pancake.PanLang.sizeOfShapeHOL shape) name
            (List.mem_flatMap.mp hsource))

private theorem cexpHeads_vars_subset {width : Nat} [NeZero width]
    (expressions : List (List (CrepExpHOL width))) (heads : List (CrepExpHOL width))
    (hheads : cexpHeads expressions = some heads) :
    ∀ name, name ∈ heads.flatMap crepExpVarsHOL →
      ∃ source, source ∈ expressions ∧
        name ∈ source.flatMap crepExpVarsHOL := by
  induction expressions generalizing heads with
  | nil =>
      intro name hname
      simp [cexpHeads] at hheads
      subst heads
      simp at hname
  | cons first rest ih =>
      cases first with
      | nil =>
          simp [cexpHeads] at hheads
      | cons firstHead firstTail =>
          cases hrest : cexpHeads rest with
          | none => simp [cexpHeads, hrest] at hheads
          | some restHeads =>
            simp [cexpHeads, hrest] at hheads
            subst heads
            intro name hname
            simp only [List.flatMap_cons] at hname
            rcases List.mem_append.mp hname with hfirst | hrestName
            · exact ⟨firstHead :: firstTail, List.mem_cons_self,
                List.mem_flatMap.mpr ⟨firstHead, by simp, hfirst⟩⟩
            · have hrestSupport := ih restHeads hrest name hrestName
              rcases hrestSupport with ⟨source, hsource, hvar⟩
              exact ⟨source, by simp [hsource], hvar⟩

private theorem loadShapeBytesHOLW_vars_subset {width : Nat} [NeZero width]
    (address : BitVec width) (count : Nat) (value : CrepExpHOL width) :
    ∀ name, name ∈ (loadShapeBytesHOLW address count value).flatMap crepExpVarsHOL →
      name ∈ crepExpVarsHOL value := by
  induction count generalizing address with
  | zero =>
      intro name hname
      simp [loadShapeBytesHOLW] at hname
  | succ count ih =>
      intro name hname
      simp only [loadShapeBytesHOLW, List.flatMap_cons] at hname
      rcases List.mem_append.mp hname with hhead | htail
      · change name ∈ crepExpVarsHOL
          (if (address == 0) = true then .load value
            else .load (.op .add [value, .const address])) at hhead
        split at hhead <;> simp [crepExpVarsHOL, crepExpVarsHOLList] at hhead ⊢ <;>
          assumption
      · exact ih (address + BitVec.ofNat width (width / 8)) name htail

/-- Exact `compile_exp` outputs contain variable names only from slots present
    in the same finite-support context. This recursive helper has no separate
    HOL declaration; it is a compiler prerequisite for the source theorem
    `eval_var_cexp_present_ctxt`, whose evaluator and state-relation premises
    remain outside this statement. -/
theorem compileExpExactHOLW_vars_from_context {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) :
    (∀ (expression : ExpHOL width) name,
      name ∈ (compileExpExactHOLW context expression).1.flatMap crepExpVarsHOL →
      ∃ sourceName shape slots,
        context.vars.lookup sourceName = some (shape, slots) ∧ name ∈ slots) ∧
    (∀ (expressions : List (ExpHOL width)) name,
      name ∈ ((compileExpExactHOLWList context expressions).flatMap Prod.fst).flatMap
        crepExpVarsHOL →
      ∃ sourceName shape slots,
        context.vars.lookup sourceName = some (shape, slots) ∧ name ∈ slots) := by
  let expSupport (expression : ExpHOL width) :=
    ∀ name, name ∈ (compileExpExactHOLW context expression).1.flatMap crepExpVarsHOL →
      ∃ sourceName shape slots,
        context.vars.lookup sourceName = some (shape, slots) ∧ name ∈ slots
  let listSupport (expressions : List (ExpHOL width)) :=
    ∀ name, name ∈ ((compileExpExactHOLWList context expressions).flatMap Prod.fst).flatMap
      crepExpVarsHOL →
      ∃ sourceName shape slots,
        context.vars.lookup sourceName = some (shape, slots) ∧ name ∈ slots
  have hExpAll : ∀ expression, expSupport expression := by
    intro expression
    apply compileExpExactHOLW.induct (context := context)
      (motive1 := expSupport) (motive2 := listSupport)
    · intro value name hname
      simp [compileExpExactHOLW, crepExpVarsHOL] at hname
    · intro sourceName shape slots hlookup name hname
      simp [compileExpExactHOLW, hlookup,
        crepExpVarsHOL, List.flatMap_map] at hname
      exact ⟨sourceName, shape, slots, hlookup, hname⟩
    · intro sourceName hlookup name hname
      simp [compileExpExactHOLW, hlookup, crepExpVarsHOL] at hname
    · intro sourceName name hname
      simp [compileExpExactHOLW, crepExpVarsHOL] at hname
    · intro expressions hexpressions name hname
      exact hexpressions name (by simpa [compileExpExactHOLW] using hname)
    · intro index expression compiled shapes hshape hexpression name hname
      have hcompiled : compileExpExactHOLW context expression = compiled := rfl
      have hname' : name ∈
          ((match compiled.2 with
              | .comb shapes => compFieldHOL index shapes compiled.1
              | _ => ([CrepExpHOL.const 0], ShapeHOL.one)).1).flatMap
            crepExpVarsHOL := by
        simpa only [compileExpExactHOLW, hcompiled, hshape] using hname
      have hshape' : compiled.2 = .comb shapes := hshape
      have hsource : name ∈ compiled.1.flatMap crepExpVarsHOL :=
        compFieldHOL_vars_subset index shapes compiled.1 name
          (by simpa only [hshape'] using hname')
      have hsupported := hexpression name hsource
      exact hsupported
    · intro index expression compiled hnotComb hexpression name hname
      have hcompiled : compileExpExactHOLW context expression = compiled := rfl
      cases hshape : compiled.2 with
      | one =>
          have hname' : name ∈
              ((match compiled.2 with
                  | .comb shapes => compFieldHOL index shapes compiled.1
                  | _ => ([CrepExpHOL.const 0], ShapeHOL.one)).1).flatMap
                crepExpVarsHOL := by
            simpa only [compileExpExactHOLW, hcompiled, hshape] using hname
          simp [hshape, crepExpVarsHOL] at hname'
      | comb shapes => exact False.elim (hnotComb shapes hshape)
      | named _ =>
          have hname' : name ∈
              ((match compiled.2 with
                  | .comb shapes => compFieldHOL index shapes compiled.1
                  | _ => ([CrepExpHOL.const 0], ShapeHOL.one)).1).flatMap
                crepExpVarsHOL := by
            simpa only [compileExpExactHOLW, hcompiled, hshape] using hname
          simp [hshape, crepExpVarsHOL] at hname'
    · intro structName fields name hname
      simp [compileExpExactHOLW, crepExpVarsHOL] at hname
    · intro fieldName expression name hname
      simp [compileExpExactHOLW, crepExpVarsHOL] at hname
    · intro shape expression address tail resultShape hcompiled hexpression name hname
      have haddress : name ∈ crepExpVarsHOL address := by
        have hload := loadShapeBytesHOLW_vars_subset (0 : BitVec width)
          (Flapjack.Pancake.PanLang.sizeOfShapeHOL shape) address name
          (by simpa [compileExpExactHOLW, hcompiled] using hname)
        exact hload
      have haddressCompiled : address ∈ (compileExpExactHOLW context expression).1 := by
        rw [hcompiled]
        simp
      have hsource : name ∈ (compileExpExactHOLW context expression).1.flatMap
          crepExpVarsHOL := List.mem_flatMap.mpr ⟨address, haddressCompiled, haddress⟩
      exact hexpression name hsource
    · intro shape expression resultShape hcompiled hexpression name hname
      simp [compileExpExactHOLW, hcompiled, crepExpVarsHOL] at hname
    · intro expression address tail hcompiled hexpression name hname
      have haddress : name ∈ crepExpVarsHOL address := by
        simpa [compileExpExactHOLW, hcompiled, crepExpVarsHOL] using hname
      exact hexpression name (List.mem_flatMap.mpr ⟨address, by rw [hcompiled]; simp, haddress⟩)
    · intro expression hnone hexpression name hname
      simp [compileExpExactHOLW, crepExpVarsHOL] at hname
    · intro expression address tail hcompiled hexpression name hname
      have haddress : name ∈ crepExpVarsHOL address := by
        simpa [compileExpExactHOLW, hcompiled, crepExpVarsHOL] using hname
      exact hexpression name (List.mem_flatMap.mpr ⟨address, by rw [hcompiled]; simp, haddress⟩)
    · intro expression hnone hexpression name hname
      simp [compileExpExactHOLW, crepExpVarsHOL] at hname
    · intro operator expressions heads hheads hexpressions name hname
      have hhead : name ∈ heads.flatMap crepExpVarsHOL :=
        by simpa [compileExpExactHOLW, hheads, crepExpVarsHOL,
          crepExpVarsHOLList_eq_flatMap] using hname
      rcases cexpHeads_vars_subset
        ((compileExpExactHOLWList context expressions).map Prod.fst) heads hheads name hhead with
        ⟨source, hsource, hsourceVars⟩
      rcases List.mem_map.mp hsource with ⟨compiled, hcompiled, rfl⟩
      rcases List.mem_flatMap.mp hsourceVars with ⟨compiledExpression, hcompiledExpression, hvar⟩
      have hcompiledName : name ∈
          ((compileExpExactHOLWList context expressions).flatMap Prod.fst).flatMap
            crepExpVarsHOL := by
        apply List.mem_flatMap.mpr
        refine ⟨compiledExpression, List.mem_flatMap.mpr ⟨compiled, hcompiled, ?_⟩, hvar⟩
        exact hcompiledExpression
      exact hexpressions name hcompiledName
    · intro operator expressions hnone hexpressions name hname
      simp [compileExpExactHOLW, hnone, crepExpVarsHOL] at hname
    · intro operator expressions heads hheads hexpressions name hname
      have hhead : name ∈ heads.flatMap crepExpVarsHOL :=
        by simpa [compileExpExactHOLW, hheads, crepExpVarsHOL,
          crepExpVarsHOLList_eq_flatMap] using hname
      rcases cexpHeads_vars_subset
        ((compileExpExactHOLWList context expressions).map Prod.fst) heads hheads name hhead with
        ⟨source, hsource, hsourceVars⟩
      rcases List.mem_map.mp hsource with ⟨compiled, hcompiled, rfl⟩
      rcases List.mem_flatMap.mp hsourceVars with ⟨compiledExpression, hcompiledExpression, hvar⟩
      have hcompiledName : name ∈
          ((compileExpExactHOLWList context expressions).flatMap Prod.fst).flatMap
            crepExpVarsHOL := by
        apply List.mem_flatMap.mpr
        refine ⟨compiledExpression, List.mem_flatMap.mpr ⟨compiled, hcompiled, ?_⟩, hvar⟩
        exact hcompiledExpression
      exact hexpressions name hcompiledName
    · intro operator expressions hnone hexpressions name hname
      simp [compileExpExactHOLW, hnone, crepExpVarsHOL] at hname
    · intro operator left right leftHead leftTail leftShape rightHead rightTail rightShape
        hright hleft hleftSupport hrightSupport name hname
      simp [compileExpExactHOLW, hleft, hright, crepExpVarsHOL] at hname
      rcases hname with hleftName | hrightName
      · exact hleftSupport name (List.mem_flatMap.mpr
          ⟨leftHead, by rw [hleft]; simp, hleftName⟩)
      · exact hrightSupport name (List.mem_flatMap.mpr
          ⟨rightHead, by rw [hright]; simp, hrightName⟩)
    · intro operator left right hfail hleftSupport hrightSupport name hname
      cases hleft : compileExpExactHOLW context left with
      | mk leftValues leftShape =>
        cases leftValues with
        | nil => simp [compileExpExactHOLW, hleft, crepExpVarsHOL] at hname
        | cons leftHead leftTail =>
          cases hright : compileExpExactHOLW context right with
          | mk rightValues rightShape =>
            cases rightValues with
            | nil => simp [compileExpExactHOLW, hleft, hright, crepExpVarsHOL] at hname
            | cons rightHead rightTail =>
              exact False.elim (hfail leftHead leftTail leftShape rightHead rightTail
                rightShape hleft hright)
    · intro operator left right leftHead leftTail leftShape rightHead rightTail rightShape
        hright hleft hleftSupport hrightSupport name hname
      simp [compileExpExactHOLW, hleft, hright, crepExpVarsHOL] at hname
      rcases hname with hleftName | hrightName
      · exact hleftSupport name (List.mem_flatMap.mpr
          ⟨leftHead, by rw [hleft]; simp, hleftName⟩)
      · exact hrightSupport name (List.mem_flatMap.mpr
          ⟨rightHead, by rw [hright]; simp, hrightName⟩)
    · intro operator left right hfail hleftSupport hrightSupport name hname
      cases hleft : compileExpExactHOLW context left with
      | mk leftValues leftShape =>
        cases leftValues with
        | nil => simp [compileExpExactHOLW, hleft, crepExpVarsHOL] at hname
        | cons leftHead leftTail =>
          cases hright : compileExpExactHOLW context right with
          | mk rightValues rightShape =>
            cases rightValues with
            | nil => simp [compileExpExactHOLW, hleft, hright, crepExpVarsHOL] at hname
            | cons rightHead rightTail =>
              exact False.elim (hfail leftHead leftTail leftShape rightHead rightTail
                rightShape hleft hright)
    · intro name hname
      simp [compileExpExactHOLW, crepExpVarsHOL] at hname
    · intro name hname
      simp [compileExpExactHOLW, crepExpVarsHOL] at hname
    · intro name hname
      simp [compileExpExactHOLW, crepExpVarsHOL] at hname
    · intro name hname
      simp [compileExpExactHOLWList] at hname
    · intro expression expressions hexpression hexpressions name hname
      simp only [compileExpExactHOLWList, List.flatMap_cons,
        List.flatMap_append] at hname
      rcases List.mem_append.mp hname with hhead | htail
      · exact hexpression name hhead
      · exact hexpressions name htail
  have hListAll : ∀ expressions, listSupport expressions := by
    intro expressions
    induction expressions with
    | nil =>
        intro name hname
        simp [compileExpExactHOLWList] at hname
    | cons expression expressions ih =>
        intro name hname
        simp only [compileExpExactHOLWList, List.flatMap_cons,
          List.flatMap_append] at hname
        rcases List.mem_append.mp hname with hhead | htail
        · exact hExpAll expression name hhead
        · exact ih name htail
  constructor
  · intro expression name hname
    exact hExpAll expression name hname
  · intro expressions name hname
    exact hListAll expressions name hname

end Flapjack
