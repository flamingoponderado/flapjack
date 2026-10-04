import Flapjack.Pancake.Proofs.PanToWord.PanToCrepCompileExpValidity
import Flapjack.Pancake.Proofs.PanToWord.LoadGlobalsValidity
namespace Flapjack.PanToCrepCompileValidity
open Pancake.PanLang
/-- Internal membership rendering of the source expression-list guard; no separate HOL declaration. -/
private abbrev panValid {width : Nat} [NeZero width] (body : ProgHOL width) : Prop :=
  ∀ e ∈ expsOfHOL body, everyExpHOL panopArityTwoHOL e = true

/-- Internal native compiler proof factoring for the full original theorem below; no separate HOL declaration. -/
private theorem expr_valid {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) (e : ExpHOL width)
    (valid : everyExpHOL panopArityTwoHOL e = true) :
    crepBinaryListNative (compileExpExactHOLW ctxt e).1 :=
  PanToCrepCompileExpValidity.everyInstOkLess_panToCrepCompileExp ctxt e _ _ valid rfl

/-- Internal native compiler proof factoring for the full original theorem below; no separate HOL declaration. -/
private theorem exprs_valid {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) (es : List (ExpHOL width))
    (valid : ∀ e ∈ es, everyExpHOL panopArityTwoHOL e = true) :
    crepBinaryListNative ((compileExpExactHOLWList ctxt es).flatMap Prod.fst) := by
  induction es with
  | nil => simp [compileExpExactHOLWList, crepBinaryListNative]
  | cons e es ih =>
    have h := expr_valid ctxt e (valid e List.mem_cons_self)
    have hs := ih (fun e he => valid e (List.mem_cons_of_mem _ he))
    simp only [compileExpExactHOLWList, List.flatMap_cons]
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h x hx
    · exact hs x hx

/-- Internal native compiler proof factoring for the full original theorem below; no separate HOL declaration. -/
private theorem nested_valid {width : Nat} [NeZero width]
    (names : List Nat) (es : List (CrepExpHOL width)) (body : CrepProgHOL width)
    (values : crepBinaryListNative es) (valid : crepBinaryProgNative body) :
    crepBinaryProgNative (nestedDecsHOL names es body) := by
  induction names generalizing es with
  | nil => cases es <;> simp_all [nestedDecsHOL, crepBinaryProgNative,
      crepBinaryListNative, crepExpsOfHOL]
  | cons name names ih =>
    cases es with
    | nil => simp [nestedDecsHOL, crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL]
    | cons e es =>
      have he := values e List.mem_cons_self
      have hs := ih es (fun x hx => values x (List.mem_cons_of_mem _ hx))
      simpa [nestedDecsHOL, crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL] using
        And.intro he hs

/-- Internal native compiler proof factoring for the full original theorem below; no separate HOL declaration. -/
private theorem seqs_valid {width : Nat} [NeZero width]
    (ps : List (CrepProgHOL width)) (valid : ∀ p ∈ ps, crepBinaryProgNative p) :
    crepBinaryProgNative (crepNestedSeqHOL ps) := by
  rw [crepBinaryProgNative, crepExpsOfNestedSeqHOL]
  simp only [crepBinaryListNative, List.mem_flatten, List.mem_map]
  intro e he
  obtain ⟨es, ⟨p, hp, rfl⟩, he⟩ := he
  exact valid p hp e he

/-- Internal native compiler proof factoring for the full original theorem below; no separate HOL declaration. -/
private theorem assigns_valid {width : Nat} [NeZero width]
    (names : List Nat) (es : List (CrepExpHOL width)) (valid : crepBinaryListNative es) :
    ∀ p ∈ names.zipWith CrepProgHOL.assign es, crepBinaryProgNative p := by
  induction names generalizing es with
  | nil => simp
  | cons name names ih =>
    cases es with
    | nil => simp
    | cons e es =>
      simp only [List.zipWith_cons_cons, List.mem_cons]
      intro p hp
      rcases hp with rfl | hp
      · simpa [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL] using
          valid e List.mem_cons_self
      · exact ih es (fun x hx => valid x (List.mem_cons_of_mem _ hx)) p hp

/-- Internal native compiler proof factoring for the full original theorem below; no separate HOL declaration. -/
private theorem vars_valid {width : Nat} [NeZero width] (names : List Nat) :
    crepBinaryListNative (names.map (CrepExpHOL.var (width := width))) := by
  simp [crepBinaryListNative, crepBinaryExpNative, crepEveryExpHOL]

/-- Internal native compiler proof factoring for the full original theorem below; no separate HOL declaration. -/
private theorem zeros_valid {width : Nat} [NeZero width] (n : Nat) :
    crepBinaryListNative (List.replicate n (CrepExpHOL.const (0 : BitVec width))) := by
  simp [crepBinaryListNative, crepBinaryExpNative, crepEveryExpHOL]

/-- Internal native compiler proof factoring for the full original theorem below; no separate HOL declaration. -/
private theorem globals_valid {width : Nat} [NeZero width] (a : BitVec 5) (n : Nat) :
    crepBinaryListNative (loadGlobalsHOL (width := width) a n) := by
  rw [loadGlobalsAlt]
  simp [crepBinaryListNative, crepBinaryExpNative, crepEveryExpHOL]

/-- Internal native compiler proof factoring for the full original theorem below; no separate HOL declaration. -/
private theorem handler_valid {width : Nat} [NeZero width]
    (vars : HolFiniteMapExact MlS (ShapeHOL × List Nat)) (name : MlS) :
    crepBinaryProgNative (expHdlExact (width := width) vars name) := by
  unfold expHdlExact
  split
  · simp [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL]
  · apply seqs_valid
    rw [panMap2_eq_zipWith]
    exact assigns_valid _ _ (globals_valid _ _)

/-- Internal native compiler proof factoring for the full original theorem below; no separate HOL declaration. -/
private theorem stores_valid {width : Nat} [NeZero width]
    (a : CrepExpHOL width) (es : List (CrepExpHOL width)) (offset : BitVec width)
    (ha : crepBinaryExpNative a) (hs : crepBinaryListNative es) :
    crepBinaryProgNative (crepNestedSeqHOL (storesHOL a es offset)) := by
  apply seqs_valid
  exact (everyInstOkLess_stores a es offset).2 ⟨fun _ => ha, hs⟩

/-- Internal native compiler proof factoring for the full original theorem below; no separate HOL declaration. -/
private theorem compile_valid {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    (body : ProgHOL width) : panValid body →
    crepBinaryProgNative (compileProgExactHOLW ctxt body) := by
  apply compileProgExactHOLW.induct
    (motive := fun ctxt body => panValid body →
      crepBinaryProgNative (compileProgExactHOLW ctxt body))
  all_goals try solve | intros; simp_all [compileProgExactHOLW, panValid, expsOfHOL,
    crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL,
    crepBinaryExpNative, List.mem_append, or_imp, forall_and,
    compileGlobalAssignExactHOLW, compileGlobalShMemLoadExactHOLW]
  case case2 =>
    intro context name shape expression body ih guard
    have hg : everyExpHOL panopArityTwoHOL expression = true ∧ panValid body := by
      simpa [panValid, expsOfHOL] using guard
    have hv := expr_valid context expression hg.1
    simp only [compileProgExactHOLW, compileDecExactHOLW]
    split
    · simp [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL]
    · exact nested_valid _ _ _ hv (ih _ hg.2)
  case case3 =>
    intro context name expression guard
    have hv := expr_valid context expression (by simpa [panValid, expsOfHOL] using guard)
    simp only [compileProgExactHOLW, compileLocalAssignExactHOLW]
    split
    · simp [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL]
    · split
      · simp [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL]
      · split
        · exact seqs_valid _ (assigns_valid _ _ hv)
        · exact nested_valid _ _ _ hv (seqs_valid _ (assigns_valid _ _ (vars_valid _)))
  case case5 =>
    intro context name operator arguments guard
    have hv := exprs_valid context arguments (by simpa [panValid, expsOfHOL] using guard)
    simp only [compileProgExactHOLW, compilePrimitiveExactHOLW]
    split
    · simp [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL]
    · apply nested_valid _ _ _ hv
      simp [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL]
  case case7 =>
    intro context address value guard
    have hg : everyExpHOL panopArityTwoHOL address = true ∧
        everyExpHOL panopArityTwoHOL value = true := by
      simpa [panValid, expsOfHOL] using guard
    have ha := expr_valid context address hg.1
    have hv := expr_valid context value hg.2
    simp only [compileProgExactHOLW, compileStore32ExactHOLW]
    split <;> simp_all [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL]
  case case8 =>
    intro context address value guard
    have hg : everyExpHOL panopArityTwoHOL address = true ∧
        everyExpHOL panopArityTwoHOL value = true := by
      simpa [panValid, expsOfHOL] using guard
    have ha := expr_valid context address hg.1
    have hv := expr_valid context value hg.2
    simp only [compileProgExactHOLW, compileStoreByteExactHOLW]
    split <;> simp_all [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL]
  case case6 =>
    intro context address value guard
    have hg : everyExpHOL panopArityTwoHOL address = true ∧
        everyExpHOL panopArityTwoHOL value = true := by
      simpa [panValid, expsOfHOL] using guard
    have ha := expr_valid context address hg.1
    have hv := expr_valid context value hg.2
    simp only [compileProgExactHOLW, compileStoreExactHOLW]
    split
    · rename_i a tail sh compiled
      have hav : crepBinaryExpNative a := by
        apply ha
        simp [compiled]
      split
      · simp [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL]
      · apply nested_valid
        · simpa [crepBinaryListNative] using And.intro hav hv
        · apply stores_valid
          · simp [crepBinaryExpNative, crepEveryExpHOL]
          · exact vars_valid _
    · simp [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL]
  case case10 =>
    intro context condition first second ih1 ih2 guard
    have hg : everyExpHOL panopArityTwoHOL condition = true ∧
        panValid first ∧ panValid second := by
      simpa [panValid, expsOfHOL, List.mem_append, or_imp, forall_and] using guard
    have he := expr_valid context condition hg.1
    have h1 := ih1 hg.2.1
    have h2 := ih2 hg.2.2
    simp only [compileProgExactHOLW, compileIfExactHOLW]
    split <;> simp_all [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL,
      List.mem_append, or_imp, forall_and]
  case case11 =>
    intro context condition body ih guard
    have hg : everyExpHOL panopArityTwoHOL condition = true ∧ panValid body := by
      simpa [panValid, expsOfHOL] using guard
    have he := expr_valid context condition hg.1
    have hb := ih hg.2
    simp only [compileProgExactHOLW, compileWhileExactHOLW]
    split <;> simp_all [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL]
  case case14 =>
    intro context function arguments guard
    have hv := exprs_valid context arguments (by simpa [panValid, expsOfHOL] using guard)
    simpa [compileProgExactHOLW, compileCallNoReturnExactHOLW,
      crepBinaryProgNative, crepExpsOfHOL] using hv
  case case15 =>
    intro context function arguments guard
    have hv := exprs_valid context arguments (by simpa [panValid, expsOfHOL] using guard)
    simp only [compileProgExactHOLW, compileCallResultNoHandlerExactHOLW]
    apply nested_valid _ _ _ (zeros_valid _)
    simpa [crepBinaryProgNative, crepExpsOfHOL] using hv
  case case16 =>
    intro context function arguments exceptionName exceptionVariable body missing guard
    have hg : (∀ e ∈ arguments, everyExpHOL panopArityTwoHOL e = true) ∧ panValid body := by
      simpa [panValid, expsOfHOL, List.mem_append, or_imp, forall_and] using guard
    have hv := exprs_valid context arguments hg.1
    simp only [compileProgExactHOLW, compileCallHandlerMissingEidExactHOLW,
      compileCallResultNoHandlerExactHOLW]
    split <;> (try solve | simp_all)
    apply nested_valid _ _ _ (zeros_valid _)
    simpa [crepBinaryProgNative, crepExpsOfHOL] using hv
  case case17 =>
    intro context function arguments exceptionName exceptionVariable body code found ih guard
    have hg : (∀ e ∈ arguments, everyExpHOL panopArityTwoHOL e = true) ∧ panValid body := by
      simpa [panValid, expsOfHOL, List.mem_append, or_imp, forall_and] using guard
    have hv := exprs_valid context arguments hg.1
    have hb := ih context hg.2
    have hh := handler_valid context.vars exceptionVariable (width := width)
    simp only [compileProgExactHOLW, compileCallHandlerPresentEidExactHOLW]
    split <;> (try solve | simp_all)
    apply nested_valid _ _ _ (zeros_valid _)
    simpa [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL,
      List.mem_append, or_imp, forall_and] using And.intro hv (And.intro hh hb)
  case case25 =>
    intro context function a b c d guard
    have hg : everyExpHOL panopArityTwoHOL a = true ∧
        everyExpHOL panopArityTwoHOL b = true ∧
        everyExpHOL panopArityTwoHOL c = true ∧
        everyExpHOL panopArityTwoHOL d = true := by
      simpa [panValid, expsOfHOL] using guard
    have ha := expr_valid context a hg.1
    have hb := expr_valid context b hg.2.1
    have hc := expr_valid context c hg.2.2.1
    have hd := expr_valid context d hg.2.2.2
    simp only [compileProgExactHOLW, compileExtCallExactHOLW]
    split <;> simp_all [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL]
  case case26 =>
    intro context exceptionName expression guard
    have hv := expr_valid context expression (by simpa [panValid, expsOfHOL] using guard)
    simp only [compileProgExactHOLW, compileRaiseExactHOLW]
    split
    · simp [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL]
    · split
      · simp [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL]
      · simp only [crepBinaryProgNative, crepExpsOfHOL, List.append_nil]
        apply nested_valid _ _ _ hv
        apply seqs_valid
        exact (everyInstOkLess_storeGlobals (width := width) _ _).2 (vars_valid _)
  case case27 =>
    intro context expression guard
    have hv := expr_valid context expression (by simpa [panValid, expsOfHOL] using guard)
    simp only [compileProgExactHOLW, compileReturnExactHOLW]
    split
    · simp [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL]
    · simpa [crepBinaryProgNative, crepExpsOfHOL] using hv
  case case28 =>
    intro context operator name address guard
    have ha := expr_valid context address (by simpa [panValid, expsOfHOL] using guard)
    simp only [compileProgExactHOLW, compileShMemLoadExactHOLW]
    split
    · split <;> simp_all [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL]
    · simp [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL]
  case case30 =>
    intro context operator value address guard
    have hg : everyExpHOL panopArityTwoHOL value = true ∧
        everyExpHOL panopArityTwoHOL address = true := by
      simpa [panValid, expsOfHOL] using guard
    have hv := expr_valid context value hg.1
    have ha := expr_valid context address hg.2
    simp only [compileProgExactHOLW, compileShMemStoreExactHOLW]
    split <;> simp_all [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL]
  case case18 =>
    intro context function arguments kind resultName wrapped guard
    have hv := exprs_valid context arguments (by simpa [panValid, expsOfHOL] using guard)
    simp only [compileProgExactHOLW, compileCallWrappedResultFallbackNoHandlerExactHOLW]
    split <;> (try solve | simp_all)
    simpa [crepBinaryProgNative, crepExpsOfHOL] using hv
  case case19 =>
    intro context function arguments kind resultName wrapped exceptionName exceptionVariable body missing guard
    have hg : (∀ e ∈ arguments, everyExpHOL panopArityTwoHOL e = true) ∧ panValid body := by
      simpa [panValid, expsOfHOL, List.mem_append, or_imp, forall_and] using guard
    have hv := exprs_valid context arguments hg.1
    simp only [compileProgExactHOLW, compileCallWrappedResultFallbackHandlerMissingEidExactHOLW,
      compileCallWrappedResultFallbackNoHandlerExactHOLW]
    split <;> (try solve | simp_all)
    split <;> (try solve | simp_all)
    simpa [crepBinaryProgNative, crepExpsOfHOL] using hv
  case case20 =>
    intro context function arguments kind resultName wrapped exceptionName exceptionVariable body code found ih guard
    have hg : (∀ e ∈ arguments, everyExpHOL panopArityTwoHOL e = true) ∧ panValid body := by
      simpa [panValid, expsOfHOL, List.mem_append, or_imp, forall_and] using guard
    have hv := exprs_valid context arguments hg.1
    have hb := ih context hg.2
    have hh := handler_valid context.vars exceptionVariable (width := width)
    simp only [compileProgExactHOLW, compileCallWrappedResultFallbackHandlerPresentEidExactHOLW]
    split <;> (try solve | simp_all)
    split <;> (try solve | simp_all)
    simpa [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL,
      List.mem_append, or_imp, forall_and] using And.intro hv (And.intro hh hb)
  case case21 =>
    intro context function arguments kind resultName shape names wrapped guard
    have hv := exprs_valid context arguments (by simpa [panValid, expsOfHOL] using guard)
    simp only [compileProgExactHOLW, compileCallWrappedResultNoHandlerExactHOLW]
    split <;> (try solve | simp_all)
    simpa [crepBinaryProgNative, crepExpsOfHOL] using hv
  case case22 =>
    intro context function arguments kind resultName shape names wrapped exceptionName exceptionVariable body missing guard
    have hg : (∀ e ∈ arguments, everyExpHOL panopArityTwoHOL e = true) ∧ panValid body := by
      simpa [panValid, expsOfHOL, List.mem_append, or_imp, forall_and] using guard
    have hv := exprs_valid context arguments hg.1
    simp only [compileProgExactHOLW, compileCallWrappedResultHandlerMissingEidExactHOLW,
      compileCallWrappedResultNoHandlerExactHOLW]
    split <;> (try solve | simp_all)
    split <;> (try solve | simp_all)
    simpa [crepBinaryProgNative, crepExpsOfHOL] using hv
  case case23 =>
    intro context function arguments kind resultName shape names wrapped exceptionName exceptionVariable body code found ih guard
    have hg : (∀ e ∈ arguments, everyExpHOL panopArityTwoHOL e = true) ∧ panValid body := by
      simpa [panValid, expsOfHOL, List.mem_append, or_imp, forall_and] using guard
    have hv := exprs_valid context arguments hg.1
    have hb := ih context hg.2
    have hh := handler_valid context.vars exceptionVariable (width := width)
    simp only [compileProgExactHOLW, compileCallWrappedResultHandlerPresentEidExactHOLW]
    split <;> (try solve | simp_all)
    split <;> (try solve | simp_all)
    simpa [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL,
      List.mem_append, or_imp, forall_and] using And.intro hv (And.intro hh hb)
  case case24 =>
    intro context name shape function arguments body ih guard
    have hg : (∀ e ∈ arguments, everyExpHOL panopArityTwoHOL e = true) ∧ panValid body := by
      simpa [panValid, expsOfHOL, List.mem_append, or_imp, forall_and] using guard
    have hv := exprs_valid context arguments hg.1
    simp only [compileProgExactHOLW, compileDecCallExactHOLW]
    apply nested_valid _ _ _ (zeros_valid _)
    simp only [crepBinaryProgNative, crepBinaryListNative, crepExpsOfHOL,
      List.mem_append, or_imp, forall_and]
    exact And.intro hv (ih _ hg.2)
/-- Canonical imported context representation roundtrip for the field qualifier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) :
    PanToCrepContextExact.ofBroad (PanToCrepContextExact.toBroad context) = context :=
  PanToCrepContextExact.holFmapAsFiniteSupportWitness context

/-- Full original body-compiler binary-expression validity implication
(`pan_to_wordProofScript.sml:1057–1105`). The original fully typed statement
quantifies ctxt and body at the same word dimension, plus `e : beta` which
occurs nowhere in the hypotheses or conclusion. Only that vacuous binder is
omitted, after source/type-capture review. The original EVERY source expression
guard is membership plus the existing exact Boolean Pan traversal; output
EVERY uses the shared native Prop-valued Crep traversal. Every recursive
compiler equation and all fallback/handler branches are covered. No context
restriction, byte-range, output validity or target-run premise is added. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml"
  "every_inst_ok_less_pan_to_crep_compile"
  (fmap_as_finite_support := [vars, funcs, eids])
  (words_as_type_indexed_bitvec)]
theorem everyInstOkLess_panToCrepCompile {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) (body : ProgHOL width)
    (guard : ∀ e ∈ expsOfHOL body, everyExpHOL panopArityTwoHOL e = true) :
    crepBinaryProgNative (compileProgExactHOLW ctxt body) :=
  compile_valid ctxt body guard

end Flapjack.PanToCrepCompileValidity
