import Flapjack.Pipeline
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.PanToCrep.CompileExact

namespace Flapjack.Test.CompileProgParity

open Flapjack Flapjack.Pancake.PanLang

def compileProgProbeContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0,
    bytesInWord := 1 }

#check @crepGetEidsFromDecls_lookup_iff_exception
#check @allocatedNames_gt
#check @freshNames_gt
#check @mem_crepExpVars_le_maxCrepExpVar

theorem maxCrepExpVar_mem_fixture :
    7 ≤ maxCrepExpVar ([.var 3, .const 0, .var 7] : List (CrepExp Nat)) := by
  apply mem_crepExpVars_le_maxCrepExpVar
  simp [crepExpVars]

theorem allocatedNames_gt_fixture : (0 : Nat) < (allocatedNames compileProgProbeContext .one).headD 0 := by
  have hmem : (allocatedNames compileProgProbeContext .one).headD 0 ∈ allocatedNames compileProgProbeContext .one := by
    simp [allocatedNames, compileProgProbeContext]
  have := allocatedNames_gt compileProgProbeContext .one hmem
  simpa [compileProgProbeContext] using this

theorem freshNames_gt_fixture : (0 : Nat) < (freshNames compileProgProbeContext 1 1).headD 0 := by
  have hmem : (freshNames compileProgProbeContext 1 1).headD 0 ∈ freshNames compileProgProbeContext 1 1 := by
    simp [freshNames, compileProgProbeContext]
  have := freshNames_gt compileProgProbeContext 1 1 (by decide) hmem
  simpa [compileProgProbeContext] using this

def compileProgProbeDecls : List (Decl Nat) :=
  [.function
     { name := "leaf", inline := true, exported := false, params := [],
       body := .return (.const 7), returnShape := .one },
   .function
     { name := "mid", inline := true, exported := false, params := [],
       body := .call none "leaf" [], returnShape := .one },
   .function
     { name := "main", inline := false, exported := true, params := [],
       body := .call none "mid" [], returnShape := .one }]

/-! Direct `compile_inl_top_def` boundary oracle: the named source pass keeps
    the function table while recursively expanding the selected inline names. -/
def compileInlTopOracle : Bool :=
  match panToCrepCompileInlTop ["first", "second"]
      [CompiledFunction.mk "first" [] (.call none "second" []) .one,
       CompiledFunction.mk "second" [] (.return [.const 9]) .one] with
  | [first, second] =>
      (match first.body with
      | .seq .tick (.return [.const 9]) => true
      | _ => false) &&
      (match second.body with
      | .return [.const 9] => true
      | _ => false)
  | _ => false

#guard compileInlTopOracle

/-! Direct HOL `compile_prog_probe.out` cases for the production triple-list
    `compile_inl_top` boundary. The first duplicate `id` definition wins in
    HOL's `alist_to_fmap`, while nested inline calls expand recursively. -/
def holInlineDuplicateInput : List (FunName × List Nat × CrepProg (BitVec 8)) :=
  [("id", [], .return [.const 7]),
   ("id", [], .return [.const 9]),
   ("main", [], .call none "id" [])]

def holInlineDuplicateParity : Bool :=
  match compileInlTopHOL ["id"] holInlineDuplicateInput with
  | [(first, [], .return [.const firstValue]),
     (second, [], .return [.const secondValue]),
     (main, [], .seq .tick (.return [.const returned]))] =>
      first == "id" && second == "id" && main == "main" &&
        firstValue == 7 && secondValue == 9 && returned == 7
  | _ => false

#guard holInlineDuplicateParity

def holInlineNestedInput : List (FunName × List Nat × CrepProg (BitVec 8)) :=
  [("leaf", [], .return [.const 7]),
   ("mid", [], .call none "leaf" []),
   ("main", [], .call none "mid" [])]

def holInlineNestedParity : Bool :=
  match compileInlTopHOL ["leaf", "mid"] holInlineNestedInput with
  | [(leaf, [], .return [.const leafValue]),
     (mid, [], .seq .tick (.return [.const midValue])),
     (main, [], .seq .tick (.seq .tick (.return [.const mainValue])))] =>
      leaf == "leaf" && mid == "mid" && main == "main" &&
        leafValue == 7 && midValue == 7 && mainValue == 7
  | _ => false

#guard holInlineNestedParity

/-! Direct `compile_prog_probe.out` parity at the new exact
    `compile_prog` triple-list boundary. These declarations are word8 as in
    the HOL EVAL query, and cover the complete empty, duplicate-first, and
    nested-inline outputs rather than testing `compile_inl_top` in isolation. -/
def compileProgTopEmptyParity : Bool :=
  match compileProgTopHOL ([] : List (Decl (BitVec 8))) with
  | [] => true
  | _ => false

def compileProgTopDuplicateParity : Bool :=
  let declarations : List (Decl (BitVec 8)) :=
    [.function
       { name := "id", inline := true, exported := false, params := [],
         body := .return (.const 7), returnShape := .one },
     .function
       { name := "id", inline := true, exported := false, params := [],
         body := .return (.const 9), returnShape := .one },
     .function
       { name := "main", inline := false, exported := true, params := [],
         body := .call none "id" [], returnShape := .one }]
  match compileProgTopHOL declarations with
  | [("id", [], .return [.const 7]),
     ("id", [], .return [.const 9]),
     ("main", [], .seq .tick (.return [.const 7]))] => true
  | _ => false

def compileProgTopNestedParity : Bool :=
  let declarations : List (Decl (BitVec 8)) :=
    [.function
       { name := "leaf", inline := true, exported := false, params := [],
         body := .return (.const 7), returnShape := .one },
     .function
       { name := "mid", inline := true, exported := false, params := [],
         body := .call none "leaf" [], returnShape := .one },
     .function
       { name := "main", inline := false, exported := true, params := [],
         body := .call none "mid" [], returnShape := .one }]
  match compileProgTopHOL declarations with
  | [("leaf", [], .return [.const 7]),
     ("mid", [], .seq .tick (.return [.const 7])),
     ("main", [], .seq .tick (.seq .tick (.return [.const 7])))] => true
  | _ => false

#guard compileProgTopEmptyParity
#guard compileProgTopDuplicateParity
#guard compileProgTopNestedParity

/-! The same committed HOL `compile_prog_probe.out` rows are exercised through
    the exact body route, with explicit constructor-level byte-range evidence
    for the hand-built syntax used by the HOL probe. -/
private theorem compileProbeNameIdRanged : NameRanged "id" := by
  intro c hc
  have hc' : c = 'i' ∨ c = 'd' := by simpa using hc
  rcases hc' with h | h <;> subst c <;> decide

private theorem compileProbeNameMainRanged : NameRanged "main" := by
  intro c hc
  have hc' : c = 'm' ∨ c = 'a' ∨ c = 'i' ∨ c = 'n' := by simpa using hc
  rcases hc' with h | h | h | h <;> subst c <;> decide

private theorem compileProbeNameLeafRanged : NameRanged "leaf" := by
  intro c hc
  have hc' : c = 'l' ∨ c = 'e' ∨ c = 'a' ∨ c = 'f' := by simpa using hc
  rcases hc' with h | h | h | h <;> subst c <;> decide

private theorem compileProbeNameMidRanged : NameRanged "mid" := by
  intro c hc
  have hc' : c = 'm' ∨ c = 'i' ∨ c = 'd' := by simpa using hc
  rcases hc' with h | h | h <;> subst c <;> decide

private theorem compileProbeNameFRanged : NameRanged "f" := by
  intro c hc
  have hc' : c = 'f' := by simpa using hc
  subst c
  decide

private theorem compileProbeNameGRanged : NameRanged "g" := by
  intro c hc
  have hc' : c = 'g' := by simpa using hc
  subst c
  decide

private theorem compileProbeNamePairRanged : NameRanged "pair" := by
  intro c hc
  have hc' : c = 'p' ∨ c = 'a' ∨ c = 'i' ∨ c = 'r' := by simpa using hc
  rcases hc' with h | h | h | h <;> subst c <;> decide

private theorem compileProbeNameERanged : NameRanged "E" := by
  intro c hc
  have hc' : c = 'E' := by simpa using hc
  subst c
  decide

private theorem compileProbeNameCaughtRanged : NameRanged "caught" := by
  intro c hc
  have hc' : c = 'c' ∨ c = 'a' ∨ c = 'u' ∨ c = 'g' ∨ c = 'h' ∨ c = 't' := by
    simpa using hc
  rcases hc' with h | h | h | h | h | h <;> subst c <;> decide

private theorem compileProbeInlineReturnRanged {width : Nat} (name : String)
    (hname : NameRanged name) (value : BitVec width) :
    DeclByteRanged (width := width) (.function
      { name := name, inline := true, exported := false, params := [],
        body := .return (.const value), returnShape := .one }) := by
  simp only [DeclByteRanged, FunDeclByteRanged]
  refine ⟨hname, ?_, ?_, ?_⟩
  · simp [ListParamByteRanged]
  · simp [ProgByteRanged, ExpByteRanged]
  · simp [ShapeByteRanged]

private theorem compileProbeInlineCallRanged {width : Nat} (name function : String)
    (hname : NameRanged name) (hfunction : NameRanged function) :
    DeclByteRanged (width := width) (.function
      { name := name, inline := false, exported := true, params := [],
        body := .call none function ([] : List (Exp (BitVec width))), returnShape := .one }) := by
  simp only [DeclByteRanged, FunDeclByteRanged]
  refine ⟨hname, ?_, ?_, ?_⟩
  · simp [ListParamByteRanged]
  · simp only [ProgByteRanged]
    exact ⟨hfunction, by simp⟩
  · simp [ShapeByteRanged]

def compileProgExactDuplicateDecls : List (Decl (BitVec 8)) :=
  let declarations : List (Decl (BitVec 8)) :=
    [.function
       { name := "id", inline := true, exported := false, params := [],
         body := .return (.const (BitVec.ofNat 8 7)), returnShape := .one },
     .function
       { name := "id", inline := true, exported := false, params := [],
         body := .return (.const (BitVec.ofNat 8 9)), returnShape := .one },
     .function
       { name := "main", inline := false, exported := true, params := [],
         body := .call none "id" [], returnShape := .one }]
  declarations

theorem compileProgExactDuplicateDeclsByteRanged :
    ∀ declaration ∈ compileProgExactDuplicateDecls, DeclByteRanged declaration := by
  intro declaration hmem
  simp [compileProgExactDuplicateDecls] at hmem
  rcases hmem with h | h | h
  · subst declaration
    exact compileProbeInlineReturnRanged (width := 8) "id" compileProbeNameIdRanged _
  · subst declaration
    exact compileProbeInlineReturnRanged (width := 8) "id" compileProbeNameIdRanged _
  · rcases h with h | h
    · exact compileProbeInlineCallRanged (width := 8) "main" "id"
        compileProbeNameMainRanged compileProbeNameIdRanged

def compileProgExactNestedDecls : List (Decl (BitVec 8)) :=
  let declarations : List (Decl (BitVec 8)) :=
    [.function
       { name := "leaf", inline := true, exported := false, params := [],
         body := .return (.const (BitVec.ofNat 8 7)), returnShape := .one },
     .function
       { name := "mid", inline := true, exported := false, params := [],
         body := .call none "leaf" [], returnShape := .one },
     .function
       { name := "main", inline := false, exported := true, params := [],
         body := .call none "mid" [], returnShape := .one }]
  declarations

theorem compileProgExactNestedDeclsByteRanged :
    ∀ declaration ∈ compileProgExactNestedDecls, DeclByteRanged declaration := by
  intro declaration hmem
  simp [compileProgExactNestedDecls] at hmem
  rcases hmem with h | h | h
  · subst declaration
    exact compileProbeInlineReturnRanged (width := 8) "leaf" compileProbeNameLeafRanged _
  · subst declaration
    exact compileProbeInlineCallRanged (width := 8) "mid" "leaf"
      compileProbeNameMidRanged compileProbeNameLeafRanged
  · rcases h with h | h
    · exact compileProbeInlineCallRanged (width := 8) "main" "mid"
        compileProbeNameMainRanged compileProbeNameMidRanged

def compileProgExactProductionEmptyParity : Bool :=
  match compileProgTopHOLProductionExactInline ([] : List (Decl (BitVec 8))) (by
      intro declaration hmem
      simp at hmem) with
  | [] => true
  | _ => false

def compileProgExactProductionDuplicateParity : Bool :=
  match compileProgTopHOLProductionExactInline compileProgExactDuplicateDecls
      compileProgExactDuplicateDeclsByteRanged with
  | [("id", [], .return [.const first]),
     ("id", [], .return [.const second]),
     ("main", [], .seq .tick (.return [.const returned]))] =>
      first == BitVec.ofNat 8 7 && second == BitVec.ofNat 8 9 &&
        returned == BitVec.ofNat 8 7
  | _ => false

def compileProgExactProductionNestedParity : Bool :=
  match compileProgTopHOLProductionExactInline compileProgExactNestedDecls
      compileProgExactNestedDeclsByteRanged with
  | [("leaf", [], .return [.const leafValue]),
     ("mid", [], .seq .tick (.return [.const midValue])),
     ("main", [], .seq .tick (.seq .tick (.return [.const mainValue])))] =>
      leafValue == BitVec.ofNat 8 7 && midValue == BitVec.ofNat 8 7 &&
        mainValue == BitVec.ofNat 8 7
  | _ => false

#guard compileProgExactProductionEmptyParity
#guard compileProgExactProductionDuplicateParity
#guard compileProgExactProductionNestedParity

/-! Further direct `compile_prog_probe.out` rows exercise the exact parser route
    on a mutual inline cycle, handler recursion, and a multi-value return. These
    distinguish HOL's per-callee `DOMSUB` recursion and handler clause from a
    top-level recursion guard, and retain the exact output shapes observed by
    the original HOL EVAL probe. -/
def compileProgExactCycleDecls : List (Decl (BitVec 8)) :=
  [.function
     { name := "f", inline := true, exported := false, params := [],
       body := .call none "g" [], returnShape := .one },
   .function
     { name := "g", inline := true, exported := false, params := [],
       body := .call none "f" [], returnShape := .one },
   .function
     { name := "main", inline := false, exported := true, params := [],
       body := .call none "f" [], returnShape := .one }]

theorem compileProgExactCycleDeclsByteRanged :
    ∀ declaration ∈ compileProgExactCycleDecls, DeclByteRanged declaration := by
  intro declaration hmem
  simp [compileProgExactCycleDecls] at hmem
  rcases hmem with h | h | h
  · subst declaration
    simpa [DeclByteRanged, FunDeclByteRanged] using
      (compileProbeInlineCallRanged (width := 8) "f" "g"
        compileProbeNameFRanged compileProbeNameGRanged)
  · subst declaration
    simpa [DeclByteRanged, FunDeclByteRanged] using
      (compileProbeInlineCallRanged (width := 8) "g" "f"
        compileProbeNameGRanged compileProbeNameFRanged)
  · subst declaration
    exact compileProbeInlineCallRanged (width := 8) "main" "f"
      compileProbeNameMainRanged compileProbeNameFRanged

def compileProgExactCycleParity : Bool :=
  match compileProgTopHOLProductionExactInline compileProgExactCycleDecls
      compileProgExactCycleDeclsByteRanged with
  | [("f", [], .seq .tick (.call none "f" [])),
     ("g", [], .seq .tick (.call none "g" [])),
     ("main", [], .seq .tick (.seq .tick (.call none "f" [])))] => true
  | _ => false

#guard compileProgExactCycleParity

def compileProgCycleCompatibilityParity : Bool :=
  match compileProgTopHOL compileProgExactCycleDecls with
  | [("f", [], .seq .tick (.call none "f" [])),
     ("g", [], .seq .tick (.call none "g" [])),
     ("main", [], .seq .tick (.seq .tick (.call none "f" [])))] => true
  | _ => false

#guard compileProgCycleCompatibilityParity

def compileProgExactHandlerDecls : List (Decl (BitVec 8)) :=
  [.exnDecl "E" .one,
   .function
     { name := "id", inline := true, exported := false, params := [],
       body := .return (.const 7), returnShape := .one },
   .function
     { name := "main", inline := false, exported := true, params := [],
       body := .call (some (none, some ("E", "caught", .call none "id" [])))
         "id" [], returnShape := .one }]

theorem compileProgExactHandlerDeclsByteRanged :
    ∀ declaration ∈ compileProgExactHandlerDecls, DeclByteRanged declaration := by
  intro declaration hmem
  simp [compileProgExactHandlerDecls] at hmem
  rcases hmem with h | h | h
  · subst declaration
    exact ⟨compileProbeNameERanged, by simp [ShapeByteRanged]⟩
  · subst declaration
    exact compileProbeInlineReturnRanged (width := 8) "id"
      compileProbeNameIdRanged 7
  · subst declaration
    simp only [DeclByteRanged, FunDeclByteRanged]
    refine ⟨compileProbeNameMainRanged, ?_, ?_, ?_⟩
    · simp [ListParamByteRanged]
    · simp only [ProgByteRanged]
      exact ⟨compileProbeNameIdRanged, by simp,
        ⟨True.intro,
          ⟨compileProbeNameERanged, compileProbeNameCaughtRanged,
            compileProbeNameIdRanged, by simp, True.intro⟩⟩⟩
    · simp [ShapeByteRanged]

def compileProgExactHandlerParity : Bool :=
  match compileProgTopHOLProductionExactInline compileProgExactHandlerDecls
      compileProgExactHandlerDeclsByteRanged with
  | [("id", [], .return [.const value]),
     ("main", [], .dec 1 (.const 0)
       (.call (some ([1], some (0, .seq .skip
         (.seq .tick (.return [.const handledValue]))))) "id" []))] =>
      value == BitVec.ofNat 8 7 && handledValue == BitVec.ofNat 8 7
  | _ => false

#guard compileProgExactHandlerParity

def compileProgHandlerCompatibilityParity : Bool :=
  match compileProgTopHOL compileProgExactHandlerDecls with
  | [("id", [], .return [.const value]),
     ("main", [], .dec 1 (.const 0)
       (.call (some ([1], some (0, .seq .skip
         (.seq .tick (.return [.const handledValue]))))) "id" []))] =>
      value == BitVec.ofNat 8 7 && handledValue == BitVec.ofNat 8 7
  | _ => false

#guard compileProgHandlerCompatibilityParity

def compileProgExactAggregateReturnDecls : List (Decl (BitVec 8)) :=
  [.function
     { name := "pair", inline := true, exported := false, params := [],
       body := .return (.rStruct [.const 7, .const 9]),
       returnShape := .comb [.one, .one] },
   .function
     { name := "main", inline := false, exported := true, params := [],
       body := .call none "pair" [], returnShape := .comb [.one, .one] }]

theorem compileProgExactAggregateReturnDeclsByteRanged :
    ∀ declaration ∈ compileProgExactAggregateReturnDecls,
      DeclByteRanged declaration := by
  intro declaration hmem
  simp [compileProgExactAggregateReturnDecls] at hmem
  rcases hmem with h | h
  · subst declaration
    simp only [DeclByteRanged, FunDeclByteRanged]
    refine ⟨compileProbeNamePairRanged, ?_, ?_, ?_⟩
    · simp [ListParamByteRanged]
    · simp [ProgByteRanged, ExpByteRanged, ListExpByteRanged]
    · simp [ShapeByteRanged]
  · subst declaration
    simp only [DeclByteRanged, FunDeclByteRanged]
    refine ⟨compileProbeNameMainRanged, ?_, ?_, ?_⟩
    · simp [ListParamByteRanged]
    · simp only [ProgByteRanged]
      exact ⟨compileProbeNamePairRanged, by simp, True.intro⟩
    · simp [ShapeByteRanged]

def compileProgExactAggregateReturnParity : Bool :=
  match compileProgTopHOLProductionExactInline compileProgExactAggregateReturnDecls
      compileProgExactAggregateReturnDeclsByteRanged with
  | [("pair", [], .return [.const first, .const second]),
     ("main", [], .seq .tick (.return [.const mainFirst, .const mainSecond]))] =>
      first == BitVec.ofNat 8 7 && second == BitVec.ofNat 8 9 &&
        mainFirst == BitVec.ofNat 8 7 && mainSecond == BitVec.ofNat 8 9
  | _ => false

#guard compileProgExactAggregateReturnParity

def compileProgAggregateReturnCompatibilityParity : Bool :=
  match compileProgTopHOL compileProgExactAggregateReturnDecls with
  | [("pair", [], .return [.const first, .const second]),
     ("main", [], .seq .tick (.return [.const mainFirst, .const mainSecond]))] =>
      first == BitVec.ofNat 8 7 && second == BitVec.ofNat 8 9 &&
        mainFirst == BitVec.ofNat 8 7 && mainSecond == BitVec.ofNat 8 9
  | _ => false

#guard compileProgAggregateReturnCompatibilityParity

def compileProgExactDuplicateMatchesProduction : Bool :=
  match compileProgTopHOL compileProgExactDuplicateDecls,
      compileProgTopHOLProductionExactInline compileProgExactDuplicateDecls
        compileProgExactDuplicateDeclsByteRanged with
  | [(_, [], .return [.const directFirst]),
     (_, [], .return [.const directSecond]),
     (_, [], .seq .tick (.return [.const directReturned]))],
    [(_, [], .return [.const exactFirst]),
     (_, [], .return [.const exactSecond]),
     (_, [], .seq .tick (.return [.const exactReturned]))] =>
      directFirst == exactFirst && directSecond == exactSecond &&
        directReturned == exactReturned
  | _, _ => false

def compileProgExactNestedMatchesProduction : Bool :=
  match compileProgTopHOL compileProgExactNestedDecls,
      compileProgTopHOLProductionExactInline compileProgExactNestedDecls
        compileProgExactNestedDeclsByteRanged with
  | [(_, [], .return [.const directLeaf]),
     (_, [], .seq .tick (.return [.const directMid])),
     (_, [], .seq .tick (.seq .tick (.return [.const directMain])))],
    [(_, [], .return [.const exactLeaf]),
     (_, [], .seq .tick (.return [.const exactMid])),
     (_, [], .seq .tick (.seq .tick (.return [.const exactMain])))] =>
      directLeaf == exactLeaf && directMid == exactMid && directMain == exactMain
  | _, _ => false

#guard compileProgExactDuplicateMatchesProduction
#guard compileProgExactNestedMatchesProduction

/-! The fixture is the direct HOL evaluation of
    `pan_to_crep$compile_prog` on the same inline callee/caller pair. -/
theorem compile_prog_inline_call_parity :
    compileProgToCrep compileProgProbeContext compileProgProbeDecls =
      [{ name := "leaf", params := [], body := .return [.const 7],
         returnShape := .one },
       { name := "mid", params := [],
         body := .seq .tick (.return [.const 7]), returnShape := .one },
       { name := "main", params := [],
         body := .seq .tick (.seq .tick (.return [.const 7])), returnShape := .one }] := by
  simp [compileProgToCrep, pipelineInlineNames, compileToCrep,
    compileFunctionsSource, compileFunDeclSource, panToCrepCompFunc,
    panToCrepVars_eq, Shape.shapeSize, panToCrepCompileInlTop,
    functionInfos, compileProgProbeContext, compileProgProbeDecls,
    compileProg, compileExp, compileArgs,
    crepInlineTopRecursiveByNames, crepInlineTopRecursive,
    crepInlineFunctionsRecursive, crepInlineActiveNames,
    crepInlineProgRecursive, crepInlineLookup, crepInlineCallBody,
    crepInlineTail, crepArgLoad, crepInlineTmpNames, crepUnreachElim,
    nestedDecs]

/-! Cake's `first_compile_prog_all_distinct` regression: the complete
    source-shaped `compile_prog` boundary keeps every function name distinct
    after the selected inline bodies have been rewritten. -/
theorem compile_prog_first_compile_prog_all_distinct :
    (compileProgToCrep compileProgProbeContext compileProgProbeDecls).map
      CompiledFunction.name |>.Nodup := by
  exact compileProgToCrep_names_nodup _ _ (by
    simp [compileProgProbeDecls, functionDeclarationNames])

/-! Cake's `compile_prog_distinct_params` regression at the same complete
    source-shaped boundary. -/
theorem compile_prog_compile_prog_distinct_params :
    ∀ function ∈ compileProgToCrep compileProgProbeContext compileProgProbeDecls,
      function.params.Nodup := by
  exact compileProgToCrep_params_nodup _ _

def parityGuard : Bool :=
  match compileProgToCrep compileProgProbeContext compileProgProbeDecls with
  | [{ name := "leaf", params := [], body := .return [.const 7],
         returnShape := .one },
     { name := "mid", params := [],
       body := .seq .tick (.return [.const 7]), returnShape := .one },
     { name := "main", params := [],
       body := .seq .tick (.seq .tick (.return [.const 7])), returnShape := .one }] => true
  | _ => false

#eval parityGuard
#guard parityGuard

/-! HOL's `ShMemStore` constructor operands are positional value then address;
    `compile_def` allocates the shared-store temporary from the first operand
    (`pan_to_crepScript.sml:285-293`). This production parity row gives that
    stored-value operand a higher variable than the destination address. -/
def shMemStoreAddressTempContext : CompileContext Nat :=
  { vars := [("out", (.one, [2])), ("len", (.one, [1]))], functions := [],
    exceptions := [], maxVar := 2, bytesInWord := 8 }

def shMemStoreAddressTempParity : Bool :=
  match compileProg shMemStoreAddressTempContext
      (.shMemStore .opW (.var .local "out") (.var .local "len")) with
  | .dec 3 (.var 1) (.shMem .store 3 (.var 2)) => true
  | _ => false

#guard shMemStoreAddressTempParity

/-! Cake's `crep_inline` prunes an inline callee at its first terminal
    statement before splicing it into the caller.  The assignment after the
    return is deliberately unreachable and must not survive the inline. -/
def compileProgUnreachableInlineEntries : List (CrepInlineEntry Nat) :=
  [("callee", ([],
    .seq (.return [.const 7]) (.assign 99 (.const 42))))]

def compileProgUnreachableInlineResult : CrepProg Nat :=
  crepInlineProgRecursive compileProgUnreachableInlineEntries
    (crepInlineActiveNames compileProgUnreachableInlineEntries)
    (.call none "callee" [])

def compileProgUnreachableInlineGuard : Bool :=
  match compileProgUnreachableInlineResult with
  | .seq .tick (.return [.const 7]) => true
  | _ => false

#guard compileProgUnreachableInlineGuard

/-! ### Direct HOL `compile_prog_probe.out` oracle rows for the exact decl-level port

These replay the committed HOL rows (`empty`, `inline_call`, `duplicate_first`,
`nested_inline`; `scripts/hol-probes/compile_prog_probe.out`) through the exact
tagged declaration-level `compileProgDeclsHOLW` (bead `flapjack-4ac.2.20.2.1`).
`CrepProgHOL` has no `DecidableEq`, so the bodies are checked with small
structural matchers for the row shapes rather than equality. -/

open Flapjack.Basis.Pure.MlString

def exactDeclIsReturnConst (n : Nat) : CrepProgHOL 8 → Bool
  | .return [.const m] => m == BitVec.ofNat 8 n
  | _ => false

def exactDeclIsSeqTickReturnConst (n : Nat) : CrepProgHOL 8 → Bool
  | .seq .tick rest => exactDeclIsReturnConst n rest
  | _ => false

def exactDeclIsSeqTickSeqTickReturnConst (n : Nat) : CrepProgHOL 8 → Bool
  | .seq .tick rest => exactDeclIsSeqTickReturnConst n rest
  | _ => false

def exactDeclTriple (name : String) (params : List Nat)
    (body : Bool) (t : MlS × List Nat × CrepProgHOL 8) : Bool :=
  (t.1 == ofString name) && (t.2.1 == params) && body

def exactDeclInlineLeaf (n : Nat) : DeclHOL 8 :=
  .function ⟨ofString "leaf", true, false, [], .return (.const (BitVec.ofNat 8 n)), .one⟩

def exactDeclInlineMid : DeclHOL 8 :=
  .function ⟨ofString "mid", true, false, [], .call none (ofString "leaf") [], .one⟩

def exactDeclInlineMain : DeclHOL 8 :=
  .function ⟨ofString "main", false, true, [], .call none (ofString "mid") [], .one⟩

def exactDeclInlineCallDecls : List (DeclHOL 8) :=
  [.function ⟨ofString "id", true, false, [], .return (.const (BitVec.ofNat 8 7)), .one⟩,
   .function ⟨ofString "main", false, true, [], .call none (ofString "id") [], .one⟩]

def exactDeclNestedDecls : List (DeclHOL 8) :=
  [exactDeclInlineLeaf 7, exactDeclInlineMid, exactDeclInlineMain]

/-- HOL `empty=[]`. -/
theorem exactDeclCompileProg_empty :
    Flapjack.compileProgDeclsHOLW ([] : List (DeclHOL 8)) = [] := rfl

/-- HOL `inline_call=[(«id»,[],Return [Const 7w]); («main»,[],Seq Tick (Return [Const 7w]))]`. -/
def exactDeclCompileProgInlineCall : Bool :=
  match Flapjack.compileProgDeclsHOLW exactDeclInlineCallDecls with
  | [t1, t2] =>
      exactDeclTriple "id" [] (exactDeclIsReturnConst 7 t1.2.2) t1 &&
      exactDeclTriple "main" [] (exactDeclIsSeqTickReturnConst 7 t2.2.2) t2
  | _ => false

#guard exactDeclCompileProgInlineCall

/-- HOL `duplicate_first`: the first `«id»` body wins, so `main` inlines `Return [Const 7w]`. -/
def exactDeclDuplicateDecls : List (DeclHOL 8) :=
  [.function ⟨ofString "id", true, false, [], .return (.const (BitVec.ofNat 8 7)), .one⟩,
   .function ⟨ofString "id", true, false, [], .return (.const (BitVec.ofNat 8 9)), .one⟩,
   .function ⟨ofString "main", false, true, [], .call none (ofString "id") [], .one⟩]

def exactDeclCompileProgDuplicateFirst : Bool :=
  match Flapjack.compileProgDeclsHOLW exactDeclDuplicateDecls with
  | [t1, t2, t3] =>
      exactDeclTriple "id" [] (exactDeclIsReturnConst 7 t1.2.2) t1 &&
      exactDeclTriple "id" [] (exactDeclIsReturnConst 9 t2.2.2) t2 &&
      exactDeclTriple "main" [] (exactDeclIsSeqTickReturnConst 7 t3.2.2) t3
  | _ => false

#guard exactDeclCompileProgDuplicateFirst

/-- HOL `nested_inline=[(«leaf»,…); («mid»,Seq Tick (Return 7)); («main»,Seq Tick (Seq Tick (Return 7)))]`. -/
def exactDeclCompileProgNestedInline : Bool :=
  match Flapjack.compileProgDeclsHOLW exactDeclNestedDecls with
  | [t1, t2, t3] =>
      exactDeclTriple "leaf" [] (exactDeclIsReturnConst 7 t1.2.2) t1 &&
      exactDeclTriple "mid" [] (exactDeclIsSeqTickReturnConst 7 t2.2.2) t2 &&
      exactDeclTriple "main" [] (exactDeclIsSeqTickSeqTickReturnConst 7 t3.2.2) t3
  | _ => false

#guard exactDeclCompileProgNestedInline

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS compile_prog inline-call source parity"
  else
    IO.println "FAIL compile_prog parity"
  if compileProgUnreachableInlineGuard then
    IO.println "PASS compile_prog unreach-before-inline parity"
  else
    IO.println "FAIL compile_prog unreach-before-inline parity"
  if shMemStoreAddressTempParity then
    IO.println "PASS compile_prog shared-store address temporary parity"
  else
    IO.println "FAIL compile_prog shared-store address temporary parity"
  pure (parityGuard && compileProgUnreachableInlineGuard &&
    shMemStoreAddressTempParity)

end Flapjack.Test.CompileProgParity
