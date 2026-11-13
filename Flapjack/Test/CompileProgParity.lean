module

public import Flapjack.Pancake.Proofs.PanSimp.ProgOfHOL
public import Flapjack.Pancake.PanGlobals
public import Flapjack.Pancake.PanStructs.CompileExpCorrespondence
public import Flapjack.Pancake.PanStructs.CompileDeclsExact
public import Flapjack.Pancake.PanToCrep.Compile
public import Flapjack.CompileFunctionDistinct
public import Flapjack.Pancake.CrepToLoop.ProductionCompileProg
public import Flapjack.Pancake.PanToCrep.CompileToCrepBridge
public import Flapjack.Pancake.CrepInline.InlineRouteNames
public import Flapjack.Pancake.CrepInline.Canonical
public import Flapjack.Pancake.LoopToWord.CompFuncExact
public import Flapjack.Pancake.LoopToWord.LoopProgCarrierCodec
public import Flapjack.RiscV.WordDiagnostics
public import Flapjack.RiscV.WordFuseConditions
public import Flapjack.RiscV.WordUnreach
public import Flapjack.RiscV.Lab
public import Flapjack.Display
public import Flapjack.Pancake.PanToCrep.CompileExact
public meta import Flapjack.Pancake.CrepInline
public meta import Flapjack.Pancake.CrepInline.Pass
public meta import Flapjack.Pancake.PanToCrep.CompileExact

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Flapjack.Test.CompileProgParity

open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

def compileProgProbeContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0,
    bytesInWord := 1 }

#check @allocatedNames_gt
#check @freshNames_gt
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
  match CrepInlineCanonical.compileInlTopHOLExact (width := 8)
      [ofString "first", ofString "second"]
      [(ofString "first", [], .call none (ofString "second") []),
       (ofString "second", [], .return [.const 9])] with
  | [first, second] =>
      (match first.2.2 with
      | .seq .tick (.return [.const 9]) => true
      | _ => false) &&
      (match second.2.2 with
      | .return [.const 9] => true
      | _ => false)
  | _ => false

#guard compileInlTopOracle

/-! Direct HOL `compile_prog_probe.out` cases for the production triple-list
    `compile_inl_top` boundary. The first duplicate `id` definition wins in
    HOL's `alist_to_fmap`, while nested inline calls expand recursively. -/
def holInlineDuplicateInput :
    List (CrepInlineMapHOLName × List Nat × CrepProgHOL 8) :=
  [(ofString "id", [], .return [.const 7]),
   (ofString "id", [], .return [.const 9]),
   (ofString "main", [], .call none (ofString "id") [])]

def holInlineDuplicateParity : Bool :=
  match CrepInlineCanonical.compileInlTopHOLExact (width := 8) [ofString "id"]
    holInlineDuplicateInput with
  | [(firstName, [], .return [.const firstValue]),
     (secondName, [], .return [.const secondValue]),
     (mainName, [], .seq .tick (.return [.const returned]))] =>
      firstName == ofString "id" && secondName == ofString "id" &&
        mainName == ofString "main" &&
        firstValue == 7 && secondValue == 9 && returned == 7
  | _ => false

#guard holInlineDuplicateParity

def holInlineNestedInput :
    List (CrepInlineMapHOLName × List Nat × CrepProgHOL 8) :=
  [(ofString "leaf", [], .return [.const 7]),
   (ofString "mid", [], .call none (ofString "leaf") []),
   (ofString "main", [], .call none (ofString "mid") [])]

def holInlineNestedParity : Bool :=
  match CrepInlineCanonical.compileInlTopHOLExact (width := 8)
    [ofString "leaf", ofString "mid"] holInlineNestedInput with
  | [(leafName, [], .return [.const leafValue]),
     (midName, [], .seq .tick (.return [.const midValue])),
     (mainName, [], .seq .tick (.seq .tick (.return [.const mainValue])))] =>
      leafName == ofString "leaf" && midName == ofString "mid" &&
        mainName == ofString "main" &&
        leafValue == 7 && midValue == 7 && mainValue == 7
  | _ => false

#guard holInlineNestedParity

/-! Direct `compile_prog_probe.out` parity at the new exact
    `compile_prog` triple-list boundary. These declarations are word8 as in
    the HOL EVAL query, and cover the complete empty, duplicate-first, and
    nested-inline outputs rather than testing `compile_inl_top` in isolation. -/
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

def compileProgExactCycleDeclsHOL : List (DeclHOL 8) :=
  [.function ⟨ofString "f", true, false, [], .call none (ofString "g") [], .one⟩,
   .function ⟨ofString "g", true, false, [], .call none (ofString "f") [], .one⟩,
   .function ⟨ofString "main", false, true, [], .call none (ofString "f") [], .one⟩]

def exactDeclIsTriple (name : MlS) (params : List Nat)
    (body : CrepProgHOL 8 → Bool) : MlS × List Nat × CrepProgHOL 8 → Bool
  | (n, ps, prog) => n == name && ps == params && body prog

def exactDeclIsCall (n : MlS) : CrepProgHOL 8 → Bool
  | .call none name [] => name == n
  | _ => false

def exactDeclIsSeqTickCall (n : MlS) : CrepProgHOL 8 → Bool
  | .seq .tick rest => exactDeclIsCall n rest
  | _ => false

def exactDeclIsSeqTickSeqTickCall (n : MlS) : CrepProgHOL 8 → Bool
  | .seq .tick rest => exactDeclIsSeqTickCall n rest
  | _ => false

def compileProgCycleCompatibilityParity : Bool :=
  match compileProgDeclsHOLW compileProgExactCycleDeclsHOL with
  | [t1, t2, t3] =>
      exactDeclIsTriple (ofString "f") []
        (exactDeclIsSeqTickCall (ofString "f")) t1 &&
      exactDeclIsTriple (ofString "g") []
        (exactDeclIsSeqTickCall (ofString "g")) t2 &&
      exactDeclIsTriple (ofString "main") []
        (exactDeclIsSeqTickSeqTickCall (ofString "f")) t3
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

def exactDeclIsReturnConst (n : Nat) : CrepProgHOL 8 → Bool
  | .return [.const m] => m == BitVec.ofNat 8 n
  | _ => false

def compileProgExactHandlerDeclsHOL : List (DeclHOL 8) :=
  [.exnDecl (ofString "E") .one,
   .function ⟨ofString "id", true, false, [], .return (.const 7), .one⟩,
   .function ⟨ofString "main", false, true, [],
     .call (some (none, some (ofString "E", ofString "caught",
       .call none (ofString "id") []))) (ofString "id") [], .one⟩]

def exactDeclIsHandlerMain : CrepProgHOL 8 → Bool
  | .dec 1 (.const 0)
      (.call (some ([1], some (0, .seq .skip
        (.seq .tick (.return [.const handledValue]))))) name []) =>
      handledValue == BitVec.ofNat 8 7 && name == ofString "id"
  | _ => false

def compileProgHandlerCompatibilityParity : Bool :=
  match compileProgDeclsHOLW compileProgExactHandlerDeclsHOL with
  | [t1, t2] =>
      exactDeclIsTriple (ofString "id") []
        (exactDeclIsReturnConst 7) t1 &&
      exactDeclIsTriple (ofString "main") [] exactDeclIsHandlerMain t2
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

def compileProgExactAggregateReturnDeclsHOL : List (DeclHOL 8) :=
  [.function ⟨ofString "pair", true, false, [],
     .return (.rstruct [.const 7, .const 9]), .comb [.one, .one]⟩,
   .function ⟨ofString "main", false, true, [],
     .call none (ofString "pair") [], .comb [.one, .one]⟩]

def exactDeclIsReturnTwo (first second : Nat) : CrepProgHOL 8 → Bool
  | .return [.const x, .const y] =>
      x == BitVec.ofNat 8 first && y == BitVec.ofNat 8 second
  | _ => false

def exactDeclIsSeqTickReturnTwo (first second : Nat) : CrepProgHOL 8 → Bool
  | .seq .tick rest => exactDeclIsReturnTwo first second rest
  | _ => false

def compileProgAggregateReturnCompatibilityParity : Bool :=
  match compileProgDeclsHOLW compileProgExactAggregateReturnDeclsHOL with
  | [t1, t2] =>
      exactDeclIsTriple (ofString "pair") []
        (exactDeclIsReturnTwo 7 9) t1 &&
      exactDeclIsTriple (ofString "main") []
        (exactDeclIsSeqTickReturnTwo 7 9) t2
  | _ => false

#guard compileProgAggregateReturnCompatibilityParity

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
  if compileProgUnreachableInlineGuard then
    IO.println "PASS compile_prog unreach-before-inline parity"
  else
    IO.println "FAIL compile_prog unreach-before-inline parity"
  if shMemStoreAddressTempParity then
    IO.println "PASS compile_prog shared-store address temporary parity"
  else
    IO.println "FAIL compile_prog shared-store address temporary parity"
  pure (compileProgUnreachableInlineGuard && shMemStoreAddressTempParity)

end Flapjack.Test.CompileProgParity
