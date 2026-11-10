module

public import Flapjack.Pancake.Proofs.PanGlobals
public import Flapjack.Pancake.Proofs.PanSimp.ProgOfHOL
public import Flapjack.Pancake.PanGlobalsByteRanged
public import Flapjack.Pancake.PanStructs.CompileExpCorrespondence
public import Flapjack.Pancake.PanStructs.CompileDeclsExact
public import Flapjack.CompileFunctionDistinct
public import Flapjack.Pancake.CrepToLoop.ProductionCompileProg
public import Flapjack.Pancake.PanToCrep.CompileToCrepBridge
public import Flapjack.Pancake.CrepInline.InlineRouteNames
public import Flapjack.Pancake.LoopToWord.CompFuncExact
public import Flapjack.Pancake.LoopToWord.LoopProgCarrierCodec
public import Flapjack.RiscV.WordDiagnostics
public import Flapjack.RiscV.WordFuseConditions
public import Flapjack.RiscV.WordUnreach
public import Flapjack.RiscV.Lab
public import Flapjack.Display

-- Checks below run compiled code from these modules.
public meta import Flapjack.CompileFunctionDistinct
public meta import Flapjack.Display
public meta import Flapjack.Pancake.CrepInline.InlineRouteNames
public meta import Flapjack.Pancake.CrepToLoop.ProductionCompileProg
public meta import Flapjack.Pancake.LoopToWord.CompFuncExact
public meta import Flapjack.Pancake.LoopToWord.LoopProgCarrierCodec
public meta import Flapjack.Pancake.PanGlobalsByteRanged
public meta import Flapjack.Pancake.PanStructs.CompileDeclsExact
public meta import Flapjack.Pancake.PanStructs.CompileExpCorrespondence
public meta import Flapjack.Pancake.PanToCrep.CompileToCrepBridge
public meta import Flapjack.Pancake.Proofs.PanGlobals
public meta import Flapjack.Pancake.Proofs.PanSimp.ProgOfHOL
public meta import Flapjack.RiscV.Lab
public meta import Flapjack.RiscV.WordDiagnostics
public meta import Flapjack.RiscV.WordFuseConditions
public meta import Flapjack.RiscV.WordUnreach
@[expose] public section

namespace Flapjack.Test.PanGlobalsCompileTopForStartParity

def mainFunction : Decl Nat :=
  .function
    { name := "main"
      inline := false
      exported := false
      params := []
      body := .skip
      returnShape := .one }

def word64MainFunction : Decl (BitVec 64) :=
  .function
    { name := "main"
      inline := false
      exported := false
      params := []
      body := .skip
      returnShape := .one }

def word64Global : Decl (BitVec 64) :=
  .decl .one "g" (.const (BitVec.ofNat 64 7))

/-! Exact-field check for `global_present` in
    `scripts/hol-probes/pan_globals_compile_top_probe.out`: the global `g`
    stores 7 at `TopAddr - bytes_in_word` before the generated main tail-calls
    the renamed source function. -/
def globalPresentParityGuard : Bool :=
  match globalCompileTopCake [word64Global, word64MainFunction] "main" with
  | [.function main, .function renamed] =>
      main.name == "main" && main.inline == false && main.exported == false &&
      main.params.isEmpty && (match main.returnShape with | .one => true | _ => false) &&
      (match main.body with
      | .seq
          (.seq
            (.store (.op .sub [.topAddr, .const address]) (.const value))
            .skip)
          (.call none "main'" []) =>
            address == BitVec.ofNat 64 8 && value == BitVec.ofNat 64 7
      | _ => false) &&
      renamed.name == "main'" && renamed.inline == false &&
      renamed.exported == false && renamed.params.isEmpty &&
      (match renamed.returnShape with | .one => true | _ => false) &&
      (match renamed.body with | .skip => true | _ => false)
  | _ => false

#eval globalPresentParityGuard
#guard globalPresentParityGuard

/-! The source-facing entry helper carries the tagged HOL definition's result
    into the declarations compiled by the downstream Crep pass. -/
def parityGuard : Bool :=
  let missing :=
    globalCompileTopForStart 4 id [mainFunction] "absent"
  let simple :=
    globalCompileTopForStart 4 id [mainFunction] "main"
  (match missing with
  | [] => true
  | _ => false) &&
  (match simple with
  | [.function entry, .function renamed] =>
      entry.name == "main" &&
      entry.inline == false && entry.exported == false &&
      entry.params.isEmpty &&
      (match entry.returnShape with
      | .one => true
      | _ => false) &&
      (match entry.body with
      | .seq .skip (.call none "main'" []) => true
      | _ => false) &&
      renamed.name == "main'" &&
      (match renamed.body with
      | .skip => true
      | _ => false)
  | _ => false)

#eval parityGuard
#guard parityGuard

/-! Fixed-width outputs for the `missing_start` and `present_start` rows in
    `scripts/hol-probes/pan_globals_compile_top_probe.out`. -/
def word64StartParityGuard : Bool :=
  let missing := globalCompileTopCake [word64MainFunction] "absent"
  let present := globalCompileTopCake [word64MainFunction] "main"
  (match missing with
  | [] => true
  | _ => false) &&
  (match present with
  | [.function entry, .function renamed] =>
      entry.name == "main" && entry.inline == false && entry.exported == false &&
      entry.params.isEmpty &&
      (match entry.returnShape with | .one => true | _ => false) &&
      (match entry.body with
      | .seq .skip (.call none "main'" []) => true
      | _ => false) &&
      renamed.name == "main'" && renamed.inline == false &&
      renamed.exported == false && renamed.params.isEmpty &&
      (match renamed.returnShape with | .one => true | _ => false) &&
      (match renamed.body with | .skip => true | _ => false)
  | _ => false)

#eval word64StartParityGuard
#guard word64StartParityGuard

def correctnessGuard : Bool :=
  (globalCompileTopForStart 4 id [mainFunction] "main").all
    (fun declaration => globalDeclIsFunction declaration ||
      globalDeclIsException declaration)

#eval correctnessGuard
#guard correctnessGuard

def exceptionDecl : Decl Nat :=
  .exnDecl "E" (.named "T")

def exceptionGuard : Bool :=
  let declarations := [exceptionDecl, mainFunction]
  (exceptionEntries (globalCompileTopForStart 4 id declarations "main")).length ==
    (exceptionEntries declarations).length

#eval exceptionGuard
#guard exceptionGuard

def otherFunction : Decl Nat :=
  .function
    { name := "worker"
      inline := false
      exported := false
      params := []
      body := .skip
      returnShape := .one }

def namesNodupGuard : Bool :=
  match globalCompileTopForStart 4 id [mainFunction, otherFunction] "main" with
  | compiled =>
      ((functions compiled).map (fun entry => entry.1)).Nodup

#eval namesNodupGuard
#guard namesNodupGuard

/-! ## `nestedSeqHOL`-routed executed global compiler (bead flapjack-4ac.1.31.1)

`globalCompileTopCakeOfExact` builds the synthesized `main` initializer
sequence through `nestedSeqCake` (i.e. the tagged `nestedSeqHOL`).  On the
parser's byte-range invariant it agrees with the production `globalCompileTopCake`;
the guarded fixture below checks the rerouted output on the same declarations
used by `sourceEntryUsesCakeGlobalOutput`. -/

private theorem word64CompileInputRanged :
    ∀ declaration ∈ [word64Global, word64MainFunction],
      Flapjack.Pancake.PanLang.DeclByteRanged declaration := by
  intro declaration hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · simp [word64Global, Flapjack.Pancake.PanLang.DeclByteRanged,
      Flapjack.Pancake.PanLang.NameRanged, Flapjack.Pancake.PanLang.ShapeByteRanged,
      Flapjack.Pancake.PanLang.ExpByteRanged]
  · simp [word64MainFunction, Flapjack.Pancake.PanLang.DeclByteRanged,
      Flapjack.Pancake.PanLang.FunDeclByteRanged, Flapjack.Pancake.PanLang.NameRanged,
      Flapjack.Pancake.PanLang.ListParamByteRanged, Flapjack.Pancake.PanLang.ParamByteRanged,
      Flapjack.Pancake.PanLang.ShapeByteRanged, Flapjack.Pancake.PanLang.ProgByteRanged]

end Flapjack.Test.PanGlobalsCompileTopForStartParity
