import Flapjack.Compiler.Backend.StackProps.ClockSupport
import Flapjack.Compiler.Backend.StackProps.StateConstants
import Flapjack.Compiler.Backend.LabProps.Native
import Flapjack.Compiler.Backend.StackToLab.Native
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopPrimitives
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopCalls
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemop.Handlers
import Flapjack.Compiler.Backend.WordAlloc.Proofs.LimitVar.Properties
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameMovePreserve
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAOptionLookupSubset
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenamePropertyWrappers
import Flapjack.Pancake.LoopToWord.Proofs.ProgramNames
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoveLookups
import Flapjack.Pancake.LoopToWord.Proofs.LabelHandlers
import Flapjack.Pancake.WordConvs.PredicateEquations
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsPhysicalStateUpdates
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoves.CorrectLeft
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapStep
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsInsert
import Flapjack.Compiler.Backend.WordToStack.Proofs.CodeLabelSafety
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsSwap
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsPhysicalInsert
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapPreservation
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsBounds
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapBounds
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoveDomains
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASetup.EvenListDistinct
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoveFrame
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoves.MoveHead
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoves.CorrectRight
import Flapjack.Compiler.Backend.WordAlloc.LimitVar
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameProperties
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARegisterFlip
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapExtend


import Flapjack
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopTop
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopPrograms
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAFixInconsistenciesCorrectLeft
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAFakeMovesCorrectRight
import Flapjack.Compiler.Backend.StackToLab.Proofs.Encoding.Full
import Flapjack.Compiler.Backend.WordAlloc.Instructions
import Flapjack.Compiler.Backend.Semantics.StackSem.StoreConsts
import Flapjack.Compiler.Backend.Semantics.StackSem.StoreConstsGuard
import Flapjack.Compiler.Backend.Semantics.StackSem.Allocation
import Flapjack.Compiler.Backend.Semantics.StackSem.Bitmap
import Flapjack.Compiler.Backend.Semantics.StackSem.WordBitmap
import Flapjack.Compiler.Backend.Semantics.StackSem.StackCodec
import Flapjack.Compiler.Backend.Semantics.StackSem.FpInstructions
import Flapjack.Compiler.Backend.Semantics.StackSem.Inst
import Flapjack.Compiler.Backend.Semantics.StackSem.FpRegisterInstructions
import Flapjack.Compiler.Encoders.Asm
import Flapjack.Pancake.CrepInline.Pass
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpPreservesEval.Load
import Flapjack.Pancake.PanCommon
import Flapjack.Pancake.PanToCrep.CompileProg
import Flapjack.Pancake.Proofs.PanStructs
import Flapjack.Pancake.Proofs.PanToCrep.CodeRelExact
import Flapjack.Pancake.Proofs.PanToCrep.CompileExpVmax
import Flapjack.Pancake.Semantics.CrepSem.Primop
import Flapjack.Pancake.Semantics.LoopSem
import Flapjack.Pancake.Semantics.PanCommonProps
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Semantics.PanSem.Primop
import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Pancake.WordLang
import Flapjack.Pancake.WordLang.OccurrencesExact
import Flapjack.Pancake.WordConvs
import Flapjack.Pancake.WordConvs.WfCutsets
import Flapjack.Pancake.WordConvs.NotCreated
import Flapjack.Pancake.WordConvs.NoInstall
import Flapjack.RiscV.CorrectnessEncoding
import Flapjack.Compiler.Backend.StackProps
import Flapjack.Pancake.PanStructs
import Flapjack.Compiler.Backend.RegAlloc.StateForeach
import Flapjack.Compiler.Backend.RegAlloc.StateFilter
import Flapjack.Compiler.Backend.RegAlloc.SortedInsert
import Flapjack.Compiler.Backend.RegAlloc.TagColour
import Flapjack.Compiler.Backend.RegAlloc.MoveTable
import Flapjack.Compiler.Backend.RegAlloc.GraphConstruction
import Flapjack.Compiler.Backend.RegAlloc.Proofs.MoveRelatedPartition
import Flapjack.Compiler.Backend.RegAlloc.Proofs.ArrayRead
import Flapjack.Compiler.Backend.RegAlloc.SplitDegree
import Flapjack.Compiler.Backend.RegAlloc.Proofs.NotCoalescedFilter
import Flapjack.Compiler.Backend.RegAlloc.ConsideredVar
import Flapjack.Compiler.Backend.RegAlloc.Proofs.ConsideredVarFilter
import Flapjack.Compiler.Backend.RegAlloc.Worklists
import Flapjack.Misc.LookupAny
import Flapjack.Compiler.Backend.RegAlloc.Coalesce
import Flapjack.Compiler.Backend.RegAlloc.SpillChoice
import Flapjack.Compiler.Backend.RegAlloc.MovePrep
import Flapjack.Compiler.Backend.RegAlloc.Proofs.ClashTreeDomain
import Flapjack.Compiler.Backend.RegAlloc.Proofs.MoveRelatedForeach
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameLookup
import Flapjack.Compiler.Backend.WordAlloc.SSAMergeMoves
import Flapjack.Compiler.Backend.WordAlloc.SSAFixInconsistencies
import Flapjack.Compiler.Backend.WordAlloc.SSATransInst
import Flapjack.Compiler.Backend.WordAlloc.SSAHelpers
import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans
import Flapjack.Compiler.Backend.WordAlloc.FullSSA
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAFixInconsistenciesCorrectRight
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAFakeMovesCorrectLeft
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMoveFrames
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoveBounds



open Lean Elab Command Flapjack

/-! List every `@[hol]`-tagged declaration with the qualifiers recorded by its
elaborated attribute and, for declarations without `(reals_as_rational_cuts)`,
whether its constant closure reaches one that carries it. Consumed by
`check_hol_ref_export.py`, which compares both against the theorem map. -/

/-- The body of a tagged definition or `opaque` declaration, if present. -/
private def definitionBody? : ConstantInfo → Option Expr
  | .defnInfo value => some value.value
  | .opaqueInfo value => some value.value
  | _ => none

/-- Constants mentioned by a declaration for the inherited-assumption closure:
    its type, and its body when it is a definition. Theorem proofs are not
    followed. -/
private def closureEdges (info : ConstantInfo) : Array Name :=
  let fromType := info.type.getUsedConstants
  match definitionBody? info with
  | some body => fromType ++ body.getUsedConstants
  | none => fromType

/-- Whether a declaration's type (and body, for a definition) transitively
    reaches a `(reals_as_rational_cuts)`-tagged declaration through Flapjack
    definitions and datatypes. `known` caches both outcomes soundly: a `true`
    result is cached when found, and when a traversal is exhausted without a
    hit every visited constant is cached as `false` (its closure lies inside
    the visited set). -/
private def reachesRealsCuts (env : Environment) (realsTagged : NameSet)
    (known : Std.HashMap Name Bool) (root : Name) : Bool × Std.HashMap Name Bool := Id.run do
  let flapjackModule (constName : Name) : Bool :=
    match env.getModuleIdxFor? constName with
    | some idx => (env.header.moduleNames[idx.toNat]!).getRoot == `Flapjack
    | none => true
  let mut known := known
  let mut visited : NameSet := {}
  let mut stack : Array Name :=
    match env.find? root with
    | some info => closureEdges info
    | none => #[]
  while !stack.isEmpty do
    let current := stack.back!
    stack := stack.pop
    if visited.contains current then continue
    visited := visited.insert current
    if realsTagged.contains current then
      return (true, known.insert root true)
    match known.get? current with
    | some true => return (true, known.insert root true)
    | some false => continue
    | none => pure ()
    if !flapjackModule current then continue
    match env.find? current with
    | some info =>
        match info with
        | .thmInfo _ => pure ()
        | _ => stack := stack ++ closureEdges info
    | none => pure ()
  for constName in visited.toList do
    known := known.insert constName false
  return (false, known.insert root false)

elab "#emit_hol_ref_export" : command => do
  let env ← getEnv
  let realsTagged : NameSet := (HolRef.all env).foldl
    (fun acc (entry : Name × HolRef) => if entry.2.realsAsRationalCuts then acc.insert entry.1 else acc) {}
  let mut known : Std.HashMap Name Bool := {}
  for (name, ref) in HolRef.all env do
    match env.find? name with
    | none => throwError "missing declaration {name}"
    | some _ =>
        let mut qualifiers : List (String × Json) := [
          ("list_as_array", toJson ref.listAsArray),
          ("names_as_string", toJson ref.namesAsString),
          ("names_as_string_boundary", toJson ref.namesAsStringBoundary),
          ("fmap_as_finite_support", toJson ref.fmapAsFiniteSupport),
          ("fmap_as_finite_support_result", toJson ref.fmapAsFiniteSupportResult),
          ("fmap_as_finite_support_function", toJson ref.fmapAsFiniteSupportFunction),
          ("fmap_as_finite_support_parameters", toJson ref.fmapAsFiniteSupportParameters),
          ("fmap_as_finite_support_existentials", toJson ref.fmapAsFiniteSupportExistentials),
          ("fmap_as_finite_support_relation",
            toJson (ref.fmapAsFiniteSupportRelation.map (fun entry => if entry.1.isEmpty then entry.2 else s!"{entry.1}.{entry.2}"))),
          ("fmap_as_finite_support_equalities", toJson ref.fmapAsFiniteSupportEqualities),
          ("words_as_type_indexed_bitvec", toJson ref.wordsAsTypeIndexedBitvec)]
        if ref.fmapAsFiniteSupportEquality then
          qualifiers := qualifiers ++ [("fmap_as_finite_support_equality", toJson true)]
        if !ref.fmapAsFiniteSupportHeterogeneousFunction.isEmpty then
          qualifiers := qualifiers ++ [
            ("fmap_as_finite_support_heterogeneous_function",
              toJson ref.fmapAsFiniteSupportHeterogeneousFunction)]
        if let some width := ref.wordDimensionAsWidth then
          qualifiers := qualifiers ++ [("word_dimension_as_width", toJson width)]
        if ref.realsAsRationalCuts then
          qualifiers := qualifiers ++ [("reals_as_rational_cuts", toJson true)]
        let mut fields : List (String × Json) := [
          ("lean_name", toJson name.toString),
          ("hol_path", toJson ref.path),
          ("hol_name", toJson ref.name),
          ("qualifiers", Json.mkObj qualifiers)]
        if !ref.realsAsRationalCuts then
          let (reaches, known') := reachesRealsCuts env realsTagged known name
          known := known'
          if reaches then
            fields := fields ++ [("inherits_reals_as_rational_cuts", toJson true)]
        liftIO <| IO.println (Json.mkObj fields).compress

#emit_hol_ref_export
