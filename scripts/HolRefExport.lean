import Flapjack.Compiler.Backend.StackProps.InstructionConstants
import Flapjack.Compiler.Backend.StackProps.ClockSupport
import Flapjack.Compiler.Backend.StackProps.ExpressionClock
import Flapjack.Compiler.Backend.StackProps.StateConstants
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoInstallPrograms
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoInstallCompiler
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopTop
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopPrograms
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemop
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
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAFixInconsistenciesCorrectLeft
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAFakeMovesCorrectRight
import Flapjack.Compiler.Backend.StackToLab.Proofs.Encoding.Full
import Flapjack.Compiler.Backend.LabToTarget.Interference
import Flapjack.Compiler.Backend.LabToTarget.NopEncoding
import Flapjack.Compiler.Backend.LabToTarget.SectionNavigation
import Flapjack.Pancake.WordConvs.ExpressionMonotonicity
import Flapjack.Compiler.Backend.WordAlloc.Proofs.MaxVarExp
import Flapjack.Compiler.Backend.WordAlloc.Proofs.MaxVarInst
import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterLabels
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileLookup
import Flapjack.Compiler.Backend.WordAlloc.GetHeuristics
import Flapjack.Compiler.Backend.Parmove.PreservesMoves.Pmov
import Flapjack.Compiler.Backend.WordToStack.Proofs.CodeLabels
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoInstall
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCodeLabels
import Flapjack.Compiler.Backend.WordToStack.Proofs.ProgramCodeLabels
import Flapjack.Compiler.Backend.WordToStack.Proofs.HandlerLabels
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopHelpers
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopCallCore
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopReturn
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopInstructions
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopFlatEffects
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopRecursive
import Flapjack.Pancake.WordConvs.CodeLabels
import Flapjack.Pancake.WordConvs.LabelSafety
import Flapjack.Compiler.Backend.StackProps.CodeLabels
import Flapjack.Compiler.Backend.StackProps.ForbiddenOperations
import Flapjack.Compiler.Backend.Parmove.PreservesMoves.Steps
import Flapjack.Compiler.Backend.Parmove.PreservesMoves.Step
import Flapjack.Compiler.Backend.LabToTarget.Navigation
import Flapjack.Compiler.Backend.LabToTarget.Memory
import Flapjack.Compiler.Backend.LabToTarget.Fetch
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar
import Flapjack.Compiler.Backend.RegAlloc.SortedMem
import Flapjack.Compiler.Backend.WordToStack.Proofs.ProgramBitmaps
import Flapjack.Compiler.Backend.Parmove.AllDistinct.Steps
import Flapjack.Compiler.Backend.RegAlloc.SortMoves
import Flapjack.Compiler.Backend.WordToStack.ProductionThreeToTwoDomain
import Flapjack.Compiler.Backend.RegAlloc.StatePartition
import Flapjack.Compiler.Backend.Parmove.MapState
import Flapjack.Compiler.Backend.Parmove.TempBeforeAssign.Steps
import Flapjack.Compiler.Backend.Parmove.StateToList
import Flapjack.Compiler.Backend.Parmove.AllDistinct.Step
import Flapjack.Compiler.Backend.RegAlloc.Initialization
import Flapjack.Compiler.Backend.WordAlloc.CanonizeMoves
import Flapjack.Translator.Monadic.MonadBase.ArrayLength
import Flapjack.Compiler.Backend.RegAlloc.StateMap
import Flapjack.Translator.Monadic.MonadBase.ListPrimitives
import Flapjack.Compiler.Backend.WordAlloc.CanonizeSort
import Flapjack.Misc.FindIndex.Append
import Flapjack.Compiler.Backend.RegAlloc.Exceptions
import Flapjack.Compiler.Backend.WordAlloc.HeuProg
import Flapjack.Compiler.Backend.RegAlloc.Remap
import Flapjack.Compiler.Backend.RegAlloc.SafeDiv
import Flapjack.Compiler.Backend.WordAlloc.CanonizeMovesAux
import Flapjack.Misc.FindIndex.ShiftZero
import Flapjack.Compiler.Backend.Parmove.TempBeforeAssign.Step
import Flapjack.Compiler.Backend.WordAlloc.HeuCall
import Flapjack.Compiler.Backend.WordAlloc.HeuMax
import Flapjack.Compiler.Backend.RegAlloc.Carriers
import Flapjack.Compiler.Backend.WordAlloc.HeuInst
import Flapjack.Misc.Sptree.Map
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.Assembly
import Flapjack.Misc.Sptree.Mapi
import Flapjack.Compiler.Backend.Parmove.Independence
import Flapjack.Compiler.Backend.WordAlloc.GetPrefs
import Flapjack.Compiler.Backend.WordAlloc.GetStackOnly
import Flapjack.Compiler.Backend.Parmove.ParseSemMapInj
import Flapjack.Compiler.Backend.Parmove.SeqsemUnchanged
import Flapjack.Compiler.Backend.WordAlloc.OracleColour
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.ReturnNoHandler
import Flapjack.Compiler.Backend.WordAlloc.HeuCounters
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.CallNone
import Flapjack.Misc.FindIndex.Bounds
import Flapjack.Compiler.Backend.Parmove.TempBeforeAssign.Append
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.ShareInst
import Flapjack.Compiler.Backend.WordAlloc.GetForced
import Flapjack.Compiler.Backend.WordAlloc.RemoveDead
import Flapjack.Compiler.Backend.WordAlloc.Proofs.RemoveDead
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead.Motive
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead.Loop
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead.Leaves
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead.Store
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead.Control
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead.StateEffect
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead.Move
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead.Inst
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead.Call
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead
import Flapjack.Compiler.Backend.WordAlloc.Proofs.GetForced
import Flapjack.Compiler.Backend.WordAlloc.CoalesceCost
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.LoopCases
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompilePrefix
import Flapjack.Compiler.Backend.Parmove.Correct
import Flapjack.Compiler.Backend.WordAlloc.Heuristics
import Flapjack.Compiler.Backend.WordAlloc.MergeStackSets
import Flapjack.Compiler.Backend.Parmove.TempBeforeAssign
import Flapjack.Compiler.Backend.Parmove.TempBeforeAssign.FirstIndex
import Flapjack.Misc.FindIndex
import Flapjack.Compiler.Backend.Parmove.DStepsSteps
import Flapjack.Compiler.Backend.WordAlloc.StackOnly
import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
import Flapjack.Misc.Sptree.UnionAlgebra
import Flapjack.Compiler.Backend.WordAlloc.EvenColour
import Flapjack.Compiler.Backend.Semantics.TargetSem.MappedMemory
import Flapjack.Compiler.Backend.WordAlloc.TotalColour
import Flapjack.Compiler.Backend.Parmove.SourceMembershipWrapper
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvenStartingLocals
import Flapjack.Compiler.Backend.WordToStack.Proofs.InsertBitmapPrefix
import Flapjack.Compiler.Backend.WordToStack.Proofs.LivePrefix
import Flapjack.Compiler.Backend.WordToStack.Proofs.LiveLength
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompLength
import Flapjack.Compiler.Backend.WordToStack.ProductionExpressionMaximum
import Flapjack.Compiler.Backend.WordToStack.ProductionCutsetMaximum
import Flapjack.Compiler.Backend.WordToStack.ProductionInstructionMaximum
import Flapjack.Compiler.Backend.WordToStack.ProductionColourDomain
import Flapjack.Compiler.Backend.WordToStack.ProductionProgramMaximum
import Flapjack.Compiler.Backend.WordToStack.ProductionSsaCodecDomain
import Flapjack.Compiler.Backend.WordToStack.ProductionDeadCodecDomain
import Flapjack.Compiler.Backend.WordToStack.ProductionCseCodecDomain
import Flapjack.Compiler.Backend.WordToStack.ProductionUnreachCodecDomain
import Flapjack.Compiler.Backend.Parmove.DestinationWrapper
import Flapjack.Compiler.Backend.Parmove.DStepStep
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileKeys
import Flapjack.Compiler.Backend.Parmove.PmovDsteps
import Flapjack.Compiler.Backend.WordToStack.NativeConfig
import Flapjack.Compiler.Backend.Parmove.DSteps
import Flapjack.Compiler.Backend.Parmove.DestinationMembership
import Flapjack.Compiler.Backend.Parmove.FstepDstep
import Flapjack.Compiler.Backend.Parmove.SourceMembership
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Install
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.FFI
import Flapjack.Pancake.WordLang.MaxVar
import Flapjack.Pancake.WordLang.CutsetsMax
import Flapjack.Pancake.WordLang.MaxVarInst
import Flapjack.Compiler.Backend.WordToStack.NativeCompile
import Flapjack.Compiler.Backend.Parmove.StepsCorrect
import Flapjack.Compiler.Backend.Parmove.PmovFinal
import Flapjack.Compiler.Backend.WordToStack.NativePrograms
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Inst
import Flapjack.Compiler.Backend.Parmove.StepsSem
import Flapjack.Pancake.WordLang.MaxVarExp
import Flapjack.Compiler.Backend.Parmove.StepSem
import Flapjack.Compiler.Backend.Parmove.StepSem.EmitHead
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.InstFp
import Flapjack.Compiler.Backend.WordToStack.NativeLive
import Flapjack.Compiler.Backend.WordToStack.NativeStubs
import Flapjack.Compiler.Backend.WordToStack.NativeHandlers
import Flapjack.Compiler.Backend.WordToStack.NativePerf
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.InstMemory
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.InstArith
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.InstAssign
import Flapjack.Compiler.Backend.LabSem.FpUpdates
import Flapjack.Compiler.Backend.LabSem.Arithmetic
import Flapjack.Compiler.Backend.WordToStack.NativeReturn
import Flapjack.Compiler.Backend.WordToStack.NativeSharedMemory
import Flapjack.Compiler.Backend.WordToStack.NativeCallArgs
import Flapjack.Compiler.Backend.WordToStack.NativeMoves
import Flapjack.Compiler.Backend.LabSem.Memory
import Flapjack.Compiler.Backend.LabSem.SharedMemory
import Flapjack.Compiler.Backend.LabSem.Inst
import Flapjack.Compiler.Backend.LabSem.Evaluate
import Flapjack.Compiler.Backend.LabSem.Semantics
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.If
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Loop
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.MustTerminate
import Flapjack.Compiler.Backend.WordToStack.NativeInstructions
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Seq
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ReadsLiveExpressions
import Flapjack.Compiler.Backend.LabSem.Navigation
import Flapjack.Compiler.Backend.LabProps.SectionEnd
import Flapjack.Compiler.Backend.LabSem.Updates
import Flapjack.Compiler.Backend.WordAlloc.Proofs.CheckPartialCol
import Flapjack.Misc.Sptree.InsertUnchanged
import Flapjack.Compiler.Backend.LabSem.Classifier
import Flapjack.Compiler.Encoders.AsmSem
import Flapjack.Compiler.Backend.LabSem.State
import Flapjack.SemanticsProps.Implements
import Flapjack.Pancake.Proofs.PanSimp.SeqAssocExact
import Flapjack.Pancake.Proofs.PanSimp.WhileBodyExact
import Flapjack.Pancake.Proofs.PanSimp.SkipSeqExact
import Flapjack.Pancake.Proofs.PanGlobals.FpermSemantics
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Prime
import Flapjack.Pancake.Proofs.PanGlobals.StateRelImpSemantics
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Decls
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Assembly
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Call
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.ExtCall
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Call
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.CallGlobalHandler
import Flapjack.Pancake.Proofs.CrepInline.ArgLoadCorrect
import Flapjack.Pancake.Proofs.CrepInline.ArgLoadStronger
import Flapjack.Compiler.Backend.StackNames.AsmAdmissibility.Defaults
import Flapjack.Compiler.Backend.StackNames.AsmAdmissibility.Assembly
import Flapjack.Compiler.Backend.StackNames.AsmAdmissibility.Recursive
import Flapjack.Compiler.Backend.StackNames.AsmAdmissibility.RegisterLeaves
import Flapjack.Compiler.Backend.StackNames.AsmAdmissibility.Inst
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.CallGlobal
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsCons
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.DecCall
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.CallHandlerNoDestination
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.CallLocalHandler
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.CallNoDestination
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.CallLocal
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.AssignGlobal
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.TailCall
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.Assemble
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.AssignPrimitive
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.ShMemStore
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.ShMemLoad
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.CallHandler
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.DecCall
import Flapjack.Pancake.Proofs.CrepInline.WhileInduction
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.While
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Raise
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Primitive
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.ExtCall
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Dec
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.If
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.AssignLocal
import Flapjack.Pancake.Proofs.PanGlobals.OptMmapEvalCorrect
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.DecCall
import Flapjack.Pancake.Proofs.PanGlobals.CompileExpCorrect
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.TailCall
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.ShMemStore
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.ExtCall
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Primitive
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Results
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Dec
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.ResVar
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Assign
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Memory
import Flapjack.Pancake.Proofs.PanGlobals.ReadBytearray
import Flapjack.Pancake.Proofs.PanGlobals.ByteStore
import Flapjack.Pancake.Proofs.PanGlobals.WriteBytearray
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Leaves
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.While
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.If
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Seq
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.ShMemLoad
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.CallNoHandler
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.CallHandler
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Assembly
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.TwoLocals
import Flapjack.Pancake.Proofs.PanGlobals.MemoryLookup
import Flapjack.Pancake.Proofs.PanGlobals.MemorySwap
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationCode
import Flapjack.Compiler.Backend.StackProps.ProgramValidity
import Flapjack.Compiler.Backend.StackProps.ProgramNames
import Flapjack.Compiler.Backend.StackProps.AllocArg
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationFfi
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationClock
import Flapjack.Pancake.Proofs.PanGlobals.CompileExpLeaves
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Base
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Seq
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.ShMem
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.ShMemGlobal
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Store
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Return
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Store32
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.StoreByte
import Flapjack.Pancake.Proofs.PanGlobals.MemStores
import Flapjack.Pancake.Proofs.PanGlobals.MemoryUpdate
import Flapjack.Pancake.Proofs.PanGlobals.ShMemLoadLemmas
import Flapjack.Compiler.Backend.StackProps.RemoveNames
import Flapjack.Pancake.Proofs.WordConvs.SmartSeqLabels
import Flapjack.Pancake.Proofs.WordConvs.RemoveDead
import Flapjack.Pancake.Proofs.PanGlobals.CompileExpOperators
import Flapjack.Pancake.Proofs.PanGlobals.CompileExpNamed
import Flapjack.Pancake.Proofs.PanGlobals.CompileExpCmpShift
import Flapjack.Pancake.Proofs.PanGlobals.CompileExpRStruct
import Flapjack.Pancake.Proofs.PanGlobals.CompileExpRField
import Flapjack.Pancake.Proofs.PanGlobals.SemanticsEmptyLocals
import Flapjack.Pancake.Proofs.PanGlobals.ShapeValueEval
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocalEval
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.If
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.Seq
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.Dec
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.While
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.CallNoHandler
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.TailCall
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.Leaves
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.Results
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.ExtCall
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationLocals
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsShape
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsDisjoint
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsSimulation
import Flapjack.Compiler.Backend.StackProps.FloatNames
import Flapjack.Compiler.Backend.StackProps.AddressNames
import Flapjack.Compiler.Backend.StackProps.InstructionNames
import Flapjack.Compiler.Backend.StackProps.ArithmeticNames
import Flapjack.Compiler.Backend.RiscVConfig.RegisterNames
import Flapjack.Compiler.Backend.StackNames.ProgramNames
import Flapjack.Compiler.Backend.StackNames.InstructionNames
import Flapjack.Compiler.Backend.StackNames.OperandNames
import Flapjack.Compiler.Backend.StackProps.FixedNames
import Flapjack.Compiler.Backend.WordAlloc.Proofs.CutEnv
import Flapjack.Compiler.Backend.WordAlloc.Proofs.CutEnvs
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EnvFrame
import Flapjack.Compiler.Backend.WordAlloc.Proofs.CutEnvLemma
import Flapjack.Compiler.Backend.WordAlloc.Proofs.PushPopEnv
import Flapjack.Compiler.Backend.WordAlloc.Proofs.PermuteSwap
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ColouringOk
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Motive
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Leaves
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Alloc
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Call
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.ShareInst
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.MoveStoreConsts
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PermuteSwap
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StackEq
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StackSwap
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StackLists
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap.Motive
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap.Leaves
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap.Alloc
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap.MustTerminate
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap.Seq
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap.If
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap.Loop
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap.Call
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap
import Flapjack.Compiler.Backend.WordAlloc.Proofs.CutNames
import Flapjack.Compiler.Backend.WordAlloc.Proofs.KeyRemap
import Flapjack.Pancake.PanStructs.CompileDeclsExact
import Flapjack.Pancake.PanStructs.CompileDeclsCorrespondence
import Flapjack.Pancake.PanStructs.CompileTopProduction
import Flapjack.Pancake.PanStructs.CompileProgTraversal
import Flapjack.Pancake.PanStructs.CompileProgCorrespondence
import Flapjack.Pancake.PanStructs.CompileProgProduction
import Flapjack.Pancake.PanStructs.CompileProgExact
import Flapjack.Pancake.PanStructs.CompileExpExact
import Flapjack.Pancake.PanStructs.OldExpShapeExact
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
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAExpressions
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAFixInconsistenciesProps
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAInstructionProps
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameShiftedProperties
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramPropsMove
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
