import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmNameCompiler
import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmNameFlat
import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmNameInstructions
import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmNameShare
import Flapjack.Pancake.WordConvs.FullInstOkLess
import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmNameHelpers
import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmRemoveCompiler
import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmRemoveHelpers
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackConventions
import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterBoundCompiler
import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterBoundRecursive
import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterBoundFlat
import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterBoundInstructions
import Flapjack.Compiler.Backend.WordToStack.Proofs.CallArgsCompiler
import Flapjack.Compiler.Backend.WordToStack.Proofs.ReturnCallArgs
import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterBoundMono
import Flapjack.Compiler.Backend.WordToStack.Proofs.ReturnRegisterBounds
import Flapjack.Compiler.Backend.WordToStack.Proofs.AllocArgs.Compiler
import Flapjack.Compiler.Backend.WordToStack.Proofs.AllocArgs.RecursiveCalls
import Flapjack.Compiler.Backend.WordToStack.Proofs.AllocArgs.Flat
import Flapjack.Compiler.Backend.WordToStack.Proofs.AllocArgs.Instructions
import Flapjack.Compiler.Backend.WordToStack.Proofs.ReturnAllocArgs
import Flapjack.Compiler.Backend.WordToStack.Proofs.ReturnLabels
import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadContinuations
import Flapjack.Compiler.Backend.WordToStack.Proofs.MoveReconstruction
import Flapjack.Compiler.Backend.WordToStack.Proofs.ALookupMap
import Flapjack.Compiler.Backend.WordToStack.Proofs.NativeInsertWf
import Flapjack.Compiler.Backend.WordToStack.Proofs.ConstMemoryAppend
import Flapjack.Compiler.Backend.WordToStack.Proofs.NativeAccessors
import Flapjack.Compiler.Backend.WordToStack.Proofs.CallLocalRecovery
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackSuffix
import Flapjack.Compiler.Backend.WordToStack.Proofs.IndexReconstruction
import Flapjack.Compiler.Backend.WordToStack.Proofs.SourceFrameSize
import Flapjack.Compiler.Backend.WordToStack.Proofs.SortedAList
import Flapjack.Compiler.Backend.WordToStack.Proofs.FrameOffsets
import Flapjack.Compiler.Backend.WordToStack.Proofs.DecodedFrameShape
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackAbstractionLength
import Flapjack.Compiler.Backend.WordToStack.Proofs.MapBitmap
import Flapjack.Compiler.Backend.WordToStack.Proofs.FilterBitmap
import Flapjack.Compiler.Backend.WordToStack.Proofs.ListUpdate
import Flapjack.Compiler.Backend.WordToStack.Proofs.WordListLength
import Flapjack.Compiler.Backend.WordToStack.Proofs.LiveListSupport
import Flapjack.Compiler.Backend.WordToStack.Proofs.SortedRelations
import Flapjack.Compiler.Backend.WordToStack.Proofs.SortedKeys
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapWrite
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapInsert
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapDecode
import Flapjack.Compiler.Backend.WordToStack.Proofs.KeyValueOrder
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapSentinelLength
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapBitStructure
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapWordLemmas
import Flapjack.Compiler.Backend.StackProps.RegisterBounds
import Flapjack.Compiler.Backend.WordCse.Proofs.ListOrder
import Flapjack.Compiler.Backend.WordCse.Proofs.DeletionFrames
import Flapjack.Compiler.Backend.WordCse.Proofs.EvaluationFrames
import Flapjack.Compiler.Backend.WordCse.Proofs.LoadEvaluation
import Flapjack.Compiler.Backend.WordCse.Proofs.ArithmeticKeys
import Flapjack.Compiler.Backend.WordCse.Proofs.InsertEquality
import Flapjack.Compiler.Backend.WordCse.Proofs.KeyInjectivity
import Flapjack.Compiler.Backend.WordCse.InstructionKeys
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoInstallTop
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoInstallCode
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
import Flapjack.Compiler.Backend.StackProps.StateConstants
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoveLookups
import Flapjack.Pancake.LoopToWord.Proofs.LabelHandlers
import Flapjack.Pancake.WordConvs.PredicateEquations
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsPhysicalStateUpdates
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoves.CorrectLeft
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapStep
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsInsert
import Flapjack.Pancake.WordConvs.PredicateEquations
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

import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASetup.ListNextVarRenameArithmetic
import Flapjack.Compiler.Encoders.AsmProps.Assertions.Iteration
import Flapjack.Compiler.Encoders.AsmSem.Arithmetic
import Flapjack.Compiler.Backend.WordAlloc.Proofs.Maximum.MaxVar
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARegisterClass
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocals
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMap
import Flapjack.Compiler.Backend.WordAlloc.SSASetup
import Flapjack.Compiler.Encoders.AsmProps.Assertions
import Flapjack.Compiler.Backend.StackProps.LabelSafety
import Flapjack.Compiler.Backend.Parmove.FstepMapInj
import Flapjack.Compiler.Encoders.AsmProps.FpPreservation
import Flapjack.Compiler.Encoders.AsmSem.FpUpdates
import Flapjack.Pancake.WordConvs.ProgramMonotonicity
import Flapjack.Compiler.Backend.Parmove.StepMapInj
import Flapjack.Compiler.Backend.Parmove.TempBeforeAssign.Parmove
import Flapjack.Pancake.WordConvs.NameMonotonicity
import Flapjack.Compiler.Encoders.AsmProps.PcCoverage
import Flapjack.Pancake.WordConvs.EveryVarInstMono
import Flapjack.Compiler.Backend.Parmove.PreservesMoves.Parmove
import Flapjack.Compiler.Backend.Parmove.AllDistinct.Parmove
import Flapjack.Compiler.Backend.Parmove.AllDistinct.Pmov
import Flapjack.Compiler.Backend.Parmove.TempBeforeAssign.Pmov
import Flapjack.Compiler.Backend.Parmove.InjOnState
import Flapjack.Compiler.Backend.LabToTarget.AsmUpdates
import Flapjack.Compiler.Backend.BackendProps

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
import Flapjack.Compiler.Backend.WordAlloc.Colour
import Flapjack.Compiler.Backend.WordAlloc.Proofs.KeyMaps
import Flapjack.Compiler.Backend.WordAlloc.Proofs.Maximum.Max3
import Flapjack.Compiler.Backend.WordAlloc.Proofs.Expressions
import Flapjack.Compiler.Backend.WordAlloc.Proofs.LiveExpressions
import Flapjack.Compiler.Backend.WordAlloc.Proofs.Updates
import Flapjack.Compiler.Backend.WordAlloc.Proofs.StateRelation
import Flapjack.Compiler.Backend.WordAlloc.Expressions
import Flapjack.Compiler.Backend.WordAlloc.ProgramLiveness
import Flapjack.Compiler.Backend.WordAlloc.InstructionWrites
import Flapjack.Compiler.Backend.WordAlloc.ReadsExp
import Flapjack.Compiler.Backend.WordAlloc.ProgramWrites
import Flapjack.Compiler.Backend.WordAlloc.ClashTreeInst
import Flapjack.Compiler.Backend.WordAlloc.ClashTreeProg
import Flapjack.Compiler.Backend.WordAlloc.Proofs.StrongLocalsRel
import Flapjack.Compiler.Backend.WordAlloc.Proofs.NumSets
import Flapjack.Compiler.Backend.WordAlloc.Proofs.NumSetDeletion
import Flapjack.Compiler.Backend.RegAlloc.Proofs
import Flapjack.Compiler.Backend.RegAlloc.SpDefault
import Flapjack.Compiler.Backend.RegAlloc.Proofs.Invariants
import Flapjack.Compiler.Backend.RegAlloc.Proofs.MkBij
import Flapjack.Compiler.Backend.RegAlloc.Accessors
import Flapjack.Compiler.Backend.RegAlloc.Proofs.AccessorEqns
import Flapjack.Compiler.Backend.RegAlloc.Colouring
import Flapjack.Compiler.Backend.RegAlloc.ExceptionFunctions
import Flapjack.Compiler.Backend.RegAlloc.StempColouring
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.Motive
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.Leaves
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.Inst
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.Control
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.CutSets
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.CallHandler
import Flapjack.Compiler.Backend.WordAlloc.Proofs.CheckCol
import Flapjack.Compiler.Backend.WordAlloc.Proofs.NumSetInsertion
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ScopedInjection
import Flapjack.Compiler.Backend.BackendCommon
import Flapjack.Compiler.Backend.Semantics.WordSem
import Flapjack.Compiler.Backend.Semantics.WordSem.State
import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
import Flapjack.Compiler.Backend.Semantics.WordSem.Env
import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport
import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers
import Flapjack.Compiler.Backend.Semantics.WordSem.Alloc
import Flapjack.Compiler.Backend.Semantics.WordSem.ShMem
import Flapjack.Compiler.Backend.Semantics.WordSem.Inst
import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate
import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateClock
import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd
import Flapjack.Compiler.Backend.Semantics.StackSem.State
import Flapjack.Compiler.Backend.Semantics.StackSem.SizeBitmapCases
import Flapjack.Compiler.Backend.Semantics.TargetSem.State
import Flapjack.Compiler.Encoders.AsmProps.Target
import Flapjack.Compiler.Encoders.AsmSem.State
import Flapjack.Compiler.Backend.Semantics.TargetSem.Machine
import Flapjack.Misc.AsmWriteBytearray
import Flapjack.Misc.BytesInMemory
import Flapjack.Compiler.Backend.Semantics.TargetSem.PostAsm
import Flapjack.Compiler.Backend.Semantics.TargetSem.FfiReads
import Flapjack.Compiler.Backend.Semantics.TargetSem.EncodedBytes
import Flapjack.Compiler.Backend.Semantics.StackSem.Control
import Flapjack.Compiler.Backend.Semantics.StackSem.Labels
import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Compiler.Backend.Semantics.StackSem.ShMem
import Flapjack.Compiler.Backend.Semantics.StackSem.Expressions
import Flapjack.Compiler.Backend.Semantics.StackSem.StoreConsts
import Flapjack.Compiler.Backend.Semantics.StackSem.StoreConstsGuard
import Flapjack.Compiler.Backend.Semantics.StackSem.Allocation
import Flapjack.Compiler.Backend.Semantics.StackSem.Bitmap
import Flapjack.Compiler.Backend.Semantics.StackSem.WordBitmap
import Flapjack.Compiler.Backend.Semantics.StackSem.StackCodec
import Flapjack.Compiler.Backend.Semantics.StackSem.FpRegisterInstructions
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateIoEventsMono
import Flapjack.Compiler.Backend.Semantics.WordSem.Semantics
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateAddClock
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateAddClockIoEventsMono
import Flapjack.Misc.ShiftSeq
import Flapjack.FpSemHOL
import Flapjack.Basis.Pure.MlList
import Flapjack.Compiler.Backend.RegAlloc
import Flapjack.Compiler.Backend.RegAlloc.ClashTree
import Flapjack.Compiler.Backend.LinearScan
import Flapjack.Compiler.Backend.LinearScan.HiddenState
import Flapjack.Compiler.Backend.LinearScan.Steps
import Flapjack.Compiler.Backend.LinearScan.Sorting
import Flapjack.Compiler.Backend.LinearScan.TopLevel
import Flapjack.Misc.Sptree.Foldi
import Flapjack.Misc.MiscThe
import Flapjack.Misc.ListEl
import Flapjack.Compiler.Backend.RegAlloc.Proofs.SpInverts
import Flapjack.Compiler.Backend.LinearScan.Proofs
import Flapjack.Misc.Sptree.ToAList
import Flapjack.Translator.Monadic.MonadBase.Arrays
import Flapjack.AstHOL
import Flapjack.Compiler.Backend.StackLang
import Flapjack.Compiler.Backend.StackLang.Prog
import Flapjack.Basis.Pure.MlString
import Flapjack.Compiler.Backend.WordToStack
import Flapjack.Compiler.Backend.WordToStack.LiveBitmap
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackSize
import Flapjack.Compiler.Backend.WordToStack.Proofs.Frames
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackAbstraction
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackAbstractionPrefix
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackAbstractionLengths
import Flapjack.Compiler.Backend.WordToStack.Proofs.IndexList
import Flapjack.Compiler.Backend.WordToStack.Proofs.IndexListLemmas
import Flapjack.Compiler.Backend.WordToStack.Proofs.MapFst
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapAppend
import Flapjack.Compiler.Backend.WordToStackRegFormat
import Flapjack.Compiler.Backend.Parmove
import Flapjack.Compiler.Backend.Parmove.Semantics
import Flapjack.Compiler.Backend.Parmove.Invariants
import Flapjack.Compiler.Backend.Parmove.Invariants.Path
import Flapjack.Compiler.Backend.Parmove.Invariants.Preservation
import Flapjack.Compiler.Backend.Parmove.StepSem.StartExtend
import Flapjack.Compiler.Backend.Parmove.StepSem.RemoveSelfEmitLast
import Flapjack.Compiler.Backend.Parmove.StepSem.Save
import Flapjack.Compiler.Backend.Parmove.EnvironmentChange
import Flapjack.Compiler.Backend.Parmove.UpdateLemmas
import Flapjack.Compiler.Backend.Parmove.Permutation
import Flapjack.Compiler.Backend.Parmove.Steps
import Flapjack.Compiler.Backend.Parmove.NoRead
import Flapjack.Compiler.Backend.LabSem
import Flapjack.Compiler.Backend.LabProps
import Flapjack.Compiler.Backend.StackNames
import Flapjack.Compiler.Backend.StackNames.NamesOk
import Flapjack.Compiler.Backend.StackNames.Labels
import Flapjack.Compiler.Backend.StackRemove
import Flapjack.Compiler.Encoders.Asm
import Flapjack.Misc.AppList
import Flapjack.Misc.Sptree
import Flapjack.Misc.FlatReplicate
import Flapjack.Misc.FoldrMaxList
import Flapjack.Misc.Uncurry
import Flapjack.Misc.OptMmapCong
import Flapjack.Misc.BinaryIeeeSqrt.RoundAgreement
import Flapjack.Pancake.CrepInline.Pass
import Flapjack.Pancake.CrepInline.Canonical
import Flapjack.Pancake.CrepLang
import Flapjack.Pancake.CrepLang.Exp
import Flapjack.Pancake.CrepLang.Prog
import Flapjack.Pancake.CrepToLoop
import Flapjack.Pancake.CrepToLoop.ContextExact
import Flapjack.Pancake.CrepToLoop.Optimise
import Flapjack.Pancake.CrepToLoop.Proofs.AssignedVars
import Flapjack.Pancake.CrepToLoop.Proofs.SurvivesMapiAssign
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpTmpBound
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpLeTmpDomain
import Flapjack.Pancake.CrepToLoop.Proofs.LoopEvaluateHelpers
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpSyntaxHelpers
import Flapjack.Pancake.CrepToLoop.Proofs.Primop
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpSurvives
import Flapjack.Pancake.CrepToLoop.Proofs.LocalListHelpers
import Flapjack.Pancake.CrepToLoop.Proofs.CrepEvalHelpers
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpOutRel
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpPreservesEval
import Flapjack.Pancake.CrepToLoop.Proofs.NcompileCorrect
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.While
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Call
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.ShMem
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Assembly
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Dec
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Primitive
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Store
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Store32
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.StoreByte
import Flapjack.Pancake.CrepToLoop.Proofs.RelationsExact
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Leaf
import Flapjack.Pancake.CrepToLoop.Proofs.LocalsRelHelpers
import Flapjack.Pancake.CrepToLoop.Proofs.LocalsRelOptMmap
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpPreservesEval.Leaf
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpPreservesEval.Load
import Flapjack.Pancake.CrepToLoop.Proofs.SemanticsWrapper
import Flapjack.Pancake.LoopLive.Fixedpoint
import Flapjack.Pancake.Proofs.LoopLive.CompileCorrect
import Flapjack.Pancake.Proofs.LoopLive.Optimise
import Flapjack.Pancake.LoopCall.IsLoad
import Flapjack.Pancake.Proofs.LoopCall.CompileCorrect
import Flapjack.Pancake.CrepToLoop.Proofs.MakeFuncsLemmas
import Flapjack.Pancake.CrepToLoop.Proofs.CodeRel2
import Flapjack.Pancake.CrepToLoop.Proofs.CodeRelEvaluateCallCorrect
import Flapjack.Pancake.CrepToLoop.Proofs.StateRelImpSemantics
import Flapjack.Pancake.CrepToLoop.Proofs.WriteBytearrayMemRel
import Flapjack.Pancake.CrepToLoop.Proofs.NotMemContextAssigned
import Flapjack.Pancake.CrepToLoop.Proofs.CallPreserveStateCodeLocalsRel
import Flapjack.Pancake.CrepToLoop.StateRel
import Flapjack.Pancake.LoopToWord
import Flapjack.Pancake.LoopToWord.Proofs.RelationsExact
import Flapjack.Pancake.LoopToWord.Proofs.FindVarExact
import Flapjack.Pancake.LoopToWord.MakeCtxtExact
import Flapjack.Pancake.LoopToWord.CompFuncExact
import Flapjack.Pancake.Proofs.LoopToWord.LocalsRel
import Flapjack.Pancake.Proofs.LoopToWord.LocalsRelUpdates
import Flapjack.Pancake.Proofs.LoopToWord.ContextSupport
import Flapjack.Pancake.Proofs.LoopToWord.LocalsRelLookups
import Flapjack.Pancake.Proofs.LoopToWord.LocalsRelAllDistinct
import Flapjack.Pancake.Proofs.LoopToWord.FindVar
import Flapjack.Pancake.Proofs.LoopToWord.LocalsRelIntro
import Flapjack.Pancake.Proofs.LoopToWord.CutsetDomain
import Flapjack.Pancake.Proofs.LoopToWord.LastNAddCons
import Flapjack.Pancake.Proofs.LoopToWord.WordShiftModDimword
import Flapjack.Pancake.Proofs.LoopToWord.CompExpPreservesEval
import Flapjack.Pancake.Proofs.LoopToWord.CutEnvSupport
import Flapjack.Pancake.Proofs.LoopToWord.WordToBytes
import Flapjack.Pancake.Proofs.LoopToWord.AccVarsAcc
import Flapjack.Pancake.Proofs.LoopToWord.TickUnfold
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Base
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.ReturnRaise
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Assign
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Arith
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Seq
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.If
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Memory
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.ShMem
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.FFI
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Loop
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Call.Support
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Call.TailCall
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Call.NoHandler
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Call.HandlerTail
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Call.SomeHandler
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Call
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Assembly
import Flapjack.Pancake.LoopToWord.Proofs.StateRelImpSemantics
import Flapjack.Pancake.LoopLang.AssignedVars
import Flapjack.Pancake.Semantics.LoopProps.AssignedVars
import Flapjack.Pancake.Semantics.LoopProps.CutSets
import Flapjack.Pancake.Semantics.LoopProps.CompSyntaxOk
import Flapjack.Pancake.PanCommon
import Flapjack.Pancake.PanGlobals
import Flapjack.Pancake.PanGlobals.CompileExpExact
import Flapjack.Pancake.PanGlobals.CompileTopExact
import Flapjack.Pancake.PanLang
import Flapjack.Pancake.PanLang.Shape
import Flapjack.Pancake.PanLang.Exp
import Flapjack.Pancake.PanLang.Prog
import Flapjack.Pancake.PanLang.Decl
import Flapjack.Pancake.PanSimp
import Flapjack.Pancake.Proofs.PanSimp.StateRel
import Flapjack.Pancake.Proofs.PanSimp.CompileEvalCorrect
import Flapjack.Pancake.Proofs.PanSimp.RetToTailCorrect
import Flapjack.Pancake.PanToCrep
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.PanToCrep.CompileExact
import Flapjack.Pancake.PanToCrep.CompileProg
import Flapjack.Pancake.PanToCrep.ExpHdlExact
import Flapjack.Pancake.PanToCrep.MakeVmapHOL
import Flapjack.Pancake.PanToCrep.ContextExact
import Flapjack.Pancake.Proofs.CrepArith
import Flapjack.Pancake.Proofs.CrepArith.HOLStateMapc
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect.Assign
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect.Call
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect.Dec
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect.If
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect.Return
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect.While
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect.Assembly
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect.Store
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrectShMem
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect.Seq
import Flapjack.Pancake.Proofs.CrepArith.MulConst
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrectPrimitiveRaise
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrectStoreGlob
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrectStore32
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrectStoreByte
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrectExtCall
import Flapjack.Pancake.Proofs.CrepInline
import Flapjack.Pancake.Proofs.CrepInline.EvaluateLocals.ExtCall
import Flapjack.Pancake.Proofs.CrepInline.EvaluateLocals.Primitive
import Flapjack.Pancake.Proofs.CrepInline.EvaluateLocals.ShMem
import Flapjack.Pancake.Proofs.CrepInline.EvaluateLocals.Structural
import Flapjack.Pancake.Proofs.CrepInline.EvaluateLocals.While
import Flapjack.Pancake.Proofs.CrepInline.EvaluateLocals.Assembly
import Flapjack.Pancake.Proofs.CrepInline.EvaluateLocals.Call
import Flapjack.Pancake.Proofs.CrepInline.EvaluateStateLocals.Atoms
import Flapjack.Pancake.Proofs.CrepInline.EvaluateStateLocals.Structural
import Flapjack.Pancake.Proofs.CrepInline.EvaluateStateLocals.MoreAtoms
import Flapjack.Pancake.Proofs.CrepInline.EvaluateStateLocals.While
import Flapjack.Pancake.Proofs.CrepInline.EvaluateStateLocals.Call
import Flapjack.Pancake.Proofs.CrepInline.EvaluateStateLocals.Assembly
import Flapjack.Pancake.Proofs.CrepInline.ArgLoad
import Flapjack.Pancake.Proofs.CrepInline.CallCase
import Flapjack.Pancake.Proofs.CrepInline.InlineProgCorrect
import Flapjack.Pancake.Proofs.CrepInline.StateRelImpSemantics
import Flapjack.Pancake.Proofs.CrepInline.FiniteMapLemmas
import Flapjack.Pancake.Proofs.CrepInline.NestedDecsSublocals
import Flapjack.Pancake.Proofs.CrepInline.NotVarProg
import Flapjack.Pancake.Proofs.CrepInline.ArgLoadStrong
import Flapjack.Pancake.Proofs.CrepInline.Expressions
import Flapjack.Pancake.Proofs.CrepInline.ExpressionRelations
import Flapjack.Pancake.Proofs.CrepInline.UpdateListLocals
import Flapjack.Pancake.Proofs.CrepInline.UnreachElim
import Flapjack.Pancake.Proofs.CrepInline.UnreachElimPredicates
import Flapjack.Pancake.Proofs.CrepInline.NoReturn
import Flapjack.Pancake.Proofs.CrepInline.ClockExpressions
import Flapjack.Pancake.Proofs.CrepInline.ExpressionCodeAgreement
import Flapjack.Pancake.Proofs.CrepInline.NotBranchReturn
import Flapjack.Pancake.Proofs.CrepInline.UnreachElimEvaluate
import Flapjack.Pancake.Proofs.CrepInline.NestedSeqAssign
import Flapjack.Pancake.Proofs.CrepInline.TransformEoc.Cases
import Flapjack.Pancake.Proofs.CrepInline.TransformEoc.While
import Flapjack.Pancake.Proofs.CrepInline.TransformEoc.Call
import Flapjack.Pancake.Proofs.CrepInline.TransformEoc.Assembly
import Flapjack.Pancake.Proofs.CrepInline.TransformBranch.Assembly
import Flapjack.Pancake.Proofs.CrepInline.WrappedTransformIf
import Flapjack.Pancake.Proofs.CrepInline.TransformBranch.Loops
import Flapjack.Pancake.Proofs.CrepInline.TransformBranch.Cases
import Flapjack.Pancake.Proofs.CrepInline.UnreachElimProgSize
import Flapjack.Pancake.Proofs.CrepInline.NestedDecs
import Flapjack.Pancake.Proofs.CrepInline.ShMem
import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Proofs.PanGlobals.MemStoresAppend
import Flapjack.Pancake.Proofs.PanGlobals.FpermCode
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Leaves
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.ReturnRaise
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Assign
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Primitive
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Store
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.FixedStores
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.ShMemLoad
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Assembly
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.ClockAnnot
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Seq
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.DecCall
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.ShMemStore
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.If
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Dec
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.While
import Flapjack.Pancake.Proofs.PanGlobals.DeclListLemmas
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationExact
import Flapjack.Pancake.Proofs.PanGlobals.CompileDecsStructural
import Flapjack.Pancake.Proofs.PanGlobals.CompileTopShapeWf
import Flapjack.Pancake.Proofs.PanGlobals.CompileTopSemanticsExact
import Flapjack.Pancake.Proofs.PanGlobals.CompileTopSemanticsDecls
import Flapjack.Pancake.Proofs.PanGlobals.SemanticsInitCall
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsMemory
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsAlignment
import Flapjack.Pancake.Proofs.PanStructs
import Flapjack.Pancake.Proofs.PanStructs.CompileCorrect
import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.Proofs.PanToCrep.CodeRelExact
import Flapjack.Pancake.Proofs.PanToCrep.CompileExpVmax
import Flapjack.Pancake.Proofs.PanToCrep.CompileProgParams
import Flapjack.Pancake.Proofs.PanToCrep.CompileExpValRel
import Flapjack.Pancake.Proofs.PanToWord
import Flapjack.Pancake.Proofs.PanToCrep.Primop
import Flapjack.Pancake.Proofs.PanToCrep.StateRelFiniteSupport
import Flapjack.Pancake.Proofs.PanToCrep.StateRelImpSemantics
import Flapjack.Pancake.Proofs.PanToCrep.StateRelImpSemanticsTop
import Flapjack.Pancake.Proofs.PanToCrep.TotalEvaluateCases
import Flapjack.Pancake.Proofs.PanToCrep.EvaluateNestedAssign
import Flapjack.Pancake.Proofs.PanToCrep.EvaluateNestedDecs
import Flapjack.Pancake.Proofs.PanToCrep.EvalDistinctLists
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Call
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.DecCall
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Skip
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Break
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Continue
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Seq
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.If
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Dec
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Tick
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Annot
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Return
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.While
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Assembly
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.StoreByte
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Store32
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Raise
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Assign
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Primitive
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Store
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.ShMemStore
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.ShMemLoad
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.ExtCall
import Flapjack.Pancake.Proofs.PanToCrep.NotMemContextAssignedMemGt
import Flapjack.Pancake.Semantics.CrepProps
import Flapjack.Pancake.Semantics.CrepProps.MemLoadFlatRel
import Flapjack.Pancake.Semantics.CrepProps.EvaluateAddClock
import Flapjack.Pancake.Semantics.CrepProps.EvalSomeVarCexp
import Flapjack.Pancake.Semantics.CrepProps.EvaluateAddClockIoEventsMono
import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.Semantics.CrepSem.CrepObservationalSemantics
import Flapjack.Pancake.Semantics.CrepSem.EvaluateInd
import Flapjack.Pancake.Semantics.CrepSem.LookupCode
import Flapjack.Pancake.Semantics.CrepSem.StateExact
import Flapjack.Pancake.Semantics.CrepSem.Primop
import Flapjack.Pancake.LoopLang
import Flapjack.Pancake.LoopLive
import Flapjack.Pancake.Semantics.LoopProps
import Flapjack.Pancake.Semantics.LoopSem
import Flapjack.Pancake.Semantics.LoopSemStateExact
import Flapjack.Pancake.Semantics.LoopSemStateExact.ShMem
import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate
import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateInd
import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateCases.StateRebinding
import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateCases.Continue
import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateCases.Ffi
import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateCases.CutState
import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateCases.FfiHook
import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateCases.SetGlobal
import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateCases.Store
import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateCases.Loads
import Flapjack.Pancake.Semantics.LoopSemStateExact.Semantics
import Flapjack.Pancake.Semantics.LoopProps.EvaluateClockExact
import Flapjack.Pancake.Semantics.LoopProps.EvaluateIoEventsExact
import Flapjack.Pancake.Semantics.LoopProps.EvalExact
import Flapjack.Pancake.Semantics.LoopProps.EveryProg
import Flapjack.Pancake.Semantics.LoopProps.NestedSeqExact
import Flapjack.Pancake.Semantics.LoopProps.UnassignedVarsExact
import Flapjack.Pancake.Semantics.LoopProps.NestedSeqSyntaxExact
import Flapjack.Pancake.Semantics.LoopProps.CompSyntaxOkLemmas
import Flapjack.Pancake.Semantics.LoopProps.CompSyntaxOkEvalExact
import Flapjack.Pancake.Semantics.LoopProps.AccVars
import Flapjack.Pancake.Semantics.PanCommonProps
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Semantics.PanProps.EvalInvariant
import Flapjack.Pancake.Semantics.PanProps.ListRelFlatten
import Flapjack.Pancake.Semantics.PanProps.ResVar
import Flapjack.Pancake.Semantics.PanProps.EvaluateResultInvariant
import Flapjack.Pancake.Semantics.PanProps.MemByteArray
import Flapjack.Pancake.Semantics.PanProps.LocalisedExpSimps
import Flapjack.Pancake.Semantics.PanProps.NamelessExpSimps
import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Pancake.Semantics.PanSem.LookupCode
import Flapjack.Pancake.Semantics.PanSem.Primop
import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Pancake.Semantics.PanSem.MemLoad32Alt
import Flapjack.Pancake.Semantics.PanSem.MemStore32Alt
import Flapjack.Pancake.Semantics.PanSem.ByteRoundtrip
import Flapjack.Misc.GoodDimindex
import Flapjack.Misc.Fp64NanRefinement
import Flapjack.Pancake.Semantics.PanSem.TotalSteps
import Flapjack.Pancake.Semantics.PanSem.ValueHOL
import Flapjack.Pancake.Semantics.PanSem.StateExact
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
import Flapjack.Pancake.Semantics.PanSem.Semantics
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
import Flapjack.Pancake.Semantics.PanSem.ClockTimeout
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockIoEventsMono
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq
import Flapjack.Pancake.Semantics.PanProps.EvaluateClockSubAtoms
import Flapjack.Pancake.Semantics.PanProps.EvaluateClockSubCall
import Flapjack.Pancake.Semantics.PanProps.EvaluateClockSubDecCall
import Flapjack.Pancake.Semantics.PanProps.EvaluateClockSubAssembly
import Flapjack.Pancake.Semantics.PanProps.EvaluateClockSub1
import Flapjack.Pancake.Semantics.PanProps.EvaluateMinClock
import Flapjack.Pancake.Semantics.PanSem.ShMemLoadCase
import Flapjack.Pancake.Semantics.PanSem.ExtCallCase
import Flapjack.Pancake.Semantics.PanSem.LocalUpdatesExact
import Flapjack.Pancake.Semantics.PanSem.IsValidValueExact
import Flapjack.Pancake.Semantics.PanSem.DecExact
import Flapjack.Pancake.Semantics.PanSem.ReturnRaiseExact
import Flapjack.Pancake.Semantics.PanSem.EvalExact
import Flapjack.Pancake.Semantics.PanSem.DecCallExact
import Flapjack.Pancake.Semantics.PanSem.DeclContextExact
import Flapjack.Pancake.Semantics.PanSem.EvaluateDeclsExact
import Flapjack.Pancake.Semantics.PanSem.ClockExact
import Flapjack.Pancake.Semantics.PanSem.StateSimpExact
import Flapjack.Pancake.Semantics.PanSem.StateDefsExact
import Flapjack.Pancake.Semantics.PanSem.EvaluateInd
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
