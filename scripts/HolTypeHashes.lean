import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Primitive
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Results
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Assign
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Memory
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.ResVar
import Flapjack.Pancake.Proofs.PanGlobals.ReadBytearray
import Flapjack.Pancake.Proofs.PanGlobals.ByteStore
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Leaves
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.If
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Seq
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.ShMemLoad
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.CallNoHandler
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
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationLocals
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsShape
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsDisjoint
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
import Flapjack.Compiler.Backend.WordAlloc.Proofs.CutNames
import Flapjack.Compiler.Backend.WordAlloc.Proofs.KeyRemap
import Flapjack.Pancake.PanStructs.CompileDeclsExact
import Flapjack.Pancake.PanStructs.CompileProgExact
import Flapjack.Pancake.PanStructs.CompileExpExact
import Flapjack.Pancake.PanStructs.OldExpShapeExact
import Flapjack.Compiler.Backend.WordAlloc.Instructions
import Flapjack.Compiler.Backend.WordAlloc.Proofs.KeyMaps
import Flapjack.Compiler.Backend.WordAlloc.Proofs.Expressions
import Flapjack.Compiler.Backend.WordAlloc.Proofs.LiveExpressions
import Flapjack.Compiler.Backend.WordAlloc.Proofs.Updates
import Flapjack.Compiler.Backend.WordAlloc.Proofs.StateRelation
import Flapjack.Compiler.Backend.WordAlloc.Expressions
import Flapjack.Compiler.Backend.WordAlloc.Proofs.StrongLocalsRel
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
import Flapjack.Compiler.Backend.Semantics.StackSem.Control
import Flapjack.Compiler.Backend.Semantics.StackSem.Labels
import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Compiler.Backend.Semantics.StackSem.Expressions
import Flapjack.Compiler.Backend.Semantics.StackSem.StoreConsts
import Flapjack.Compiler.Backend.Semantics.StackSem.StoreConstsGuard
import Flapjack.Compiler.Backend.Semantics.StackSem.Allocation
import Flapjack.Compiler.Backend.Semantics.StackSem.Bitmap
import Flapjack.Compiler.Backend.Semantics.StackSem.WordBitmap
import Flapjack.Compiler.Backend.Semantics.StackSem.StackCodec
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateIoEventsMono
import Flapjack.Compiler.Backend.Semantics.WordSem.Semantics
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateAddClock
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateAddClockIoEventsMono
import Flapjack.Misc.ShiftSeq
import Flapjack.FpSemHOL
import Flapjack.Basis.Pure.MlList
import Flapjack.Compiler.Backend.RegAlloc
import Flapjack.AstHOL
import Flapjack.Compiler.Backend.StackLang
import Flapjack.Compiler.Backend.StackLang.Prog
import Flapjack.Basis.Pure.MlString
import Flapjack.Compiler.Backend.WordToStack
import Flapjack.Compiler.Backend.WordToStackRegFormat
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
import Flapjack.Pancake.Proofs.CrepInline.EvaluateLocals.Call
import Flapjack.Pancake.Proofs.CrepInline.EvaluateStateLocals.Atoms
import Flapjack.Pancake.Proofs.CrepInline.Expressions
import Flapjack.Pancake.Proofs.CrepInline.UpdateListLocals
import Flapjack.Pancake.Proofs.CrepInline.UnreachElim
import Flapjack.Pancake.Proofs.CrepInline.UnreachElimPredicates
import Flapjack.Pancake.Proofs.CrepInline.NoReturn
import Flapjack.Pancake.Proofs.CrepInline.ClockExpressions
import Flapjack.Pancake.Proofs.CrepInline.ExpressionCodeAgreement
import Flapjack.Pancake.Proofs.CrepInline.NotBranchReturn
import Flapjack.Pancake.Proofs.CrepInline.UnreachElimEvaluate
import Flapjack.Pancake.Proofs.CrepInline.UnreachElimProgSize
import Flapjack.Pancake.Proofs.CrepInline.NestedDecs
import Flapjack.Pancake.Proofs.CrepInline.ShMem
import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Proofs.PanGlobals.MemStoresAppend
import Flapjack.Pancake.Proofs.PanGlobals.FpermCode
import Flapjack.Pancake.Proofs.PanGlobals.DeclListLemmas
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationExact
import Flapjack.Pancake.Proofs.PanGlobals.CompileDecsStructural
import Flapjack.Pancake.Proofs.PanGlobals.CompileTopShapeWf
import Flapjack.Pancake.Proofs.PanGlobals.CompileTopSemanticsExact
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
import Flapjack.Pancake.WordConvs
import Flapjack.Pancake.WordConvs.NotCreated
import Flapjack.RiscV.CorrectnessEncoding
import Flapjack.Compiler.Backend.StackProps
import Flapjack.Pancake.PanStructs

open Lean Elab Command Flapjack

/-! Export kernel-visible declaration types and definition bodies, not
source-text approximations. Binder names and metadata do not affect the
proposition and are removed before serializing the elaborated expression. The
pinned Lean toolchain determines the format of the structural `repr` consumed
by `check_hol_type_hashes.py`.

Theorem proof terms are deliberately excluded: they may be refactored without
changing the reviewed statement. Definition and `opaque` bodies are included
because a tagged definition body can drift without changing its elaborated
type. -/
private partial def canonicalExpr : Expr → Expr
  | .forallE _ type body info =>
      .forallE `_ (canonicalExpr type) (canonicalExpr body) info
  | .lam _ type body info =>
      .lam `_ (canonicalExpr type) (canonicalExpr body) info
  | .letE _ type value body nondep =>
      .letE `_ (canonicalExpr type) (canonicalExpr value) (canonicalExpr body) nondep
  | .app fn arg => .app (canonicalExpr fn) (canonicalExpr arg)
  | .proj name index body => .proj name index (canonicalExpr body)
  | .mdata _ body => canonicalExpr body
  | expr => expr

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

elab "#emit_hol_type_hashes" : command => do
  let env ← getEnv
  let realsTagged : NameSet := (HolRef.all env).foldl
    (fun acc (entry : Name × HolRef) => if entry.2.realsAsRationalCuts then acc.insert entry.1 else acc) {}
  let mut known : Std.HashMap Name Bool := {}
  for (name, ref) in HolRef.all env do
    match env.find? name with
    | none => throwError "missing declaration {name}"
    | some info =>
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
          ("type_expr", toJson (reprStr (canonicalExpr info.type))),
          ("qualifiers", Json.mkObj qualifiers)]
        match definitionBody? info with
        | some body =>
            fields := fields ++ [("value_expr", toJson (reprStr (canonicalExpr body)))]
        | none => pure ()
        if !ref.realsAsRationalCuts then
          let (reaches, known') := reachesRealsCuts env realsTagged known name
          known := known'
          if reaches then
            fields := fields ++ [("inherits_reals_as_rational_cuts", toJson true)]
        liftIO <| IO.println (Json.mkObj fields).compress

#emit_hol_type_hashes
