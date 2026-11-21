module

public import Flapjack.Compiler.Backend.Backend.FromSource
public import Flapjack.Basis.Pure.MlString.EmptyFfi

@[expose] public section

/-! backendScript.sml 41-82 and 298-317: the backend compiler `compile` and
its equation with the staged pipeline `from_source`. -/
namespace Flapjack.Compiler.Backend.BackendDefs

open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.Backend

/-- Exact HOL `backend$compile_def` (`backendScript.sml:41-82`), pass for pass,
including the `empty_ffi` logging calls whose unit results are discarded.
This is the source-shaped proof definition. The executed `flapjack-compile`
CakeML path does not yet call it: its front end runs the fuel-based
`SourceToFlat.compileCakeToBviConfiguredFuel`, which agrees with this
pipeline up to BVI (`Backend.toBvi_executable`); routing the remaining stages
through this definition is open production-path work. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "compile_def"
  (words_as_type_indexed_bitvec)]
noncomputable def compile {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config) (p : List AstHOL.Dec) :
    Option (List (BitVec 8) × List (BitVec width) × Flapjack.Compiler.Backend.Backend.Config) :=
  let p := SourceToSource.compile p
  let _ := emptyFfi (ofString "finished: source_to_source")
  let (c', p) := SourceToFlat.compileTotal c.sourceConf p
  let _ := emptyFfi (ofString "finished: source_to_flat")
  let c := { c with sourceConf := c' }
  let p := FlatToClos.compileProg p
  let _ := emptyFfi (ofString "finished: flat_to_clos")
  let (c', p, names) := ClosToBvl.compileSource c.closConf p
  let c := { c with closConf := c' }
  let _ := emptyFfi (ofString "finished: clos_to_bvl")
  let (s, p, l, bl, n1, n2, n3, names) :=
    BvlToBvi.compileSource c.closConf.start c.bvlConf names p
  let c := { c with closConf := { c.closConf with start := s } }
  let c := { c with bvlConf := { c.bvlConf with
    inlines := l, bviInlines := bl, nextName1 := n1, nextName2 := n2, nextName3 := n3 } }
  let _ := emptyFfi (ofString "finished: bvl_to_bvi")
  let p := BviToData.compileProg p
  let _ := emptyFfi (ofString "finished: bvi_to_data")
  let (col, p) := DataToWord.compile c.dataConf c.wordToWordConf asmConf p
  let c := { c with wordToWordConf := { c.wordToWordConf with colOracle := col } }
  let names := sptUnion (sptFromAList (DataToWord.stubNames () ++ WordToStack.stubNames () ++
    StackAlloc.stubNames () ++ StackRemove.stubNames ())) names
  let _ := emptyFfi (ofString "finished: data_to_word")
  let (bm, c', _fs, p) := WordToStack.Native.compileNative asmConf c.stackConf.perfCalls p
  let c := { c with wordConf := c' }
  let _ := emptyFfi (ofString "finished: word_to_stack")
  let p := StackToLab.compile c.stackConf c.dataConf
    (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
    (asmConf.regCount - (asmConf.avoidRegs.length + 3)) asmConf.addrOffset p
  let _ := emptyFfi (ofString "finished: stack_to_lab")
  let res := attachBitmaps names c bm (LabToTarget.compile asmConf c.labConf p)
  let _ := emptyFfi (ofString "finished: lab_to_target")
  res

/-- Exact HOL `backend$compile_eq_from_source` (`backendScript.sml:298-317`):
the backend compiler is the staged pipeline. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "compile_eq_from_source"
  (words_as_type_indexed_bitvec)]
theorem compile_eq_fromSource {width : Nat} [NeZero width] :
    (compile : AsmConfigExact width → Flapjack.Compiler.Backend.Backend.Config → List AstHOL.Dec →
        Option (List (BitVec 8) × List (BitVec width) × Flapjack.Compiler.Backend.Backend.Config)) = fromSource := by
  funext asmConf c p
  rfl

end Flapjack.Compiler.Backend.BackendDefs
