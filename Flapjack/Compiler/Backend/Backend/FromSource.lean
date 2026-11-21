module

public import Flapjack.Compiler.Backend.Backend
public import Flapjack.Compiler.Backend.Backend.SourcePipeline
public import Flapjack.Compiler.Backend.DataToWord.Compile

@[expose] public section

/-! backendScript.sml 242-296: the upper backend pipeline `from_data` ...
`from_source`, each stage composing one compiler pass with the next stage,
down to the reviewed `from_word`. -/
namespace Flapjack.Compiler.Backend.BackendDefs

open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.Backend

/-- Exact HOL `backend$from_data_def` (`backendScript.sml:242-247`). -/
@[hol "cakeml/compiler/backend/backendScript.sml" "from_data_def"
  (words_as_type_indexed_bitvec)]
noncomputable def fromData {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config) (names : Spt MlString)
    (p : List (Nat × Nat × DataLang.Prog)) :
    Option (List (BitVec 8) × List (BitVec width) × Flapjack.Compiler.Backend.Backend.Config) :=
  let (col, p) := DataToWord.compile c.dataConf c.wordToWordConf asmConf p
  let c := { c with wordToWordConf := { c.wordToWordConf with colOracle := col } }
  fromWord asmConf c names p

/-- Exact HOL `backend$from_bvi_def` (`backendScript.sml:258-262`). -/
@[hol "cakeml/compiler/backend/backendScript.sml" "from_bvi_def"
  (words_as_type_indexed_bitvec)]
noncomputable def fromBvi {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config) (names : Spt MlString)
    (p : List (Nat × Nat × Bvi.Exp)) :
    Option (List (BitVec 8) × List (BitVec width) × Flapjack.Compiler.Backend.Backend.Config) :=
  let p := BviToData.compileProg p
  fromData asmConf c names p

/-- Exact HOL `backend$from_bvl_def` (`backendScript.sml:264-275`). -/
@[hol "cakeml/compiler/backend/backendScript.sml" "from_bvl_def"
  (words_as_type_indexed_bitvec)]
noncomputable def fromBvl {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config) (names : Spt MlString)
    (p : List (Nat × Nat × Bvl.Exp)) :
    Option (List (BitVec 8) × List (BitVec width) × Flapjack.Compiler.Backend.Backend.Config) :=
  let (s, p, l, bl, n1, n2, n3, names) :=
    BvlToBvi.compileSource c.closConf.start c.bvlConf names p
  let names := sptUnion (sptFromAList (DataToWord.stubNames () ++ WordToStack.stubNames () ++
    StackAlloc.stubNames () ++ StackRemove.stubNames ())) names
  let c := { c with closConf := { c.closConf with start := s } }
  let c := { c with bvlConf := { c.bvlConf with
    inlines := l, bviInlines := bl, nextName1 := n1, nextName2 := n2, nextName3 := n3 } }
  fromBvi asmConf c names p

/-- Exact HOL `backend$from_clos_def` (`backendScript.sml:277-282`). -/
@[hol "cakeml/compiler/backend/backendScript.sml" "from_clos_def"
  (words_as_type_indexed_bitvec)]
noncomputable def fromClos {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config) (e : List ClosLang.Exp) :
    Option (List (BitVec 8) × List (BitVec width) × Flapjack.Compiler.Backend.Backend.Config) :=
  let (c', p, names) := ClosToBvl.compileSource c.closConf e
  let c := { c with closConf := c' }
  fromBvl asmConf c names p

/-- Exact HOL `backend$from_flat_def` (`backendScript.sml:284-288`). -/
@[hol "cakeml/compiler/backend/backendScript.sml" "from_flat_def"
  (words_as_type_indexed_bitvec)]
noncomputable def fromFlat {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config) (p : List FlatLang.Exp) :
    Option (List (BitVec 8) × List (BitVec width) × Flapjack.Compiler.Backend.Backend.Config) :=
  let p := FlatToClos.compileProg p
  fromClos asmConf c p

/-- Exact HOL `backend$from_source_def` (`backendScript.sml:290-296`). -/
@[hol "cakeml/compiler/backend/backendScript.sml" "from_source_def"
  (words_as_type_indexed_bitvec)]
noncomputable def fromSource {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config) (p : List AstHOL.Dec) :
    Option (List (BitVec 8) × List (BitVec width) × Flapjack.Compiler.Backend.Backend.Config) :=
  let p := SourceToSource.compile p
  let (c', p) := SourceToFlat.compileTotal c.sourceConf p
  let c := { c with sourceConf := c' }
  fromFlat asmConf c p

end Flapjack.Compiler.Backend.BackendDefs
