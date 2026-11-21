module

public import Flapjack.Compiler.Backend.Backend
public import Flapjack.Compiler.Backend.SourceToSource
public import Flapjack.Compiler.Backend.SourceToFlat.CompileProg
public import Flapjack.Compiler.Backend.FlatToClos.Compile
public import Flapjack.Compiler.Backend.ClosToBvl.FullIncremental
public import Flapjack.Compiler.Backend.BvlToBvi.CompileIncAll
public import Flapjack.Compiler.Backend.BviToData.CompileSource
public import Flapjack.Compiler.Backend.DataToWord.Total
public import Flapjack.Compiler.Backend.WordToWord.Compile
public import Flapjack.Compiler.Backend.WordToStack.NativePrograms
public import Flapjack.Compiler.Backend.StackToLab.Compile
public import Flapjack.Compiler.Backend.LabToTarget.Compile
public import Flapjack.Compiler.Backend.BackendCommon.UpperW2w

@[expose] public section

/-! backendScript.sml 536-604: the per-pass program record kept by the
incremental compiler and the incremental compiler `compile_inc_progs` used to
build the evaluation oracle. -/
namespace Flapjack.Compiler.Backend.BackendDefs

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.Backend

/-- Exact HOL `backend$backend_progs` (`backendScript.sml:536-550`), at the
positive word width of HOL's `'a`. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "backend_progs"
  (words_as_type_indexed_bitvec)]
structure BackendProgs (width : Nat) [NeZero width] where
  envId : Nat × Nat
  sourceProg : List AstHOL.Dec
  flatProg : List FlatLang.Exp
  closProg : List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)
  bvlProg : List (Nat × Nat × Bvl.Exp)
  bviProg : List (Nat × Nat × Bvi.Exp)
  dataProg : List (Nat × Nat × DataLang.Prog)
  wordProg : List (Nat × Nat × WordLangProgHOL (BitVec width))
  stackProg : List (Nat × StackLang.HolProg width)
  curBm : List (BitVec width)
  labProg : LabSem.LabProgHOL width
  targetProg : Option (List (BitVec 8) × List (BitVec width))

/-- Exact HOL `backend$empty_progs_def` (`backendScript.sml:553-558`). -/
@[hol "cakeml/compiler/backend/backendScript.sml" "empty_progs_def"
  (words_as_type_indexed_bitvec)]
def emptyProgs {width : Nat} [NeZero width] : BackendProgs width :=
  { envId := (0, 0), sourceProg := [], flatProg := [], closProg := ([], []), bvlProg := [],
    bviProg := [], dataProg := [], wordProg := [], stackProg := [], curBm := [],
    labProg := [], targetProg := some ([], []) }

/-- Exact HOL `backend$keep_progs_def` (`backendScript.sml:560-562`):
`case k of T => ps | _ => []`, captured as `if k then ps else []`. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "keep_progs_def"]
def keepProgs {α : Type} (k : Bool) (ps : List α) : List α :=
  if k then ps else []

/-- Exact HOL `backend$compile_inc_progs_def` (`backendScript.sml:564-604`),
step for step with the reviewed incremental passes. HOL's
`(keep_progs k ## keep_progs k)` is `Prod.map`, `append` is the reviewed
`appListAppend`, `OPTION_MAP (λ(bytes,_). (bytes,cur_bm))` is `Option.map`,
and `lab_conf updated_by (case target of NONE => I | SOME (_,c') => K c')`
is the record update with that function applied to the old field. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "compile_inc_progs_def"
  (words_as_type_indexed_bitvec)]
noncomputable def compileIncProgs {width : Nat} [NeZero width] (k : Bool)
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config) (pTup : (Nat × Nat) × List AstHOL.Dec) :
    Flapjack.Compiler.Backend.Backend.Config × BackendProgs width :=
  let (envId, p) := pTup
  let ps : BackendProgs width := { emptyProgs with envId := envId, sourceProg := p }
  let p := SourceToSource.compile p
  let (c', p) := SourceToFlat.incCompile envId c.sourceConf p
  let ps := { ps with flatProg := keepProgs k p }
  let c := { c with sourceConf := c' }
  let p : List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp) := FlatToClos.incCompileDecs p
  let ps := { ps with closProg := Prod.map (keepProgs k) (keepProgs k) p }
  let (c', p) := ClosToBvl.closToBvlCompileInc c.closConf p
  let c := { c with closConf := c' }
  let ps := { ps with bvlProg := keepProgs k p }
  let (c', p) := BvlToBvi.bvlToBviCompileIncAll c.bvlConf p
  let c := { c with bvlConf := c' }
  let ps := { ps with bviProg := keepProgs k p }
  let p := BviToData.compileProg p
  let ps := { ps with dataProg := keepProgs k p }
  let dc := ensureFpConfOk asmConf c.dataConf
  let p : List (Nat × Nat × WordLangProgHOL (BitVec width)) := p.map (DataToWord.compilePart dc)
  let regCount1 := asmConf.regCount - (5 + asmConf.avoidRegs.length)
  let p := p.map fun p => WordToWord.fullCompileSingle asmConf.twoRegArith regCount1
    c.wordToWordConf.regAlg asmConf (p, none)
  let ps := { ps with wordProg := keepProgs k p }
  let bm0 := c.wordConf.bitmapsLength
  let (p, _fs, bm) := WordToStack.Native.compileWordToStackNative asmConf c.stackConf.perfCalls
    regCount1 p (.nil, bm0)
  let curBm := appListAppend bm.1
  let c := { c with wordConf := { c.wordConf with bitmapsLength := bm.2 } }
  let ps := { ps with stackProg := keepProgs k p, curBm := curBm }
  let regCount2 := asmConf.regCount - (3 + asmConf.avoidRegs.length)
  let p := StackToLab.compileNoStubs c.stackConf.regNames c.stackConf.jump asmConf.addrOffset
    regCount2 p
  let ps := { ps with labProg := keepProgs k p }
  let target := LabToTarget.compile asmConf c.labConf p
  let ps := { ps with targetProg := target.map fun (bytes, _) => (bytes, curBm) }
  let c := { c with labConf :=
    (match target with
      | none => id
      | some (_, c') => fun _ => c') c.labConf }
  (c, ps)

/-- Exact HOL `backend$compile_inc_progs_for_eval_def`
(`backendScript.sml:605-611`): the evaluation compiler keeps all programs,
returns the new configuration with the target bytes, and converts the bitmap
words with the reviewed `upper_w2w`. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "compile_inc_progs_for_eval_def"
  (words_as_type_indexed_bitvec)]
noncomputable def compileIncProgsForEval {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width)
    (x : (Nat × Nat) × Flapjack.Compiler.Backend.Backend.Config × List AstHOL.Dec) :
    Option (Flapjack.Compiler.Backend.Backend.Config × List (BitVec 8) × List (BitVec 64)) :=
  let (envId, c', decs) := x
  let (c'', ps) := compileIncProgs true asmConf c' (envId, decs)
  ps.targetProg.map fun (bs, ws) => (c'', bs, ws.map upperW2w)

end Flapjack.Compiler.Backend.BackendDefs
