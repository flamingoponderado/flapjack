import Flapjack.Compiler.Backend.WordToWord.ExecutableCompile
import Flapjack.Compiler.Backend.WordAlloc.WordAllocDef

/-! Allocator-parametric executable word-to-word compilation.

A `@[csimp]` replacement only rewrites code compiled in modules that import it. The compiled
`select_reg_alloc` (`WordAlloc/SelectRegAlloc.lean`) cannot import a faster allocator
proved equal to `RegAlloc.regAlloc` (that proof imports it), so its compiled code keeps
calling `regAlloc`. These literal mirrors of `selectRegAlloc`, `wordAlloc` and the
executable word-to-word composition take the graph-colouring allocator as an argument
instead; each equals its reviewed counterpart when the argument is `regAlloc`, so an
executable allocator with a kernel equality to `regAlloc` can be supplied without changing
any result, including the colouring-oracle table. Flapjack computation infrastructure; no
HOL declaration. -/

namespace Flapjack.Compiler.Backend.WordToWord
open Flapjack Flapjack.RegAlloc Flapjack.Compiler.Encoders.Asm
set_option autoImplicit false

/-- The type of `RegAlloc.regAlloc`, the graph-colouring allocator `reg_alloc`. -/
abbrev RegAllocFn : Type :=
  Algorithm → Option (Spt Nat) → Nat → List (Nat × (Nat × Nat)) → ClashTree →
    List (Nat × Nat) → NumSet → Translator.Monadic.MonadBase.Exc (Spt Nat) StateException

/-- `select_reg_alloc` with the graph-colouring allocator supplied as `ra`. -/
def selectRegAllocWith (ra : RegAllocFn) (alg : Nat) (spillcosts : Option (Spt Nat)) (k : Nat)
    (heu_moves : List (Nat × (Nat × Nat))) (tree : ClashTree) (forced : List (Nat × Nat))
    (fs : NumSet) : Translator.Monadic.MonadBase.Exc (Spt Nat) StateException :=
  if 4 ≤ alg then LinearScan.linearScanRegAlloc k heu_moves tree forced
  else ra (if alg ≤ 1 then .Simple else .IRC) spillcosts k heu_moves tree forced fs

/-- `word_alloc` with the graph-colouring allocator supplied as `ra`. -/
def wordAllocWith (ra : RegAllocFn) {width : Nat} [NeZero width] (fc : Nat)
    (c : AsmConfigExact width) (alg k : Nat) (prog : WordLangProgHOL (BitVec width))
    (col_opt : Option (Spt Nat)) : WordLangProgHOL (BitVec width) :=
  let tree := WordAlloc.getClashTree prog []
  let fs := WordAlloc.getStackOnly prog
  let forced := WordAlloc.getForced c prog []
  match WordAlloc.oracleColourOk k col_opt tree prog forced with
  | none =>
    let (heu_moves, spillcosts) := WordAlloc.getHeuristics alg fc prog
    match selectRegAllocWith ra alg spillcosts k heu_moves tree forced fs with
    | .success col => WordAlloc.applyColour (WordAlloc.totalColour col) prog
    | .failure _ => prog
  | some col_prog => col_prog

/-- `compileSingleExecutable` with the allocator supplied as `ra`. -/
def compileSingleWith (ra : RegAllocFn) {width : Nat} [NeZero width] (twoRegArith : Bool)
    (regCount alg : Nat) (c : AsmConfigExact width)
    (p : (Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat)) :
    Nat × Nat × WordLangProgHOL (BitVec width) :=
  let ((nameNum, argCount, prog), colOpt) := p
  let prog := WordSimp.compileExp prog
  let maxv := maxVarHOL prog + 1
  let instProg := WordInst.instSelectExecutable c maxv prog
  let ssaProg := WordAlloc.fullSsaCcTrans argCount instProg
  let rmSsaProg := WordAlloc.removeDeadProg ssaProg
  let cseProg := WordCse.wordCommonSubexpElim rmSsaProg
  let cpProg := WordCopy.copyProp cseProg
  let twoProg := WordInst.threeToTwoRegProg twoRegArith cpProg
  let unreachProg := WordUnreach.removeUnreach twoProg
  let rmProg := WordAlloc.removeDeadProg unreachProg
  let regProg := wordAllocWith ra nameNum c alg regCount rmProg colOpt
  (nameNum, argCount, regProg)

/-- `fullCompileSingleExecutable` with the allocator supplied as `ra`. -/
def fullCompileSingleWith (ra : RegAllocFn) {width : Nat} [NeZero width] (twoRegArith : Bool)
    (regCount alg : Nat) (c : AsmConfigExact width)
    (p : (Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat)) :
    Nat × Nat × WordLangProgHOL (BitVec width) :=
  let (nameNum, argCount, regProg) := compileSingleWith ra twoRegArith regCount alg c p
  (nameNum, argCount, WordRemove.removeMustTerminate regProg)

/-- `compileExecutable` with the allocator supplied as `ra`. -/
def compileWith (ra : RegAllocFn) {width : Nat} [NeZero width] (wordConf : Config)
    (asmConf : AsmConfigExact width) (progs : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    List (Option (Spt Nat)) × List (Nat × Nat × WordLangProgHOL (BitVec width)) :=
  let (twoRegArith, regCount) :=
    (asmConf.twoRegArith, asmConf.regCount - (5 + asmConf.avoidRegs.length))
  let (nOracles, col) := nextNOracle progs.length wordConf.colOracle
  let progs := progs.zip nOracles
  (col, progs.map (fullCompileSingleWith ra twoRegArith regCount wordConf.regAlg asmConf))

theorem selectRegAllocWith_eq (ra : RegAllocFn) (same : ra = regAlloc) :
    selectRegAllocWith ra = WordAlloc.selectRegAlloc := by
  subst same
  rfl

theorem wordAllocWith_eq (ra : RegAllocFn) (same : ra = regAlloc) {width : Nat} [NeZero width] :
    wordAllocWith ra (width := width) = WordAlloc.wordAlloc := by
  subst same
  rfl

/-- With `ra = regAlloc` the allocator-parametric composition is the whole executable
word-to-word compiler, including the colouring-oracle table, and hence `word_to_word$compile`. -/
theorem compileWith_eq (ra : RegAllocFn) (same : ra = regAlloc) {width : Nat} [NeZero width] :
    compileWith ra (width := width) = compileExecutable := by
  subst same
  rfl

theorem compileWith_eq_compile (ra : RegAllocFn) (same : ra = regAlloc) {width : Nat}
    [NeZero width] (conf : Config) (c : AsmConfigExact width)
    (ps : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    compileWith ra conf c ps = compile conf c ps := by
  rw [compileWith_eq ra same, compileExecutable_eq]

end Flapjack.Compiler.Backend.WordToWord
