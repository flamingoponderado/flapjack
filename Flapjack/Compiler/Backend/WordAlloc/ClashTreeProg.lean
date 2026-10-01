import Flapjack.Compiler.Backend.WordAlloc.ClashTreeInst
import Flapjack.Compiler.Backend.WordAlloc.ReadsExp
import Flapjack.Compiler.Backend.WordAlloc.ProgramLiveness

namespace Flapjack.WordAlloc

open Flapjack.RegAlloc
open Flapjack.Compiler.Encoders.Asm

/-- Exact HOL `get_clash_tree_def` (`word_allocScript.sml:1131-1198`), clause by
clause over the exact native program carrier `WordLangProgHOL (BitVec width)` and
the literal `ClashTree` receiver. The extra loop-context argument is HOL's
`lt : (num_set # num_set) list`.

`Skip`/`Tick`/`MustTerminate Skip` yield `Delta [] []`; `Move` splits the
register pairs into `MAP FST`/`MAP SND`; `Inst` delegates to the already-reviewed
`getDeltaInst` through the exact `HolInst.ofWordLangInst` codec (the program
stores the production `WordLangInst` mirror, which is bijective to HOL's
`'a inst`); `Assign`/`Set` read the expression through `getReadsExpHOL`; `Store`
prepends its value `num` before those reads; `Get`/`LocValue` write only.
`Seq` recurses on both children in order; `If` builds `Seq (Delta [] [r1;r2])
(Branch NONE e2t e3t)` for a `Reg` right operand and `Seq (Delta [] [r1]) (...)`
otherwise. `Alloc`, `Install`, `FFI` use `sptUnion (FST numset) (SND numset)`;
`Install` also writes `r1`. `CodeBufferWrite`/`DataBufferWrite` read `r2;r1`.
`Return` writes nothing and reads `num1 :: nums`. `OpCurrHeap` writes `dst`, reads `src`.
`StoreConsts a b c d ws` writes `a;b;c;d`, reads `c;d`. `ShareInst` treats the
four store widths like `Store` (value prepended before reads) and otherwise like
`LocValue`. `Loop` wraps `Set names`, `Set exit_names`, the body at the extended
context `(names,exit_names)::lt`, and `Set names`. `Break`/`Continue` use the
indexed lookup `lt[n]?`, falling back to `Set LN` (HOL `oEL n lt = NONE`), with
`Break` selecting the `exit_names` component and `Continue` the `names`
component. `Call` computes `args_set = numsetListInsert args .ln`, then for a
`none` return `Set args_set`; otherwise with `cutset = sptUnion cutsets.1
cutsets.2`, `live_set = sptUnion cutset args_set`, and `ret_tree = Seq (Set
(numsetListInsert vs cutset)) (getClashTree retHandler lt)`, it yields
`Seq (Set live_set) ret_tree` with no handler and `Branch (SOME live_set)
ret_tree (Seq (Set (sptInsert v' () cutset)) (getClashTree prog lt))` with one.

The sole carrier translation is HOL's type-indexed `'a word`
(`dimindex (:α)`) to Lean's positive-width `BitVec width`, with HOL's positive
dimension discharged by `[NeZero width]`. All list orders, duplicate reads,
finite-map operators, and clause guards are literal. This proof-side port does
not replace the executed `get_clash_tree` caller yet. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "get_clash_tree_def"
  (words_as_type_indexed_bitvec)]
def getClashTree {width : Nat} [NeZero width] :
    WordLangProgHOL (BitVec width) → List (NumSet × NumSet) → ClashTree
  | .skip, _ => .delta [] []
  | .move _ moves, _ => .delta (moves.map Prod.fst) (moves.map Prod.snd)
  | .inst instruction, _ => getDeltaInst (HolInst.ofWordLangInst instruction)
  | .assign name value, _ => .delta [name] (getReadsExpHOL value)
  | .get name _, _ => .delta [name] []
  | .store address value, _ => .delta [] (value :: getReadsExpHOL address)
  | .seq first second, lt => .seq (getClashTree first lt) (getClashTree second lt)
  | .ite _ condition right thenBranch elseBranch, lt =>
      let thenTree := getClashTree thenBranch lt
      let elseTree := getClashTree elseBranch lt
      match right with
      | .reg register => .seq (.delta [] [condition, register]) (.branch none thenTree elseTree)
      | .imm _ => .seq (.delta [] [condition]) (.branch none thenTree elseTree)
  | .mustTerminate body, lt => getClashTree body lt
  | .alloc destination cutsets, _ =>
      .seq (.delta [] [destination]) (.set (sptUnion cutsets.1 cutsets.2))
  | .install r1 r2 r3 r4 cutsets, _ =>
      .seq (.delta [] [r4, r3, r2, r1])
        (.seq (.set (sptUnion cutsets.1 cutsets.2)) (.delta [r1] []))
  | .codeBufferWrite r1 r2, _ => .delta [] [r2, r1]
  | .dataBufferWrite r1 r2, _ => .delta [] [r2, r1]
  | .ffi _ cptr clen ptr len cutsets, _ =>
      .seq (.delta [] [cptr, clen, ptr, len]) (.set (sptUnion cutsets.1 cutsets.2))
  | .raise num, _ => .delta [] [num]
  | .return num1 nums, _ => .delta [] (num1 :: nums)
  | .tick, _ => .delta [] []
  | .locValue r _, _ => .delta [r] []
  | .set _ value, _ => .delta [] (getReadsExpHOL value)
  | .opCurrHeap _ dst src, _ => .delta [dst] [src]
  | .storeConsts a b c d _, _ => .delta [a, b, c, d] [c, d]
  | .shareInst operator name address, _ =>
      if operator = .store ∨ operator = .store8 ∨ operator = .store16 ∨ operator = .store32
      then .delta [] (name :: getReadsExpHOL address)
      else .delta [name] (getReadsExpHOL address)
  | .loop names body exitNames, lt =>
      .seq (.set names)
        (.seq (.set exitNames)
          (.seq (getClashTree body ((names, exitNames) :: lt)) (.set names)))
  | .break index, lt => .set ((lt[index]?).map Prod.snd |>.getD .ln)
  | .continue index, lt => .set ((lt[index]?).map Prod.fst |>.getD .ln)
  | .call returns _ arguments handler, lt =>
      let argsSet := numsetListInsert arguments .ln
      match returns with
      | none => .set argsSet
      | some (vs, cutsets, retHandler, _, _) =>
          let cutset := sptUnion cutsets.1 cutsets.2
          let liveSet := sptUnion cutset argsSet
          let retTree := .seq (.set (numsetListInsert vs cutset)) (getClashTree retHandler lt)
          match handler with
          | none => .seq (.set liveSet) retTree
          | some (v', prog, _, _) =>
              .branch (some liveSet) retTree
                (.seq (.set (sptInsert v' () cutset)) (getClashTree prog lt))
termination_by program _ => sizeOf program
decreasing_by all_goals decreasing_trivial

end Flapjack.WordAlloc
