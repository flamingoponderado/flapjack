import Flapjack.HolRef
import Flapjack.Compiler.Backend.WordAlloc.ProgramLiveness
import Flapjack.Compiler.Backend.WordAlloc.Instructions

/-!
# word_alloc dead-code removal

Counterpart of `word_allocScript.sml:891-1005` `remove_dead_def` and
`remove_dead_prog_def`. The pass walks the program backwards with the live
register set `live`, the dead-store list `nlive` and the loop context `lt`,
dropping assignments to dead registers and repeated `Set`s of dead stores.
HOL's program comparisons `s = Skip` are decided by matching on `.skip`.
This proof-side port does not yet replace the executed dead-code elimination
(bead flapjack-pxn.18.5.15.2.31.5).
-/

namespace Flapjack.WordAlloc


/-- Exact HOL `remove_dead_def` (`word_allocScript.sml:891-1001`), clause by
clause in HOL order with HOL's final catchall. `Move` keeps only live
destinations; `Inst`, `Get`, `OpCurrHeap` and `LocValue` become `Skip` when
their written register is dead; `Set` of a register to a dead store is removed;
`Seq` and `If` drop `Skip` children; returning calls reset to the cut-set
liveness; non-returning calls, `Alloc`, `Raise`, `Return`, `Loop`, `Break` and
`Continue` reset the dead-store list. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def removeDead {width : Nat} [NeZero width] :
    WordLangProgHOL (BitVec width) → NumSet → List WordStoreHOL → List (NumSet × NumSet) →
      WordLangProgHOL (BitVec width) × NumSet × List WordStoreHOL
  | .move pri ls, live, nlive, _ =>
    let ls := ls.filter fun p => sptLookup p.1 live = some ()
    if ls = [] then (.skip, live, nlive)
    else
      let killed := (ls.map Prod.fst).foldr sptDelete live
      (.move pri ls, numsetListInsert (ls.map Prod.snd) killed, nlive)
  | .inst i, live, nlive, _ =>
    if removeDeadInst i live then (.skip, live, nlive)
    else (.inst i, getLiveInst i live, nlive)
  | .get num store, live, nlive, _ =>
    if sptLookup num live = none then (.skip, live, nlive)
    else (.get num store, sptDelete num live, nlive.filter fun s => store ≠ s)
  | .opCurrHeap b num src, live, nlive, _ =>
    if sptLookup num live = none then (.skip, live, nlive)
    else (.opCurrHeap b num src, sptInsert src () (sptDelete num live),
      nlive.filter fun s => WordStore.currHeap ≠ s)
  | .locValue r l1, live, nlive, _ =>
    if sptLookup r live = none then (.skip, live, nlive)
    else (.locValue r l1, sptDelete r live, nlive)
  | .set storeName exp, live, nlive, lt =>
    match exp with
    | .var r =>
      if storeName ∈ nlive then (.skip, live, nlive)
      else (.set storeName (.var r), sptInsert r () live, storeName :: nlive)
    | _ =>
      let prog := WordLangProgHOL.set storeName exp
      (prog, getLive prog live lt, [])
  | .seq s1 s2, live, nlive, lt =>
    let (s2, s2live, s2nlive) := removeDead s2 live nlive lt
    let (s1, s1live, s1nlive) := removeDead s1 s2live s2nlive lt
    let prog := match s1, s2 with
      | .skip, _ => s2
      | _, .skip => s1
      | _, _ => .seq s1 s2
    (prog, s1live, s1nlive)
  | .mustTerminate s1, live, nlive, lt =>
    let (s1, s1live, s1nlive) := removeDead s1 live nlive lt
    (.mustTerminate s1, s1live, s1nlive)
  | .ite cmp r1 ri e2 e3, live, nlive, lt =>
    let (e2, e2Live, e2Nlive) := removeDead e2 live nlive lt
    let (e3, e3Live, e3Nlive) := removeDead e3 live nlive lt
    let unionLive := sptUnion e2Live e3Live
    let liveset := match ri with
      | .reg r2 => sptInsert r2 () (sptInsert r1 () unionLive)
      | _ => sptInsert r1 () unionLive
    let nliveset := e2Nlive.filter fun s => s ∈ e3Nlive
    let prog := match e2, e3 with
      | .skip, .skip => .skip
      | _, _ => .ite cmp r1 ri e2 e3
    (prog, liveset, nliveset)
  | .call (some (v, cutsets, retHandler, l1, l2)) dest args h, live, nlive, lt =>
    let argsSet := numsetListInsert args .ln
    let cutset := sptUnion cutsets.1 cutsets.2
    let liveSet := sptUnion cutset argsSet
    let retHandler := (removeDead retHandler live nlive lt).1
    let h := match h with
      | none => none
      | some (v', prog, l1', l2') => some (v', (removeDead prog live nlive lt).1, l1', l2')
    (.call (some (v, cutsets, retHandler, l1, l2)) dest args h, liveSet, [])
  | .call none a b c, live, _, lt =>
    let prog := WordLangProgHOL.call none a b c
    (prog, getLive prog live lt, [])
  | .alloc a b, live, _, lt =>
    let prog := WordLangProgHOL.alloc a b
    (prog, getLive prog live lt, [])
  | .raise a, live, _, lt =>
    let prog := WordLangProgHOL.raise a
    (prog, getLive prog live lt, [])
  | .return a b, live, _, lt =>
    let prog := WordLangProgHOL.return a b
    (prog, getLive prog live lt, [])
  | .loop names body exitNames, _, _, lt =>
    let lt' := (names, exitNames) :: lt
    let body' := (removeDead body names [] lt').1
    (.loop names body' exitNames, names, [])
  | .break n, live, _, lt =>
    let prog := WordLangProgHOL.break n
    (prog, getLive prog live lt, [])
  | .continue n, live, _, lt =>
    let prog := WordLangProgHOL.continue n
    (prog, getLive prog live lt, [])
  | prog, live, nlive, lt => (prog, getLive prog live lt, nlive)
termination_by program _ _ _ => sizeOf program
decreasing_by all_goals decreasing_trivial

/-- Exact HOL `remove_dead_prog_def` (`word_allocScript.sml:1004-1006`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def removeDeadProg {width : Nat} [NeZero width] (prog : WordLangProgHOL (BitVec width)) :
    WordLangProgHOL (BitVec width) :=
  (removeDead prog .ln [] []).1

end Flapjack.WordAlloc
