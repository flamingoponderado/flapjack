import Flapjack.RiscV.WordDeadCode
import Flapjack.RiscV.WordInstSelect

namespace Flapjack.Test.WordDeadCodeParity

open Flapjack Flapjack.RiscV

def raiseTail : WordProg Nat :=
  .seq (.raise 2)
    (.seq (.move 0 [(413, 0)]) (.return 389 [2]))

def raiseTailGuard : WordProg Nat → Bool
  | .seq (.raise 2) (.return 389 [2]) => true
  | _ => false

#guard raiseTailGuard (wordRemoveDeadProgram raiseTail)

/- Cake's `get_live (Raise num)` keeps the incoming continuation live set even
   when the enclosing function has a return label.  Filtering that set by the
   return labels changes the allocator-visible frame, so keep this rule as a
   small executable regression. -/
def raisePreservesContinuationLiveGuard : Bool :=
  match wordDeadCodeAuxWithLabels
      (.raise 2 : WordProg Nat) [57] [] [61] with
  | (.raise 2, live) => live == [57, 2]
  | _ => false

#guard raisePreservesContinuationLiveGuard

/- Cake's remove_dead drops an If after both branches become Skip, while
   retaining the condition in the backward live set. -/
def deadIfBranchesGuard : Bool :=
  match wordDeadCodeAux
      (.ite .equal 4 (.imm 0) (.skip : WordProg Nat) .skip) [9] [] with
  | (.skip, live) => live == [9, 4]
  | _ => false

#guard deadIfBranchesGuard

/- Cake's `remove_dead` tracks `nlive` globals backwards: an earlier
   `Set globals (Var 7)` is dead once a later write to the same global is
   retained.  This is `word_allocScript.sml:952-961`, distinct from ordinary
   local-variable dead assignment removal. -/
def deadGlobalOverwrite : WordProg Nat :=
  .seq (.set (.globals : WordStore Nat) (.var 7))
    (.set (.globals : WordStore Nat) (.var 8))

def deadGlobalOverwriteGuard : Bool :=
  match wordRemoveDeadProgram deadGlobalOverwrite with
  | .set .globals (.var 8) => true
  | _ => false

#guard deadGlobalOverwriteGuard

/- The actual allocator rejects unsupported instructions before dead-code
removal can erase a dead load. Both call continuations are checked. -/
#guard CakeRegAlloc.cakeAllocateWordFunctionAfterDead 0 []
  (.inst (.mem .load16 2 4) : WordProg Nat) |>.isNone
#guard CakeRegAlloc.cakeAllocateWordFunctionAfterDead 0 []
  (.inst (.memOffset .store16 2 4 8) : WordProg Nat) |>.isNone
#guard CakeRegAlloc.cakeAllocateWordFunctionAfterDead 0 []
  (.call (some ([], ([], []), .inst (.memOffset .load16 2 4 8), 0, 0))
    none [] none : WordProg Nat) |>.isNone
#guard CakeRegAlloc.cakeAllocateWordFunctionAfterDead 0 []
  (.call none none [] (some (2, .inst (.mem .store16 2 4), 0, 0)) : WordProg Nat) |>.isNone
#guard CakeRegAlloc.cakeAllocateWordFunctionAfterDead 0 []
  (.seq (.inst (.mem .store 2 4)) (.return 0 []) : WordProg Nat) |>.isSome

/- The production address selector keeps the store opcode in the negative
memOffset route. This is the actual selector, not its proof-side helper. -/
def selectedNegativeStore : WordProg (BitVec 64) :=
  wordInstSelectProgram 100 (.store
    (.op .add [.var 4, .const (BitVec.ofInt 64 (-8))]) 2)

#guard match selectedNegativeStore with
  | .seq (.move 0 [(100, 4)]) (.inst (.memOffset .store 2 100 offset)) =>
      offset == BitVec.ofInt 64 (-8)
  | _ => false
#guard allocatorMemorySupported selectedNegativeStore

/-- Universal equation for the actual production valid-offset Store branch.
This is Flapjack-specific selection infrastructure, not a tagged HOL port. -/
theorem selectedStoreOpcode (temp value : Nat)
    (expression base : WordExp (BitVec 64)) (prelude : WordProg (BitVec 64))
    (selectedBase : WordExp (BitVec 64)) (offset : BitVec 64)
    (normalized : wordInstNormalizeExp expression = .op .add [base, .const offset])
    (selected : wordInstSelectAtom temp base = (prelude, selectedBase))
    (allowed : wordInstSelectShareOffsetAllowed .store offset = true) :
    wordInstSelectProgram temp (.store expression value) =
      wordDeadSelectSeq prelude (.inst (.memOffset .store value temp offset)) := by
  simp [wordInstSelectProgram, wordInstSelectStoreCake, normalized, selected, allowed]

end Flapjack.Test.WordDeadCodeParity
