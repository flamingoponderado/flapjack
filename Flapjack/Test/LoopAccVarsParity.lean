import Flapjack.Pancake.LoopLive
import Flapjack.Pancake.LoopLang.AccVars

/-!
# Original-domain parity for `acc_vars`

`loopAccVars` is the Lean counterpart of
`cakeml/pancake/loopLangScript.sml:117-158`.  The checked-in expected values
come from `loop_lang_acc_vars_probeScript.sml`, so these tests expose the
source behavior that allocation analysis must follow: expression operands,
stores, returns, call arguments, and FFI operands are not accumulated by
`acc_vars`.

The second half replays the same `loop_lang_acc_vars_probe.out` rows over the
exact width-indexed `HolLoopProg` carrier through the tagged
`Flapjack.accVarsHOL`, checking the observed `num_set` membership directly.
-/

namespace Flapjack.Test.LoopAccVarsParity

open Flapjack

def originalSkip : List Nat := []
def originalAssign : List Nat := [7]
def originalReturn : List Nat := []
def originalStore : List Nat := []
def originalLongDiv : List Nat := [1, 2]
def originalCallNone : List Nat := []

def probeSkip : LoopProg Nat := .skip
def probeAssign : LoopProg Nat := .assign 7 (.const 1)
def probeReturn : LoopProg Nat := .return [7, 8]
def probeStore : LoopProg Nat := .store (.var 4) 7
def probeLongDiv : LoopProg Nat := .arith (.longDiv 1 2 3 4 5)
def probeCallNone : LoopProg Nat := .call none (some 3) [4, 5] none
def probeIf : LoopProg Nat :=
  .ite .less 8 (.reg 9) (.assign 11 (.const 1)) (.assign 12 (.const 2)) []

#guard loopAccVars probeSkip [] == originalSkip
#guard loopAccVars probeAssign [] == originalAssign
#guard loopAccVars probeReturn [] == originalReturn
#guard loopAccVars probeStore [] == originalStore
#guard loopAccVars probeLongDiv [] == originalLongDiv
#guard loopAccVars probeCallNone [] == originalCallNone
#guard loopAccVars probeIf [] == [11, 12]

/-! ## Exact `HolLoopProg` replay of every `loop_lang_acc_vars_probe.out` row

Each row observes the `num_set` membership over the key universe `0..11`
(every probe key is below 12), matching the HOL `num_set` printer output in
`scripts/hol-probes/loop_lang_acc_vars_probe.out`. -/

private def probeImage (tree : Spt Unit) : List Bool :=
  (List.range 12).map fun key => (sptLookup key tree).isSome

private def expectedImage (keys : List Nat) : List Bool :=
  (List.range 12).map fun key => keys.contains key

def accProbeSkip : HolLoopProg 32 := .skip
def accProbeAssign : HolLoopProg 32 := .assign 7 (.var 7)
def accProbeReturn : HolLoopProg 32 := .return [7, 8]
def accProbeStore : HolLoopProg 32 := .store (.var 4) 7
def accProbeLongDiv : HolLoopProg 32 := .arith (.longDiv 1 2 3 4 5)
def accProbeCallNone : HolLoopProg 32 := .call none (some 3) [4, 5] none
def accProbeSeq : HolLoopProg 32 :=
  .seq (.assign 1 (.var 1)) (.assign 2 (.var 2))
def accProbeLoopMark : HolLoopProg 32 :=
  .loop .ln (.mark (.assign 3 (.var 3))) .ln
def accProbeCallHandler : HolLoopProg 32 :=
  .call (some ([7, 8], .ln)) (some 3) [4, 5]
    (some (9, .assign 10 (.var 10), .skip, .ln))
def accProbePrimitive : HolLoopProg 32 := .primitive [1, 2] .addCarry []
def accProbeLoad32 : HolLoopProg 32 := .load32 3 4
def accProbeShMem : HolLoopProg 32 := .shMem .load 5 (.var 6)

#guard probeImage (accVarsHOL accProbeSkip .ln) == expectedImage []
#guard probeImage (accVarsHOL accProbeAssign .ln) == expectedImage [7]
#guard probeImage (accVarsHOL accProbeReturn .ln) == expectedImage []
#guard probeImage (accVarsHOL accProbeStore .ln) == expectedImage []
#guard probeImage (accVarsHOL accProbeLongDiv .ln) == expectedImage [1, 2]
#guard probeImage (accVarsHOL accProbeCallNone .ln) == expectedImage []
#guard probeImage (accVarsHOL accProbeSeq .ln) == expectedImage [1, 2]
#guard probeImage (accVarsHOL accProbeLoopMark .ln) == expectedImage [3]
#guard probeImage (accVarsHOL accProbeCallHandler .ln) == expectedImage [7, 8, 9, 10]
#guard probeImage (accVarsHOL accProbePrimitive .ln) == expectedImage [1, 2]
#guard probeImage (accVarsHOL accProbeLoad32 .ln) == expectedImage [4]
#guard probeImage (accVarsHOL accProbeShMem .ln) == expectedImage [5]

def check (name : String) (actual expected : List Nat) : IO Bool := do
  if actual == expected then
    IO.println s!"PASS {name}"
    pure true
  else
    IO.println s!"FAIL {name}: expected {repr expected}, got {repr actual}"
    pure false

def runChecks : IO Bool := do
  let results ← [
    check "acc_vars skip" (loopAccVars probeSkip []) originalSkip,
    check "acc_vars assign" (loopAccVars probeAssign []) originalAssign,
    check "acc_vars ignores return values"
      (loopAccVars probeReturn []) originalReturn,
    check "acc_vars ignores store operands"
      (loopAccVars probeStore []) originalStore,
    check "acc_vars long division" (loopAccVars probeLongDiv []) originalLongDiv,
    check "acc_vars ignores call arguments"
      (loopAccVars probeCallNone []) originalCallNone,
    check "acc_vars ignores if condition operands"
      (loopAccVars probeIf []) [11, 12] ].mapM id
  let exactOk :=
    probeImage (accVarsHOL accProbeSkip .ln) == expectedImage [] &&
    probeImage (accVarsHOL accProbeAssign .ln) == expectedImage [7] &&
    probeImage (accVarsHOL accProbeReturn .ln) == expectedImage [] &&
    probeImage (accVarsHOL accProbeStore .ln) == expectedImage [] &&
    probeImage (accVarsHOL accProbeLongDiv .ln) == expectedImage [1, 2] &&
    probeImage (accVarsHOL accProbeCallNone .ln) == expectedImage [] &&
    probeImage (accVarsHOL accProbeSeq .ln) == expectedImage [1, 2] &&
    probeImage (accVarsHOL accProbeLoopMark .ln) == expectedImage [3] &&
    probeImage (accVarsHOL accProbeCallHandler .ln) == expectedImage [7, 8, 9, 10] &&
    probeImage (accVarsHOL accProbePrimitive .ln) == expectedImage [1, 2] &&
    probeImage (accVarsHOL accProbeLoad32 .ln) == expectedImage [4] &&
    probeImage (accVarsHOL accProbeShMem .ln) == expectedImage [5]
  if exactOk then
    IO.println "PASS acc_vars exact HolLoopProg HOL rows"
  else
    IO.println "FAIL acc_vars exact HolLoopProg HOL rows"
  pure (results.all id && exactOk)

end Flapjack.Test.LoopAccVarsParity
