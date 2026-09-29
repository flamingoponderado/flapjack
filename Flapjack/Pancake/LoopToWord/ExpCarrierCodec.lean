import Flapjack.Pancake.LoopLang

/-!
# Executable/exact Loop expression codec for Loop-to-Word

`loop_to_word`'s HOL source expression is `HolLoopExp width`, while the
executed compiler accepts the wider `LoopExp (BitVec width)` carrier.  This
codec recovers the exact source expression where possible; executable-only
`crepOp` and `cmp` nodes are rejected.  It is a carrier bridge only: production
`wordCompileExp` is not routed through `compExpHOL` by this module.
-/

namespace Flapjack

/-- Recover the exact fixed-width HOL source expression from its executable
projection. The two executable-only expression constructors have no HOL
preimage and return `none`. -/
def executableLoopExpToHol {width : Nat} [NeZero width] :
    LoopExp (BitVec width) → Option (HolLoopExp width)
  | .const value => some (.const value)
  | .var name => some (.var name)
  | .lookup address => some (.lookup address)
  | .load address => (executableLoopExpToHol address).map .load
  | .op operator args => executableLoopExpListToHol args |>.map (.op operator)
  | .crepOp _ _ => none
  | .cmp _ _ _ => none
  | .shift operator left right => do
      let left ← executableLoopExpToHol left
      let right ← executableLoopExpToHol right
      pure (.shift operator left right)
  | .baseAddr => some .baseAddr
  | .topAddr => some .topAddr
termination_by expression => sizeOf expression
where
  executableLoopExpListToHol {width : Nat} [NeZero width] :
      List (LoopExp (BitVec width)) → Option (List (HolLoopExp width))
    | [] => some []
    | expression :: rest => do
        let expression ← executableLoopExpToHol expression
        let rest ← executableLoopExpListToHol rest
        pure (expression :: rest)
  termination_by expressions => sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

/-- The codec is a left inverse of `holLoopExpToExecutable` on every exact
HOL expression. -/
theorem executableLoopExpToHol_holLoopExpToExecutable
    {width : Nat} [NeZero width] (expression : HolLoopExp width) :
      executableLoopExpToHol (holLoopExpToExecutable expression) =
      some expression := by
  refine HolLoopExp.rec
    (motive_1 := fun expression =>
      executableLoopExpToHol (holLoopExpToExecutable expression) = some expression)
    (motive_2 := fun expressions =>
      executableLoopExpToHol.executableLoopExpListToHol
        (expressions.map holLoopExpToExecutable) = some expressions)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ expression
  · intro value
    simp [holLoopExpToExecutable, executableLoopExpToHol]
  · intro name
    simp [holLoopExpToExecutable, executableLoopExpToHol]
  · intro address
    simp [holLoopExpToExecutable, executableLoopExpToHol]
  · intro address ih
    simpa [holLoopExpToExecutable, executableLoopExpToHol] using ih
  · intro operator args ih
    simpa [holLoopExpToExecutable, executableLoopExpToHol] using ih
  · intro operator left right ihLeft ihRight
    simp [holLoopExpToExecutable, executableLoopExpToHol, ihLeft, ihRight]
  · simp [holLoopExpToExecutable, executableLoopExpToHol]
  · simp [holLoopExpToExecutable, executableLoopExpToHol]
  · simp [executableLoopExpToHol.executableLoopExpListToHol]
  · intro head tail ihHead ihTail
    simp [executableLoopExpToHol.executableLoopExpListToHol,
      ihHead, ihTail]

@[simp] theorem executableLoopExpToHol_rejects_crepOp
    {width : Nat} [NeZero width] (operator : CrepOp)
    (args : List (LoopExp (BitVec width))) :
    executableLoopExpToHol (.crepOp operator args) = none := by
  simp [executableLoopExpToHol]

@[simp] theorem executableLoopExpToHol_rejects_cmp
    {width : Nat} [NeZero width] (operator : Cmp)
    (left right : LoopExp (BitVec width)) :
    executableLoopExpToHol (.cmp operator left right) = none := by
  simp [executableLoopExpToHol]

end Flapjack
