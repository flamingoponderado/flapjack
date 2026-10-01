import Flapjack.Compiler.Backend.WordToStack.Proofs.StackAbstraction
import Flapjack.Compiler.Backend.WordToStack.Proofs.Frames
import Flapjack.Compiler.Backend.WordToStack.Proofs.IndexList
import Flapjack.Compiler.Backend.Semantics.StackSem.Bitmap

/-! Literal Word-to-Stack `stack_rel_aux` over exact carriers. -/
namespace Flapjack.WordToStackProofs
open Flapjack.StackSem

/-- HOL `oEL i l`: the total list lookup returning `NONE` past the end. -/
def oEL {α : Type} (i : Nat) (l : List α) : Option α := l[i]?

/-- HOL `the d x`: return the payload of `x` or the default `d` for `NONE`. -/
def holThe {α : Type} (d : α) (x : Option α) : α := x.getD d

/-- HOL `LASTN n l`: the trailing `n` elements (empty when `n` exceeds the
length). -/
def lastN {α : Type} (n : Nat) (l : List α) : List α := l.drop (l.length - n)

/-- HOL `ALOOKUP l n`: first-match association-list lookup. -/
def aLookup {β : Type} : List (Nat × β) → Nat → Option β
  | [], _ => none
  | (m, v) :: rest, n => if m = n then some v else aLookup rest n

/-- HOL `EL i l` rendered total with an explicit out-of-range default (the
`ARB` analogue). Only reached inside guards that exclude the default case. -/
def holEl {α : Type} (i : Nat) (l : List α) (d : α) : α := l.getD i d

/-- Default frame used only as the out-of-range `EL` default in `stack_rel_aux`
(untagged `ARB` rendering; never selected by the source guard). -/
def holElDefaultFrame {width : Nat} [NeZero width] : WordSemStackFrame width :=
  .stackFrame none [] [] none

/-- Literal source `stack_rel_aux` (`word_to_stackProofScript.sml:815`), kept
PROVISIONAL and untagged: its body uses the untagged renderings `holEl` (HOL
total `EL`, ARB out-of-range), `holThe` (HOL `the`), `lastN` and
`holElDefaultFrame` (an arbitrary ARB witness). The faithful total HD/EL/`the`
rendering and the HOL `listScript` provenance pin are tracked by
`flapjack-pxn.18.5.15.3.38` and `.38.1`; until those are source-reviewed this
is not an accepted exact HOL port. -/
def stackRelAux {width : Nat} [NeZero width] (k len : Nat)
    (sourceStack : List (WordSemStackFrame width))
    (stack : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width))) :
    Prop :=
  match sourceStack, stack with
  | [], [] => True
  | .stackFrame n l0 l none :: xs, (none, bits, frame) :: rest =>
      (∀ n' v, aLookup l0 n' = some v → aLookup l n' = none →
          adjustNames n' < k + bits.length ∧
          oEL (k + bits.length - (adjustNames n' + 1)) bits = some false ∧
          aLookup (indexList frame k) (n' / 2) = some v) ∧
      filterBitmap bits (indexList frame k) = some (l.map (fun p => (adjustNames p.1, p.2)), []) ∧
      holThe (frame.length + 1) n = frame.length + 1 ∧
      stackRelAux k len xs rest
  | .stackFrame n l0 l (some (h1, l1, l2)) :: xs, (some (loc, hv), bits, frame) :: rest =>
      (h1 < rest.length →
          isHandlerFrame (holEl (rest.length - (h1 + 1)) xs holElDefaultFrame) →
          hv = .word (BitVec.ofNat width (len - handlerVal (lastN (h1 + 1) rest)))) ∧
      loc = .loc l1 l2 ∧
      (∀ n' v, aLookup l0 n' = some v → aLookup l n' = none →
          adjustNames n' < k + bits.length ∧
          oEL (k + bits.length - (adjustNames n' + 1)) bits = some false ∧
          aLookup (indexList frame k) (n' / 2) = some v) ∧
      filterBitmap bits (indexList frame k) = some (l.map (fun p => (adjustNames p.1, p.2)), []) ∧
      holThe (frame.length + 1) n = frame.length + 1 ∧
      stackRelAux k len xs rest
  | _, _ => False

end Flapjack.WordToStackProofs
