import Flapjack.HolRef
import Flapjack.Pancake.WordLang
import Flapjack.Misc.Anub
import Flapjack.Misc.Sptree

/-!
# `word_unreach`: removing trivially unreachable code

Counterpart of `cakeml/compiler/backend/word_unreachScript.sml`: right-associate `Seq`,
drop the continuation after an unconditional transfer, and merge adjacent `Move`s. HOL
`ALOOKUP` on the move list is the untagged library rendering `sptAListLookup`. This is a
native port used by the executed allocator pipeline through its checked codec.
The separate legacy implementation in `RiscV/WordUnreach.lean` is not evidence
for correctness of this native route.
-/

namespace Flapjack.Compiler.Backend.WordUnreach

open Flapjack

/-- Whether a program is `Skip` (Flapjack infrastructure deciding HOL's `p = Skip`). -/
def isSkip {α : Type} : WordLangProgHOL α → Bool
  | .skip => true
  | _ => false

theorem isSkip_iff {α : Type} (p : WordLangProgHOL α) : isSkip p = true ↔ p = .skip := by
  cases p <;> simp [isSkip]

instance decEqSkip {α : Type} (p : WordLangProgHOL α) : Decidable (p = .skip) :=
  decidable_of_iff _ (isSkip_iff p)

/-- Exact HOL `dest_Seq_Move_def` (`word_unreachScript.sml:12-16`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def destSeqMove {width : Nat} [NeZero width] :
    WordLangProgHOL (BitVec width) →
      Option (Nat × List (Nat × Nat) × WordLangProgHOL (BitVec width))
  | .move n l => some (n, l, .skip)
  | .seq (.move n l) rest => some (n, l, rest)
  | _ => none

/-- Exact HOL `merge_moves_def` (`word_unreachScript.sml:18-24`). -/
@[hol "cakeml/compiler/backend/word_unreachScript.sml" "merge_moves_def"]
def mergeMoves (l1 l2 : List (Nat × Nat)) : List (Nat × Nat) :=
  let l2' := l2.map (fun (x, y) =>
    match sptAListLookup y l1 with
    | none => (x, y)
    | some v => (x, v))
  anub (l2' ++ l1) ([] : List Nat)

/-- Exact HOL `SimpSeq_def` (`word_unreachScript.sml:26-46`), including the commented-out
`n1 ≠ n2` guard being absent. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def simpSeq {width : Nat} [NeZero width] (p1 p2 : WordLangProgHOL (BitVec width)) : WordLangProgHOL (BitVec width) :=
  let default := WordLangProgHOL.seq p1 p2
  if p2 = .skip then p1 else
    match p1 with
    | .skip => p2
    | .raise _ => p1
    | .return _ _ => p1
    | .break _ => p1
    | .continue _ => p1
    | .move n1 l1 =>
        match destSeqMove p2 with
        | none => default
        | some (n2, l2, rest) =>
            let l := mergeMoves l1 l2
            if rest = .skip then .move (max n1 n2) l
            else .seq (.move (max n1 n2) l) rest
    | _ => default

/-- Exact HOL `Seq_assoc_right_def` (`word_unreachScript.sml:48-68`); a `Call` without a
return continuation drops the accumulator, as in HOL. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def seqAssocRight {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) → WordLangProgHOL (BitVec width) →
    WordLangProgHOL (BitVec width)
  | .skip, acc => acc
  | .seq q1 q2, acc => seqAssocRight q1 (seqAssocRight q2 acc)
  | .ite v n r q1 q2, acc =>
      simpSeq (.ite v n r (seqAssocRight q1 .skip) (seqAssocRight q2 .skip)) acc
  | .mustTerminate q, acc => simpSeq (.mustTerminate (seqAssocRight q .skip)) acc
  | .call retProg dest args handler, acc =>
      match retProg with
      | none => .call retProg dest args handler
      | some (x1, x2, q1, x3, x4) =>
          simpSeq (.call (some (x1, x2, seqAssocRight q1 .skip, x3, x4)) dest args
            (match handler with
              | none => none
              | some (y1, q2, y2, y3) => some (y1, seqAssocRight q2 .skip, y2, y3))) acc
  | .loop names body exitNames, acc =>
      simpSeq (.loop names (seqAssocRight body .skip) exitNames) acc
  | p1, acc => simpSeq p1 acc

/-- Exact HOL `remove_unreach_def` (`word_unreachScript.sml:70-73`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def removeUnreach {width : Nat} [NeZero width] (e : WordLangProgHOL (BitVec width)) : WordLangProgHOL (BitVec width) :=
  seqAssocRight e .skip

end Flapjack.Compiler.Backend.WordUnreach
