module

public import Flapjack.RiscV.Heuristics
public import Flapjack.Compiler.Backend.WordAlloc.CanonizeMoves

@[expose] public section

/-!
# Spill costs and canonical move priorities

This is the final arithmetic part of CakeML's heuristic allocator boundary.
The source computes spill costs from the five usage counters, canonicalizes
unordered move pairs, groups repeated moves, and then uses the resulting
weighted count as the coalescing priority.
-/

namespace Flapjack

/-! Cake's `Portable.sort` is `mergesort_tail`, not a stable insertion sort.
    This generic helper is kept at the heuristic boundary because both
    `word_alloc$canonize_moves` and `reg_alloc$sort_moves` use that relation.
    The recursive DIV2 split and negate toggle are observable for equal keys. -/
def cakeMergeTail {α : Type u} (negate : Bool) (ord : α → α → Bool) :
    List α → List α → List α → List α
  | [], [], acc => acc
  | left, [], acc => left.reverse ++ acc
  | [], right, acc => right.reverse ++ acc
  | leftHead :: leftTail, rightHead :: rightTail, acc =>
      if ord leftHead rightHead != negate then
        cakeMergeTail negate ord leftTail (rightHead :: rightTail)
          (leftHead :: acc)
      else
        cakeMergeTail negate ord (leftHead :: leftTail) rightTail
          (rightHead :: acc)
  termination_by left right _acc => left.length + right.length
  decreasing_by all_goals simp +arith

def cakeSort2Tail {α : Type u} (negate : Bool) (ord : α → α → Bool)
    (x y : α) : List α :=
  if ord x y != negate then [x, y] else [y, x]

def cakeSort3Tail {α : Type u} (negate : Bool) (ord : α → α → Bool)
    (x y z : α) : List α :=
  if ord x y != negate then
    if ord y z != negate then [x, y, z]
    else if ord x z != negate then [x, z, y]
    else [z, x, y]
  else if ord y z != negate then
    if ord x z != negate then [y, x, z]
    else [y, z, x]
  else [z, y, x]

def cakeSortN {α : Type u} (negate : Bool) (ord : α → α → Bool) :
    Nat → List α → List α
  | 0, _ => []
  | 1, [] => []
  | 1, x :: _ => [x]
  | 2, [] => []
  | 2, [x] => [x]
  | 2, x :: y :: _ => cakeSort2Tail negate ord x y
  | 3, [] => []
  | 3, [x] => [x]
  | 3, [x, y] => cakeSort2Tail negate ord x y
  | 3, x :: y :: z :: _ => cakeSort3Tail negate ord x y z
  | n + 4, items =>
      let len1 := (n + 4) / 2
      let nextNegate := !negate
      cakeMergeTail nextNegate ord
        (cakeSortN nextNegate ord ((n + 4) / 2) items)
        (cakeSortN nextNegate ord (n + 4 - len1) (items.drop len1)) []
  termination_by n _items => n
  decreasing_by
    all_goals
      have hn : 0 < n + 4 := by omega
      have hdiv : (n + 4) / 2 < n + 4 := Nat.div_lt_self hn (by decide)
      omega

def cakeSortTail {α : Type u} (ord : α → α → Bool) (items : List α) : List α :=
  cakeSortN false ord items.length items

end Flapjack
