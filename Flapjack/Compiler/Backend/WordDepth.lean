import Flapjack.HolRef
import Flapjack.Misc.Sptree

/-!
# CakeML `word_depth`

Counterpart of `cakeml/compiler/backend/word_depthScript.sml`. This module ports
the acyclic call-graph representation and the static maximum-stack-depth
computation used by Pancake's `compile_prog_max`:

* `cakeml/compiler/backend/word_depthScript.sml:20-27` `call_tree`
  (`Leaf | Unknown | Const num call_tree | Call num call_tree |
   Branch call_tree call_tree`);
* `cakeml/compiler/backend/word_depthScript.sml:24-35` `max_depth`.

`max_depth` reads frame sizes through HOL `lookup` on a `num_map`
(`num spt`); the Lean carrier is the reviewed exact `Spt Nat` with
`Flapjack.sptLookup`, so both declarations are unqualified exact ports. The
`frame_sizes` argument is the only map, and it is the exact tree-map carrier,
not a `|->` finite map. `Option` is HOL `option` and `Nat` is HOL `num`.

The sibling `mk_Branch` / `call_graph` / `full_call_graph` / `max_depth_graphs`
ports are tracked separately (bead `flapjack-28je.2`).
-/

namespace Flapjack.Compiler.Backend.WordDepth

open Flapjack (Spt sptLookup)

/-- HOL `OPTION_MAP2 f (SOME x) (SOME y) = SOME (f x y)`, otherwise `NONE`
    (`optionTheory`). Untagged Flapjack infrastructure. -/
def optionMap₂ {α β γ : Type} (f : α → β → γ) : Option α → Option β → Option γ
  | some x, some y => some (f x y)
  | _, _ => none

/-- Exact HOL `call_tree`
    (`cakeml/compiler/backend/word_depthScript.sml:20-27`):
    `Leaf | Unknown | Const num call_tree | Call num call_tree |
     Branch call_tree call_tree`. -/
@[hol "cakeml/compiler/backend/word_depthScript.sml" "call_tree"]
inductive CallTree where
  | leaf : CallTree
  | unknown : CallTree
  | const (n : Nat) (t : CallTree) : CallTree
  | call (n : Nat) (t : CallTree) : CallTree
  | branch (t1 t2 : CallTree) : CallTree
  deriving DecidableEq, Repr

/-- Exact HOL `max_depth`
    (`cakeml/compiler/backend/word_depthScript.sml:24-35`):
    `max_depth frame_sizes Leaf = SOME 0`,
    `max_depth frame_sizes Unknown = NONE`,
    `max_depth frame_sizes (Const n t) = OPTION_MAP ((+) n) (max_depth frame_sizes t)`,
    `max_depth frame_sizes (Branch t1 t2) =
       OPTION_MAP2 MAX (max_depth frame_sizes t1) (max_depth frame_sizes t2)`,
    `max_depth frame_sizes (Call n t) =
       OPTION_MAP2 (+) (lookup n frame_sizes) (max_depth frame_sizes t)`.

    `frame_sizes` is HOL `num_map` (`num spt`), rendered by the exact
    `Spt Nat` carrier and `sptLookup`; a missing frame is `NONE`, so an
    unknown/cyclic `Call` propagates as `NONE` with no invented bound. -/
@[hol "cakeml/compiler/backend/word_depthScript.sml" "max_depth_def"]
def maxDepth (frameSizes : Spt Nat) : CallTree → Option Nat
  | .leaf => some 0
  | .unknown => none
  | .const n t => (maxDepth frameSizes t).map (fun d => n + d)
  | .branch t1 t2 => optionMap₂ max (maxDepth frameSizes t1) (maxDepth frameSizes t2)
  | .call n t => optionMap₂ (· + ·) (sptLookup n frameSizes) (maxDepth frameSizes t)

end Flapjack.Compiler.Backend.WordDepth
