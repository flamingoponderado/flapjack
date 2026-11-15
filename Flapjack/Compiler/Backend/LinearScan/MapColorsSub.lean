module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.LinearScan.HiddenState
public import Flapjack.Compiler.Backend.RegAlloc.StateMap

@[expose] public section

/-!
# linear_scan translation helper `map_colors_sub`

These declarations follow the `map_colors_sub` text at
`linear_scanScript.sml:1264-1274`, the monadic map of `colors_sub` defined for
the CakeML translator, and its equation with the tagged `st_ex_MAP`
(`stExMap`). That text is **not a live HOL declaration**: the script opens an
SML comment at line 1148 and closes it only at the final `*)` of the file, so
neither definition reaches `linear_scanTheory` and a theory-DB lookup fails.
The declarations therefore carry no `@[hol]` tag: they are Flapjack
infrastructure ported from commented-out source text, and their `@[hol]` tags
were withdrawn. The executed allocator is unchanged.
-/

namespace Flapjack.LinearScan

open Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-- Port of the commented-out `map_colors_sub` text at
    `linear_scanScript.sml:1264-1268`. Flapjack infrastructure: the cited source
    block is inside an SML comment, so there is no live HOL declaration to cite
    and no `@[hol]` tag. -/
def mapColorsSub : List Nat → LsM (List Nat)
  | [] => ret []
  | x :: xs => bind (colorsSub x) fun fx => bind (mapColorsSub xs) fun fxs => ret (fx :: fxs)

/-- Port of the commented-out `map_colors_sub = st_ex_MAP colors_sub` equation at
    `linear_scanScript.sml:1270-1274`. Flapjack infrastructure: the cited source
    block is inside an SML comment, so there is no live HOL declaration to cite
    and no `@[hol]` tag. -/
theorem mapColorsSubEq : mapColorsSub = stExMap colorsSub := by
  funext l
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [mapColorsSub, stExMap, ih]

end Flapjack.LinearScan
