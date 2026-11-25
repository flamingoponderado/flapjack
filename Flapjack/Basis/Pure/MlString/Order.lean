module

public import Flapjack.Basis.Pure.MlString.Ops

@[expose] public section

/-!
# Cake `mlstring` ordering

Lean counterparts of `compare_aux_def`, `compare_def`, `mlstring_lt_def`,
`mlstring_le_def`, `mlstring_gt_def`, `mlstring_ge_def`, `fast_lt_def`,
`fast_le_def`, `fast_gt_def`, `fast_ge_def`, `collate_aux_def` and
`collate_def` in `cakeml/basis/pure/mlstringScript.sml`.

HOL's `ordering` is Lean's `Ordering`, so `Less`, `Equal` and `Greater` are
`.lt`, `.eq` and `.gt`; HOL `char_lt` is the unsigned byte order on
`HolChar = BitVec 8`; and `strsub` and `strlen` are the tagged renderings, which
makes the definitions noncomputable. The four ordering predicates are
bool-valued in HOL, so they are `decide` of the corresponding `Ordering`
comparison.
-/

namespace Flapjack.Basis.Pure.MlString.Order

open Flapjack.Basis.Pure.MlString.MlString

/-- Original `compare_aux_def`: compare `len` characters starting at `start`,
    keeping `ord` while they are equal. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "compare_aux_def"]
noncomputable def compareAux (s1 s2 : MlString) (ord : Ordering) (start len : Nat) : Ordering :=
  if len = 0 then ord
  else if strsub s2 start < strsub s1 start then .gt
  else if strsub s1 start < strsub s2 start then .lt
  else compareAux s1 s2 ord (start + 1) (len - 1)
termination_by len

/-- Original `compare_def`: the shorter string is smaller, and otherwise the
    common prefix decides. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "compare_def"]
noncomputable def compare (s1 s2 : MlString) : Ordering :=
  if strlen s1 < strlen s2 then compareAux s1 s2 .lt 0 (strlen s1)
  else if strlen s2 < strlen s1 then compareAux s1 s2 .gt 0 (strlen s2)
  else compareAux s1 s2 .eq 0 (strlen s2)

/-- Original `mlstring_lt_def`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "mlstring_lt_def"]
noncomputable def mlstringLt (s1 s2 : MlString) : Bool := decide (compare s1 s2 = .lt)

/-- Original `mlstring_le_def`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "mlstring_le_def"]
noncomputable def mlstringLe (s1 s2 : MlString) : Bool := decide (compare s1 s2 ≠ .gt)

/-- Original `mlstring_gt_def`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "mlstring_gt_def"]
noncomputable def mlstringGt (s1 s2 : MlString) : Bool := decide (compare s1 s2 = .gt)

/-- Original `mlstring_ge_def`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "mlstring_ge_def"]
noncomputable def mlstringGe (s1 s2 : MlString) : Bool := decide (compare s1 s2 ≠ .lt)

/-- Original `fast_lt_def`: order by length first, then by the common prefix. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "fast_lt_def"]
noncomputable def fastLt (s1 s2 : MlString) : Bool :=
  if strlen s1 = strlen s2 then mlstringLt s1 s2 else decide (strlen s1 < strlen s2)

/-- Original `fast_le_def`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "fast_le_def"]
noncomputable def fastLe (s1 s2 : MlString) : Bool :=
  if strlen s1 = strlen s2 then mlstringLe s1 s2 else decide (strlen s1 ≤ strlen s2)

/-- Original `fast_gt_def`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "fast_gt_def"]
noncomputable def fastGt (s1 s2 : MlString) : Bool :=
  if strlen s1 = strlen s2 then mlstringGt s1 s2 else decide (strlen s1 > strlen s2)

/-- Original `fast_ge_def`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "fast_ge_def"]
noncomputable def fastGe (s1 s2 : MlString) : Bool :=
  if strlen s1 = strlen s2 then mlstringGe s1 s2 else decide (strlen s1 ≥ strlen s2)

/-- Original `collate_aux_def`: compare `len` characters with the given
    character comparison, keeping `ord` while it reports `Equal`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "collate_aux_def"]
noncomputable def collateAux (f : HolChar → HolChar → Ordering) (s1 s2 : MlString)
    (ord : Ordering) (n : Nat) : Nat → Ordering
  | 0 => ord
  | len + 1 =>
    if f (strsub s1 n) (strsub s2 n) = .eq then collateAux f s1 s2 ord (n + 1) len
    else f (strsub s1 n) (strsub s2 n)

/-- Original `collate_def`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "collate_def"]
noncomputable def collate (f : HolChar → HolChar → Ordering) (s1 s2 : MlString) : Ordering :=
  if strlen s1 < strlen s2 then collateAux f s1 s2 .lt 0 (strlen s1)
  else if strlen s2 < strlen s1 then collateAux f s1 s2 .gt 0 (strlen s2)
  else collateAux f s1 s2 .eq 0 (strlen s2)

/-- Original `compare_thm`: the ordering predicates describe `compare`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "compare_thm"]
theorem compare_thm (s1 s2 : MlString) :
    compare s1 s2 =
      if mlstringLt s1 s2 then .lt else if mlstringLe s1 s2 then .eq else .gt := by
  unfold mlstringLt mlstringLe
  cases compare s1 s2
  · simp
  · simp
  · simp

end Flapjack.Basis.Pure.MlString.Order
