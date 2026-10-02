import Flapjack.Misc.BalancedMap.Core

namespace Flapjack.Misc.BalancedMap

/-! The original constructor clauses specify whole functions only partially.
Each realization chooses a whole function satisfying exactly those clauses.
Tip outputs in existence witnesses do not constrain the chosen functions.
No missing-case or cross-function equality is claimed. The realizations are
untagged infrastructure; the tagged equation theorems are the complete source
specifications. This is source treatment, not cross-assistant equivalence. -/

private def singleLSpec {κ ν : Type} (f : κ → ν → Map κ ν → Map κ ν → Map κ ν) : Prop :=
  ∀ k1 x1 t1 n k2 x2 t2 t3, f k1 x1 t1 (.bin n k2 x2 t2 t3) = bin k2 x2 (bin k1 x1 t1 t2) t3

private theorem singleLExists {κ ν : Type} :
    ∃ f : κ → ν → Map κ ν → Map κ ν → Map κ ν, singleLSpec f := by
  refine ⟨fun k x left right => match right with
    | .bin _ k2 x2 t2 t3 => bin k2 x2 (bin k x left t2) t3
    | .tip => .tip, ?_⟩
  intro k1 x1 t1 n k2 x2 t2 t3
  rfl

/-- Whole-function realization of the source specification. No separate HOL
original is claimed for this choice infrastructure; see the tagged equation. -/
noncomputable def singleL {κ ν : Type} : κ → ν → Map κ ν → Map κ ν → Map κ ν :=
  Classical.choose (singleLExists (κ := κ) (ν := ν))

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "singleL_def"]
theorem singleLDef {κ ν : Type} (k1 : κ) (x1 : ν) (t1 : Map κ ν) (n : Nat) (k2 : κ) (x2 : ν) (t2 t3 : Map κ ν) :
    singleL k1 x1 t1 (.bin n k2 x2 t2 t3) = bin k2 x2 (bin k1 x1 t1 t2) t3 :=
  Classical.choose_spec singleLExists k1 x1 t1 n k2 x2 t2 t3

private def singleRSpec {κ ν : Type} (f : κ → ν → Map κ ν → Map κ ν → Map κ ν) : Prop :=
  ∀ k1 x1 n k2 x2 t1 t2 t3, f k1 x1 (.bin n k2 x2 t1 t2) t3 = bin k2 x2 t1 (bin k1 x1 t2 t3)

private theorem singleRExists {κ ν : Type} :
    ∃ f : κ → ν → Map κ ν → Map κ ν → Map κ ν, singleRSpec f := by
  refine ⟨fun k x left right => match left with
    | .bin _ k2 x2 t1 t2 => bin k2 x2 t1 (bin k x t2 right)
    | .tip => .tip, ?_⟩
  intro k1 x1 n k2 x2 t1 t2 t3
  rfl

/-- Whole-function realization of the source specification. No separate HOL
original is claimed for this choice infrastructure; see the tagged equation. -/
noncomputable def singleR {κ ν : Type} : κ → ν → Map κ ν → Map κ ν → Map κ ν :=
  Classical.choose (singleRExists (κ := κ) (ν := ν))

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "singleR_def"]
theorem singleRDef {κ ν : Type} (k1 : κ) (x1 : ν) (n : Nat) (k2 : κ) (x2 : ν) (t1 t2 t3 : Map κ ν) :
    singleR k1 x1 (.bin n k2 x2 t1 t2) t3 = bin k2 x2 t1 (bin k1 x1 t2 t3) :=
  Classical.choose_spec singleRExists k1 x1 n k2 x2 t1 t2 t3

private def doubleLSpec {κ ν : Type} (f : κ → ν → Map κ ν → Map κ ν → Map κ ν) : Prop :=
  ∀ k1 x1 t1 n k2 x2 m k3 x3 t2 t3 t4, f k1 x1 t1 (.bin n k2 x2 (.bin m k3 x3 t2 t3) t4) = bin k3 x3 (bin k1 x1 t1 t2) (bin k2 x2 t3 t4)

private theorem doubleLExists {κ ν : Type} :
    ∃ f : κ → ν → Map κ ν → Map κ ν → Map κ ν, doubleLSpec f := by
  refine ⟨fun k x left right => match right with
    | .bin _ k2 x2 (.bin _ k3 x3 t2 t3) t4 => bin k3 x3 (bin k x left t2) (bin k2 x2 t3 t4)
    | _ => .tip, ?_⟩
  intro k1 x1 t1 n k2 x2 m k3 x3 t2 t3 t4
  rfl

/-- Whole-function realization of the source specification. No separate HOL
original is claimed for this choice infrastructure; see the tagged equation. -/
noncomputable def doubleL {κ ν : Type} : κ → ν → Map κ ν → Map κ ν → Map κ ν :=
  Classical.choose (doubleLExists (κ := κ) (ν := ν))

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "doubleL_def"]
theorem doubleLDef {κ ν : Type} (k1 : κ) (x1 : ν) (t1 : Map κ ν) (n : Nat) (k2 : κ) (x2 : ν) (m : Nat) (k3 : κ) (x3 : ν) (t2 t3 t4 : Map κ ν) :
    doubleL k1 x1 t1 (.bin n k2 x2 (.bin m k3 x3 t2 t3) t4) = bin k3 x3 (bin k1 x1 t1 t2) (bin k2 x2 t3 t4) :=
  Classical.choose_spec doubleLExists k1 x1 t1 n k2 x2 m k3 x3 t2 t3 t4

private def doubleRSpec {κ ν : Type} (f : κ → ν → Map κ ν → Map κ ν → Map κ ν) : Prop :=
  ∀ k1 x1 n k2 x2 t1 m k3 x3 t2 t3 t4, f k1 x1 (.bin n k2 x2 t1 (.bin m k3 x3 t2 t3)) t4 = bin k3 x3 (bin k2 x2 t1 t2) (bin k1 x1 t3 t4)

private theorem doubleRExists {κ ν : Type} :
    ∃ f : κ → ν → Map κ ν → Map κ ν → Map κ ν, doubleRSpec f := by
  refine ⟨fun k x left right => match left with
    | .bin _ k2 x2 t1 (.bin _ k3 x3 t2 t3) => bin k3 x3 (bin k2 x2 t1 t2) (bin k x t3 right)
    | _ => .tip, ?_⟩
  intro k1 x1 n k2 x2 t1 m k3 x3 t2 t3 t4
  rfl

/-- Whole-function realization of the source specification. No separate HOL
original is claimed for this choice infrastructure; see the tagged equation. -/
noncomputable def doubleR {κ ν : Type} : κ → ν → Map κ ν → Map κ ν → Map κ ν :=
  Classical.choose (doubleRExists (κ := κ) (ν := ν))

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "doubleR_def"]
theorem doubleRDef {κ ν : Type} (k1 : κ) (x1 : ν) (n : Nat) (k2 : κ) (x2 : ν) (t1 : Map κ ν) (m : Nat) (k3 : κ) (x3 : ν) (t2 t3 t4 : Map κ ν) :
    doubleR k1 x1 (.bin n k2 x2 t1 (.bin m k3 x3 t2 t3)) t4 = bin k3 x3 (bin k2 x2 t1 t2) (bin k1 x1 t3 t4) :=
  Classical.choose_spec doubleRExists k1 x1 n k2 x2 t1 m k3 x3 t2 t3 t4

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "rotateL_def"]
noncomputable def rotateL {κ ν : Type} (k : κ) (v : ν) (left : Map κ ν) : Map κ ν → Map κ ν
  | .bin n k2 v2 middle right =>
      if size middle < ratio * size right then singleL k v left (.bin n k2 v2 middle right)
      else doubleL k v left (.bin n k2 v2 middle right)
  | .tip => doubleL k v left .tip

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "rotateR_def"]
noncomputable def rotateR {κ ν : Type} (k : κ) (v : ν) (left right : Map κ ν) : Map κ ν :=
  match left with
  | .bin n k2 v2 first middle =>
      if size middle < ratio * size first then singleR k v (.bin n k2 v2 first middle) right
      else doubleR k v (.bin n k2 v2 first middle) right
  | .tip => doubleR k v .tip right

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "bal_def"]
noncomputable def bal {κ ν : Type} (k : κ) (v : ν) (left right : Map κ ν) : Map κ ν :=
  if size left + size right ≤ 1 then .bin (size left + size right + 1) k v left right
  else if size right > delta * size left then rotateL k v left right
  else if size left > delta * size right then rotateR k v left right
  else .bin (size left + size right + 1) k v left right

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "balL_def"]
noncomputable def balL {κ ν : Type} (k : κ) (v : ν) (left right : Map κ ν) : Map κ ν :=
  if size left + size right ≤ 1 then .bin (size left + size right + 1) k v left right
  else if size left > delta * size right then rotateR k v left right
  else .bin (size left + size right + 1) k v left right

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "balR_def"]
noncomputable def balR {κ ν : Type} (k : κ) (v : ν) (left right : Map κ ν) : Map κ ν :=
  if size left + size right ≤ 1 then .bin (size left + size right + 1) k v left right
  else if size right > delta * size left then rotateL k v left right
  else .bin (size left + size right + 1) k v left right

end Flapjack.Misc.BalancedMap
