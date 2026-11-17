module

public import Flapjack.Compiler.Backend.BviTailrec.Proofs.ScanCorrespondence
public import Flapjack.Misc.ListEl

@[expose] public section

namespace Flapjack.Compiler.Backend.BviTailrec

local instance : Nonempty ValueType := ⟨.any⟩

/-- An in-bounds context entry after an optional index refinement. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "try_update_EL"]
theorem tryUpdate_el (n : Nat) (ts : List ValueType) (ty : ValueType) (idx : Option Nat)
    (bound : n < ts.length) :
    holEl n (tryUpdate ty idx ts) =
      match idx with
      | none => holEl n ts
      | some m => if n < m then holEl n ts else if n > m then holEl n ts
        else if holEl n ts = .any ∨ holEl n ts = ty then ty else holEl n ts := by
  cases idx with
  | none => rfl
  | some m =>
    by_cases hm : m < ts.length
    · have lookup : ts[m]? = some (holEl m ts) := by
        rw [holEl_eq_getElem m ts hm, List.getElem?_eq_getElem hm]
      have beqInt : (some ValueType.int == some ValueType.any) = false := rfl
      have beqList : (some ValueType.list == some ValueType.any) = false := rfl
      have beqAny : (some ValueType.any == some ValueType.any) = true := rfl
      by_cases same : n = m
      · subst n
        cases hc : holEl m ts <;> cases ty <;>
          simp [tryUpdate, lookup, hc, holEl_set ts m m _ hm, beqInt, beqList, beqAny]
      · have neq : m ≠ n := Ne.symm same
        by_cases lt : n < m
        · cases hc : holEl m ts <;> cases ty <;>
            simp [tryUpdate, lookup, hc, holEl_set ts m n _ hm, neq, lt, beqInt, beqList, beqAny]
        · have gt : m < n := by omega
          cases hc : holEl m ts <;> cases ty <;>
            simp [tryUpdate, lookup, hc, holEl_set ts m n _ hm, neq, lt, gt, beqInt, beqList, beqAny]
    · have lookup : ts[m]? = none := List.getElem?_eq_none (by omega)
      have lt : n < m := by omega
      simp [tryUpdate, lookup, lt]

/-- The result of refining two optional indices at an in-bounds entry. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "try_update_twice"]
theorem tryUpdate_twice (n : Nat) (ts : List ValueType) (ty : ValueType)
    (idx1 idx2 : Option Nat) (bound : n < ts.length) :
    holEl n (tryUpdate ty idx1 (tryUpdate ty idx2 ts)) =
      match idx1, idx2 with
      | none, none => holEl n ts
      | none, some b => if n ≠ b then holEl n ts else if holEl n ts = .any then ty else holEl n ts
      | some a, none => if n ≠ a then holEl n ts else if holEl n ts = .any then ty else holEl n ts
      | some a, some b => if n ≠ a ∧ n ≠ b then holEl n ts
        else if holEl n ts = .any then ty else holEl n ts := by
  have bound2 : n < (tryUpdate ty idx2 ts).length := by simpa [tryUpdate_length] using bound
  rw [tryUpdate_el n (tryUpdate ty idx2 ts) ty idx1 bound2]
  rw [tryUpdate_el n ts ty idx2 bound]
  cases idx1 <;> cases idx2 <;> simp only [tryUpdate_length] at *
  all_goals repeat' (split <;> simp_all <;> try omega)
  all_goals grind

/-- An expression has an index precisely when it is that variable. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "index_of_simp"]
theorem indexOf_simp (exp : Bvi.Exp) (n : Nat) : indexOf exp = some n ↔ exp = .var n := by
  cases exp <;> simp [indexOf]

end Flapjack.Compiler.Backend.BviTailrec
