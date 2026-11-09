import Flapjack.Compiler.Backend.ClosOp.Proofs.LiftReduction
import Flapjack.Compiler.Backend.Semantics.ClosProps.FreeVars

/-! Free-variable invariants for source closure lifting. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang ClosProps

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem fvAppend (n : Nat) (xs ys : List Exp) :
    freeVars n (xs ++ ys) ↔ freeVars n xs ∨ freeVars n ys := by
  induction xs with
  | nil => simp [freeVars]
  | cons x xs ih => simp [freeVars, ih, or_assoc]

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem dontFV (x : Exp) (h : dontLift x = true) (n : Nat) : ¬ freeVarExp n x := by
  rcases (dontLiftCharacterization x).mp h with ⟨t,i,rfl⟩ | ⟨t,i,rfl⟩ | ⟨t,s,rfl⟩ | ⟨t,i,rfl⟩ | ⟨t,w,rfl⟩ <;>
    simp [freeVarExp, freeVars]

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem consFV (x : Exp) (tag : Nat) (ys : List Exp)
    (h : cons x = some (tag,ys)) (l : Nat) : freeVarExp l x ↔ freeVars l ys := by
  rw [destOpCons_eq_previous] at h
  cases x <;> try simp at h
  case op t op args =>
    cases op <;> try simp at h
    case blockOp op =>
      cases op <;> try simp at h
      case cons tag2 => obtain ⟨rfl,rfl⟩ := h; rfl

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem liftFV (xs : List Exp) (n : Nat) (binds : List Exp)
    (hn : n = binds.length) :
    (∀ l, freeVars l (liftExpsHOL xs n binds).2.2 → freeVars l xs ∨ freeVars l binds) ∧
    (∀ l, freeVars l (liftExpsHOL xs n binds).1 → l < (liftExpsHOL xs n binds).2.1) := by
  fun_induction liftExpsHOL xs n binds <;> simp_all [freeVars]
  case case2 =>
    rename_i x xs n binds hd xs1 n1 binds1 hx ih
    constructor
    · intro l hv
      rcases ih.1 l hv with hv | hv
      · exact Or.inl (Or.inr hv)
      · exact Or.inr hv
    · intro l hv
      rcases hv with hv | hv
      · exact False.elim (dontFV x hd l hv)
      · exact ih.2 l hv
  case case3 =>
    rename_i x xs n binds tag ys ys1 n1 binds1 xs1 n2 binds2 hd hc hy hx ihy ihx
    have hidx : n1 = binds1.length := liftExpsN ys binds.length binds ys1 n1 binds1 ⟨hy,rfl⟩
    have ihx := ihx hidx
    rw [← hidx, hx] at ihx
    obtain ⟨p,hp⟩ := liftExpsAcc xs n1 binds1 xs1 n2 binds2 hx
    have hidx2 : n2 = binds2.length := liftExpsN xs n1 binds1 xs1 n2 binds2 ⟨hx,hidx⟩
    have hle : n1 ≤ n2 := by rw [hidx2,hp,List.length_append] at *; omega
    constructor
    · intro l hv
      rcases ihx.1 l hv with hv | hv
      · exact Or.inl (Or.inr hv)
      · rcases ihy.1 l hv with hv | hv
        · exact Or.inl (Or.inl ((consFV x tag ys hc l).mpr hv))
        · exact Or.inr hv
    · intro l hv
      rcases hv with hv | hv
      · have hy1 : freeVars l ys1 := by simpa [freeVarExp] using hv
        exact Nat.lt_of_lt_of_le (ihy.2 l hy1) hle
      · exact ihx.2 l hv
  case case4 =>
    rename_i x xs n binds xs1 n1 binds1 hd hc hx ih
    obtain ⟨p,hp⟩ := liftExpsAcc xs (binds.length + 1) (binds ++ [x]) xs1 n1 binds1 hx
    have hidx : n1 = binds1.length := liftExpsN xs (binds.length + 1) (binds ++ [x]) xs1 n1 binds1 ⟨hx,by simp⟩
    have hlt : binds.length < n1 := by rw [hidx,hp]; simp
    constructor
    · intro l hv
      rcases ih.1 l hv with hv | hv
      · exact Or.inl (Or.inr hv)
      · rw [fvAppend] at hv
        simp only [freeVars, or_false] at hv
        rcases hv with hv | hv
        · exact Or.inr hv
        · exact Or.inl (Or.inl hv)
    · intro l hv
      rcases hv with hv | hv
      · simp only [freeVarExp] at hv
        omega
      · exact ih.2 l hv

/-- Source lifting preserves free-variable origins and bounds fresh indices. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "lift_exps_fv"]
theorem liftExpsFV (xs : List Exp) (n : Nat) (binds ys : List Exp) (k : Nat) (binds2 : List Exp)
    (h : liftExpsHOL xs n binds = (ys,k,binds2) ∧ n = binds.length) :
    k = binds2.length ∧
      (∀ l, freeVars l binds2 → freeVars l xs ∨ freeVars l binds) ∧
      (∀ l, freeVars l ys → l < k) := by
  have inv := liftFV xs n binds h.2
  rw [h.1] at inv
  exact ⟨liftExpsN xs n binds ys k binds2 h, inv⟩

/-- A source conjunction has exactly its input free variables. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "fv1_ConjList"]
theorem freeVarConjList (n : Nat) (xs : List Exp) :
    freeVar n (conjList xs) ↔ freeVars n xs := by
  induction xs with
  | nil => simp [conjList, mkBool, freeVar, freeVarExp, freeVars]
  | cons x xs ih =>
    cases xs with
    | nil => simp [conjList, freeVar, freeVars]
    | cons y zs =>
      simp only [conjList, freeVar, freeVars, freeVarExp] at ih ⊢
      simp [mkBool, freeVars, freeVarExp, ih]
end Flapjack.Compiler.Backend.ClosOp
