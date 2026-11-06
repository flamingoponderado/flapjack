import Flapjack.Compiler.Backend.ClosOp.Proofs.SmartReduction
import Flapjack.Compiler.Backend.Semantics.ClosProps.Globals

/-! Invariants of the source reduction relation and smart operation. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang
open Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.FlatProps (emptyGlobalBag unionGlobalBag)

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem pureListAppend (xs ys : List Exp) : pureList (xs ++ ys) = (pureList xs && pureList ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [pureList, ih, Bool.and_assoc]

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem redPureBool (xs ys : List Exp) (h : RedRel xs ys) :
    (pureList xs = true ↔ pureList ys = true) := by
  induction h with
  | op n xs ys t op iop i tag t1 t2 s w hr hm ih =>
    have hp : pureOp op = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    simp [pureList, ClosLang.pure, hp, ih]
  | nil => simp [pureList]
  | refl x => rfl
  | var v t => simp [pureList, ClosLang.pure]
  | multi x y zs x1 x2 hx hy ihx ihy =>
    simp_all [pureList, pureListAppend, Bool.and_eq_true]
  | letE xs x x1 t hx hy ihx ihy =>
    simp_all [pureList, ClosLang.pure]
  | ite t x y z x1 x2 x3 hx hy hz ihx ihy ihz =>
    simp_all [pureList, pureListAppend, ClosLang.pure, Bool.and_eq_true, and_assoc]

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem pureListIff (xs : List Exp) :
    pureList xs = true ↔ ∀ e ∈ xs, ClosLang.pure e = true := by
  induction xs with
  | nil => simp [pureList]
  | cons x xs ih => simp [pureList, Bool.and_eq_true, ih]

/-- Reduction preserves purity of every expression. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "red_rel_pure"]
theorem redPure (xs ys : List Exp) (h : RedRel xs ys) :
    (∀ e ∈ xs, ClosLang.pure e = true) ↔ (∀ e ∈ ys, ClosLang.pure e = true) := by
  rw [← pureListIff, ← pureListIff]
  exact redPureBool xs ys h

/-- Purity projection used in the combined proof; Flapjack infrastructure without a separate HOL declaration. -/
theorem smartPure (t : BackendCommon.Tra) (op : Op) (xs : List Exp) :
    ClosLang.pure (smartOp t op xs) = ClosLang.pure (.op t op xs) := by
  obtain ⟨ys, h1, h2⟩ := smartRed t op xs
  have a := redPure _ _ h1
  have b := redPure _ _ h2
  simp only [List.mem_singleton, forall_eq] at a b
  have c := b.trans a.symm
  cases hs : ClosLang.pure (smartOp t op xs) <;> cases ho : ClosLang.pure (.op t op xs) <;> simp_all

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem esgcAppend (xs ys : List Exp) :
    esgcFreeList (xs ++ ys) ↔ esgcFreeList xs ∧ esgcFreeList ys := by
  induction xs with
  | nil => simp [esgcFreeList]
  | cons x xs ih => simp [esgcFreeList, ih, and_assoc]

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem redEsgcList (xs ys : List Exp) (h : RedRel xs ys) :
    esgcFreeList xs ↔ esgcFreeList ys := by
  induction h with
  | op n xs ys t op iop i tag t1 t2 s w hr hm ih =>
    simp [esgcFreeList, esgcFree, ih]
  | nil => simp [esgcFreeList]
  | refl x => rfl
  | var v t => simp [esgcFreeList, esgcFree]
  | multi x y zs x1 x2 hx hy ihx ihy =>
    simp_all [esgcFreeList, esgcAppend]
  | letE xs x x1 t hx hy ihx ihy =>
    simp_all [esgcFreeList, esgcFree]
  | ite t x y z x1 x2 x3 hx hy hz ihx ihy ihz =>
    simp_all [esgcFreeList, esgcAppend, esgcFree]

/-- Reduction preserves closure safety of every expression. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "red_rel_esgc_free"]
theorem redEsgc (xs ys : List Exp) (h : RedRel xs ys) :
    (∀ e ∈ xs, esgcFree e) ↔ (∀ e ∈ ys, esgcFree e) := by
  rw [← esgcFreeList_iff, ← esgcFreeList_iff]
  exact redEsgcList xs ys h

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem globalsAppend (xs ys : List Exp) :
    elistGlobals (xs ++ ys) = unionGlobalBag (elistGlobals xs) (elistGlobals ys) := by
  funext k
  induction xs with
  | nil => simp [elistGlobals, emptyGlobalBag, unionGlobalBag]
  | cons x xs ih => simp [elistGlobals, unionGlobalBag, ih, Nat.add_assoc]

/-- Reduction preserves the complete global-write bag. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "red_rel_elist_globals"]
theorem redGlobals (xs ys : List Exp) (h : RedRel xs ys) : elistGlobals xs = elistGlobals ys := by
  induction h with
  | op n xs ys t op iop i tag t1 t2 s w hr hm ih =>
    have hp : opGlobalBag op = emptyGlobalBag := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    funext k
    simp [elistGlobals, setGlobals, hp, emptyGlobalBag, unionGlobalBag, congrFun ih k]
  | nil => rfl
  | refl x => rfl
  | var v t => funext k; simp [elistGlobals, setGlobals, emptyGlobalBag, unionGlobalBag]
  | multi x y zs x1 x2 hx hy ihx ihy =>
    funext k
    have h1 := congrFun ihx k
    have h2 := congrFun ihy k
    simp [elistGlobals, unionGlobalBag, emptyGlobalBag] at h1 h2
    simp [elistGlobals, globalsAppend, unionGlobalBag]
    omega
  | letE xs x x1 t hx hy ihx ihy =>
    funext k
    have h1 := congrFun ihx k
    have h2 := congrFun ihy k
    simp [elistGlobals, unionGlobalBag, emptyGlobalBag] at h2
    simp [elistGlobals, setGlobals, emptyGlobalBag, unionGlobalBag]
    omega
  | ite t x y z x1 x2 x3 hx hy hz ihx ihy ihz =>
    funext k
    have h1 := congrFun ihx k
    have h2 := congrFun ihy k
    have h3 := congrFun ihz k
    simp [elistGlobals, unionGlobalBag, emptyGlobalBag] at h1 h2 h3
    simp [elistGlobals, globalsAppend, setGlobals, emptyGlobalBag, unionGlobalBag]
    omega

/-- Smart operation preserves purity, global writes and closure safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "SmartOp_simp"]
theorem smartSimp (t : BackendCommon.Tra) (op : Op) (xs : List Exp) :
    (ClosLang.pure (smartOp t op xs) = true ↔ ClosLang.pure (.op t op xs) = true) ∧
    setGlobals (smartOp t op xs) = setGlobals (.op t op xs) ∧
    (esgcFree (smartOp t op xs) ↔ esgcFree (.op t op xs)) := by
  obtain ⟨ys,h1,h2⟩ := smartRed t op xs
  have hg := (redGlobals _ _ h2).trans (redGlobals _ _ h1).symm
  have he := (redEsgc _ _ h2).trans (redEsgc _ _ h1).symm
  simp only [List.mem_singleton, forall_eq] at he
  refine ⟨by rw [smartPure t op xs], ?_, he⟩
  funext k
  have hgk := congrFun hg k
  simpa [elistGlobals, unionGlobalBag, emptyGlobalBag] using hgk
end Flapjack.Compiler.Backend.ClosOp
