module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.FreeVariables
public import Flapjack.Compiler.Backend.ClosAnnotate.Free.OriginalEquivalence
public import Flapjack.Compiler.Backend.ClosAnnotate.Shift.OriginalEquivalence

@[expose] public section

/-! Source-shaped free-variable observation for closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang DbVars

/-- Free-variable traversal and shifting preserve the position of each expression. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "EL_shift_alt_free"]
theorem el_shift_altFree (l m : Nat) (i : Spt Nat) (expressions : List Exp) (index : Nat)
    (bound : index < expressions.length) :
    [@Flapjack.holEl Exp ⟨.var .none 0⟩ index (shiftSource (altFreeSource expressions).1 l m i)] =
      shiftSource (altFreeSource [@Flapjack.holEl Exp ⟨.var .none 0⟩ index expressions]).1 l m i := by
  let : Nonempty Exp := ⟨.var .none 0⟩
  have freeMap : ∀ xs : List Exp, (altFree xs).1 = xs.map (fun x => (altFreeSing x).1) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      change (altFreeList xs).1 = _ at ih
      simp [altFree, altFreeList, ih]
  have shiftMap : ∀ xs : List Exp, shiftList xs l m i = xs.map (fun x => shiftSing x l m i) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [shiftList, ih]
  rw [altFreeSource_eq_altFree, altFreeSource_eq_altFree, shiftSource_eq_shiftList,
    shiftSource_eq_shiftList, freeMap, freeMap, shiftMap, shiftMap]
  simp only [List.map_cons, List.map_nil, Flapjack.holEl_eq_getElem index expressions bound]
  rw [Flapjack.holEl_eq_getElem]
  · simp
  · simpa using bound

/-- Folding paired values separates the payload list from the variable-set fold. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "FOLDR_mk_Union"]
theorem foldr_mkUnion {α : Type} (ys : List (α × DbVarSet))
    (aux : List α) (live : DbVarSet) :
    ys.foldr (fun (x, vars) (tail, frees) => (x :: tail, mkUnion vars frees)) (aux, live) =
      (ys.map Prod.fst ++ aux, (ys.map Prod.snd).foldr mkUnion live) := by
  induction ys with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨x, vars⟩
    simp only [List.foldr_cons, List.map_cons, List.cons_append, ih]

/-- The source free-variable observation uses the original free-variable pass. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "alt_fv_def"]
noncomputable def altFvSource (index : Nat) (expressions : List Exp) : Bool :=
  hasVar index (altFreeSource expressions).2

/-- The free-variable observation reads the second component of the pass. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "alt_free_thm"]
theorem altFreeSource_observation (expressions : List Exp) :
    let (_, live) := altFreeSource expressions
    ∀ index, altFvSource index expressions = hasVar index live := by
  cases result : altFreeSource expressions with
  | mk output live => simp [altFvSource, result]

/-- The optimized observation computes the source free-variable predicate. -/
theorem altFvSource_eq_altFv (index : Nat) (expressions : List Exp) :
    altFvSource index expressions = altFv index expressions := by
  simp [altFvSource, altFv, altFreeSource_eq_altFree]

/-- Free-variable membership in a singleton expression. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "alt_fv1_def"]
noncomputable def altFvOneSource (index : Nat) (expression : Exp) : Bool :=
  altFvSource index [expression]

/-- Singleton observations agree with the single-expression predicate. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "alt_fv1_intro"]
theorem altFvOneSource_intro (index : Nat) (expression : Exp) :
    (altFvSource index [expression] = true ↔ altFvOneSource index expression = true) :=
  Iff.rfl

/-- The empty expression list has no free variables. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "alt_fv_nil"]
theorem altFvSource_nil (index : Nat) : altFvSource index [] = false := by
  rw [altFvSource_eq_altFv, altFv_nil]

/-- Free-variable membership of a list is membership in its head or tail. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "alt_fv_cons"]
theorem altFvSource_cons (index : Nat) (first : Exp) (rest : List Exp) :
    altFvSource index (first :: rest) =
      (altFvOneSource index first || altFvSource index rest) := by
  simp only [altFvOneSource, altFvSource_eq_altFv]
  exact altFv_cons index first rest

/-- Replication has the same free variables as its element when nonempty. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "alt_fv_REPLICATE"]
theorem altFvSource_replicate (index count : Nat) (expression : Exp) :
    altFvSource index (List.replicate count expression) =
      (decide (0 < count) && altFvOneSource index expression) := by
  induction count with
  | zero => simp [altFvSource_nil]
  | succ count ih =>
    rw [List.replicate_succ, altFvSource_cons, ih]
    cases count <;> simp

/-- Source free-variable observations for every closure-language constructor. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "alt_fv"]
theorem altFvSource_equations :
    (∀ n, altFvSource n [] = true ↔ False) ∧
    (∀ (y : Exp) (xs : List Exp) (x : Exp) n,
      altFvSource n (x :: y :: xs) = true ↔ altFvSource n [x] = true ∨ altFvSource n (y :: xs) = true) ∧
    (∀ (trace : BackendCommon.Tra) v n, altFvSource n [.var trace v] = true ↔ n = v) ∧
    (∀ (x3 x2 x1 : Exp) (trace : BackendCommon.Tra) n,
      altFvSource n [.ifThenElse trace x1 x2 x3] = true ↔
      altFvSource n [x1] = true ∨ altFvSource n [x2] = true ∨ altFvSource n [x3] = true) ∧
    (∀ (xs : List Exp) (body : Exp) (trace : BackendCommon.Tra) n,
      altFvSource n [.let trace xs body] = true ↔
      if noOverlap xs.length (altFreeSource [body]).2 = true ∧ ∀ e ∈ xs, pure e = true then
        altFvSource (n + xs.length) [body] = true
      else altFvSource n xs = true ∨ altFvSource (n + xs.length) [body] = true) ∧
    (∀ (body : Exp) (trace : BackendCommon.Tra) n,
      altFvSource n [.raise trace body] = true ↔ altFvSource n [body] = true) ∧
    (∀ (body : Exp) (trace : BackendCommon.Tra) n,
      altFvSource n [.tick trace body] = true ↔ altFvSource n [body] = true) ∧
    (∀ (xs : List Exp) (trace : BackendCommon.Tra) (op : Op) n,
      altFvSource n [.op trace op xs] = true ↔ altFvSource n xs = true) ∧
    (∀ (xs : List Exp) (fn : Exp) (trace : BackendCommon.Tra) n (loc : Option Nat),
      altFvSource n [.app trace loc fn xs] = true ↔ altFvSource n [fn] = true ∨ altFvSource n xs = true) ∧
    (∀ (body : Exp) (vs : Option (List Nat)) (name : Flapjack.Basis.Pure.MlString.MlString) arity n (loc : Option Nat),
      altFvSource n [.fn name loc vs arity body] = true ↔ altFvSource (n + arity) [body] = true) ∧
    (∀ (body : Exp) (vs : Option (List Nat)) (names : List Flapjack.Basis.Pure.MlString.MlString) n (loc : Option Nat)
       (fns : List (Nat × Exp)),
      altFvSource n [.letrec names loc vs fns body] = true ↔
      (∃ arity expr, (arity, expr) ∈ fns ∧ altFvSource (n + arity + fns.length) [expr] = true) ∨
        altFvSource (n + fns.length) [body] = true) ∧
    (∀ (handler body : Exp) (trace : BackendCommon.Tra) n,
      altFvSource n [.handle trace body handler] = true ↔
        altFvSource n [body] = true ∨ altFvSource (n + 1) [handler] = true) ∧
    (∀ (xs : List Exp) (trace : BackendCommon.Tra) ticks n dest,
      altFvSource n [.call trace ticks dest xs] = true ↔ altFvSource n xs = true) := by
  simp only [altFvSource_eq_altFv]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n; simp [altFv_nil]
  · intro y xs x n; rw [altFv_cons]; simp only [Bool.or_eq_true]
  · intros; simp [altFv_var]
  · intros; simp [altFv_if]
  · intro xs body trace n
    rw [altFv_let, altFreeSource_eq_altFree, pureList_eq_all]
    simp only [altFree, Bool.and_eq_true, List.all_eq_true]
    by_cases h : noOverlap xs.length (altFreeList [body]).2 = true
    · by_cases hs : ∀ e ∈ xs, pure e = true <;> simp [h, hs]
    · simp [h]
  · intros; simp [altFv_raise]
  · intros; simp [altFv_tick]
  · intros; simp [altFv_op]
  · intros; simp [altFv_app]
  · intros; simp [altFv_fn]
  · intros; simp [altFv_letrec, List.any_eq_true]
  · intros; simp [altFv_handle]
  · intros; simp [altFv_call]

/-- Singleton free-variable observations for the source constructor equations. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "alt_fv1_thm"]
theorem altFvOneSource_equations :
    (∀ (y : Exp) (xs : List Exp) (x : Exp) n,
      altFvSource n (x :: y :: xs) = true ↔ altFvOneSource n (x) = true ∨ altFvSource n (y :: xs) = true) ∧
    (∀ (trace : BackendCommon.Tra) v n, altFvOneSource n (.var trace v) = true ↔ n = v) ∧
    (∀ (x3 x2 x1 : Exp) (trace : BackendCommon.Tra) n,
      altFvOneSource n (.ifThenElse trace x1 x2 x3) = true ↔
      altFvOneSource n (x1) = true ∨ altFvOneSource n (x2) = true ∨ altFvOneSource n (x3) = true) ∧
    (∀ (xs : List Exp) (body : Exp) (trace : BackendCommon.Tra) n,
      altFvOneSource n (.let trace xs body) = true ↔
      if noOverlap xs.length (altFreeSource [body]).2 = true ∧ ∀ e ∈ xs, pure e = true then
        altFvOneSource (n + xs.length) (body) = true
      else altFvSource n xs = true ∨ altFvOneSource (n + xs.length) (body) = true) ∧
    (∀ (body : Exp) (trace : BackendCommon.Tra) n,
      altFvOneSource n (.raise trace body) = true ↔ altFvOneSource n (body) = true) ∧
    (∀ (body : Exp) (trace : BackendCommon.Tra) n,
      altFvOneSource n (.tick trace body) = true ↔ altFvOneSource n (body) = true) ∧
    (∀ (xs : List Exp) (trace : BackendCommon.Tra) (op : Op) n,
      altFvOneSource n (.op trace op xs) = true ↔ altFvSource n xs = true) ∧
    (∀ (xs : List Exp) (fn : Exp) (trace : BackendCommon.Tra) n (loc : Option Nat),
      altFvOneSource n (.app trace loc fn xs) = true ↔ altFvOneSource n (fn) = true ∨ altFvSource n xs = true) ∧
    (∀ (body : Exp) (vs : Option (List Nat)) (name : Flapjack.Basis.Pure.MlString.MlString) arity n (loc : Option Nat),
      altFvOneSource n (.fn name loc vs arity body) = true ↔ altFvOneSource (n + arity) (body) = true) ∧
    (∀ (body : Exp) (vs : Option (List Nat)) (names : List Flapjack.Basis.Pure.MlString.MlString) n (loc : Option Nat)
       (fns : List (Nat × Exp)),
      altFvOneSource n (.letrec names loc vs fns body) = true ↔
      (∃ arity expr, (arity, expr) ∈ fns ∧ altFvOneSource (n + arity + fns.length) (expr) = true) ∨
        altFvOneSource (n + fns.length) (body) = true) ∧
    (∀ (handler body : Exp) (trace : BackendCommon.Tra) n,
      altFvOneSource n (.handle trace body handler) = true ↔
        altFvOneSource n (body) = true ∨ altFvOneSource (n + 1) (handler) = true) ∧
    (∀ (xs : List Exp) (trace : BackendCommon.Tra) ticks n dest,
      altFvOneSource n (.call trace ticks dest xs) = true ↔ altFvSource n xs = true) := by
  simpa only [altFvOneSource] using altFvSource_equations.2

end Flapjack.Compiler.Backend.ClosAnnotate
