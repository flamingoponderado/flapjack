module

public import Flapjack.Compiler.Backend.ClosOp.Proofs.SmartFreeVars
public import Flapjack.Compiler.Backend.ClosKnown.Fuel

@[expose] public section

/-! Free-variable bounds used in the known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang ClosProps

/-- Recursive-closure approximations enumerate the input arities in order. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "clos_gen_noinline_eq"]
theorem closGenNoInlineEq {α : Type} (n c : Nat) (fns : List (Nat × α)) :
    closGenNoInline n c fns =
      List.ofFn (fun i : Fin fns.length =>
        ValApprox.closNoInline (2 * (i.val + c) + n) (fns[i.val]'i.isLt).1) := by
  induction fns generalizing c with
  | nil => simp [closGenNoInline]
  | cons head tail ih =>
    cases head with
    | mk arity body =>
      simp [closGenNoInline, List.ofFn_succ, ih, Nat.add_comm, Nat.add_left_comm, Nat.mul_add]

/-- Check a predicate on every variable represented by a shifted set. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "every_var_def"]
def everyVar (P : Nat → Prop) : DbVars.DbVarSet → Prop
  | .empty => True
  | .var v => P v
  | .shift k d => everyVar (fun v => k ≤ v → P (v - k)) d
  | .union d1 d2 => everyVar P d1 ∧ everyVar P d2

/-- The smart union retains exactly the predicates of both inputs. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "every_var_mk_Union"]
theorem everyVarMkUnion (P : Nat → Prop) (d1 d2 : DbVars.DbVarSet) :
    everyVar P (DbVars.mkUnion d1 d2) ↔ everyVar P d1 ∧ everyVar P d2 := by
  cases d1 <;> cases d2 <;> simp [DbVars.mkUnion, everyVar]

/-- Every free de Bruijn index is below the given bound. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "fv_max_def"]
def fvMax (n : Nat) (xs : List ClosLang.Exp) : Prop :=
  ∀ v, freeVars v xs → v < n

/-- Smart operations preserve free-variable bounds. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "fv_max_SmartOp"]
theorem fvMaxSmartOp (n : Nat) (t : BackendCommon.Tra) (op : ClosLang.Op)
    (xs : List ClosLang.Exp) (h : fvMax n [.op t op xs]) :
    fvMax n [ClosOp.smartOp t op xs] := by
  intro v hv
  exact h v (ClosOp.smartFV v t op xs hv)

/-- A free-variable bound distributes over list cons. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "fv_max_cons"]
theorem fvMaxCons (n : Nat) (x : ClosLang.Exp) (xs : List ClosLang.Exp) :
    fvMax n (x :: xs) ↔ fvMax n [x] ∧ fvMax n xs := by
  simp [fvMax, freeVars, or_imp, forall_and]

/-- A free-variable bound distributes over append. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "fv_max_append"]
theorem fvMaxAppend (xs ys : List ClosLang.Exp) (n : Nat) :
    fvMax n (xs ++ ys) ↔ fvMax n xs ∧ fvMax n ys := by
  induction xs with
  | nil => simp [fvMax, freeVars]
  | cons x xs ih =>
    rw [List.cons_append, fvMaxCons n x (xs ++ ys), ih, fvMaxCons n x xs, and_assoc]

/-- Increasing the bound preserves the free-variable condition. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "fv_max_less"]
theorem fvMaxLess (m n : Nat) (xs : List ClosLang.Exp)
    (h : fvMax m xs ∧ m ≤ n) : fvMax n xs := by
  intro v hv
  exact Nat.lt_of_lt_of_le (h.1 v hv) h.2

/-- Shifting a de Bruijn index under binders adjusts its free-variable
bound. This is Flapjack proof infrastructure. -/
private theorem shiftedBound (P : Nat → Prop) (n k : Nat) :
    (∀ v, P (v + k) → v < n) ↔ ∀ v, P v → v < n + k := by
  constructor
  · intro h v hv
    by_cases small : v < k
    · omega
    · have kv : k ≤ v := by omega
      have shifted : P ((v - k) + k) := by simpa only [Nat.sub_add_cancel kv] using hv
      have bound := h (v - k) shifted
      omega
  · intro h v hv
    have bound := h (v + k) hv
    omega

/-- Variable case of the source free-variable bound equations. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "fv_max_rw"]
theorem fvMaxVar (n v : Nat) (t : BackendCommon.Tra) :
    fvMax n [.var t v] ↔ v < n := by
  simp [fvMax, freeVars, freeVarExp]

/-- Let case of the source free-variable bound equations. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "fv_max_rw"]
theorem fvMaxLet (n : Nat) (t : BackendCommon.Tra) (xs : List ClosLang.Exp) (body : ClosLang.Exp) :
    fvMax n [.let t xs body] ↔ fvMax n xs ∧ fvMax (n + xs.length) [body] := by
  simp only [fvMax, freeVars, freeVarExp, or_false, or_imp, forall_and]
  exact and_congr_right (fun _ => shiftedBound (fun v => freeVarExp v body) n xs.length)

/-- Function case of the source free-variable bound equations. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "fv_max_rw"]
theorem fvMaxFn (n arity : Nat) (name : Flapjack.Basis.Pure.MlString.MlString) (loc : Option Nat)
    (vars : Option (List Nat)) (body : ClosLang.Exp) :
    fvMax n [.fn name loc vars arity body] ↔ fvMax (n + arity) [body] := by
  simp only [fvMax, freeVars, freeVarExp, or_false]
  exact shiftedBound (fun v => freeVarExp v body) n arity

/-- Handler case of the source free-variable bound equations. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "fv_max_rw"]
theorem fvMaxHandle (n : Nat) (t : BackendCommon.Tra) (body handler : ClosLang.Exp) :
    fvMax n [.handle t body handler] ↔ fvMax n [body] ∧ fvMax (n + 1) [handler] := by
  simp only [fvMax, freeVars, freeVarExp, or_false, or_imp, forall_and]
  exact and_congr_right (fun _ => shiftedBound (fun v => freeVarExp v handler) n 1)

/-- Recursive-function-group case of the source free-variable bound equations. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "fv_max_rw"]
theorem fvMaxLetrec (n : Nat) (names : List Flapjack.Basis.Pure.MlString.MlString)
    (loc : Option Nat) (vars : Option (List Nat)) (fns : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) :
    fvMax n [.letrec names loc vars fns body] ↔
      (∀ p ∈ fns, fvMax (n + p.1 + fns.length) [p.2]) ∧
      fvMax (n + fns.length) [body] := by
  have group : (∀ v, freeVarFuns v fns.length fns → v < n) ↔
      ∀ p ∈ fns, fvMax (n + p.1 + fns.length) [p.2] := by
    constructor
    · intro bound p member
      simp only [fvMax, freeVars, or_false]
      have shifted := (shiftedBound (fun v => freeVarExp v p.2) n (p.1 + fns.length)).mp
      have h := shifted (by
        intro v hv
        apply bound v
        apply (freeVarFuns_exists v fns.length fns).mpr
        exact ⟨p, member, by simpa [Nat.add_assoc] using hv⟩)
      simpa [Nat.add_assoc] using h
    · intro bound v hv
      obtain ⟨p, member, free⟩ := (freeVarFuns_exists v fns.length fns).mp hv
      have h := bound p member
      simp only [fvMax, freeVars, or_false] at h
      have shifted := (shiftedBound (fun v => freeVarExp v p.2) n (p.1 + fns.length)).mpr
      apply shifted (by simpa [Nat.add_assoc] using h) v
      simpa [Nat.add_assoc] using free
  simp only [fvMax, freeVars, freeVarExp, or_false, or_imp, forall_and]
  simp only [fvMax, freeVars, or_false] at group
  exact and_congr group (shiftedBound (fun v => freeVarExp v body) n fns.length)

/-- The source equations for free-variable bounds over closure syntax. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "fv_max_rw"]
theorem fvMaxRw (n v arity ticks dest : Nat) (tr : BackendCommon.Tra)
    (x y x1 x2 x3 : ClosLang.Exp) (xs : List ClosLang.Exp) (op : ClosLang.Op)
    (lopt loc : Option Nat) (name : Flapjack.Basis.Pure.MlString.MlString)
    (names : List Flapjack.Basis.Pure.MlString.MlString) (vars : Option (List Nat))
    (fns : List (Nat × ClosLang.Exp)) :
    (fvMax n [] ↔ True) ∧
    (fvMax n (x :: y :: xs) ↔ fvMax n [x] ∧ fvMax n (y :: xs)) ∧
    (fvMax n [.var tr v] ↔ v < n) ∧
    (fvMax n [.ifThenElse tr x1 x2 x3] ↔ fvMax n [x1] ∧ fvMax n [x2] ∧ fvMax n [x3]) ∧
    (fvMax n [.let tr xs x1] ↔ fvMax n xs ∧ fvMax (n + xs.length) [x1]) ∧
    (fvMax n [.raise tr x1] ↔ fvMax n [x1]) ∧
    (fvMax n [.tick tr x1] ↔ fvMax n [x1]) ∧
    (fvMax n [.op tr op xs] ↔ fvMax n xs) ∧
    (fvMax n [.app tr lopt x1 xs] ↔ fvMax n [x1] ∧ fvMax n xs) ∧
    (fvMax n [.fn name loc vars arity x1] ↔ fvMax (n + arity) [x1]) ∧
    (fvMax n [.letrec names loc vars fns x1] ↔
      (∀ p ∈ fns, fvMax (n + p.1 + fns.length) [p.2]) ∧ fvMax (n + fns.length) [x1]) ∧
    (fvMax n [.handle tr x1 x2] ↔ fvMax n [x1] ∧ fvMax (n + 1) [x2]) ∧
    (fvMax n [.call tr ticks dest xs] ↔ fvMax n xs) := by
  refine ⟨by simp [fvMax, freeVars], fvMaxCons n x (y :: xs), fvMaxVar n v tr, ?_,
    fvMaxLet n tr xs x1, ?_, ?_, ?_, ?_, fvMaxFn n arity name loc vars x1,
    fvMaxLetrec n names loc vars fns x1, fvMaxHandle n tr x1 x2, ?_⟩ <;>
    simp [fvMax, freeVars, freeVarExp, or_imp, forall_and]

/-- Inserting the source tick sequence preserves free-variable bounds. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "fv_max_mk_Ticks"]
theorem fvMaxTicks (n : Nat) (t : BackendCommon.Tra) (trc i : Nat) (e : ClosLang.Exp) :
    fvMax n [ticks t trc i e] ↔ fvMax n [e] := by
  induction i generalizing trc e with
  | zero => rfl
  | succ i ih =>
    rw [ticks, ih]
    simp [fvMax, freeVars, freeVarExp]

end Flapjack.Compiler.Backend.ClosKnown
