import Flapjack.Compiler.Backend.ClosKnown.Proofs.Relations
import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic

/-! Value relation for the known-function semantic simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Relations
open ClosSem ClosProps

/-- Inductive closure-value relation for the semantic simulation. It retains
exactly the scalar values, approximation environments and expression-body
requirements of the source relation. This inductive carrier is Flapjack
infrastructure; its source-shaped equations are proved separately. -/
inductive ValueRel (c : Config) (g : Spt ValApprox) : ClosSem.Value → ClosSem.Value → Prop where
  | number (i : Int) : ValueRel c g (.number i) (.number i)
  | word64 (w : BitVec 64) : ValueRel c g (.word64 w) (.word64 w)
  | byteVector (bytes : List (BitVec 8)) : ValueRel c g (.byteVector bytes) (.byteVector bytes)
  | refPtr (flag : Bool) (address : Nat) : ValueRel c g (.refPtr flag address) (.refPtr flag address)
  | block (tag : Nat) (xs ys : List ClosSem.Value) :
      List.Forall₂ (ValueRel c g) xs ys → ValueRel c g (.block tag xs) (.block tag ys)
  | closure (loc : Option Nat) (args1 args2 env1a env1b env2a env2b : List ClosSem.Value)
      (arity : Nat) (e1 e2 : ClosLang.Exp) (aenv : List ValApprox) :
      everyFnVarsNone [e1] → fvMax (arity + env1a.length) [e1] →
      List.Forall₂ (ValueRel c g) args1 args2 → List.Forall₂ (ValueRel c g) env1a env2a →
      List.Forall₂ ValApproxVal aenv env1a →
      expRel c (List.replicate arity .other ++ aenv) g e1 e2 →
      ValueRel c g (.closure loc args1 (env1a ++ env1b) arity e1)
        (.closure loc args2 (env2a ++ env2b) arity e2)
  | recclosure (loc : Option Nat) (args1 args2 env1a env1b env2a env2b : List ClosSem.Value)
      (fns1 fns2 : List (Nat × ClosLang.Exp)) (index : Nat) (aenv : List ValApprox) :
      (∀ f ∈ fns1, everyFnVarsNone [f.2]) →
      (∀ f ∈ fns1, fvMax (f.1 + fns1.length + env1a.length) [f.2]) →
      List.Forall₂ (ValueRel c g) args1 args2 → List.Forall₂ (ValueRel c g) env1a env2a →
      List.Forall₂ ValApproxVal aenv env1a →
      List.Forall₂ (fRel c ((match loc with
        | none => List.replicate fns1.length .other
        | some n => closGenNoInline n 0 fns1) ++ aenv) g) fns1 fns2 →
      ValueRel c g (.recclosure loc args1 (env1a ++ env1b) fns1 index)
        (.recclosure loc args2 (env2a ++ env2b) fns2 index)

/-- Scalar values relate exactly to the same scalar. -/
theorem valueRelNumber (c : Config) (g : Spt ValApprox) (i : Int) (v : ClosSem.Value) :
    ValueRel c g (.number i) v ↔ v = .number i := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst v; exact .number i

/-- Block values preserve their tags and relate their components. -/
theorem valueRelBlock (c : Config) (g : Spt ValApprox) (tag : Nat)
    (xs : List ClosSem.Value) (v : ClosSem.Value) :
    ValueRel c g (.block tag xs) v ↔ ∃ ys, v = .block tag ys ∧ List.Forall₂ (ValueRel c g) xs ys := by
  constructor
  · intro h; cases h with | block _ _ ys rel => exact ⟨ys, rfl, rel⟩
  · rintro ⟨ys, rfl, rel⟩; exact .block tag xs ys rel

/-- Closure relation unfolds to the captured-prefix and body-relation
conditions of the source. -/
theorem valueRelClosure (c : Config) (g : Spt ValApprox) (loc : Option Nat)
    (args1 env1 : List ClosSem.Value) (arity : Nat) (e1 : ClosLang.Exp) (v : ClosSem.Value) :
    ValueRel c g (.closure loc args1 env1 arity e1) v ↔
      everyFnVarsNone [e1] ∧ ∃ aenv env1a env1b args2 env2a env2b e2,
        env1 = env1a ++ env1b ∧ fvMax (arity + env1a.length) [e1] ∧
        List.Forall₂ (ValueRel c g) args1 args2 ∧ List.Forall₂ (ValueRel c g) env1a env2a ∧
        List.Forall₂ ValApproxVal aenv env1a ∧ expRel c (List.replicate arity .other ++ aenv) g e1 e2 ∧
        v = .closure loc args2 (env2a ++ env2b) arity e2 := by
  constructor
  · intro h
    cases h with
    | closure _ _ args2 env1a env1b env2a env2b _ _ e2 aenv none fv args env approx body =>
      exact ⟨none, aenv, env1a, env1b, args2, env2a, env2b, e2, rfl, fv, args, env, approx, body, rfl⟩
  · rintro ⟨none, aenv, env1a, env1b, args2, env2a, env2b, e2, rfl, fv, args, env, approx, body, rfl⟩
    exact .closure loc args1 args2 env1a env1b env2a env2b arity e1 e2 aenv none fv args env approx body

/-- Recursive closures relate pointwise and retain the source captured-prefix
conditions. -/
theorem valueRelRecclosure (c : Config) (g : Spt ValApprox) (loc : Option Nat)
    (args1 env1 : List ClosSem.Value) (fns1 : List (Nat × ClosLang.Exp)) (index : Nat) (v : ClosSem.Value) :
    ValueRel c g (.recclosure loc args1 env1 fns1 index) v ↔
      (∀ f ∈ fns1, everyFnVarsNone [f.2]) ∧
      ∃ aenv env1a env1b args2 env2a env2b fns2,
        env1 = env1a ++ env1b ∧
        (∀ f ∈ fns1, fvMax (f.1 + fns1.length + env1a.length) [f.2]) ∧
        List.Forall₂ (ValueRel c g) args1 args2 ∧ List.Forall₂ (ValueRel c g) env1a env2a ∧
        List.Forall₂ ValApproxVal aenv env1a ∧
        List.Forall₂ (fRel c ((match loc with
          | none => List.replicate fns1.length .other
          | some n => closGenNoInline n 0 fns1) ++ aenv) g) fns1 fns2 ∧
        v = .recclosure loc args2 (env2a ++ env2b) fns2 index := by
  constructor
  · intro h
    cases h with
    | recclosure _ _ args2 env1a env1b env2a env2b _ fns2 _ aenv none fv args env approx fns =>
      exact ⟨none, aenv, env1a, env1b, args2, env2a, env2b, fns2, rfl, fv, args, env, approx, fns, rfl⟩
  · rintro ⟨none, aenv, env1a, env1b, args2, env2a, env2b, fns2, rfl, fv, args, env, approx, fns, rfl⟩
    exact .recclosure loc args1 args2 env1a env1b env2a env2b fns1 fns2 index aenv none fv args env approx fns

/-- The complete source equations for the value relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "v_rel_def" 2619]
theorem valueRelSourceEquations :
    (∀ c g i v, ValueRel c g (.number i) v ↔ v = .number i) ∧
    (∀ c g w v, ValueRel c g (.word64 w) v ↔ v = .word64 w) ∧
    (∀ c g ws v, ValueRel c g (.byteVector ws) v ↔ v = .byteVector ws) ∧
    (∀ c g b n v, ValueRel c g (.refPtr b n) v ↔ v = .refPtr b n) ∧
    (∀ c g n xs v, ValueRel c g (.block n xs) v ↔
      ∃ ys, v = .block n ys ∧ List.Forall₂ (ValueRel c g) xs ys) ∧
    (∀ c g loc args1 env1 arity e1 v, ValueRel c g (.closure loc args1 env1 arity e1) v ↔
      everyFnVarsNone [e1] ∧ ∃ aenv env1a env1b args2 env2a env2b e2,
        env1 = env1a ++ env1b ∧ fvMax (arity + env1a.length) [e1] ∧
        List.Forall₂ (ValueRel c g) args1 args2 ∧ List.Forall₂ (ValueRel c g) env1a env2a ∧
        List.Forall₂ ValApproxVal aenv env1a ∧ expRel c (List.replicate arity .other ++ aenv) g e1 e2 ∧
        v = .closure loc args2 (env2a ++ env2b) arity e2) ∧
    (∀ c g loc args1 env1 fns1 index v, ValueRel c g (.recclosure loc args1 env1 fns1 index) v ↔
      (∀ f ∈ fns1, everyFnVarsNone [f.2]) ∧
      ∃ aenv env1a env1b args2 env2a env2b fns2,
        env1 = env1a ++ env1b ∧
        (∀ f ∈ fns1, fvMax (f.1 + fns1.length + env1a.length) [f.2]) ∧
        List.Forall₂ (ValueRel c g) args1 args2 ∧ List.Forall₂ (ValueRel c g) env1a env2a ∧
        List.Forall₂ ValApproxVal aenv env1a ∧
        List.Forall₂ (fRel c ((match loc with
          | none => List.replicate fns1.length .other
          | some n => closGenNoInline n 0 fns1) ++ aenv) g) fns1 fns2 ∧
        v = .recclosure loc args2 (env2a ++ env2b) fns2 index) := by
  refine ⟨valueRelNumber, ?_, ?_, ?_, valueRelBlock, valueRelClosure, valueRelRecclosure⟩
  · intro c g w v
    constructor
    · intro h; cases h; rfl
    · intro h; subst v; exact .word64 w
  · intro c g ws v
    constructor
    · intro h; cases h; rfl
    · intro h; subst v; exact .byteVector ws
  · intro c g b n v
    constructor
    · intro h; cases h; rfl
    · intro h; subst v; exact .refPtr b n

/-- Application-specific value relation, allowing the source argument
approximations to replace unknown argument approximations for closures. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "v_rel_app_def"]
def valueRelApp (c : Config) (g : Spt ValApprox) (v1 v2 : ClosSem.Value)
    (args : Option (List ClosSem.Value)) : Prop :=
  match v1 with
  | .closure loc pargs1 env1 arity e1 =>
    everyFnVarsNone [e1] ∧ ∃ aenv env1a env1b pargs2 env2a env2b e2 aargs,
      env1 = env1a ++ env1b ∧ fvMax (arity + env1a.length) [e1] ∧
      List.Forall₂ (ValueRel c g) pargs1 pargs2 ∧ List.Forall₂ (ValueRel c g) env1a env2a ∧
      List.Forall₂ ValApproxVal aenv env1a ∧
      (match args with
        | none => aargs = List.replicate arity .other
        | some values => List.Forall₂ ValApproxVal aargs values ∧ pargs1 = []) ∧
      expRel c (aargs ++ aenv) g e1 e2 ∧
      v2 = .closure loc pargs2 (env2a ++ env2b) arity e2
  | _ => ValueRel c g v1 v2

/-- Without argument approximations the application relation is the ordinary
value relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "v_rel_app_NONE"]
theorem valueRelAppNone (c : Config) (g : Spt ValApprox) (v1 v2 : ClosSem.Value) :
    valueRelApp c g v1 v2 none = ValueRel c g v1 v2 := by
  apply propext
  cases v1 with
  | closure loc args env arity body =>
    simp only [valueRelApp, valueRelClosure]
    constructor
    · rintro ⟨safe, aenv, env1a, env1b, args2, env2a, env2b, e2, aargs,
        eq, fv, ar, er, approx, rfl, expr, result⟩
      exact ⟨safe, aenv, env1a, env1b, args2, env2a, env2b, e2, eq, fv, ar, er, approx, expr, result⟩
    · rintro ⟨safe, aenv, env1a, env1b, args2, env2a, env2b, e2, eq, fv, ar, er, approx, expr, result⟩
      exact ⟨safe, aenv, env1a, env1b, args2, env2a, env2b, e2, _, eq, fv, ar, er, approx, rfl, expr, result⟩
  | _ => rfl

/-- Extending the global approximation tree preserves the value relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "v_rel_subspt"]
theorem valueRelSubspt (c : Config) (g : Spt ValApprox) (v1 v2 : ClosSem.Value) (g' : Spt ValApprox)
    (h : ValueRel c g v1 v2 ∧ sptSubspt g g') : ValueRel c g' v1 v2 := by
  obtain ⟨rel, sub⟩ := h
  have listStep : ∀ xs ys, List.Forall₂ (ValueRel c g) xs ys →
      (∀ v ∈ xs, sizeOf v < sizeOf v1) → List.Forall₂ (ValueRel c g') xs ys := by
    intro xs ys hs smaller
    induction hs with
    | nil => exact .nil
    | @cons x y xs ys head tail ih =>
      exact .cons (valueRelSubspt c g x y g' ⟨head, sub⟩)
        (ih (fun v member => smaller v (by simp [member])))
  cases rel with
  | number i => exact .number i
  | word64 w => exact .word64 w
  | byteVector bytes => exact .byteVector bytes
  | refPtr b n => exact .refPtr b n
  | block tag xs ys entries =>
    apply ValueRel.block
    apply listStep xs ys entries
    intro v member
    have bound := List.sizeOf_lt_of_mem member
    simp_wf
    omega
  | closure loc args1 args2 env1a env1b env2a env2b arity e1 e2 aenv safe fv args env approx expr =>
    apply ValueRel.closure loc args1 args2 env1a env1b env2a env2b arity e1 e2 aenv safe fv ?_ ?_ approx
      (expRelSubspt c _ g g' e1 e2 expr sub)
    · apply listStep args1 args2 args
      intro v member
      have bound := List.sizeOf_lt_of_mem member
      simp_wf
      omega
    · apply listStep env1a env2a env
      intro v member
      have inEnv : v ∈ env1a ++ env1b := List.mem_append_left _ member
      have bound := List.sizeOf_lt_of_mem inEnv
      simp_wf
      omega
  | recclosure loc args1 args2 env1a env1b env2a env2b fns1 fns2 index aenv safe fv args env approx fns =>
    apply ValueRel.recclosure loc args1 args2 env1a env1b env2a env2b fns1 fns2 index aenv safe fv ?_ ?_ approx ?_
    · apply listStep args1 args2 args
      intro v member
      have bound := List.sizeOf_lt_of_mem member
      simp_wf
      omega
    · apply listStep env1a env2a env
      intro v member
      have inEnv : v ∈ env1a ++ env1b := List.mem_append_left _ member
      have bound := List.sizeOf_lt_of_mem inEnv
      simp_wf
      omega
    · apply List.Forall₂.imp ?_ fns
      intro f1 f2 rel
      exact ⟨rel.1, expRelSubspt c _ g g' f1.2 f2.2 rel.2 sub⟩
termination_by sizeOf v1
decreasing_by exact smaller x (by simp)

/-- Changing an inline factor in the source value relation preserves it.
This direction is Flapjack induction infrastructure. -/
private theorem valueRelFactorForward (c : Config) (k : Nat) (g : Spt ValApprox)
    (v1 v2 : ClosSem.Value) (rel : ValueRel { c with inlineFactor := k } g v1 v2) : ValueRel c g v1 v2 := by
  have listStep : ∀ xs ys, List.Forall₂ (ValueRel { c with inlineFactor := k } g) xs ys →
      (∀ v ∈ xs, sizeOf v < sizeOf v1) → List.Forall₂ (ValueRel c g) xs ys := by
    intro xs ys hs smaller
    induction hs with
    | nil => exact .nil
    | @cons x y xs ys head tail ih =>
      exact .cons (valueRelFactorForward c k g x y head)
        (ih (fun v member => smaller v (by simp [member])))
  cases rel with
  | number i => exact .number i
  | word64 w => exact .word64 w
  | byteVector bytes => exact .byteVector bytes
  | refPtr b n => exact .refPtr b n
  | block tag xs ys entries =>
    apply ValueRel.block
    apply listStep xs ys entries
    intro v member
    have bound := List.sizeOf_lt_of_mem member
    simp_wf
    omega
  | closure loc args1 args2 env1a env1b env2a env2b arity e1 e2 aenv safe fv args env approx expr =>
    apply ValueRel.closure loc args1 args2 env1a env1b env2a env2b arity e1 e2 aenv safe fv ?_ ?_ approx
      (by simpa [expRelUpdateInlineFactor] using expr)
    · apply listStep args1 args2 args
      intro v member
      have bound := List.sizeOf_lt_of_mem member
      simp_wf
      omega
    · apply listStep env1a env2a env
      intro v member
      have inEnv : v ∈ env1a ++ env1b := List.mem_append_left _ member
      have bound := List.sizeOf_lt_of_mem inEnv
      simp_wf
      omega
  | recclosure loc args1 args2 env1a env1b env2a env2b fns1 fns2 index aenv safe fv args env approx fns =>
    apply ValueRel.recclosure loc args1 args2 env1a env1b env2a env2b fns1 fns2 index aenv safe fv ?_ ?_ approx ?_
    · apply listStep args1 args2 args
      intro v member
      have bound := List.sizeOf_lt_of_mem member
      simp_wf
      omega
    · apply listStep env1a env2a env
      intro v member
      have inEnv : v ∈ env1a ++ env1b := List.mem_append_left _ member
      have bound := List.sizeOf_lt_of_mem inEnv
      simp_wf
      omega
    · simpa [fRelUpdateInlineFactor] using fns
termination_by sizeOf v1
decreasing_by exact smaller x (by simp)

/-- Value relation is independent of the current inline factor. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "v_rel_upd_inline_factor"]
theorem valueRelUpdateInlineFactor (c : Config) (k : Nat) :
    ValueRel { c with inlineFactor := k } = ValueRel c := by
  funext g v1 v2
  apply propext
  constructor
  · exact valueRelFactorForward c k g v1 v2
  · intro rel
    have result := valueRelFactorForward { c with inlineFactor := k } c.inlineFactor g v1 v2 (by simpa using rel)
    exact result

/-- Pointwise value relation is preserved when the approximation tree grows. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "v_rel_LIST_REL_subspt"]
theorem valueRelListSubspt (c : Config) (g : Spt ValApprox) (vs1 vs2 : List ClosSem.Value)
    (h : List.Forall₂ (ValueRel c g) vs1 vs2) (g' : Spt ValApprox) (sub : sptSubspt g g') :
    List.Forall₂ (ValueRel c g') vs1 vs2 :=
  List.Forall₂.imp (fun _ _ rel => valueRelSubspt c g _ _ g' ⟨rel, sub⟩) h

/-- References relate equal byte arrays and pointwise-related value arrays or
thunks. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "ref_rel"]
inductive RefRel (c : Config) (g : Spt ValApprox) : Ref ClosSem.Value → Ref ClosSem.Value → Prop where
  | byteArray (bytes : List (BitVec 8)) : RefRel c g (.byteArray bytes) (.byteArray bytes)
  | valueArray (xs ys : List ClosSem.Value) :
      List.Forall₂ (ValueRel c g) xs ys → RefRel c g (.valueArray xs) (.valueArray ys)
  | thunk (mode : Flapjack.AstHOL.ThunkMode) (v w : ClosSem.Value) :
      ValueRel c g v w → RefRel c g (.thunk mode v) (.thunk mode w)

/-- Reference relation is independent of the current inline factor. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "ref_rel_upd_inline_factor"]
theorem refRelUpdateInlineFactor (c : Config) (k : Nat) :
    RefRel { c with inlineFactor := k } = RefRel c := by
  have relation : ValueRel { c with inlineFactor := k } = ValueRel c := valueRelUpdateInlineFactor c k
  funext g r1 r2
  apply propext
  constructor <;> intro h <;> cases h with
  | byteArray bytes => exact .byteArray bytes
  | valueArray xs ys rel => exact .valueArray xs ys (by simpa [relation] using rel)
  | thunk mode v w rel => exact .thunk mode v w (by simpa [relation] using rel)

/-- Extending the approximation tree preserves the reference relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "ref_rel_subspt"]
theorem refRelSubspt (c : Config) (g : Spt ValApprox) (r1 r2 : Ref ClosSem.Value) (g' : Spt ValApprox)
    (h : RefRel c g r1 r2 ∧ sptSubspt g g') : RefRel c g' r1 r2 := by
  obtain ⟨rel, sub⟩ := h
  cases rel with
  | byteArray bytes => exact .byteArray bytes
  | valueArray xs ys values => exact .valueArray xs ys (valueRelListSubspt c g xs ys values g' sub)
  | thunk mode v w values => exact .thunk mode v w (valueRelSubspt c g v w g' ⟨values, sub⟩)

end Flapjack.Compiler.Backend.ClosKnown.Relations
