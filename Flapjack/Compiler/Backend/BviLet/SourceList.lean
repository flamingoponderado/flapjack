module

public import Flapjack.Compiler.Backend.BviLet.SourceSing
public import Flapjack.Misc.ListEl

@[expose] public section

/-! The original list-recursive BVI let-propagation compiler. -/
namespace Flapjack.Compiler.Backend.BviLet
open Bvi

/-- Every expression type is inhabited, for HOL's `HD` rendering. -/
instance : Nonempty Exp := ⟨.var 0⟩

/-- Every expression has positive size. -/
theorem one_le_sizeOf_exp (expression : Exp) : 1 ≤ sizeOf expression := by
  cases expression with
  | var v => simp
  | ifThenElse x y z =>
    simp
    all_goals omega
  | «let» xs body =>
    simp
    all_goals omega
  | raise x =>
    simp
    all_goals omega
  | tick x =>
    simp
    all_goals omega
  | call ticks dest xs handler =>
    simp
    all_goals omega
  | force loc v =>
    simp
    all_goals omega
  | op op xs =>
    simp
    all_goals omega
  | letCall rets ticks dest xs body =>
    simp
    all_goals omega
  | «return» xs =>
    simp
    all_goals omega

/-- Dropping the last element does not increase the size. -/
theorem sizeOf_dropLast_le (xs : List Exp) : sizeOf xs.dropLast ≤ sizeOf xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      simp at ih ⊢
      all_goals omega

/-- A member's size is at most the list's size. -/
theorem sizeOf_le_of_mem (xs : List Exp) (expression : Exp) (member : expression ∈ xs) :
    sizeOf expression ≤ sizeOf xs := by
  induction xs with
  | nil => simp at member
  | cons x xs ih =>
    simp only [List.mem_cons] at member
    simp
    rcases member with rfl | member
    · omega
    · have := ih member
      omega

/-- A list's last element is no larger than the list. -/
theorem sizeOf_getLast_le (xs : List Exp) (nonempty : xs ≠ []) :
    sizeOf (xs.getLast nonempty) ≤ sizeOf xs :=
  sizeOf_le_of_mem xs (xs.getLast nonempty) (List.getLast_mem nonempty)

/-- The original list-recursive let optimizer: empty, the multi-element split,
and the per-constructor singleton clauses. -/
@[hol "cakeml/compiler/backend/bvi_letScript.sml" "compile_def"]
noncomputable def compile (env : List Nat) (d : Nat) : List Exp → List Exp
  | [] => []
  | x :: y :: xs => compile env d [x] ++ compile env d (y :: xs)
  | [.var v] =>
      match env[v]? with
      | some n => [.var (v + n)]
      | none => [.var (v + d)]
  | [.ifThenElse x y z] =>
      [.ifThenElse (Flapjack.holHd (compile env d [x]))
        (Flapjack.holHd (compile env d [y])) (Flapjack.holHd (compile env d [z]))]
  | [.«let» xs body] =>
      if hlen : xs.length = 0 then compile env d [body]
      else
        have hne : xs ≠ [] := by
          intro empty
          subst empty
          simp at hlen
        match body with
        | .var v =>
            if v = xs.length - 1 then
              let last := xs.getLast hne
              [.«let» (compile env d xs.dropLast)
                (Flapjack.holHd (compile (env.map ((xs.length - 1) + ·))
                  (d + (xs.length - 1)) [last]))]
            else
              [.«let» ((compile env d xs).map deleteVar)
                (Flapjack.holHd (compile (extractList (compile env d xs) ++ env) d [.var v]))]
        | other =>
            [.«let» ((compile env d xs).map deleteVar)
              (Flapjack.holHd (compile (extractList (compile env d xs) ++ env) d [other]))]
  | [.raise x] => [.raise (Flapjack.holHd (compile env d [x]))]
  | [.op op xs] => [.op op (compile env d xs)]
  | [.tick x] => [.tick (Flapjack.holHd (compile env d [x]))]
  | [.force loc v] =>
      match env[v]? with
      | some n => [.force loc (v + n)]
      | none => [.force loc (v + d)]
  | [.call ticks dest xs handler] =>
      match handler with
      | none => [.call ticks dest (compile env d xs) none]
      | some e => [.call ticks dest (compile env d xs)
          (some (Flapjack.holHd (compile (0 :: env) d [e])))]
  | [.«return» xs] => [.«return» (compile env d xs)]
  | [.letCall rets ticks dest xs body] =>
      [.letCall rets ticks dest (compile env d xs)
        (Flapjack.holHd (compile (List.replicate rets 0 ++ env) d [body]))]
termination_by xs => sizeOf xs
decreasing_by
  all_goals try have := sizeOf_dropLast_le xs
  all_goals try have := sizeOf_getLast_le xs hne
  all_goals try have hx : 1 ≤ sizeOf x := one_le_sizeOf_exp x
  all_goals try have hy : 1 ≤ sizeOf y := one_le_sizeOf_exp y
  all_goals try have hz : 1 ≤ sizeOf z := one_le_sizeOf_exp z
  all_goals try have hbody : 1 ≤ sizeOf body := one_le_sizeOf_exp body
  all_goals try have he : 1 ≤ sizeOf e := one_le_sizeOf_exp e
  all_goals try have hother : 1 ≤ sizeOf other := one_le_sizeOf_exp other
  all_goals simp
  all_goals omega

/-- The original single-expression compiler: the head of the list traversal,
with HOL's impossible-case fallback. -/
@[hol "cakeml/compiler/backend/bvi_letScript.sml" "compile_exp_def"]
noncomputable def compileExp (exp : Exp) : Exp :=
  match compile [] 0 [exp] with
  | y :: _ => y
  | [] => .var 0

/-- The list traversal agrees with the executable single/list rewrites. -/
theorem compile_eq_compileList (env : List Nat) (d : Nat) (xs : List Exp) :
    compile env d xs = compileList env d xs := by
  fun_induction compile env d xs
  all_goals simp_all [compileSing, compileList, Flapjack.holHd]
  case case7 env d xs hne last ih2 ih1 =>
    cases xs with
    | nil => exact absurd rfl hne
    | cons head tail => simp [compileSing, last]
  case case8 env d xs v hne h ih2 ih1 =>
    cases xs with
    | nil => exact absurd rfl hne
    | cons head tail =>
      simp [compileSing, compileList]
      intro hv
      have hlen : (head :: tail).length = tail.length + 1 := by simp
      have hvk : v = (head :: tail).length - 1 := by omega
      exact absurd hvk h
  case case9 env d xs other hne h ih2 ih1 =>
    cases xs with
    | nil => exact absurd rfl hne
    | cons head tail => simp [compileSing, compileList]

/-- HOL's compile_sing theorem: singleton compilation and the list rewrite. -/
@[hol "cakeml/compiler/backend/bvi_letScript.sml" "compile_sing"]
theorem compile_sing :
    (∀ env d e, compile env d [e] = [compileSing env d e]) ∧
    (∀ env d xs, compileList env d xs = compile env d xs) := by
  constructor
  · intro env d e
    have := compile_eq_compileList env d [e]
    simpa [compileList] using this
  · intro env d xs
    exact (compile_eq_compileList env d xs).symm

/-- HOL's compile_exp_eq: the single-expression compiler is the singleton rewrite. -/
@[hol "cakeml/compiler/backend/bvi_letScript.sml" "compile_exp_eq"]
theorem compileExp_eq (exp : Exp) : compileExp exp = compileSing [] 0 exp := by
  have singleton := compile_sing.1 [] 0 exp
  simp [compileExp, singleton]

end Flapjack.Compiler.Backend.BviLet
