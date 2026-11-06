import Flapjack.Compiler.Backend.BvlConst.Proofs.ArithmeticMul
/-! Source operation rewrite correctness, including addition and subtraction. -/
namespace Flapjack.Compiler.Backend.BvlConst.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps

/-- Source addition rewrite with a constant right operand. -/
theorem add_const_general {C F : Type} (x : Bvl.Exp) (n : Int)
    (env : List Value) (state final : State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .add) [x, .op (.intOp (.const n)) []]], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .add, x, .op (.intOp (.const n)) [])], env, state) = (result, final) := by
  cases hx : opConst x with
  | none =>
    cases hs : simple x with
    | none =>
      change evaluateTuple ([match opConst x with
        | some (.intOp .add, a, m) => if n + m == 0 then a else .op (.intOp .add) [a, .op (.intOp (.const (n + m))) []]
        | some (.intOp .sub, a, m) => .op (.intOp .sub) [a, .op (.intOp (.const (n + m))) []]
        | some _ => .op (.intOp .add) [x, .op (.intOp (.const n)) []]
        | none => match simple x with
          | some m => .op (.intOp (.const (n + m))) []
          | none => if n == 0 then x else .op (.intOp .add) [x, .op (.intOp (.const n)) []]], env, state) = _
      simp only [hx, hs]
      by_cases hn : n = 0
      · simp only [hn, beq_self_eq_true, ↓reduceIte]
        exact evaluate_add_zero x env state final result (by simpa [hn] using run) notTypeError
      · simpa [hn] using run
    | some m =>
      have ex := (simple_eq x m).1 hs
      subst x
      exact smartOp2_add_constants_correct m n env state final result run notTypeError
  | some v =>
    obtain ⟨op, a, m, rfl, ex⟩ := (opConst_eq x v).1 hx
    subst x
    cases op <;> try (exact run)
    case intOp operation =>
      cases operation <;> try (exact run)
      case add => exact smartOp2_add_nestedAdd_correct a m n env state final result run notTypeError
      case sub => exact smartOp2_add_nestedSub_correct a m n env state final result run notTypeError

/-- Source subtraction rewrite with a constant right operand. -/
theorem sub_const_general {C F : Type} (x : Bvl.Exp) (n : Int)
    (env : List Value) (state final : State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .sub) [x, .op (.intOp (.const n)) []]], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .sub, x, .op (.intOp (.const n)) [])], env, state) = (result, final) := by
  cases hx : opConst x with
  | none =>
    cases hs : simple x with
    | none =>
      change evaluateTuple ([match opConst x with
        | some (.intOp .add, a, m) => .op (.intOp .sub) [a, .op (.intOp (.const (n - m))) []]
        | some (.intOp .sub, a, m) => if n - m == 0 then a else .op (.intOp .add) [a, .op (.intOp (.const (n - m))) []]
        | some _ => .op (.intOp .sub) [x, .op (.intOp (.const n)) []]
        | none => match simple x with
          | some m => .op (.intOp (.const (n - m))) []
          | none => .op (.intOp .sub) [x, .op (.intOp (.const n)) []]], env, state) = _
      simpa [hx, hs] using run
    | some m =>
      have ex := (simple_eq x m).1 hs
      subst x
      exact smartOp2_sub_constants_correct m n env state final result run notTypeError
  | some v =>
    obtain ⟨op, a, m, rfl, ex⟩ := (opConst_eq x v).1 hx
    subst x
    cases op <;> try (exact run)
    case intOp operation =>
      cases operation <;> try (exact run)
      case add => exact smartOp2_sub_nestedAdd_correct a m n env state final result run notTypeError
      case sub => exact smartOp2_sub_nestedSub_correct a m n env state final result run notTypeError

/-- Expose the source add rewrite when the right operand is not simple. -/
theorem add_nonconstant_eq (x y : Bvl.Exp) (hy : simple y = none) :
    smartOp2 (.intOp .add, x, y) =
      match opConst x, opConst y with
      | some (.intOp .add, a, m), some (.intOp .add, b, n) => if n + m == 0 then .op (.intOp .add) [a, b] else .op (.intOp .add) [.op (.intOp .add) [a, b], .op (.intOp (.const (n + m))) []]
      | some (.intOp .add, a, m), some (.intOp .sub, b, n) => .op (.intOp .sub) [.op (.intOp .sub) [a, b], .op (.intOp (.const (n + m))) []]
      | some (.intOp .sub, a, m), some (.intOp .add, b, n) => if n + m == 0 then .op (.intOp .sub) [a, b] else .op (.intOp .add) [.op (.intOp .sub) [a, b], .op (.intOp (.const (n + m))) []]
      | _, _ => .op (.intOp .add) [x, y] := by
  change ((match simple y with
    | some n => match opConst x with
      | some (.intOp .add, a, m) => if n + m == 0 then a else .op (.intOp .add) [a, .op (.intOp (.const (n + m))) []]
      | some (.intOp .sub, a, m) => .op (.intOp .sub) [a, .op (.intOp (.const (n + m))) []]
      | some _ => .op (.intOp .add) [x, y]
      | none => match simple x with
        | some m => .op (.intOp (.const (n + m))) []
        | none => if n == 0 then x else .op (.intOp .add) [x, .op (.intOp (.const n)) []]
    | none => match opConst x, opConst y with
      | some (.intOp .add, a, m), some (.intOp .add, b, n) => if n + m == 0 then .op (.intOp .add) [a, b] else .op (.intOp .add) [.op (.intOp .add) [a, b], .op (.intOp (.const (n + m))) []]
      | some (.intOp .add, a, m), some (.intOp .sub, b, n) => .op (.intOp .sub) [.op (.intOp .sub) [a, b], .op (.intOp (.const (n + m))) []]
      | some (.intOp .sub, a, m), some (.intOp .add, b, n) => if n + m == 0 then .op (.intOp .sub) [a, b] else .op (.intOp .add) [.op (.intOp .sub) [a, b], .op (.intOp (.const (n + m))) []]
      | _, _ => .op (.intOp .add) [x, y]) : Bvl.Exp) = _
  simp only [hy]

/-- Expose the source sub rewrite when the right operand is not simple. -/
theorem sub_nonconstant_eq (x y : Bvl.Exp) (hy : simple y = none) :
    smartOp2 (.intOp .sub, x, y) =
      match opConst x, opConst y with
      | some (.intOp .add, a, m), some (.intOp .add, b, n) => .op (.intOp .add) [.op (.intOp .sub) [a, b], .op (.intOp (.const (n - m))) []]
      | some (.intOp .add, a, m), some (.intOp .sub, b, n) => .op (.intOp .sub) [.op (.intOp .add) [a, b], .op (.intOp (.const (n - m))) []]
      | some (.intOp .sub, a, m), some (.intOp .add, b, n) => if n - m == 0 then .op (.intOp .add) [a, b] else .op (.intOp .add) [.op (.intOp .add) [a, b], .op (.intOp (.const (n - m))) []]
      | _, _ => .op (.intOp .sub) [x, y] := by
  change ((match simple y with
    | some n => match opConst x with
      | some (.intOp .add, a, m) => .op (.intOp .sub) [a, .op (.intOp (.const (n - m))) []]
      | some (.intOp .sub, a, m) => if n - m == 0 then a else .op (.intOp .add) [a, .op (.intOp (.const (n - m))) []]
      | some _ => .op (.intOp .sub) [x, y]
      | none => match simple x with
        | some m => .op (.intOp (.const (n - m))) []
        | none => .op (.intOp .sub) [x, y]
    | none => match opConst x, opConst y with
      | some (.intOp .add, a, m), some (.intOp .add, b, n) => .op (.intOp .add) [.op (.intOp .sub) [a, b], .op (.intOp (.const (n - m))) []]
      | some (.intOp .add, a, m), some (.intOp .sub, b, n) => .op (.intOp .sub) [.op (.intOp .add) [a, b], .op (.intOp (.const (n - m))) []]
      | some (.intOp .sub, a, m), some (.intOp .add, b, n) => if n - m == 0 then .op (.intOp .add) [a, b] else .op (.intOp .add) [.op (.intOp .add) [a, b], .op (.intOp (.const (n - m))) []]
      | _, _ => .op (.intOp .sub) [x, y]) : Bvl.Exp) = _
  simp only [hy]

namespace AddSubCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end AddSubCarrier

/-- The complete add case of the binary source rewrite. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_add_correct {C F : Type} (x y : Bvl.Exp)
    (env : List Value) (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .add) [x, y]], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .add, x, y)], env, state) = (result, final) := by
  cases hy : simple y with
  | some n =>
    have ey := (simple_eq y n).1 hy
    subst y
    exact add_const_general x n env state final result run notTypeError
  | none =>
    rw [add_nonconstant_eq x y hy]
    cases hx : opConst x with
    | none => simpa [hx] using run
    | some v =>
      cases hz : opConst y with
      | none => simpa [hx, hz] using run
      | some w =>
        obtain ⟨ox, a, m, rfl, ex⟩ := (opConst_eq x v).1 hx
        obtain ⟨oy, b, n, rfl, ey⟩ := (opConst_eq y w).1 hz
        subst x
        subst y
        cases ox <;> try (exact run)
        case intOp opx =>
          cases opx <;> try (exact run)
          case add =>
            cases oy <;> try (exact run)
            case intOp opy =>
              cases opy <;> try (exact run)
              case add => exact smartOp2_add_nestedAdd_nestedAdd_correct a b m n env state final result run notTypeError
              case sub => exact smartOp2_add_add_sub_correct a b m n env state final result run notTypeError
          case sub =>
            cases oy <;> try (exact run)
            case intOp opy =>
              cases opy <;> try (exact run)
              case add => exact smartOp2_add_sub_add_correct a b m n env state final result run notTypeError

/-- The complete sub case of the binary source rewrite. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_sub_correct {C F : Type} (x y : Bvl.Exp)
    (env : List Value) (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .sub) [x, y]], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .sub, x, y)], env, state) = (result, final) := by
  cases hy : simple y with
  | some n =>
    have ey := (simple_eq y n).1 hy
    subst y
    exact sub_const_general x n env state final result run notTypeError
  | none =>
    rw [sub_nonconstant_eq x y hy]
    cases hx : opConst x with
    | none => simpa [hx] using run
    | some v =>
      cases hz : opConst y with
      | none => simpa [hx, hz] using run
      | some w =>
        obtain ⟨ox, a, m, rfl, ex⟩ := (opConst_eq x v).1 hx
        obtain ⟨oy, b, n, rfl, ey⟩ := (opConst_eq y w).1 hz
        subst x
        subst y
        cases ox <;> try (exact run)
        case intOp opx =>
          cases opx <;> try (exact run)
          case add =>
            cases oy <;> try (exact run)
            case intOp opy =>
              cases opy <;> try (exact run)
              case add => exact smartOp2_sub_add_add_correct a b m n env state final result run notTypeError
              case sub => exact smartOp2_sub_add_sub_correct a b m n env state final result run notTypeError
          case sub =>
            cases oy <;> try (exact run)
            case intOp opy =>
              cases opy <;> try (exact run)
              case add => exact smartOp2_sub_sub_add_correct a b m n env state final result run notTypeError


/-- Binary source rewrites preserve every non-type-error evaluation and final state. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_correct {C F : Type} (op : ClosLang.Op) (x y : Bvl.Exp)
    (env : List Value) (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op op [x, y]], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (op, x, y)], env, state) = (result, final) := by
  cases op <;> try (exact run)
  case intOp operation =>
    cases operation <;> try (exact run)
    case add => exact smartOp2_add_correct x y env state final result run notTypeError
    case sub => exact smartOp2_sub_correct x y env state final result run notTypeError
    case mult => exact smartOp2_mul_correct x y env state final result run notTypeError
    case div => exact smartOp2_div_correct x y env state final result run notTypeError
    case mod => exact smartOp2_mod_correct x y env state final result run notTypeError
    case less => exact smartOp2_less_correct x y env state final result run notTypeError
    case lessEq => exact smartOp2_lessEq_correct x y env state final result run notTypeError
    case greater => exact smartOp2_greater_correct x y env state final result run notTypeError
    case greaterEq => exact smartOp2_greaterEq_correct x y env state final result run notTypeError
  case blockOp operation =>
    cases operation <;> try (exact run)
    case equal => exact smartOp2_equal_correct x y env state final result run notTypeError
  case memOp operation =>
    cases operation <;> try (exact run)
    case el => exact smartOp2_el_correct x y env state final result run notTypeError


/-- Source operation rewriting preserves every non-type-error evaluation and final state. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp_correct {C F : Type} (op : ClosLang.Op) (xs : List Bvl.Exp)
    (env : List Value) (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op op xs], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp op xs], env, state) = (result, final) := by
  cases xs with
  | nil => exact run
  | cons x tail =>
    cases tail with
    | nil => exact smartOp1_correct op x env state final result run notTypeError
    | cons y rest =>
      cases rest with
      | cons z rest => exact run
      | nil =>
        change evaluateTuple ([smartOp2 (smartOpFlip op x y)], env, state) = _
        rcases h : smartOpFlip op x y with ⟨op', x', y'⟩
        have flipped := smartOpFlip_correct op op' x y x' y' env state final result h.symm run notTypeError
        exact smartOp2_correct op' x' y' env state final result flipped notTypeError

end Flapjack.Compiler.Backend.BvlConst.Proofs
