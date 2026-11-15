module

public import Flapjack.Compiler.Inference.InferT
public import Flapjack.HOL.Unification.Term

@[expose] public section

/-! Encoding inference types into the original first-order unification terms. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

@[hol "cakeml/compiler/inference/unifyScript.sml" "atom"]
inductive Atom where
  | tcTag : Nat → Atom
  | dbTag : Nat → Atom
  | tappTag : Atom
  | nullTag : Atom
  deriving DecidableEq, Repr

mutual
@[hol "cakeml/compiler/inference/unifyScript.sml" "encode_infer_t_def"]
def encodeInferT : InferT → Term Atom
  | .varDb n => .const (.dbTag n)
  | .app ts tc => .pair (.const .tappTag) (.pair (.const (.tcTag tc)) (encodeInferTs ts))
  | .uvar n => .var n
termination_by t => sizeOf t

@[hol "cakeml/compiler/inference/unifyScript.sml" "encode_infer_t_def"]
def encodeInferTs : List InferT → Term Atom
  | [] => .const .nullTag
  | t :: ts => .pair (encodeInferT t) (encodeInferTs ts)
termination_by ts => sizeOf ts
end

mutual
@[hol "cakeml/compiler/inference/unifyScript.sml" "decode_infer_t_def"]
def decodeInferT : Term Atom → InferT
  | .var n => .uvar n
  | .const (.dbTag n) => .varDb n
  | .pair (.const .tappTag) (.pair (.const (.tcTag tc)) rest) => .app (decodeInferTs rest) tc
  | _ => .uvar 5
termination_by t => sizeOf t

@[hol "cakeml/compiler/inference/unifyScript.sml" "decode_infer_t_def"]
def decodeInferTs : Term Atom → List InferT
  | .const .nullTag => []
  | .pair t ts => decodeInferT t :: decodeInferTs ts
  | _ => []
termination_by ts => sizeOf ts
end

mutual
private theorem decodeEncodeType (t : InferT) : decodeInferT (encodeInferT t) = t := by
  cases t with
  | varDb n => simp [encodeInferT, decodeInferT]
  | uvar n => simp [encodeInferT, decodeInferT]
  | app ts tc => simp [encodeInferT, decodeInferT, decodeEncodeTypes ts]
termination_by sizeOf t

private theorem decodeEncodeTypes (ts : List InferT) : decodeInferTs (encodeInferTs ts) = ts := by
  cases ts with
  | nil => simp [encodeInferTs, decodeInferTs]
  | cons t ts => simp [encodeInferTs, decodeInferTs, decodeEncodeType t, decodeEncodeTypes ts]
termination_by sizeOf ts
end

@[hol "cakeml/compiler/inference/unifyScript.sml" "decode_left_inverse"]
theorem decodeLeftInverse :
    (∀ t, decodeInferT (encodeInferT t) = t) ∧
      (∀ ts, decodeInferTs (encodeInferTs ts) = ts) :=
  ⟨decodeEncodeType, decodeEncodeTypes⟩

@[hol "cakeml/compiler/inference/unifyScript.sml" "encode_infer_t_11"]
theorem encodeInferTInjective :
    (∀ x y, encodeInferT x = encodeInferT y ↔ x = y) ∧
      (∀ xs ys, encodeInferTs xs = encodeInferTs ys ↔ xs = ys) := by
  constructor
  · intro x y
    constructor
    · intro equal
      have decoded := congrArg decodeInferT equal
      simpa only [decodeLeftInverse.1] using decoded
    · intro equal
      cases equal
      rfl
  · intro xs ys
    constructor
    · intro equal
      have decoded := congrArg decodeInferTs equal
      simpa only [decodeLeftInverse.2] using decoded
    · intro equal
      cases equal
      rfl

@[hol "cakeml/compiler/inference/unifyScript.sml" "decode_left_inverse_I"]
theorem decodeLeftInverseI : decodeInferT ∘ encodeInferT = id := by
  funext t
  exact decodeLeftInverse.1 t

@[hol "cakeml/compiler/inference/unifyScript.sml" "encode_eq_var"]
theorem encodeEqVar (n : Nat) (t : InferT) :
    (Term.var n = encodeInferT t ↔ t = .uvar n) ∧
      (encodeInferT t = Term.var n ↔ t = .uvar n) := by
  constructor <;> cases t <;> simp [encodeInferT, eq_comm]

end Flapjack.Compiler.Inference.Unify
