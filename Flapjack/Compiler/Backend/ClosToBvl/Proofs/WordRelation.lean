import Flapjack.Compiler.Backend.ClosToBvl.Proofs.IntegerRelation
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Word

/-! Word primitive correspondence for the closure-to-BVL simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Word-sized values cannot change representation through the value relation. -/
theorem vRel_word64_inv {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {w : BitVec 64} {target : BvlSem.Value} (related : vRel maxApp f refs code (.word64 w) target) :
    target = .word64 w := by
  cases related with
  | word64 => rfl
  | closure _ closure => cases closure
  | partialClosure _ _ _ _ _ added _ closure => cases closure <;> simp [addArgs] at added

def wordPrimitive : ClosSem.Value → Prop
  | .number _ | .word64 _ => True
  | _ => False

/-- Successful word operations consume only numeric or word values. -/
theorem doWordApp_success_args (op : ClosLang.WordOp) (args : List ClosSem.Value)
    (result : ClosSem.Value) (success : ClosSem.doWordApp op args = some result) :
    ∀ value ∈ args, wordPrimitive value := by
  cases op <;> cases args with
  | nil => simp
  | cons a args =>
    cases args with
    | nil =>
      cases a <;> simp_all [ClosSem.doWordApp, ClosSem.doWordAppIntegral, wordPrimitive]
    | cons b args =>
      cases args with
      | nil =>
        cases a <;> simp_all [ClosSem.doWordApp, ClosSem.doWordAppIntegral, wordPrimitive] <;>
          cases b <;> simp_all
      | cons c args =>
        cases args with
        | nil =>
          cases a <;> simp_all [ClosSem.doWordApp, ClosSem.doWordAppIntegral, wordPrimitive] <;>
            cases b <;> simp_all <;>
            cases c <;> simp_all
        | cons d rest => simp [ClosSem.doWordApp, ClosSem.doWordAppIntegral] at success

/-- Source integer and word values share their representations with BVL. -/
def primitiveToBvl : ClosSem.Value → BvlSem.Value
  | .number n => .number n
  | .word64 w => .word64 w
  | _ => .block 0 []

/-- Related primitive argument lists have the canonical BVL representation. -/
theorem related_primitives {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {args : List ClosSem.Value} {targets : List BvlSem.Value}
    (related : List.Forall₂ (vRel maxApp f refs code) args targets)
    (valid : ∀ value ∈ args, wordPrimitive value) : targets = args.map primitiveToBvl := by
  induction related with
  | nil => rfl
  | @cons a b xs ys head tail ih =>
    have validHead := valid a (by simp)
    have validTail : ∀ value ∈ xs, wordPrimitive value := by
      intro value member
      exact valid value (by simp [member])
    have tailEq := ih validTail
    cases a with
    | number n => simp [primitiveToBvl, vRel_number_inv head, tailEq]
    | word64 w => simp [primitiveToBvl, vRel_word64_inv head, tailEq]
    | block | byteVector | refPtr | closure | recclosure => contradiction


/-- Binary 64-bit operations preserve the value relation. -/
theorem wordOp64_related {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (op : BackendCommon.Opw) (a b : BitVec 64) (x y : BvlSem.Value)
    (first : vRel maxApp f refs code (.word64 a) x)
    (second : vRel maxApp f refs code (.word64 b) y) :
    ∃ source target, ClosSem.doWordApp (.wordOpw .w64 op) [.word64 a, .word64 b] = some source ∧
      BvlSem.doWordApp (.wordOpw .w64 op) [x, y] = some target ∧
      vRel maxApp f refs code source target := by
  have := vRel_word64_inv first
  have := vRel_word64_inv second
  subst x; subst y
  exact ⟨_, _, (wordOp64_agree op a b).1, (wordOp64_agree op a b).2, .word64 _⟩

/-- Ternary floating-point operations preserve the value relation under the
shared floating-point model. -/
theorem fpTop_related {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (op : FpTop) (a b c : BitVec 64) (x y z : BvlSem.Value)
    (first : vRel maxApp f refs code (.word64 a) x)
    (second : vRel maxApp f refs code (.word64 b) y)
    (third : vRel maxApp f refs code (.word64 c) z) :
    ∃ source target, ClosSem.doWordApp (.fpTop op) [.word64 a, .word64 b, .word64 c] = some source ∧
      BvlSem.doWordApp (.fpTop op) [x, y, z] = some target ∧
      vRel maxApp f refs code source target := by
  have := vRel_word64_inv first
  have := vRel_word64_inv second
  have := vRel_word64_inv third
  subst x; subst y; subst z
  exact ⟨_, _, rfl, rfl, .word64 _⟩

end Flapjack.Compiler.Backend.ClosToBvl
