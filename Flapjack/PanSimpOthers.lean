import Flapjack.Pancake.PanSimp
import Flapjack.Pancake.Proofs.PanSimp.Evaluate

namespace Flapjack

/-! Counterpart of Cake's `compile_Others_tac` simple cases
    (`cakeml/pancake/proofs/pan_simpProofScript.sml:667-1015`): `pan_simp`
    leaves a fixed family of program constructs syntactically unchanged, so
    the compiled program evaluates exactly as the source program. -/

/-- `compile_Others` evaluation preservation: whenever `panSimpProg` leaves a
    program unchanged, the compiled program evaluates exactly as the source
    program. -/
theorem evalPanValueFfiClockProg_eq_of_panSimpProg_eq
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (program : Prog α) (h : panSimpProg program = program) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
        (panSimpProg program) =
      evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
        program := by
  rw [h]

end Flapjack
