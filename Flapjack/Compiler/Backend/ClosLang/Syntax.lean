module

public import Flapjack.AstHOL.BackendOperators
public import Flapjack.Basis.Pure.MlString
public import Flapjack.Compiler.Backend.BackendCommon.Trace
public import Flapjack.Compiler.Backend.BackendCommon.Operators
public import Flapjack.FpSemHOL

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Flapjack.Compiler.Backend.ClosLang

open Flapjack.Basis.Pure.MlString

/-! Complete source syntax carriers. HOL word64 payloads are fixed BitVec 64,
not a variable-width substitute. All names use native MlString. FP payloads
are the exact operation enums, without importing an evaluator into the syntax.
Lists retain their literal order and recursive payloads, including Letrec pairs. -/

/-- Complete original `const` datatype, preserving every constructor and payload. -/
@[hol "cakeml/compiler/backend/closLangScript.sml" "const"]
inductive Const where
  | constCons : Nat → List Const → Const
  | constInt : Int → Const
  | constStr : MlString → Const
  | constWord64 : BitVec 64 → Const
/-! The nested syntax needs explicit terminating comparisons: Lean’s derived
comparison for nested inductives is opaque to the kernel. These comparisons and
their laws are Flapjack infrastructure, with no separate HOL declarations. -/
mutual
 private def constEq : Const → Const → Bool
 | .constCons a xs, .constCons b ys => a == b && constListEq xs ys
 | .constInt a, .constInt b => a == b
 | .constStr a, .constStr b => a == b
 | .constWord64 a, .constWord64 b => a == b
 | _, _ => false
 termination_by x _ => sizeOf x
 decreasing_by all_goals simp_wf <;> omega
 private def constListEq : List Const → List Const → Bool
 | [], [] => true
 | a :: xs, b :: ys => constEq a b && constListEq xs ys
 | _, _ => false
 termination_by x _ => sizeOf x
 decreasing_by all_goals simp_wf <;> omega
end
mutual
 /-- Reflexivity of Flapjack's constant comparison; this instance proof has no
 separate HOL declaration. -/
 private theorem constEq_refl : ∀ a : Const, constEq a a = true
 | .constCons n xs => by simp [constEq, constListEq_refl xs]
 | .constInt n => by simp [constEq]
 | .constStr n => by simp [constEq]
 | .constWord64 n => by simp [constEq]
 termination_by a => sizeOf a
 decreasing_by all_goals simp_wf <;> omega
 /-- List case of the Flapjack constant-comparison reflexivity proof. -/
 private theorem constListEq_refl : ∀ a : List Const, constListEq a a = true
 | [] => by simp [constListEq]
 | x :: xs => by simp [constListEq, constEq_refl x, constListEq_refl xs]
 termination_by a => sizeOf a
 decreasing_by all_goals simp_wf <;> omega
end
mutual
 /-- Soundness of Flapjack's constant comparison; this instance proof has no
 separate HOL declaration. -/
 private theorem constEq_sound : ∀ a b : Const, constEq a b = true → a = b
 | .constCons n xs, .constCons m ys, h => by
   simp only [constEq, Bool.and_eq_true, beq_iff_eq] at h
   simp [h.1, constListEq_sound xs ys h.2]
 | .constInt n, .constInt m, h => by simpa [constEq] using h
 | .constStr n, .constStr m, h => by simpa [constEq] using h
 | .constWord64 n, .constWord64 m, h => by simpa [constEq] using h
 | .constCons .., .constInt .., h => by simp [constEq] at h
 | .constCons .., .constStr .., h => by simp [constEq] at h
 | .constCons .., .constWord64 .., h => by simp [constEq] at h
 | .constInt .., .constCons .., h => by simp [constEq] at h
 | .constInt .., .constStr .., h => by simp [constEq] at h
 | .constInt .., .constWord64 .., h => by simp [constEq] at h
 | .constStr .., .constCons .., h => by simp [constEq] at h
 | .constStr .., .constInt .., h => by simp [constEq] at h
 | .constStr .., .constWord64 .., h => by simp [constEq] at h
 | .constWord64 .., .constCons .., h => by simp [constEq] at h
 | .constWord64 .., .constInt .., h => by simp [constEq] at h
 | .constWord64 .., .constStr .., h => by simp [constEq] at h
 termination_by a _ _ => sizeOf a
 decreasing_by all_goals simp_wf <;> omega
 /-- List case of the Flapjack constant-comparison soundness proof. -/
 private theorem constListEq_sound : ∀ a b : List Const, constListEq a b = true → a = b
 | [], [], _ => rfl
 | _ :: _, [], h => by simp [constListEq] at h
 | [], _ :: _, h => by simp [constListEq] at h
 | x :: xs, y :: ys, h => by
   simp only [constListEq, Bool.and_eq_true] at h
   simp [constEq_sound x y h.1, constListEq_sound xs ys h.2]
 termination_by a _ _ => sizeOf a
 decreasing_by all_goals simp_wf <;> omega
end

instance : BEq Const := ⟨constEq⟩
instance : ReflBEq Const := ⟨constEq_refl _⟩
instance : LawfulBEq Const := ⟨constEq_sound _ _⟩

/-- Complete original `const_part` datatype, preserving every constructor and payload. -/
@[hol "cakeml/compiler/backend/closLangScript.sml" "const_part"]
inductive ConstPart where
  | con : Nat → List Nat → ConstPart
  | int : Int → ConstPart
  | str : MlString → ConstPart
  | w64 : BitVec 64 → ConstPart
  deriving DecidableEq

/-- Complete original `int_op` datatype, preserving every constructor and payload. -/
@[hol "cakeml/compiler/backend/closLangScript.sml" "int_op"]
inductive IntOp where
  | const : Int → IntOp
  | add
  | sub
  | mult
  | div
  | mod
  | less
  | lessEq
  | greater
  | greaterEq
  | lessConstSmall : Nat → IntOp
  deriving BEq, ReflBEq, LawfulBEq

/-- Complete original `word_op` datatype, preserving every constructor and payload. -/
@[hol "cakeml/compiler/backend/closLangScript.sml" "word_op"]
inductive WordOp where
  | wordOpw : AstHOL.WordSize → BackendCommon.Opw → WordOp
  | wordShift : AstHOL.WordSize → Shift → Nat → WordOp
  | wordTest : AstHOL.WordSize → AstHOL.Test → WordOp
  | wordFromInt
  | wordToInt
  | wordFromWord : Bool → WordOp
  | fpCmp : FpCmp → WordOp
  | fpUop : FpUop → WordOp
  | fpBop : FpBop → WordOp
  | fpTop : FpTop → WordOp
  deriving BEq, ReflBEq, LawfulBEq

/-- Complete original `block_op` datatype, preserving every constructor and payload. -/
@[hol "cakeml/compiler/backend/closLangScript.sml" "block_op"]
inductive BlockOp where
  | cons : Nat → BlockOp
  | elemAt : Nat → BlockOp
  | tagLenEq : Nat → Nat → BlockOp
  | lenEq : Nat → BlockOp
  | tagEq : Nat → BlockOp
  | lengthBlock
  | boolTest : AstHOL.Test → BlockOp
  | boolNot
  | boundsCheckBlock
  | consExtend : Nat → BlockOp
  | fromList : Nat → BlockOp
  | listAppend
  | constant : Const → BlockOp
  | equal
  | equalConst : ConstPart → BlockOp
  | build : List ConstPart → BlockOp
  deriving BEq, ReflBEq, LawfulBEq

/-- Complete original `glob_op` datatype, preserving every constructor and payload. -/
@[hol "cakeml/compiler/backend/closLangScript.sml" "glob_op"]
inductive GlobOp where
  | global : Nat → GlobOp
  | setGlobal : Nat → GlobOp
  | allocGlobal
  | globalsPtr
  | setGlobalsPtr
  deriving BEq, ReflBEq, LawfulBEq

/-- Complete original `mem_op` datatype, preserving every constructor and payload. -/
@[hol "cakeml/compiler/backend/closLangScript.sml" "mem_op"]
inductive MemOp where
  | ref
  | update
  | el
  | length
  | lengthByte
  | refByte : Bool → MemOp
  | refArray
  | derefByte
  | updateByte
  | concatByteVec
  | copyByte : Bool → MemOp
  | fromListByte
  | toListByte
  | lengthByteVec
  | derefByteVec
  | stringCmp : Bool → Opb → MemOp
  | xorByte
  | boundsCheckArray
  | boundsCheckByte : Bool → MemOp
  | mutCons : Nat → Nat → MemOp
  | updateCons
  | finaliseCons
  | configGC
  deriving BEq, ReflBEq, LawfulBEq

/-- Complete original `op` datatype, preserving every constructor and payload. -/
@[hol "cakeml/compiler/backend/closLangScript.sml" "op"]
inductive Op where
  | label : Nat → Op
  | ffi : MlString → Op
  | intOp : IntOp → Op
  | wordOp : WordOp → Op
  | blockOp : BlockOp → Op
  | globOp : GlobOp → Op
  | memOp : MemOp → Op
  | install
  | thunkOp : AstHOL.ThunkOp → Op
  deriving BEq, ReflBEq, LawfulBEq

/-- Complete original `exp` datatype, preserving every constructor and payload. -/
@[hol "cakeml/compiler/backend/closLangScript.sml" "exp"]
inductive Exp where
  | var : BackendCommon.Tra → Nat → Exp
  | ifThenElse : BackendCommon.Tra → Exp → Exp → Exp → Exp
  | «let» : BackendCommon.Tra → List Exp → Exp → Exp
  | raise : BackendCommon.Tra → Exp → Exp
  | handle : BackendCommon.Tra → Exp → Exp → Exp
  | tick : BackendCommon.Tra → Exp → Exp
  | call : BackendCommon.Tra → Nat → Nat → List Exp → Exp
  | app : BackendCommon.Tra → Option Nat → Exp → List Exp → Exp
  | fn : MlString → Option Nat → Option (List Nat) → Nat → Exp → Exp
  | letrec : List MlString → Option Nat → Option (List Nat) → List (Nat × Exp) → Exp → Exp
  | op : BackendCommon.Tra → Op → List Exp → Exp


/-! As for constants, the expression comparison below is total and its
reflexivity and soundness provide a kernel-checked `LawfulBEq` instance. -/
mutual
private def expEq : Exp → Exp → Bool
  | .var a0 a1, .var b0 b1 => (a0 == b0) && (a1 == b1)
  | .ifThenElse a0 a1 a2 a3, .ifThenElse b0 b1 b2 b3 => (a0 == b0) && expEq a1 b1 && expEq a2 b2 && expEq a3 b3
  | .«let» a0 a1 a2, .«let» b0 b1 b2 => (a0 == b0) && expListEq a1 b1 && expEq a2 b2
  | .raise a0 a1, .raise b0 b1 => (a0 == b0) && expEq a1 b1
  | .handle a0 a1 a2, .handle b0 b1 b2 => (a0 == b0) && expEq a1 b1 && expEq a2 b2
  | .tick a0 a1, .tick b0 b1 => (a0 == b0) && expEq a1 b1
  | .call a0 a1 a2 a3, .call b0 b1 b2 b3 => (a0 == b0) && (a1 == b1) && (a2 == b2) && expListEq a3 b3
  | .app a0 a1 a2 a3, .app b0 b1 b2 b3 => (a0 == b0) && (a1 == b1) && expEq a2 b2 && expListEq a3 b3
  | .fn a0 a1 a2 a3 a4, .fn b0 b1 b2 b3 b4 => (a0 == b0) && (a1 == b1) && (a2 == b2) && (a3 == b3) && expEq a4 b4
  | .letrec a0 a1 a2 a3 a4, .letrec b0 b1 b2 b3 b4 => (a0 == b0) && (a1 == b1) && (a2 == b2) && expFnsEq a3 b3 && expEq a4 b4
  | .op a0 a1 a2, .op b0 b1 b2 => (a0 == b0) && (a1 == b1) && expListEq a2 b2
  | _, _ => false
termination_by a _ => sizeOf a
decreasing_by all_goals simp_wf <;> omega
private def expListEq : List Exp → List Exp → Bool
  | [], [] => true
  | a :: xs, b :: ys => expEq a b && expListEq xs ys
  | _, _ => false
termination_by a _ => sizeOf a
decreasing_by all_goals simp_wf <;> omega
private def expFnsEq : List (Nat × Exp) → List (Nat × Exp) → Bool
  | [], [] => true
  | (n, a) :: xs, (m, b) :: ys => (n == m) && expEq a b && expFnsEq xs ys
  | _, _ => false
termination_by a _ => sizeOf a
decreasing_by all_goals simp_wf <;> omega
end
mutual
/-- Reflexivity of Flapjack's expression comparison; this instance proof has
no separate HOL declaration. -/
private theorem expEq_refl : ∀ a : Exp, expEq a a = true
  | .var a0 a1 => by simp [expEq]
  | .ifThenElse a0 a1 a2 a3 => by simp [expEq , expEq_refl a1, expEq_refl a2, expEq_refl a3]
  | .«let» a0 a1 a2 => by simp [expEq , expListEq_refl a1, expEq_refl a2]
  | .raise a0 a1 => by simp [expEq , expEq_refl a1]
  | .handle a0 a1 a2 => by simp [expEq , expEq_refl a1, expEq_refl a2]
  | .tick a0 a1 => by simp [expEq , expEq_refl a1]
  | .call a0 a1 a2 a3 => by simp [expEq , expListEq_refl a3]
  | .app a0 a1 a2 a3 => by simp [expEq , expEq_refl a2, expListEq_refl a3]
  | .fn a0 a1 a2 a3 a4 => by simp [expEq , expEq_refl a4]
  | .letrec a0 a1 a2 a3 a4 => by simp [expEq , expFnsEq_refl a3, expEq_refl a4]
  | .op a0 a1 a2 => by simp [expEq , expListEq_refl a2]
termination_by a => sizeOf a
decreasing_by all_goals simp_wf <;> omega
/-- Expression-list case of the Flapjack comparison reflexivity proof. -/
private theorem expListEq_refl : ∀ a : List Exp, expListEq a a = true
  | [] => by simp [expListEq]
  | x :: xs => by simp [expListEq, expEq_refl x, expListEq_refl xs]
termination_by a => sizeOf a
decreasing_by all_goals simp_wf <;> omega
/-- Recursive-function-list case of the Flapjack comparison reflexivity proof. -/
private theorem expFnsEq_refl : ∀ a : List (Nat × Exp), expFnsEq a a = true
  | [] => by simp [expFnsEq]
  | (n, x) :: xs => by simp [expFnsEq, expEq_refl x, expFnsEq_refl xs]
termination_by a => sizeOf a
decreasing_by all_goals simp_wf <;> omega
end
mutual
/-- Soundness of Flapjack's expression comparison; this instance proof has no
separate HOL declaration. -/
private theorem expEq_sound : ∀ a b : Exp, expEq a b = true → a = b
  | .var a0 a1, .var b0 b1, h => by
    simp only [expEq, Bool.and_eq_true, beq_iff_eq] at h
    simp_all
  | .ifThenElse a0 a1 a2 a3, .ifThenElse b0 b1 b2 b3, h => by
    simp only [expEq, Bool.and_eq_true, beq_iff_eq] at h
    have h_a1 : expEq a1 b1 = true := by grind
    have eq_a1 := expEq_sound a1 b1 h_a1
    have h_a2 : expEq a2 b2 = true := by grind
    have eq_a2 := expEq_sound a2 b2 h_a2
    have h_a3 : expEq a3 b3 = true := by grind
    have eq_a3 := expEq_sound a3 b3 h_a3
    simp_all
  | .«let» a0 a1 a2, .«let» b0 b1 b2, h => by
    simp only [expEq, Bool.and_eq_true, beq_iff_eq] at h
    have h_a1 : expListEq a1 b1 = true := by grind
    have eq_a1 := expListEq_sound a1 b1 h_a1
    have h_a2 : expEq a2 b2 = true := by grind
    have eq_a2 := expEq_sound a2 b2 h_a2
    simp_all
  | .raise a0 a1, .raise b0 b1, h => by
    simp only [expEq, Bool.and_eq_true, beq_iff_eq] at h
    have h_a1 : expEq a1 b1 = true := by grind
    have eq_a1 := expEq_sound a1 b1 h_a1
    simp_all
  | .handle a0 a1 a2, .handle b0 b1 b2, h => by
    simp only [expEq, Bool.and_eq_true, beq_iff_eq] at h
    have h_a1 : expEq a1 b1 = true := by grind
    have eq_a1 := expEq_sound a1 b1 h_a1
    have h_a2 : expEq a2 b2 = true := by grind
    have eq_a2 := expEq_sound a2 b2 h_a2
    simp_all
  | .tick a0 a1, .tick b0 b1, h => by
    simp only [expEq, Bool.and_eq_true, beq_iff_eq] at h
    have h_a1 : expEq a1 b1 = true := by grind
    have eq_a1 := expEq_sound a1 b1 h_a1
    simp_all
  | .call a0 a1 a2 a3, .call b0 b1 b2 b3, h => by
    simp only [expEq, Bool.and_eq_true, beq_iff_eq] at h
    have h_a3 : expListEq a3 b3 = true := by grind
    have eq_a3 := expListEq_sound a3 b3 h_a3
    simp_all
  | .app a0 a1 a2 a3, .app b0 b1 b2 b3, h => by
    simp only [expEq, Bool.and_eq_true, beq_iff_eq] at h
    have h_a2 : expEq a2 b2 = true := by grind
    have eq_a2 := expEq_sound a2 b2 h_a2
    have h_a3 : expListEq a3 b3 = true := by grind
    have eq_a3 := expListEq_sound a3 b3 h_a3
    simp_all
  | .fn a0 a1 a2 a3 a4, .fn b0 b1 b2 b3 b4, h => by
    simp only [expEq, Bool.and_eq_true, beq_iff_eq] at h
    have h_a4 : expEq a4 b4 = true := by grind
    have eq_a4 := expEq_sound a4 b4 h_a4
    simp_all
  | .letrec a0 a1 a2 a3 a4, .letrec b0 b1 b2 b3 b4, h => by
    simp only [expEq, Bool.and_eq_true, beq_iff_eq] at h
    have h_a3 : expFnsEq a3 b3 = true := by grind
    have eq_a3 := expFnsEq_sound a3 b3 h_a3
    have h_a4 : expEq a4 b4 = true := by grind
    have eq_a4 := expEq_sound a4 b4 h_a4
    simp_all
  | .op a0 a1 a2, .op b0 b1 b2, h => by
    simp only [expEq, Bool.and_eq_true, beq_iff_eq] at h
    have h_a2 : expListEq a2 b2 = true := by grind
    have eq_a2 := expListEq_sound a2 b2 h_a2
    simp_all
  | .var .., .ifThenElse .., h => by simp [expEq] at h
  | .var .., .«let» .., h => by simp [expEq] at h
  | .var .., .raise .., h => by simp [expEq] at h
  | .var .., .handle .., h => by simp [expEq] at h
  | .var .., .tick .., h => by simp [expEq] at h
  | .var .., .call .., h => by simp [expEq] at h
  | .var .., .app .., h => by simp [expEq] at h
  | .var .., .fn .., h => by simp [expEq] at h
  | .var .., .letrec .., h => by simp [expEq] at h
  | .var .., .op .., h => by simp [expEq] at h
  | .ifThenElse .., .var .., h => by simp [expEq] at h
  | .ifThenElse .., .«let» .., h => by simp [expEq] at h
  | .ifThenElse .., .raise .., h => by simp [expEq] at h
  | .ifThenElse .., .handle .., h => by simp [expEq] at h
  | .ifThenElse .., .tick .., h => by simp [expEq] at h
  | .ifThenElse .., .call .., h => by simp [expEq] at h
  | .ifThenElse .., .app .., h => by simp [expEq] at h
  | .ifThenElse .., .fn .., h => by simp [expEq] at h
  | .ifThenElse .., .letrec .., h => by simp [expEq] at h
  | .ifThenElse .., .op .., h => by simp [expEq] at h
  | .«let» .., .var .., h => by simp [expEq] at h
  | .«let» .., .ifThenElse .., h => by simp [expEq] at h
  | .«let» .., .raise .., h => by simp [expEq] at h
  | .«let» .., .handle .., h => by simp [expEq] at h
  | .«let» .., .tick .., h => by simp [expEq] at h
  | .«let» .., .call .., h => by simp [expEq] at h
  | .«let» .., .app .., h => by simp [expEq] at h
  | .«let» .., .fn .., h => by simp [expEq] at h
  | .«let» .., .letrec .., h => by simp [expEq] at h
  | .«let» .., .op .., h => by simp [expEq] at h
  | .raise .., .var .., h => by simp [expEq] at h
  | .raise .., .ifThenElse .., h => by simp [expEq] at h
  | .raise .., .«let» .., h => by simp [expEq] at h
  | .raise .., .handle .., h => by simp [expEq] at h
  | .raise .., .tick .., h => by simp [expEq] at h
  | .raise .., .call .., h => by simp [expEq] at h
  | .raise .., .app .., h => by simp [expEq] at h
  | .raise .., .fn .., h => by simp [expEq] at h
  | .raise .., .letrec .., h => by simp [expEq] at h
  | .raise .., .op .., h => by simp [expEq] at h
  | .handle .., .var .., h => by simp [expEq] at h
  | .handle .., .ifThenElse .., h => by simp [expEq] at h
  | .handle .., .«let» .., h => by simp [expEq] at h
  | .handle .., .raise .., h => by simp [expEq] at h
  | .handle .., .tick .., h => by simp [expEq] at h
  | .handle .., .call .., h => by simp [expEq] at h
  | .handle .., .app .., h => by simp [expEq] at h
  | .handle .., .fn .., h => by simp [expEq] at h
  | .handle .., .letrec .., h => by simp [expEq] at h
  | .handle .., .op .., h => by simp [expEq] at h
  | .tick .., .var .., h => by simp [expEq] at h
  | .tick .., .ifThenElse .., h => by simp [expEq] at h
  | .tick .., .«let» .., h => by simp [expEq] at h
  | .tick .., .raise .., h => by simp [expEq] at h
  | .tick .., .handle .., h => by simp [expEq] at h
  | .tick .., .call .., h => by simp [expEq] at h
  | .tick .., .app .., h => by simp [expEq] at h
  | .tick .., .fn .., h => by simp [expEq] at h
  | .tick .., .letrec .., h => by simp [expEq] at h
  | .tick .., .op .., h => by simp [expEq] at h
  | .call .., .var .., h => by simp [expEq] at h
  | .call .., .ifThenElse .., h => by simp [expEq] at h
  | .call .., .«let» .., h => by simp [expEq] at h
  | .call .., .raise .., h => by simp [expEq] at h
  | .call .., .handle .., h => by simp [expEq] at h
  | .call .., .tick .., h => by simp [expEq] at h
  | .call .., .app .., h => by simp [expEq] at h
  | .call .., .fn .., h => by simp [expEq] at h
  | .call .., .letrec .., h => by simp [expEq] at h
  | .call .., .op .., h => by simp [expEq] at h
  | .app .., .var .., h => by simp [expEq] at h
  | .app .., .ifThenElse .., h => by simp [expEq] at h
  | .app .., .«let» .., h => by simp [expEq] at h
  | .app .., .raise .., h => by simp [expEq] at h
  | .app .., .handle .., h => by simp [expEq] at h
  | .app .., .tick .., h => by simp [expEq] at h
  | .app .., .call .., h => by simp [expEq] at h
  | .app .., .fn .., h => by simp [expEq] at h
  | .app .., .letrec .., h => by simp [expEq] at h
  | .app .., .op .., h => by simp [expEq] at h
  | .fn .., .var .., h => by simp [expEq] at h
  | .fn .., .ifThenElse .., h => by simp [expEq] at h
  | .fn .., .«let» .., h => by simp [expEq] at h
  | .fn .., .raise .., h => by simp [expEq] at h
  | .fn .., .handle .., h => by simp [expEq] at h
  | .fn .., .tick .., h => by simp [expEq] at h
  | .fn .., .call .., h => by simp [expEq] at h
  | .fn .., .app .., h => by simp [expEq] at h
  | .fn .., .letrec .., h => by simp [expEq] at h
  | .fn .., .op .., h => by simp [expEq] at h
  | .letrec .., .var .., h => by simp [expEq] at h
  | .letrec .., .ifThenElse .., h => by simp [expEq] at h
  | .letrec .., .«let» .., h => by simp [expEq] at h
  | .letrec .., .raise .., h => by simp [expEq] at h
  | .letrec .., .handle .., h => by simp [expEq] at h
  | .letrec .., .tick .., h => by simp [expEq] at h
  | .letrec .., .call .., h => by simp [expEq] at h
  | .letrec .., .app .., h => by simp [expEq] at h
  | .letrec .., .fn .., h => by simp [expEq] at h
  | .letrec .., .op .., h => by simp [expEq] at h
  | .op .., .var .., h => by simp [expEq] at h
  | .op .., .ifThenElse .., h => by simp [expEq] at h
  | .op .., .«let» .., h => by simp [expEq] at h
  | .op .., .raise .., h => by simp [expEq] at h
  | .op .., .handle .., h => by simp [expEq] at h
  | .op .., .tick .., h => by simp [expEq] at h
  | .op .., .call .., h => by simp [expEq] at h
  | .op .., .app .., h => by simp [expEq] at h
  | .op .., .fn .., h => by simp [expEq] at h
  | .op .., .letrec .., h => by simp [expEq] at h
termination_by a _ _ => sizeOf a
decreasing_by all_goals simp_wf <;> omega
/-- Expression-list case of the Flapjack comparison soundness proof. -/
private theorem expListEq_sound : ∀ a b : List Exp, expListEq a b = true → a = b
  | [], [], _ => rfl
  | _ :: _, [], h => by simp [expListEq] at h
  | [], _ :: _, h => by simp [expListEq] at h
  | x :: xs, y :: ys, h => by
    simp only [expListEq, Bool.and_eq_true] at h
    simp [expEq_sound x y h.1, expListEq_sound xs ys h.2]
termination_by a _ _ => sizeOf a
decreasing_by all_goals simp_wf <;> omega
/-- Recursive-function-list case of the Flapjack comparison soundness proof. -/
private theorem expFnsEq_sound : ∀ a b : List (Nat × Exp), expFnsEq a b = true → a = b
  | [], [], _ => rfl
  | _ :: _, [], h => by simp [expFnsEq] at h
  | [], _ :: _, h => by simp [expFnsEq] at h
  | (n, x) :: xs, (m, y) :: ys, h => by
    simp only [expFnsEq, Bool.and_eq_true, beq_iff_eq] at h
    have he := expEq_sound x y h.1.2
    have ht := expFnsEq_sound xs ys h.2
    simp_all
termination_by a _ _ => sizeOf a
decreasing_by all_goals simp_wf <;> omega
end
instance : BEq Exp := ⟨expEq⟩
instance : ReflBEq Exp := ⟨expEq_refl _⟩
instance : LawfulBEq Exp := ⟨expEq_sound _ _⟩

end Flapjack.Compiler.Backend.ClosLang
