import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Word8

/-! Unsigned byte comparisons in the 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- The byte comparisons supported by the source and compiler. -/
inductive ByteComparison where
  | equal | less | lessEq
  deriving DecidableEq

def ByteComparison.test : ByteComparison → AstHOL.Test
  | .equal => .equal
  | .less => .compare .lt
  | .lessEq => .compare .leq

def ByteComparison.result (kind : ByteComparison) (x y : BitVec 8) : Bool :=
  match kind with
  | .equal => decide (x = y)
  | .less => x.ult y
  | .lessEq => !(y.ult x)

/-- Target comparison emitted for each supported source byte comparison. -/
def byteCompareProg64 (kind : ByteComparison) (dest left right : Nat) : WordLangProgHOL (BitVec 64) :=
  let (cmp, first, second) := match kind with
    | .equal => (Cmp.equal, left, right)
    | .less => (Cmp.lower, left, right)
    | .lessEq => (Cmp.notLower, right, left)
  .ite cmp (adjustVar first) (.reg (adjustVar second))
    (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2))

/-- The comparison instruction agrees with source unsigned byte comparison. -/
theorem byteCompare64 (kind : ByteComparison) (x y : BitVec 8) :
    (match kind with
     | .equal => Compiler.Encoders.Asm.wordCmpHOL .equal (smallnum (Int.ofNat x.toNat) : BitVec 64) (smallnum (Int.ofNat y.toNat))
     | .less => Compiler.Encoders.Asm.wordCmpHOL .lower (smallnum (Int.ofNat x.toNat) : BitVec 64) (smallnum (Int.ofNat y.toNat))
     | .lessEq => Compiler.Encoders.Asm.wordCmpHOL .notLower (smallnum (Int.ofNat y.toNat) : BitVec 64) (smallnum (Int.ofNat x.toNat))) =
      kind.result x y := by
  cases kind with
  | equal =>
    apply Bool.eq_iff_iff.mpr
    simpa [Compiler.Encoders.Asm.wordCmpHOL, ByteComparison.result] using (byte64_cmp x y).1
  | less =>
    simpa [Compiler.Encoders.Asm.wordCmpHOL, ByteComparison.result, BitVec.lt_def,
      BitVec.ult_eq_decide] using (byte64_cmp x y).2
  | lessEq =>
    simpa [Compiler.Encoders.Asm.wordCmpHOL, ByteComparison.result, BitVec.lt_def,
      BitVec.ult_eq_decide] using congrArg Bool.not (byte64_cmp y x).2

/-- Source byte comparisons produce the corresponding Boolean value. -/
theorem byteCompare_source (kind : ByteComparison) (x y : BitVec 8) :
    DataSem.doWordApp (.wordTest .w8 kind.test)
      [.number (Int.ofNat x.toNat), .number (Int.ofNat y.toNat)] = some (DataSem.boolValue (kind.result x y)) := by
  have xb : x.toNat < 256 := by simpa using x.isLt
  have yb : y.toNat < 256 := by simpa using y.isLt
  have valEq : x.toNat = y.toNat ↔ x = y := ⟨BitVec.eq_of_toNat_eq, fun h => by subst y; rfl⟩
  cases kind <;> simp [DataSem.doWordApp, DataSem.doWordAppIntegral, ByteComparison.test,
    ByteComparison.result, xb, yb, BitVec.ult_eq_decide, valEq]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp

/-- All three unsigned byte comparisons simulate the source operation. -/
theorem assignByteCompare64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest left right : Nat) (kind : ByteComparison) (x y : BitVec 8)
    (leftRun : DataSem.getVar left source.locals = some (.number (Int.ofNat x.toNat)))
    (rightRun : DataSem.getVar right source.locals = some (.number (Int.ofNat y.toNat))) :
    continues64 conf secn label l1 l2 (.assign dest (.wordOp (.wordTest .w8 kind.test)) [left, right] none) source target locs := by
  let operation := ClosLang.Op.wordOp (.wordTest .w8 kind.test)
  let args : List DataSem.Value := [.number (Int.ofNat x.toNat), .number (Int.ofNat y.toNat)]
  let middle := DataSem.doStack operation args (DataSem.doLimSafe source operation args)
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related operation args
  have leftWord := stateRel64_getSmallNumber conf l1 l2 source target locs related left _ leftRun (byte_small64 x)
  have rightWord := stateRel64_getSmallNumber conf l1 l2 source target locs related right _ rightRun (byte_small64 y)
  let result := kind.result x y
  refine ⟨DataSem.setVar dest (DataSem.boolValue result) middle,
    WordSemStateFiniteExact.setVar (adjustVar dest) (.word (if result then 18 else 2)) target, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, leftRun, rightRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.installSfs, operation, args, middle, result]
    have computed := byteCompare_source kind x y
    change DataSem.doWordApp (.wordTest .w8 kind.test) [.number (x.toNat : Int), .number (y.toNat : Int)] = _ at computed
    rw [computed]
    rfl
  · have cmp := byteCompare64 kind x y
    cases kind with
    | equal =>
      simp only [compileControl64, compileControl?, ByteComparison.test, Option.getD_some]
      change WordSemStateFiniteExact.evaluate (byteCompareProg64 .equal dest left right) target = _
      simp [byteCompareProg64, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
        wordSemWordCmp, leftWord, rightWord, WordSemStateFiniteExact.wordExp, ByteComparison.result, result] at cmp ⊢
      simp_all
      by_cases h : x = y <;> simp [h]
    | less =>
      simp only [compileControl64, compileControl?, ByteComparison.test, Option.getD_some]
      change WordSemStateFiniteExact.evaluate (byteCompareProg64 .less dest left right) target = _
      simp [byteCompareProg64, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
        wordSemWordCmp, leftWord, rightWord, WordSemStateFiniteExact.wordExp, ByteComparison.result, result] at cmp ⊢
      simp_all
      cases h : x.ult y <;> simp
    | lessEq =>
      simp only [compileControl64, compileControl?, ByteComparison.test, Option.getD_some]
      change WordSemStateFiniteExact.evaluate (byteCompareProg64 .lessEq dest left right) target = _
      simp [byteCompareProg64, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
        wordSemWordCmp, leftWord, rightWord, WordSemStateFiniteExact.wordExp, ByteComparison.result, result] at cmp ⊢
      simp_all
      cases h : y.ult x <;> simp
  · exact stateRel64_setBool conf l1 l2 middle target locs middleRel dest result

/-- Source safety ensures that both operands are bytes. -/
theorem assignByteCompare64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest left right : Nat) (kind : ByteComparison)
    (safe : (DataSem.evaluate (.assign dest (.wordOp (.wordTest .w8 kind.test)) [left, right] none) source).1 ≠
      some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.wordOp (.wordTest .w8 kind.test)) [left, right] none) source target locs := by
  cases leftRun : DataSem.getVar left source.locals with
  | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, leftRun] at safe
  | some first =>
    cases rightRun : DataSem.getVar right source.locals with
    | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, leftRun, rightRun] at safe
    | some second =>
      cases kind <;> cases first <;> cases second <;>
        simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, leftRun, rightRun,
          DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
          DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral, DataSem.doStack, DataSem.doLimSafe,
          ByteComparison.test] at safe
      all_goals
        rename_i a b
        by_cases bounds : 0 ≤ a ∧ a < 256 ∧ 0 ≤ b ∧ b < 256
        · have xa : ClosSem.intToByte a = some (BitVec.ofInt 8 a) := by simp [ClosSem.intToByte, bounds.1, bounds.2.1]
          have yb : ClosSem.intToByte b = some (BitVec.ofInt 8 b) := by simp [ClosSem.intToByte, bounds.2.2.1, bounds.2.2.2]
          have aEq := (ClosSem.intToByte_iff a _).mp xa
          have bEq := (ClosSem.intToByte_iff b _).mp yb
          rw [aEq] at leftRun
          rw [bEq] at rightRun
          exact assignByteCompare64 conf secn label l1 l2 source target locs related dest left right _
            (BitVec.ofInt 8 a) (BitVec.ofInt 8 b) leftRun rightRun
        · simp [bounds] at safe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
