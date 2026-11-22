-- Generated from scripts/hol-probes/word_bignum_stubs_eq_typed_probe.out by
-- scripts/generate-bignum-stubs-eq.py; do not edit.
module

public import Flapjack.Pancake.WordLang

@[expose] public section

/-! Part 3 of the programs in HOL `generated_bignum_stubs_eq`
(`word_bignumScript.sml:576-577`). No separate HOL declarations. -/

namespace Flapjack.Compiler.Backend.WordBignum.GeneratedStubsEq
open Flapjack

/-- Program of entry 18 of HOL `generated_bignum_stubs_eq`, rendered term by
term from the capture. -/
def stubsEqProg18 (width : Nat) [NeZero width] (n : Nat) : WordLangProgHOL (BitVec width) :=
  (.seq (.seq (.assign 13 (.lookup (.temp 1))) (.ite .equal 13 (.imm 1) (.seq (.seq (.assign 1 (.const 0)) (.set (.temp 1) (.var 1))) .skip) (.seq (.seq (.assign 2 (.op .sub [(.lookup (.temp 1)), (.const 1)])) (.set (.temp 1) (.var 2))) (.seq (.seq (.assign 3 (.op .add [(.lookup (.temp 31)), (.shift .lsl (.lookup (.temp 10)) (.const (BitVec.ofNat width (if width = 32 then 2 else 3))))])) (.seq (.assign 4 (.load (.var 3))) (.set (.temp 8) (.var 4)))) (.seq (.seq (.assign 9 (.lookup (.temp 3))) (.seq (.assign 8 (.lookup (.temp 9))) (.seq (.assign 8 (.op .xor [(.var 8), (.const (BitVec.ofNat width (2 ^ width - 1)))])) (.seq (.assign 7 (.lookup (.temp 8))) (.seq (.inst (.arith (.addCarry 6 7 8 9))) (.seq (.set (.temp 8) (.var 6)) (.set (.temp 3) (.var 9)))))))) (.seq (.seq (.assign 10 (.lookup (.temp 8))) (.seq (.assign 11 (.op .add [(.lookup (.temp 29)), (.shift .lsl (.lookup (.temp 10)) (.const (BitVec.ofNat width (if width = 32 then 2 else 3))))])) (.store (.var 11) 10))) (.seq (.seq (.assign 12 (.op .add [(.lookup (.temp 10)), (.const 1)])) (.set (.temp 10) (.var 12))) (.call none (some (n + 5)) [0] none)))))))) (.return 0 [0]))

/-- Program of entry 19 of HOL `generated_bignum_stubs_eq`, rendered term by
term from the capture. -/
def stubsEqProg19 (width : Nat) [NeZero width] (n : Nat) : WordLangProgHOL (BitVec width) :=
  (.seq (.seq (.assign 15 (.lookup (.temp 1))) (.ite .equal 15 (.imm 1) (.seq (.seq (.assign 1 (.const 0)) (.set (.temp 1) (.var 1))) .skip) (.seq (.seq (.assign 2 (.op .sub [(.lookup (.temp 1)), (.const 1)])) (.set (.temp 1) (.var 2))) (.seq (.seq (.assign 3 (.op .add [(.lookup (.temp 31)), (.shift .lsl (.lookup (.temp 10)) (.const (BitVec.ofNat width (if width = 32 then 2 else 3))))])) (.seq (.assign 4 (.load (.var 3))) (.set (.temp 8) (.var 4)))) (.seq (.seq (.assign 5 (.op .add [(.lookup (.temp 30)), (.shift .lsl (.lookup (.temp 10)) (.const (BitVec.ofNat width (if width = 32 then 2 else 3))))])) (.seq (.assign 6 (.load (.var 5))) (.set (.temp 9) (.var 6)))) (.seq (.seq (.assign 11 (.lookup (.temp 3))) (.seq (.assign 10 (.lookup (.temp 9))) (.seq (.assign 10 (.op .xor [(.var 10), (.const (BitVec.ofNat width (2 ^ width - 1)))])) (.seq (.assign 9 (.lookup (.temp 8))) (.seq (.inst (.arith (.addCarry 8 9 10 11))) (.seq (.set (.temp 8) (.var 8)) (.set (.temp 3) (.var 11)))))))) (.seq (.seq (.assign 12 (.lookup (.temp 8))) (.seq (.assign 13 (.op .add [(.lookup (.temp 29)), (.shift .lsl (.lookup (.temp 10)) (.const (BitVec.ofNat width (if width = 32 then 2 else 3))))])) (.store (.var 13) 12))) (.seq (.seq (.assign 14 (.op .add [(.lookup (.temp 10)), (.const 1)])) (.set (.temp 10) (.var 14))) (.call none (some (n + 4)) [0] none))))))))) (.return 0 [0]))

/-- Program of entry 20 of HOL `generated_bignum_stubs_eq`, rendered term by
term from the capture. -/
def stubsEqProg20 (width : Nat) [NeZero width] (n : Nat) : WordLangProgHOL (BitVec width) :=
  (.seq (.seq (.assign 12 (.lookup (.temp 10))) (.ite .equal 12 (.imm 0) (.seq .skip .skip) (.seq (.seq (.assign 1 (.op .sub [(.lookup (.temp 10)), (.const 1)])) (.set (.temp 10) (.var 1))) (.seq (.seq (.assign 2 (.op .add [(.lookup (.temp 31)), (.shift .lsl (.lookup (.temp 10)) (.const (BitVec.ofNat width (if width = 32 then 2 else 3))))])) (.seq (.assign 3 (.load (.var 2))) (.set (.temp 8) (.var 3)))) (.seq (.seq (.assign 4 (.op .add [(.lookup (.temp 30)), (.shift .lsl (.lookup (.temp 10)) (.const (BitVec.ofNat width (if width = 32 then 2 else 3))))])) (.seq (.assign 5 (.load (.var 4))) (.set (.temp 9) (.var 5)))) (.seq (.assign 10 (.lookup (.temp 8))) (.seq (.assign 11 (.lookup (.temp 9))) (.ite .equal 10 (.reg 11) (.seq .skip (.call none (some (n + 3)) [0] none)) (.seq (.assign 8 (.lookup (.temp 8))) (.seq (.assign 9 (.lookup (.temp 9))) (.ite .lower 8 (.reg 9) (.seq (.seq (.assign 6 (.const 1)) (.set (.temp 10) (.var 6))) (.seq .skip .skip)) (.seq (.seq (.assign 7 (.const 2)) (.set (.temp 10) (.var 7))) (.seq .skip .skip))))))))))))) (.return 0 [0]))

/-- Program of entry 21 of HOL `generated_bignum_stubs_eq`, rendered term by
term from the capture. -/
def stubsEqProg21 (width : Nat) [NeZero width] (n : Nat) : WordLangProgHOL (BitVec width) :=
  (.seq (.seq (.assign 13 (.lookup (.temp 1))) (.ite .equal 13 (.imm 1) (.seq (.seq (.assign 1 (.const 0)) (.set (.temp 1) (.var 1))) .skip) (.seq (.seq (.assign 2 (.op .sub [(.lookup (.temp 1)), (.const 1)])) (.set (.temp 1) (.var 2))) (.seq (.seq (.assign 3 (.op .add [(.lookup (.temp 31)), (.shift .lsl (.lookup (.temp 10)) (.const (BitVec.ofNat width (if width = 32 then 2 else 3))))])) (.seq (.assign 4 (.load (.var 3))) (.set (.temp 8) (.var 4)))) (.seq (.seq (.assign 9 (.lookup (.temp 3))) (.seq (.assign 8 (.lookup (.temp 9))) (.seq (.assign 7 (.lookup (.temp 8))) (.seq (.inst (.arith (.addCarry 6 7 8 9))) (.seq (.set (.temp 8) (.var 6)) (.set (.temp 3) (.var 9))))))) (.seq (.seq (.assign 10 (.lookup (.temp 8))) (.seq (.assign 11 (.op .add [(.lookup (.temp 29)), (.shift .lsl (.lookup (.temp 10)) (.const (BitVec.ofNat width (if width = 32 then 2 else 3))))])) (.store (.var 11) 10))) (.seq (.seq (.assign 12 (.op .add [(.lookup (.temp 10)), (.const 1)])) (.set (.temp 10) (.var 12))) (.call none (some (n + 2)) [0] none)))))))) (.return 0 [0]))

/-- Program of entry 22 of HOL `generated_bignum_stubs_eq`, rendered term by
term from the capture. -/
def stubsEqProg22 (width : Nat) [NeZero width] (n : Nat) : WordLangProgHOL (BitVec width) :=
  (.seq (.seq (.assign 15 (.lookup (.temp 1))) (.ite .equal 15 (.imm 1) (.seq (.seq (.assign 1 (.const 0)) (.set (.temp 1) (.var 1))) .skip) (.seq (.seq (.assign 2 (.op .sub [(.lookup (.temp 1)), (.const 1)])) (.set (.temp 1) (.var 2))) (.seq (.seq (.assign 3 (.op .add [(.lookup (.temp 31)), (.shift .lsl (.lookup (.temp 10)) (.const (BitVec.ofNat width (if width = 32 then 2 else 3))))])) (.seq (.assign 4 (.load (.var 3))) (.set (.temp 8) (.var 4)))) (.seq (.seq (.assign 5 (.op .add [(.lookup (.temp 30)), (.shift .lsl (.lookup (.temp 10)) (.const (BitVec.ofNat width (if width = 32 then 2 else 3))))])) (.seq (.assign 6 (.load (.var 5))) (.set (.temp 9) (.var 6)))) (.seq (.seq (.assign 11 (.lookup (.temp 3))) (.seq (.assign 10 (.lookup (.temp 9))) (.seq (.assign 9 (.lookup (.temp 8))) (.seq (.inst (.arith (.addCarry 8 9 10 11))) (.seq (.set (.temp 8) (.var 8)) (.set (.temp 3) (.var 11))))))) (.seq (.seq (.assign 12 (.lookup (.temp 8))) (.seq (.assign 13 (.op .add [(.lookup (.temp 29)), (.shift .lsl (.lookup (.temp 10)) (.const (BitVec.ofNat width (if width = 32 then 2 else 3))))])) (.store (.var 13) 12))) (.seq (.seq (.assign 14 (.op .add [(.lookup (.temp 10)), (.const 1)])) (.set (.temp 10) (.var 14))) (.call none (some (n + 1)) [0] none))))))))) (.return 0 [0]))

end Flapjack.Compiler.Backend.WordBignum.GeneratedStubsEq
