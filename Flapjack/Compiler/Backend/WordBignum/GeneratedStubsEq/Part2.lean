-- Generated from scripts/hol-probes/word_bignum_stubs_eq_typed_probe.out by
-- scripts/generate-bignum-stubs-eq.py; do not edit.
module

public import Flapjack.Pancake.WordLang

@[expose] public section

/-! Part 2 of the programs in HOL `generated_bignum_stubs_eq`
(`word_bignumScript.sml:576-577`). No separate HOL declarations. -/

namespace Flapjack.Compiler.Backend.WordBignum.GeneratedStubsEq
open Flapjack

/-- Program of entry 12 of HOL `generated_bignum_stubs_eq`, rendered term by
term from the capture. -/
def stubsEqProg12 (width : Nat) [NeZero width] (n : Nat) : WordLangProgHOL (BitVec width) :=
  (.seq (.seq (.assign 11 (.lookup (.temp 10))) (.ite .equal 11 (.imm 0) (.seq .skip .skip) (.seq (.seq (.assign 1 (.op .sub [(.lookup (.temp 10)), (.const 1)])) (.set (.temp 10) (.var 1))) (.seq (.seq (.assign 2 (.op .add [(.lookup (.temp 31)), (.shift .lsl (.lookup (.temp 10)) (.const (BitVec.ofNat width (if width = 32 then 2 else 3))))])) (.seq (.assign 3 (.load (.var 2))) (.set (.temp 0) (.var 3)))) (.seq (.seq (.seq (.assign 8 (.lookup (.temp 9))) (.seq (.assign 7 (.lookup (.temp 0))) (.seq (.assign 6 (.lookup (.temp 2))) (.seq (.mustTerminate (.seq (.call (some ([4], ((.ls ()), .ln), .skip, n + 11, 2)) (some 23) [6, 7, 8] none) (.assign 5 (.lookup (.temp 28))))) (.seq (.set (.temp 0) (.var 4)) (.set (.temp 2) (.var 5))))))) .skip) (.seq (.seq (.assign 9 (.lookup (.temp 0))) (.seq (.assign 10 (.op .add [(.lookup (.temp 29)), (.shift .lsl (.lookup (.temp 10)) (.const (BitVec.ofNat width (if width = 32 then 2 else 3))))])) (.store (.var 10) 9))) (.seq .skip (.call none (some (n + 11)) [0] none)))))))) (.return 0 [0]))

/-- Program of entry 13 of HOL `generated_bignum_stubs_eq`, rendered term by
term from the capture. -/
def stubsEqProg13 (width : Nat) [NeZero width] (n : Nat) : WordLangProgHOL (BitVec width) :=
  (.seq (.seq (.assign 6 (.lookup (.temp 10))) (.ite .equal 6 (.imm 0) (.seq .skip .skip) (.seq (.seq (.assign 1 (.op .sub [(.lookup (.temp 10)), (.const 1)])) (.set (.temp 10) (.var 1))) (.seq (.seq (.assign 2 (.op .add [(.lookup (.temp 31)), (.shift .lsl (.lookup (.temp 10)) (.const (BitVec.ofNat width (if width = 32 then 2 else 3))))])) (.seq (.assign 3 (.load (.var 2))) (.set (.temp 0) (.var 3)))) (.seq (.seq (.assign 4 (.lookup (.temp 0))) (.seq (.assign 5 (.op .add [(.lookup (.temp 29)), (.shift .lsl (.lookup (.temp 10)) (.const (BitVec.ofNat width (if width = 32 then 2 else 3))))])) (.store (.var 5) 4))) (.seq .skip (.call none (some (n + 10)) [0] none))))))) (.return 0 [0]))

/-- Program of entry 14 of HOL `generated_bignum_stubs_eq`, rendered term by
term from the capture. -/
def stubsEqProg14 (width : Nat) [NeZero width] (n : Nat) : WordLangProgHOL (BitVec width) :=
  (.seq (.seq (.assign 10 (.lookup (.temp 7))) (.ite .equal 10 (.imm 0) (.seq (.seq (.assign 1 (.op .add [(.lookup (.temp 10)), (.lookup (.temp 9))])) (.set (.temp 10) (.var 1))) (.seq .skip .skip)) (.seq (.seq (.assign 2 (.op .sub [(.lookup (.temp 7)), (.const 1)])) (.set (.temp 7) (.var 2))) (.seq (.seq (.assign 3 (.op .add [(.lookup (.temp 31)), (.shift .lsl (.lookup (.temp 12)) (.const (BitVec.ofNat width (if width = 32 then 2 else 3))))])) (.seq (.assign 4 (.load (.var 3))) (.set (.temp 8) (.var 4)))) (.seq (.seq (.assign 5 (.op .add [(.lookup (.temp 12)), (.const 1)])) (.set (.temp 12) (.var 5))) (.seq (.seq (.assign 6 (.const 0)) (.set (.temp 11) (.var 6))) (.seq (.seq (.assign 7 (.lookup (.temp 11))) (.set (.temp 1) (.var 7))) (.seq (.call (some ([8], ((.ls ()), .ln), .skip, n + 8, 2)) (some (n + 9)) [] none) (.seq (.seq (.assign 9 (.op .sub [(.lookup (.temp 10)), (.lookup (.temp 9))])) (.set (.temp 10) (.var 9))) (.seq .skip (.call none (some (n + 8)) [0] none))))))))))) (.return 0 [0]))

/-- Program of entry 15 of HOL `generated_bignum_stubs_eq`, rendered term by
term from the capture. -/
def stubsEqProg15 (width : Nat) [NeZero width] (n : Nat) : WordLangProgHOL (BitVec width) :=
  (.seq (.seq (.assign 38 (.lookup (.temp 9))) (.seq (.assign 39 (.lookup (.temp 11))) (.ite .equal 38 (.reg 39) (.seq (.seq (.assign 1 (.lookup (.temp 1))) (.seq (.assign 2 (.op .add [(.lookup (.temp 29)), (.shift .lsl (.lookup (.temp 10)) (.const (BitVec.ofNat width (if width = 32 then 2 else 3))))])) (.store (.var 2) 1))) (.seq (.seq (.assign 3 (.op .add [(.lookup (.temp 10)), (.const 1)])) (.set (.temp 10) (.var 3))) (.seq .skip .skip))) (.seq (.seq (.assign 4 (.op .add [(.lookup (.temp 29)), (.shift .lsl (.lookup (.temp 10)) (.const (BitVec.ofNat width (if width = 32 then 2 else 3))))])) (.seq (.assign 5 (.load (.var 4))) (.set (.temp 3) (.var 5)))) (.seq (.seq (.assign 6 (.op .add [(.lookup (.temp 30)), (.shift .lsl (.lookup (.temp 11)) (.const (BitVec.ofNat width (if width = 32 then 2 else 3))))])) (.seq (.assign 7 (.load (.var 6))) (.set (.temp 2) (.var 7)))) (.seq (.seq (.assign 8 (.lookup (.temp 8))) (.set (.temp 0) (.var 8))) (.seq (.seq (.seq (.assign 12 (.lookup (.temp 2))) (.seq (.assign 11 (.lookup (.temp 0))) (.seq (.inst (.arith (.longMul 9 10 11 12))) (.seq (.set (.temp 2) (.var 9)) (.set (.temp 0) (.var 10)))))) (.seq (.seq (.assign 17 (.const 0)) (.seq (.assign 16 (.lookup (.temp 1))) (.seq (.assign 15 (.lookup (.temp 0))) (.seq (.inst (.arith (.addCarry 14 15 16 17))) (.seq (.set (.temp 0) (.var 14)) (.set (.temp 4) (.var 17))))))) (.seq (.seq (.assign 22 (.lookup (.temp 4))) (.seq (.assign 21 (.const 0)) (.seq (.assign 20 (.lookup (.temp 2))) (.seq (.inst (.arith (.addCarry 19 20 21 22))) (.seq (.set (.temp 2) (.var 19)) (.set (.temp 4) (.var 22))))))) (.seq (.seq (.assign 27 (.const 0)) (.seq (.assign 26 (.lookup (.temp 3))) (.seq (.assign 25 (.lookup (.temp 0))) (.seq (.inst (.arith (.addCarry 24 25 26 27))) (.seq (.set (.temp 0) (.var 24)) (.set (.temp 4) (.var 27))))))) (.seq (.seq (.assign 32 (.lookup (.temp 4))) (.seq (.assign 31 (.const 0)) (.seq (.assign 30 (.lookup (.temp 2))) (.seq (.inst (.arith (.addCarry 29 30 31 32))) (.seq (.set (.temp 2) (.var 29)) (.set (.temp 4) (.var 32))))))) (.seq .skip .skip)))))) (.seq (.seq (.assign 33 (.lookup (.temp 0))) (.seq (.assign 34 (.op .add [(.lookup (.temp 29)), (.shift .lsl (.lookup (.temp 10)) (.const (BitVec.ofNat width (if width = 32 then 2 else 3))))])) (.store (.var 34) 33))) (.seq (.seq (.assign 35 (.lookup (.temp 2))) (.set (.temp 1) (.var 35))) (.seq (.seq (.assign 36 (.op .add [(.lookup (.temp 10)), (.const 1)])) (.set (.temp 10) (.var 36))) (.seq (.seq (.assign 37 (.op .add [(.lookup (.temp 11)), (.const 1)])) (.set (.temp 11) (.var 37))) (.seq .skip (.call none (some (n + 9)) [0] none))))))))))))) (.return 0 [0]))

/-- Program of entry 16 of HOL `generated_bignum_stubs_eq`, rendered term by
term from the capture. -/
def stubsEqProg16 (width : Nat) [NeZero width] (n : Nat) : WordLangProgHOL (BitVec width) :=
  (.seq (.seq (.assign 4 (.lookup (.temp 10))) (.ite .equal 4 (.imm 0) (.seq .skip .skip) (.seq (.seq (.assign 1 (.op .sub [(.lookup (.temp 10)), (.const 1)])) (.set (.temp 10) (.var 1))) (.seq (.seq (.assign 2 (.lookup (.temp 0))) (.seq (.assign 3 (.op .add [(.lookup (.temp 29)), (.shift .lsl (.lookup (.temp 10)) (.const (BitVec.ofNat width (if width = 32 then 2 else 3))))])) (.store (.var 3) 2))) (.call none (some (n + 7)) [0] none))))) (.return 0 [0]))

/-- Program of entry 17 of HOL `generated_bignum_stubs_eq`, rendered term by
term from the capture. -/
def stubsEqProg17 (width : Nat) [NeZero width] (n : Nat) : WordLangProgHOL (BitVec width) :=
  (.seq (.seq (.assign 6 (.lookup (.temp 10))) (.ite .equal 6 (.imm 0) .skip (.seq (.seq (.assign 1 (.op .sub [(.lookup (.temp 10)), (.const 1)])) (.set (.temp 10) (.var 1))) (.seq (.seq (.assign 2 (.op .add [(.lookup (.temp 29)), (.shift .lsl (.lookup (.temp 10)) (.const (BitVec.ofNat width (if width = 32 then 2 else 3))))])) (.seq (.assign 3 (.load (.var 2))) (.set (.temp 8) (.var 3)))) (.seq (.assign 5 (.lookup (.temp 8))) (.ite .equal 5 (.imm 0) (.call none (some (n + 6)) [0] none) (.seq (.seq (.assign 4 (.op .add [(.lookup (.temp 10)), (.const 1)])) (.set (.temp 10) (.var 4))) .skip))))))) (.return 0 [0]))

end Flapjack.Compiler.Backend.WordBignum.GeneratedStubsEq
