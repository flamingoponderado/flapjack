import Flapjack.Compiler.Backend.WordCopy

namespace Flapjack.Test.WordCopyDefParity
open Flapjack Flapjack.Compiler.Backend.WordCopy

/-! Kernel replay of `scripts/hol-probes/word_copy_def_probe.out`: original HOL `copy_prop`
and `copy_prop_prog` (program and final `copy_state`) on small 64-bit programs. Programs are
compared through a length-prefixed structural observation (each expected side is checked to
be observed); `num_map`s, which HOL prints as finite maps, are compared through their lookups
on keys `0..31` (every key in the probe is below 32). Finite observations do not establish
cross-prover equivalence. -/

abbrev P := WordLangProgHOL (BitVec 64)

private def obsS : WordStoreHOL → Nat
  | .temp a => 100 + a.toNat
  | s => [WordStore.nextFree, .endOfHeap, .triggerGC, .currHeap, .heapLength, .progStart,
      .bitmapBase, .otherHeap, .allocSize, .globals, .globReal, .handler, .genStart,
      .codeBuffer, .codeBufferEnd, .bitmapBuffer, .bitmapBufferEnd].idxOf s

private def obsRI : WordRegImm (BitVec 64) → List Nat
  | .imm w => [0, w.toNat]
  | .reg n => [1, n]

private def obsAtom : WordLangExpHOL (BitVec 64) → Option (List Nat)
  | .const w => some [0, w.toNat]
  | .var n => some [1, n]
  | _ => none

private def obsBinOp (b : BinOp) : Nat := [BinOp.add, .sub, .and, .or, .xor].idxOf b

private def obsE : WordLangExpHOL (BitVec 64) → Option (List Nat)
  | .op b [x, y] => do
      let a ← obsAtom x
      let c ← obsAtom y
      some (2 :: obsBinOp b :: a ++ c)
  | e => obsAtom e

private def obsMemOp (m : WordMemOp) : Nat :=
  [WordMemOp.load, .load8, .load16, .load32, .store, .store8, .store16, .store32].idxOf m

private def obsI : WordLangInst (BitVec 64) → Option (List Nat)
  | .skip => some [0]
  | .const r w => some [1, r, w.toNat]
  | .arith (.binop b r1 r2 ri) => some ([2, obsBinOp b, r1, r2] ++ obsRI ri)
  | .arith (.shift s r1 r2 ri) => some ([3, [Shift.lsl, .lsr, .asr, .ror].idxOf s, r1, r2] ++ obsRI ri)
  | .arith (.div a b c) => some [4, a, b, c]
  | .arith (.longMul a b c d) => some [5, a, b, c, d]
  | .arith (.longDiv a b c d e) => some [6, a, b, c, d, e]
  | .arith (.addCarry a b c d) => some [7, a, b, c, d]
  | .arith (.addOverflow a b c d) => some [8, a, b, c, d]
  | .arith (.subOverflow a b c d) => some [9, a, b, c, d]
  | .mem m r (.addr a w) => some [10, obsMemOp m, r, a, w.toNat]
  | .fp (.fpLess a b c) => some [11, a, b, c]
  | .fp (.fpLessEqual a b c) => some [12, a, b, c]
  | .fp (.fpEqual a b c) => some [13, a, b, c]
  | .fp (.fpMovFromReg a b c) => some [14, a, b, c]
  | .fp (.fpMovToReg a b c) => some [15, a, b, c]
  | .fp (.fpAdd a b c) => some [16, a, b, c]
  | _ => none

private def obsCuts (c : WordLangCutsetsHOL) : Option (List Nat) :=
  match c with
  | (.ln, .ln) => some [0]
  | _ => none

private def obsP : P → Option (List Nat)
  | .skip => some [0]
  | .move p ls => some (1 :: p :: ls.length :: ls.flatMap fun (x, y) => [x, y])
  | .seq a b => do
      let x ← obsP a
      let y ← obsP b
      some (2 :: x.length :: x ++ y)
  | .raise n => some [3, n]
  | .return n ms => some (4 :: n :: ms.length :: ms)
  | .tick => some [5]
  | .break n => some [6, n]
  | .continue n => some [7, n]
  | .mustTerminate p => do let x ← obsP p; some (8 :: x)
  | .loop .ln b .ln => do let x ← obsP b; some (9 :: x)
  | .ite c r ri a b => do
      let x ← obsP a
      let y ← obsP b
      some ([10, [Cmp.equal, .lower, .less, .test, .notEqual, .notLower, .notLess, .notTest].idxOf c,
        r] ++ obsRI ri ++ x.length :: x ++ y)
  | .call none dest args none =>
      some ([11] ++ (match dest with | none => [0] | some t => [1, t]) ++ args.length :: args)
  | .inst i => do let x ← obsI i; some (12 :: x)
  | .set s e => do let x ← obsE e; some (13 :: obsS s :: x)
  | .get n s => some [14, n, obsS s]
  | .shareInst m v e => do let x ← obsE e; some (15 :: obsMemOp m :: v :: x)
  | .opCurrHeap b d s => some [16, obsBinOp b, d, s]
  | .codeBufferWrite a b => some [17, a, b]
  | .dataBufferWrite a b => some [18, a, b]
  | .storeConsts a b c d ws =>
      some ([19, a, b, c, d, ws.length] ++ ws.flatMap fun (t, w) => [if t then 1 else 0, w.toNat])
  | .locValue r l => some [20, r, l]
  | .alloc r c => do let x ← obsCuts c; some (21 :: r :: x)
  | .assign n e => do let x ← obsE e; some (22 :: n :: x)
  | .store e n => do let x ← obsE e; some (23 :: n :: x)
  | .install a b c d cs => do let x ← obsCuts cs; some ([24, a, b, c, d] ++ x)
  | _ => none

private def obsMap (t : Spt Nat) : List (Nat × Nat) :=
  (List.range 32).filterMap fun k => (sptLookup k t).map (k, ·)

private def obsCS (cs : CopyState) :
    List (Nat × Nat) × List (Nat × Nat) × List (Nat × Nat) × Nat :=
  (obsMap cs.toEq, obsMap cs.fromEq, cs.storeToEq.map (fun (s, c) => (obsS s, c)), cs.next)

private def expS (toEq fromEq : List (Nat × Nat)) (st : List (WordStoreHOL × Nat)) (n : Nat) :
    List (Nat × Nat) × List (Nat × Nat) × List (Nat × Nat) × Nat :=
  (toEq, fromEq, st.map (fun (s, c) => (obsS s, c)), n)

-- wc_cp_type=:α prog -> α prog
example : P → P := copyProp
-- wc_cpp_type=:α prog -> copy_state -> α prog # copy_state
example : P → CopyState → P × CopyState := copyPropProg
-- wc_binop=Seq (Move 0 [(5,1)]) (Inst (Arith (Binop Add 9 5 (Reg 5))))
example : obsP (copyProp ((.seq (.move 0 [(5, 1)]) (.inst (.arith (.binop .add 9 1 (.reg 1))))) : P)) = obsP (.seq (.move 0 [(5, 1)]) (.inst (.arith (.binop .add 9 5 (.reg 5)))) : P) ∧ (obsP (.seq (.move 0 [(5, 1)]) (.inst (.arith (.binop .add 9 5 (.reg 5)))) : P)).isSome := by
  decide +kernel
-- wc_binop_self=Seq (Move 0 [(5,1)]) (Inst (Arith (Binop Add 5 9 (Reg 1))))
example : obsP (copyProp ((.seq (.move 0 [(5, 1)]) (.inst (.arith (.binop .add 5 9 (.reg 1))))) : P)) = obsP (.seq (.move 0 [(5, 1)]) (.inst (.arith (.binop .add 5 9 (.reg 1)))) : P) ∧ (obsP (.seq (.move 0 [(5, 1)]) (.inst (.arith (.binop .add 5 9 (.reg 1)))) : P)).isSome := by
  decide +kernel
-- wc_chain=Seq (Move 0 [(5,1)]) (Seq (Move 0 [(9,5)]) (Return 9 [9; 9; 9]))
example : obsP (copyProp ((.seq (.move 0 [(5, 1)]) (.seq (.move 0 [(9, 5)]) (.return 1 [1, 5, 9]))) : P)) = obsP (.seq (.move 0 [(5, 1)]) (.seq (.move 0 [(9, 5)]) (.return 9 [9, 9, 9])) : P) ∧ (obsP (.seq (.move 0 [(5, 1)]) (.seq (.move 0 [(9, 5)]) (.return 9 [9, 9, 9])) : P)).isSome := by
  decide +kernel
-- wc_chain_state=<|to_eq := ⦕ 1 ↦ 0; 5 ↦ 0; 9 ↦ 0 ⦖; from_eq := ⦕ 0 ↦ 9 ⦖; store_to_eq := []; next := 1|>
example : obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.move 0 [(9, 5)])) : P) emptyEq).2 = expS [(1, 0), (5, 0), (9, 0)] [(0, 9)] ([] : List (WordStoreHOL × Nat)) 1 := by decide +kernel
-- wc_overlap=(Seq (Move 0 [(5,1); (1,5)]) (Return 1 [1]),<|to_eq := LN; from_eq := LN; store_to_eq := []; next := 0|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1), (1, 5)]) (.return 1 [1])) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1), (1, 5)]) (.return 1 [1]) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1), (1, 5)]) (.return 1 [1])) : P) emptyEq).2 = expS [] [] ([] : List (WordStoreHOL × Nat)) 0 ∧
    (obsP (.seq (.move 0 [(5, 1), (1, 5)]) (.return 1 [1]) : P)).isSome := by decide +kernel
-- wc_multi=(Seq (Move 2 [(5,1); (9,13)]) (Raise 9),<|to_eq := ⦕ 1 ↦ 1; 5 ↦ 1; 9 ↦ 0; 13 ↦ 0 ⦖; from_eq := ⦕ 0 ↦ 9; 1 ↦ 5 ⦖; store_to_eq := []; next := 2|>)
example : obsP (copyPropProg ((.seq (.move 2 [(5, 1), (9, 13)]) (.raise 13)) : P) emptyEq).1 = obsP (.seq (.move 2 [(5, 1), (9, 13)]) (.raise 9) : P) ∧
    obsCS (copyPropProg ((.seq (.move 2 [(5, 1), (9, 13)]) (.raise 13)) : P) emptyEq).2 = expS [(1, 1), (5, 1), (9, 0), (13, 0)] [(0, 9), (1, 5)] ([] : List (WordStoreHOL × Nat)) 2 ∧
    (obsP (.seq (.move 2 [(5, 1), (9, 13)]) (.raise 9) : P)).isSome := by decide +kernel
-- wc_nonalloc=(Seq (Move 0 [(4,1)]) (Raise 1),<|to_eq := LN; from_eq := LN; store_to_eq := []; next := 0|>)
example : obsP (copyPropProg ((.seq (.move 0 [(4, 1)]) (.raise 1)) : P) emptyEq).1 = obsP (.seq (.move 0 [(4, 1)]) (.raise 1) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(4, 1)]) (.raise 1)) : P) emptyEq).2 = expS [] [] ([] : List (WordStoreHOL × Nat)) 0 ∧
    (obsP (.seq (.move 0 [(4, 1)]) (.raise 1) : P)).isSome := by decide +kernel
-- wc_const=(Seq (Move 0 [(5,1)]) (Seq (Inst (Const 1 3w)) (Return 1 [5])),<|to_eq := LN; from_eq := LN; store_to_eq := []; next := 0|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.inst (.const 1 3)) (.return 1 [5]))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.seq (.inst (.const 1 3)) (.return 1 [5])) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.inst (.const 1 3)) (.return 1 [5]))) : P) emptyEq).2 = expS [] [] ([] : List (WordStoreHOL × Nat)) 0 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.seq (.inst (.const 1 3)) (.return 1 [5])) : P)).isSome := by decide +kernel
-- wc_shift=Seq (Move 0 [(5,1)]) (Seq (Inst (Arith (Shift Lsl 9 5 (Reg 5)))) (Inst (Arith (Shift Asr 5 5 (Reg 1)))))
example : obsP (copyProp ((.seq (.move 0 [(5, 1)]) (.seq (.inst (.arith (.shift .lsl 9 1 (.reg 1)))) (.inst (.arith (.shift .asr 5 1 (.reg 1)))))) : P)) = obsP (.seq (.move 0 [(5, 1)]) (.seq (.inst (.arith (.shift .lsl 9 5 (.reg 5)))) (.inst (.arith (.shift .asr 5 5 (.reg 1))))) : P) ∧ (obsP (.seq (.move 0 [(5, 1)]) (.seq (.inst (.arith (.shift .lsl 9 5 (.reg 5)))) (.inst (.arith (.shift .asr 5 5 (.reg 1))))) : P)).isSome := by
  decide +kernel
-- wc_div=(Seq (Move 0 [(5,1)]) (Inst (Arith (Div 9 5 5))),<|to_eq := ⦕ 1 ↦ 0; 5 ↦ 0 ⦖; from_eq := ⦕ 0 ↦ 5 ⦖; store_to_eq := []; next := 1|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.inst (.arith (.div 9 1 1)))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.inst (.arith (.div 9 5 5))) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.inst (.arith (.div 9 1 1)))) : P) emptyEq).2 = expS [(1, 0), (5, 0)] [(0, 5)] ([] : List (WordStoreHOL × Nat)) 1 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.inst (.arith (.div 9 5 5))) : P)).isSome := by decide +kernel
-- wc_carry=(Seq (Move 0 [(5,1); (9,13)]) (Inst (Arith (AddCarry 5 5 9 17))),<|to_eq := LN; from_eq := LN; store_to_eq := []; next := 0|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1), (9, 13)]) (.inst (.arith (.addCarry 5 1 13 17)))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1), (9, 13)]) (.inst (.arith (.addCarry 5 5 9 17))) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1), (9, 13)]) (.inst (.arith (.addCarry 5 1 13 17)))) : P) emptyEq).2 = expS [] [] ([] : List (WordStoreHOL × Nat)) 0 ∧
    (obsP (.seq (.move 0 [(5, 1), (9, 13)]) (.inst (.arith (.addCarry 5 5 9 17))) : P)).isSome := by decide +kernel
-- wc_carry_self=Seq (Move 0 [(5,1)]) (Inst (Arith (AddCarry 5 9 1 17)))
example : obsP (copyProp ((.seq (.move 0 [(5, 1)]) (.inst (.arith (.addCarry 5 9 1 17)))) : P)) = obsP (.seq (.move 0 [(5, 1)]) (.inst (.arith (.addCarry 5 9 1 17))) : P) ∧ (obsP (.seq (.move 0 [(5, 1)]) (.inst (.arith (.addCarry 5 9 1 17))) : P)).isSome := by
  decide +kernel
-- wc_overflow=Seq (Move 0 [(5,1)]) (Seq (Inst (Arith (AddOverflow 9 5 5 17))) (Inst (Arith (SubOverflow 21 5 5 25))))
example : obsP (copyProp ((.seq (.move 0 [(5, 1)]) (.seq (.inst (.arith (.addOverflow 9 1 1 17))) (.inst (.arith (.subOverflow 21 1 1 25))))) : P)) = obsP (.seq (.move 0 [(5, 1)]) (.seq (.inst (.arith (.addOverflow 9 5 5 17))) (.inst (.arith (.subOverflow 21 5 5 25)))) : P) ∧ (obsP (.seq (.move 0 [(5, 1)]) (.seq (.inst (.arith (.addOverflow 9 5 5 17))) (.inst (.arith (.subOverflow 21 5 5 25)))) : P)).isSome := by
  decide +kernel
-- wc_longmul=(Seq (Move 0 [(5,1)]) (Inst (Arith (LongMul 9 13 1 1))),<|to_eq := ⦕ 1 ↦ 0; 5 ↦ 0 ⦖; from_eq := ⦕ 0 ↦ 5 ⦖; store_to_eq := []; next := 1|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.inst (.arith (.longMul 9 13 1 1)))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.inst (.arith (.longMul 9 13 1 1))) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.inst (.arith (.longMul 9 13 1 1)))) : P) emptyEq).2 = expS [(1, 0), (5, 0)] [(0, 5)] ([] : List (WordStoreHOL × Nat)) 1 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.inst (.arith (.longMul 9 13 1 1))) : P)).isSome := by decide +kernel
-- wc_longdiv=(Seq (Move 0 [(5,1)]) (Inst (Arith (LongDiv 9 13 5 5 5))),<|to_eq := ⦕ 1 ↦ 0; 5 ↦ 0 ⦖; from_eq := ⦕ 0 ↦ 5 ⦖; store_to_eq := []; next := 1|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.inst (.arith (.longDiv 9 13 1 1 1)))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.inst (.arith (.longDiv 9 13 5 5 5))) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.inst (.arith (.longDiv 9 13 1 1 1)))) : P) emptyEq).2 = expS [(1, 0), (5, 0)] [(0, 5)] ([] : List (WordStoreHOL × Nat)) 1 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.inst (.arith (.longDiv 9 13 5 5 5))) : P)).isSome := by decide +kernel
-- wc_mem=(Seq (Move 0 [(5,1)]) (Seq (Inst (Mem Load 9 (Addr 5 8w))) (Seq (Inst (Mem Store 5 (Addr 5 0w))) (Seq (Inst (Mem Load8 13 (Addr 5 1w))) (Seq (Inst (Mem Store8 5 (Addr 5 2w))) (Seq (Inst (Mem Load16 17 (Addr 5 3w))) (Seq (Inst (Mem Store16 5 (Addr 5 4w))) (Seq (Inst (Mem Load32 21 (Addr 5 5w))) (Inst (Mem Store32 5 (Addr 5 6w)))))))))),<|to_eq := ⦕ 1 ↦ 0; 5 ↦ 0 ⦖; from_eq := ⦕ 0 ↦ 5 ⦖; store_to_eq := []; next := 1|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.inst (.mem .load 9 (.addr 1 8))) (.seq (.inst (.mem .store 1 (.addr 1 0))) (.seq (.inst (.mem .load8 13 (.addr 1 1))) (.seq (.inst (.mem .store8 1 (.addr 1 2))) (.seq (.inst (.mem .load16 17 (.addr 1 3))) (.seq (.inst (.mem .store16 1 (.addr 1 4))) (.seq (.inst (.mem .load32 21 (.addr 1 5))) (.inst (.mem .store32 1 (.addr 1 6))))))))))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.seq (.inst (.mem .load 9 (.addr 5 8))) (.seq (.inst (.mem .store 5 (.addr 5 0))) (.seq (.inst (.mem .load8 13 (.addr 5 1))) (.seq (.inst (.mem .store8 5 (.addr 5 2))) (.seq (.inst (.mem .load16 17 (.addr 5 3))) (.seq (.inst (.mem .store16 5 (.addr 5 4))) (.seq (.inst (.mem .load32 21 (.addr 5 5))) (.inst (.mem .store32 5 (.addr 5 6)))))))))) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.inst (.mem .load 9 (.addr 1 8))) (.seq (.inst (.mem .store 1 (.addr 1 0))) (.seq (.inst (.mem .load8 13 (.addr 1 1))) (.seq (.inst (.mem .store8 1 (.addr 1 2))) (.seq (.inst (.mem .load16 17 (.addr 1 3))) (.seq (.inst (.mem .store16 1 (.addr 1 4))) (.seq (.inst (.mem .load32 21 (.addr 1 5))) (.inst (.mem .store32 1 (.addr 1 6))))))))))) : P) emptyEq).2 = expS [(1, 0), (5, 0)] [(0, 5)] ([] : List (WordStoreHOL × Nat)) 1 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.seq (.inst (.mem .load 9 (.addr 5 8))) (.seq (.inst (.mem .store 5 (.addr 5 0))) (.seq (.inst (.mem .load8 13 (.addr 5 1))) (.seq (.inst (.mem .store8 5 (.addr 5 2))) (.seq (.inst (.mem .load16 17 (.addr 5 3))) (.seq (.inst (.mem .store16 5 (.addr 5 4))) (.seq (.inst (.mem .load32 21 (.addr 5 5))) (.inst (.mem .store32 5 (.addr 5 6)))))))))) : P)).isSome := by decide +kernel
-- wc_mem_kill=(Seq (Move 0 [(5,1)]) (Inst (Mem Load 1 (Addr 5 8w))),<|to_eq := LN; from_eq := LN; store_to_eq := []; next := 0|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.inst (.mem .load 1 (.addr 1 8)))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.inst (.mem .load 1 (.addr 5 8))) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.inst (.mem .load 1 (.addr 1 8)))) : P) emptyEq).2 = expS [] [] ([] : List (WordStoreHOL × Nat)) 0 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.inst (.mem .load 1 (.addr 5 8))) : P)).isSome := by decide +kernel
-- wc_fp=(Seq (Move 0 [(5,1)]) (Seq (Inst (FP (FPLess 9 2 3))) (Seq (Inst (FP (FPMovFromReg 4 5 13))) (Seq (Inst (FP (FPMovFromReg 6 1 5))) (Seq (Inst (FP (FPAdd 7 8 9))) (Inst (FP (FPMovToReg 21 25 3))))))),<|to_eq := ⦕ 1 ↦ 0; 5 ↦ 0 ⦖; from_eq := ⦕ 0 ↦ 5 ⦖; store_to_eq := []; next := 1|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.inst (.fp (.fpLess 9 2 3))) (.seq (.inst (.fp (.fpMovFromReg 4 1 13))) (.seq (.inst (.fp (.fpMovFromReg 6 1 5))) (.seq (.inst (.fp (.fpAdd 7 8 9))) (.inst (.fp (.fpMovToReg 21 25 3)))))))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.seq (.inst (.fp (.fpLess 9 2 3))) (.seq (.inst (.fp (.fpMovFromReg 4 5 13))) (.seq (.inst (.fp (.fpMovFromReg 6 1 5))) (.seq (.inst (.fp (.fpAdd 7 8 9))) (.inst (.fp (.fpMovToReg 21 25 3))))))) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.inst (.fp (.fpLess 9 2 3))) (.seq (.inst (.fp (.fpMovFromReg 4 1 13))) (.seq (.inst (.fp (.fpMovFromReg 6 1 5))) (.seq (.inst (.fp (.fpAdd 7 8 9))) (.inst (.fp (.fpMovToReg 21 25 3)))))))) : P) emptyEq).2 = expS [(1, 0), (5, 0)] [(0, 5)] ([] : List (WordStoreHOL × Nat)) 1 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.seq (.inst (.fp (.fpLess 9 2 3))) (.seq (.inst (.fp (.fpMovFromReg 4 5 13))) (.seq (.inst (.fp (.fpMovFromReg 6 1 5))) (.seq (.inst (.fp (.fpAdd 7 8 9))) (.inst (.fp (.fpMovToReg 21 25 3))))))) : P)).isSome := by decide +kernel
-- wc_fp_kill=(Seq (Move 0 [(5,1)]) (Seq (Inst (FP (FPEqual 1 2 3))) (Seq (Move 0 [(9,13)]) (Inst (FP (FPLessEqual 13 2 3))))),<|to_eq := LN; from_eq := LN; store_to_eq := []; next := 0|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.inst (.fp (.fpEqual 1 2 3))) (.seq (.move 0 [(9, 13)]) (.inst (.fp (.fpLessEqual 13 2 3)))))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.seq (.inst (.fp (.fpEqual 1 2 3))) (.seq (.move 0 [(9, 13)]) (.inst (.fp (.fpLessEqual 13 2 3))))) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.inst (.fp (.fpEqual 1 2 3))) (.seq (.move 0 [(9, 13)]) (.inst (.fp (.fpLessEqual 13 2 3)))))) : P) emptyEq).2 = expS [] [] ([] : List (WordStoreHOL × Nat)) 0 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.seq (.inst (.fp (.fpEqual 1 2 3))) (.seq (.move 0 [(9, 13)]) (.inst (.fp (.fpLessEqual 13 2 3))))) : P)).isSome := by decide +kernel
-- wc_skip_inst=(Seq (Move 0 [(5,1)]) Skip,<|to_eq := ⦕ 1 ↦ 0; 5 ↦ 0 ⦖; from_eq := ⦕ 0 ↦ 5 ⦖; store_to_eq := []; next := 1|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.inst .skip)) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) .skip : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.inst .skip)) : P) emptyEq).2 = expS [(1, 0), (5, 0)] [(0, 5)] ([] : List (WordStoreHOL × Nat)) 1 ∧
    (obsP (.seq (.move 0 [(5, 1)]) .skip : P)).isSome := by decide +kernel
-- wc_set_get=(Seq (Set NextFree (Var 5)) (Move 0 [(9,5)]),<|to_eq := ⦕ 5 ↦ 0; 9 ↦ 0 ⦖; from_eq := ⦕ 0 ↦ 9 ⦖; store_to_eq := [(NextFree,0)]; next := 1|>)
example : obsP (copyPropProg ((.seq (.set .nextFree (.var 5)) (.get 9 .nextFree)) : P) emptyEq).1 = obsP (.seq (.set .nextFree (.var 5)) (.move 0 [(9, 5)]) : P) ∧
    obsCS (copyPropProg ((.seq (.set .nextFree (.var 5)) (.get 9 .nextFree)) : P) emptyEq).2 = expS [(5, 0), (9, 0)] [(0, 9)] ([(.nextFree, 0)] : List (WordStoreHOL × Nat)) 1 ∧
    (obsP (.seq (.set .nextFree (.var 5)) (.move 0 [(9, 5)]) : P)).isSome := by decide +kernel
-- wc_get_same=(Seq (Set NextFree (Var 5)) Skip,<|to_eq := ⦕ 5 ↦ 0 ⦖; from_eq := ⦕ 0 ↦ 5 ⦖; store_to_eq := [(NextFree,0)]; next := 1|>)
example : obsP (copyPropProg ((.seq (.set .nextFree (.var 5)) (.get 5 .nextFree)) : P) emptyEq).1 = obsP (.seq (.set .nextFree (.var 5)) .skip : P) ∧
    obsCS (copyPropProg ((.seq (.set .nextFree (.var 5)) (.get 5 .nextFree)) : P) emptyEq).2 = expS [(5, 0)] [(0, 5)] ([(.nextFree, 0)] : List (WordStoreHOL × Nat)) 1 ∧
    (obsP (.seq (.set .nextFree (.var 5)) .skip : P)).isSome := by decide +kernel
-- wc_get_none=(Get 9 (Temp 3w),<|to_eq := ⦕ 9 ↦ 0 ⦖; from_eq := ⦕ 0 ↦ 9 ⦖; store_to_eq := [(Temp 3w,0)]; next := 1|>)
example : obsP (copyPropProg ((.get 9 (.temp 3)) : P) emptyEq).1 = obsP (.get 9 (.temp 3) : P) ∧
    obsCS (copyPropProg ((.get 9 (.temp 3)) : P) emptyEq).2 = expS [(9, 0)] [(0, 9)] ([(.temp 3, 0)] : List (WordStoreHOL × Nat)) 1 ∧
    (obsP (.get 9 (.temp 3) : P)).isSome := by decide +kernel
-- wc_set_class=(Seq (Move 0 [(5,1)]) (Seq (Set Handler (Var 5)) (Move 0 [(9,5)])),<|to_eq := ⦕ 1 ↦ 0; 5 ↦ 0; 9 ↦ 0 ⦖; from_eq := ⦕ 0 ↦ 9 ⦖; store_to_eq := [(Handler,0)]; next := 1|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.set .handler (.var 1)) (.get 9 .handler))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.seq (.set .handler (.var 5)) (.move 0 [(9, 5)])) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.set .handler (.var 1)) (.get 9 .handler))) : P) emptyEq).2 = expS [(1, 0), (5, 0), (9, 0)] [(0, 9)] ([(.handler, 0)] : List (WordStoreHOL × Nat)) 1 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.seq (.set .handler (.var 5)) (.move 0 [(9, 5)])) : P)).isSome := by decide +kernel
-- wc_set_nonalloc=(Seq (Move 0 [(5,1)]) (Set Handler (Var 2)),<|to_eq := LN; from_eq := LN; store_to_eq := []; next := 0|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.set .handler (.var 2))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.set .handler (.var 2)) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.set .handler (.var 2))) : P) emptyEq).2 = expS [] [] ([] : List (WordStoreHOL × Nat)) 0 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.set .handler (.var 2)) : P)).isSome := by decide +kernel
-- wc_set_exp=(Seq (Move 0 [(5,1)]) (Set Handler (Const 2w)),<|to_eq := LN; from_eq := LN; store_to_eq := []; next := 0|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.set .handler (.const 2))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.set .handler (.const 2)) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.set .handler (.const 2))) : P) emptyEq).2 = expS [] [] ([] : List (WordStoreHOL × Nat)) 0 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.set .handler (.const 2)) : P)).isSome := by decide +kernel
-- wc_if=(Seq (Move 0 [(5,1)]) (Seq (If Equal 5 (Reg 5) (Move 0 [(9,5)]) (Seq (Move 0 [(9,5)]) (Move 0 [(13,9)]))) (Return 1 [1; 9; 13])),<|to_eq := ⦕ 1 ↦ 0; 5 ↦ 0; 9 ↦ 0 ⦖; from_eq := LN; store_to_eq := []; next := 1|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.ite .equal 1 (.reg 1) (.move 0 [(9, 5)]) (.seq (.move 0 [(9, 5)]) (.move 0 [(13, 1)]))) (.return 1 [1, 9, 13]))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.seq (.ite .equal 5 (.reg 5) (.move 0 [(9, 5)]) (.seq (.move 0 [(9, 5)]) (.move 0 [(13, 9)]))) (.return 1 [1, 9, 13])) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.ite .equal 1 (.reg 1) (.move 0 [(9, 5)]) (.seq (.move 0 [(9, 5)]) (.move 0 [(13, 1)]))) (.return 1 [1, 9, 13]))) : P) emptyEq).2 = expS [(1, 0), (5, 0), (9, 0)] [] ([] : List (WordStoreHOL × Nat)) 1 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.seq (.ite .equal 5 (.reg 5) (.move 0 [(9, 5)]) (.seq (.move 0 [(9, 5)]) (.move 0 [(13, 9)]))) (.return 1 [1, 9, 13])) : P)).isSome := by decide +kernel
-- wc_if_imm=(Seq (Set NextFree (Var 5)) (If Less 5 (Imm 3w) (Move 0 [(9,5)]) Skip),<|to_eq := ⦕ 5 ↦ 0 ⦖; from_eq := LN; store_to_eq := [(NextFree,0)]; next := 1|>)
example : obsP (copyPropProg ((.seq (.set .nextFree (.var 5)) (.ite .less 5 (.imm 3) (.get 9 .nextFree) .skip)) : P) emptyEq).1 = obsP (.seq (.set .nextFree (.var 5)) (.ite .less 5 (.imm 3) (.move 0 [(9, 5)]) .skip) : P) ∧
    obsCS (copyPropProg ((.seq (.set .nextFree (.var 5)) (.ite .less 5 (.imm 3) (.get 9 .nextFree) .skip)) : P) emptyEq).2 = expS [(5, 0)] [] ([(.nextFree, 0)] : List (WordStoreHOL × Nat)) 1 ∧
    (obsP (.seq (.set .nextFree (.var 5)) (.ite .less 5 (.imm 3) (.move 0 [(9, 5)]) .skip) : P)).isSome := by decide +kernel
-- wc_loop=(Seq (Move 0 [(5,1)]) (Seq (Loop LN (Seq (Move 0 [(9,13)]) (Seq (Raise 9) (Continue 0))) LN) (Return 1 [1])),<|to_eq := LN; from_eq := LN; store_to_eq := []; next := 0|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.loop .ln (.seq (.move 0 [(9, 13)]) (.seq (.raise 13) (.continue 0))) .ln) (.return 1 [1]))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.seq (.loop .ln (.seq (.move 0 [(9, 13)]) (.seq (.raise 9) (.continue 0))) .ln) (.return 1 [1])) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.loop .ln (.seq (.move 0 [(9, 13)]) (.seq (.raise 13) (.continue 0))) .ln) (.return 1 [1]))) : P) emptyEq).2 = expS [] [] ([] : List (WordStoreHOL × Nat)) 0 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.seq (.loop .ln (.seq (.move 0 [(9, 13)]) (.seq (.raise 9) (.continue 0))) .ln) (.return 1 [1])) : P)).isSome := by decide +kernel
-- wc_mt=(Seq (Move 0 [(5,1)]) (MustTerminate (Seq Tick (Seq (Break 2) (Raise 5)))),<|to_eq := ⦕ 1 ↦ 0; 5 ↦ 0 ⦖; from_eq := ⦕ 0 ↦ 5 ⦖; store_to_eq := []; next := 1|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.mustTerminate (.seq .tick (.seq (.break 2) (.raise 1))))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.mustTerminate (.seq .tick (.seq (.break 2) (.raise 5)))) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.mustTerminate (.seq .tick (.seq (.break 2) (.raise 1))))) : P) emptyEq).2 = expS [(1, 0), (5, 0)] [(0, 5)] ([] : List (WordStoreHOL × Nat)) 1 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.mustTerminate (.seq .tick (.seq (.break 2) (.raise 5)))) : P)).isSome := by decide +kernel
-- wc_share=(Seq (Move 0 [(5,1)]) (Seq (ShareInst Load 9 (Op Add [Var 5; Const 4w])) (Seq (ShareInst Store 13 (Var 5)) (ShareInst Load8 17 (Op Sub [Var 1; Const 4w])))),<|to_eq := ⦕ 1 ↦ 0; 5 ↦ 0 ⦖; from_eq := ⦕ 0 ↦ 5 ⦖; store_to_eq := []; next := 1|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.shareInst .load 9 (.op .add [.var 1, .const 4])) (.seq (.shareInst .store 13 (.var 1)) (.shareInst .load8 17 (.op .sub [.var 1, .const 4]))))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.seq (.shareInst .load 9 (.op .add [.var 5, .const 4])) (.seq (.shareInst .store 13 (.var 5)) (.shareInst .load8 17 (.op .sub [.var 1, .const 4])))) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.shareInst .load 9 (.op .add [.var 1, .const 4])) (.seq (.shareInst .store 13 (.var 1)) (.shareInst .load8 17 (.op .sub [.var 1, .const 4]))))) : P) emptyEq).2 = expS [(1, 0), (5, 0)] [(0, 5)] ([] : List (WordStoreHOL × Nat)) 1 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.seq (.shareInst .load 9 (.op .add [.var 5, .const 4])) (.seq (.shareInst .store 13 (.var 5)) (.shareInst .load8 17 (.op .sub [.var 1, .const 4])))) : P)).isSome := by decide +kernel
-- wc_heap=(Seq (Move 0 [(5,1)]) (Seq (OpCurrHeap Add 9 5) (Seq (OpCurrHeap Add 5 1) (Return 1 [1]))),<|to_eq := LN; from_eq := LN; store_to_eq := []; next := 0|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.opCurrHeap .add 9 1) (.seq (.opCurrHeap .add 5 1) (.return 1 [1])))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.seq (.opCurrHeap .add 9 5) (.seq (.opCurrHeap .add 5 1) (.return 1 [1]))) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.opCurrHeap .add 9 1) (.seq (.opCurrHeap .add 5 1) (.return 1 [1])))) : P) emptyEq).2 = expS [] [] ([] : List (WordStoreHOL × Nat)) 0 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.seq (.opCurrHeap .add 9 5) (.seq (.opCurrHeap .add 5 1) (.return 1 [1]))) : P)).isSome := by decide +kernel
-- wc_buffers=(Seq (Move 0 [(5,1)]) (Seq (CodeBufferWrite 5 5) (DataBufferWrite 5 9)),<|to_eq := ⦕ 1 ↦ 0; 5 ↦ 0 ⦖; from_eq := ⦕ 0 ↦ 5 ⦖; store_to_eq := []; next := 1|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.codeBufferWrite 1 1) (.dataBufferWrite 1 9))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.seq (.codeBufferWrite 5 5) (.dataBufferWrite 5 9)) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.codeBufferWrite 1 1) (.dataBufferWrite 1 9))) : P) emptyEq).2 = expS [(1, 0), (5, 0)] [(0, 5)] ([] : List (WordStoreHOL × Nat)) 1 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.seq (.codeBufferWrite 5 5) (.dataBufferWrite 5 9)) : P)).isSome := by decide +kernel
-- wc_consts=(Seq (Move 0 [(5,1); (9,13)]) (Seq (StoreConsts 2 3 4 6 [(T,1w)]) (Seq (LocValue 7 3) (Return 5 [5; 9]))),<|to_eq := ⦕ 1 ↦ 1; 5 ↦ 1; 9 ↦ 0; 13 ↦ 0 ⦖; from_eq := ⦕ 0 ↦ 9; 1 ↦ 5 ⦖; store_to_eq := []; next := 2|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1), (9, 13)]) (.seq (.storeConsts 2 3 4 6 [(true, 1)]) (.seq (.locValue 7 3) (.return 1 [1, 13])))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1), (9, 13)]) (.seq (.storeConsts 2 3 4 6 [(true, 1)]) (.seq (.locValue 7 3) (.return 5 [5, 9]))) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1), (9, 13)]) (.seq (.storeConsts 2 3 4 6 [(true, 1)]) (.seq (.locValue 7 3) (.return 1 [1, 13])))) : P) emptyEq).2 = expS [(1, 1), (5, 1), (9, 0), (13, 0)] [(0, 9), (1, 5)] ([] : List (WordStoreHOL × Nat)) 2 ∧
    (obsP (.seq (.move 0 [(5, 1), (9, 13)]) (.seq (.storeConsts 2 3 4 6 [(true, 1)]) (.seq (.locValue 7 3) (.return 5 [5, 9]))) : P)).isSome := by decide +kernel
-- wc_consts_kill=(Seq (Move 0 [(5,1)]) (Seq (StoreConsts 5 3 4 6 []) (Return 1 [1])),<|to_eq := LN; from_eq := LN; store_to_eq := []; next := 0|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.storeConsts 5 3 4 6 []) (.return 1 [1]))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.seq (.storeConsts 5 3 4 6 []) (.return 1 [1])) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.storeConsts 5 3 4 6 []) (.return 1 [1]))) : P) emptyEq).2 = expS [] [] ([] : List (WordStoreHOL × Nat)) 0 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.seq (.storeConsts 5 3 4 6 []) (.return 1 [1])) : P)).isSome := by decide +kernel
-- wc_locvalue_kill=(Seq (Move 0 [(5,1)]) (Seq (LocValue 1 3) (Return 1 [1])),<|to_eq := LN; from_eq := LN; store_to_eq := []; next := 0|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.locValue 1 3) (.return 1 [1]))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.seq (.locValue 1 3) (.return 1 [1])) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.locValue 1 3) (.return 1 [1]))) : P) emptyEq).2 = expS [] [] ([] : List (WordStoreHOL × Nat)) 0 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.seq (.locValue 1 3) (.return 1 [1])) : P)).isSome := by decide +kernel
-- wc_call=(Seq (Move 0 [(5,1)]) (Seq (Call NONE (SOME 7) [1] NONE) (Return 1 [1])),<|to_eq := LN; from_eq := LN; store_to_eq := []; next := 0|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.call none (some 7) [1] none) (.return 1 [1]))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.seq (.call none (some 7) [1] none) (.return 1 [1])) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.call none (some 7) [1] none) (.return 1 [1]))) : P) emptyEq).2 = expS [] [] ([] : List (WordStoreHOL × Nat)) 0 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.seq (.call none (some 7) [1] none) (.return 1 [1])) : P)).isSome := by decide +kernel
-- wc_alloc=(Seq (Move 0 [(5,1)]) (Seq (Alloc 1 (LN,LN)) (Return 1 [1])),<|to_eq := LN; from_eq := LN; store_to_eq := []; next := 0|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.alloc 1 (.ln, .ln)) (.return 1 [1]))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.seq (.alloc 1 (.ln, .ln)) (.return 1 [1])) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.alloc 1 (.ln, .ln)) (.return 1 [1]))) : P) emptyEq).2 = expS [] [] ([] : List (WordStoreHOL × Nat)) 0 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.seq (.alloc 1 (.ln, .ln)) (.return 1 [1])) : P)).isSome := by decide +kernel
-- wc_assign=(Seq (Move 0 [(5,1)]) (Seq (Assign 9 (Var 1)) (Return 1 [1])),<|to_eq := LN; from_eq := LN; store_to_eq := []; next := 0|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.assign 9 (.var 1)) (.return 1 [1]))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.seq (.assign 9 (.var 1)) (.return 1 [1])) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.assign 9 (.var 1)) (.return 1 [1]))) : P) emptyEq).2 = expS [] [] ([] : List (WordStoreHOL × Nat)) 0 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.seq (.assign 9 (.var 1)) (.return 1 [1])) : P)).isSome := by decide +kernel
-- wc_store=(Seq (Move 0 [(5,1)]) (Seq (Store (Var 1) 1) (Return 1 [1])),<|to_eq := LN; from_eq := LN; store_to_eq := []; next := 0|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.store (.var 1) 1) (.return 1 [1]))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.seq (.store (.var 1) 1) (.return 1 [1])) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.store (.var 1) 1) (.return 1 [1]))) : P) emptyEq).2 = expS [] [] ([] : List (WordStoreHOL × Nat)) 0 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.seq (.store (.var 1) 1) (.return 1 [1])) : P)).isSome := by decide +kernel
-- wc_install=(Seq (Move 0 [(5,1)]) (Seq (Install 2 3 4 6 (LN,LN)) (Raise 1)),<|to_eq := LN; from_eq := LN; store_to_eq := []; next := 0|>)
example : obsP (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.install 2 3 4 6 (.ln, .ln)) (.raise 1))) : P) emptyEq).1 = obsP (.seq (.move 0 [(5, 1)]) (.seq (.install 2 3 4 6 (.ln, .ln)) (.raise 1)) : P) ∧
    obsCS (copyPropProg ((.seq (.move 0 [(5, 1)]) (.seq (.install 2 3 4 6 (.ln, .ln)) (.raise 1))) : P) emptyEq).2 = expS [] [] ([] : List (WordStoreHOL × Nat)) 0 ∧
    (obsP (.seq (.move 0 [(5, 1)]) (.seq (.install 2 3 4 6 (.ln, .ln)) (.raise 1)) : P)).isSome := by decide +kernel

end Flapjack.Test.WordCopyDefParity
