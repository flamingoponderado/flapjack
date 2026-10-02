import Flapjack.Compiler.Backend.WordUnreach

namespace Flapjack.Test.WordUnreachDefParity
open Flapjack Flapjack.Compiler.Backend.WordUnreach

/-! Kernel replay of `scripts/hol-probes/word_unreach_def_probe.out`: original HOL
`dest_Seq_Move`, `merge_moves`, `SimpSeq` and `remove_unreach` (through `Seq_assoc_right`)
on small 64-bit programs. Programs are compared through a length-prefixed structural
observation, and each expected side is checked to be observed. Finite observations do not
establish cross-prover equivalence. -/

abbrev P := WordLangProgHOL (BitVec 64)

private def obs : P → Option (List Nat)
  | .skip => some [0]
  | .move p ls => some (1 :: p :: ls.length :: ls.flatMap fun (x, y) => [x, y])
  | .seq a b => do
      let x ← obs a
      let y ← obs b
      some (2 :: x.length :: x ++ y)
  | .raise n => some [3, n]
  | .return n ms => some (4 :: n :: ms.length :: ms)
  | .tick => some [5]
  | .break n => some [6, n]
  | .continue n => some [7, n]
  | .mustTerminate p => do let x ← obs p; some (8 :: x)
  | .loop _ b _ => do let x ← obs b; some (9 :: x)
  | .ite _ r (.imm w) a b => do
      let x ← obs a
      let y ← obs b
      some (10 :: r :: w.toNat :: x.length :: x ++ y)
  | .call ret dest args h => do
      let r ← match ret with
        | none => some [0]
        | some (vs, _, q, l1, l2) => do
            let x ← obs q
            some (1 :: vs.length :: vs ++ [l1, l2] ++ x)
      let d := match dest with | none => [0] | some t => [1, t]
      let hh ← match h with
        | none => some [0]
        | some (v, q, l1, l2) => do
            let x ← obs q
            some ([1, v, l1, l2] ++ x)
      some (11 :: r.length :: r ++ d ++ args.length :: args ++ hh)
  | _ => none

private def same (a b : P) : Bool := obs a == obs b && (obs b).isSome

private def obsD : Option (Nat × List (Nat × Nat) × P) → Option (Option (List Nat))
  | none => none
  | some (n, l, r) => some (obs (.seq (.move n l) r))

-- wu_ru_type=:α prog -> α prog
example : P → P := removeUnreach
-- wu_mm_type=:(num # num) list -> (num # num) list -> (num # num) list
example : List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat) := mergeMoves
-- wu_dsm_move=SOME (3,[(1,2)],Skip)
example : obsD (destSeqMove (.move 3 [(1, 2)] : P)) = obsD (some (3, [(1, 2)], .skip)) ∧
    (obs (.seq (.move 3 [(1, 2)]) .skip : P)).isSome := by decide +kernel
-- wu_dsm_seq=SOME (3,[(1,2)],Raise 5)
example : obsD (destSeqMove (.seq (.move 3 [(1, 2)]) (.raise 5) : P)) =
    obsD (some (3, [(1, 2)], .raise 5)) := by decide +kernel
-- wu_dsm_other=NONE
example : obsD (destSeqMove (.seq (.raise 5) (.move 3 [(1, 2)]) : P)) = none := by decide +kernel
-- wu_mm_basic=[(3,11); (2,99); (1,11)]
example : mergeMoves [(1, 11), (2, 22), (3, 33)] [(3, 1), (2, 99)] = [(3, 11), (2, 99), (1, 11)] := by
  decide +kernel
-- wu_mm_dup=[(4,2); (1,2)]
example : mergeMoves [(1, 2), (1, 3)] [(4, 1), (4, 5)] = [(4, 2), (1, 2)] := by decide +kernel
-- wu_ss_skip_r=Raise 1
example : same (simpSeq (.raise 1) .skip) (.raise 1) := by decide +kernel
-- wu_ss_skip_l=Raise 1
example : same (simpSeq .skip (.raise 1)) (.raise 1) := by decide +kernel
-- wu_ss_raise=Raise 1
example : same (simpSeq (.raise 1) (.return 2 [3])) (.raise 1) := by decide +kernel
-- wu_ss_move_move=Move 4 [(2,11); (1,11)]
example : same (simpSeq (.move 1 [(1, 11)]) (.move 4 [(2, 1)])) (.move 4 [(2, 11), (1, 11)]) := by
  decide +kernel
-- wu_ss_move_rest=Seq (Move 1 [(2,11); (1,11)]) (Raise 7)
example : same (simpSeq (.move 1 [(1, 11)]) (.seq (.move 0 [(2, 1)]) (.raise 7)))
    (.seq (.move 1 [(2, 11), (1, 11)]) (.raise 7)) := by decide +kernel
-- wu_ss_move_other=Seq (Move 1 [(1,11)]) (Raise 7)
example : same (simpSeq (.move 1 [(1, 11)]) (.raise 7)) (.seq (.move 1 [(1, 11)]) (.raise 7)) := by
  decide +kernel
-- wu_ss_default=Seq Tick (Raise 7)
example : same (simpSeq .tick (.raise 7)) (.seq .tick (.raise 7)) := by decide +kernel
-- wu_test=Move 1 [(3,11); (2,99); (1,11)]
example : same (removeUnreach (.seq (.move 1 [(1, 11), (2, 22), (3, 33)]) (.move 1 [(3, 1), (2, 99)])))
    (.move 1 [(3, 11), (2, 99), (1, 11)]) := by decide +kernel
-- wu_after_return=Return 1 [2]
example : same (removeUnreach (.seq (.seq (.return 1 [2]) (.raise 3)) (.move 0 [(4, 5)])))
    (.return 1 [2]) := by decide +kernel
-- wu_call_none=Call NONE (SOME 7) [1] NONE
example : same (removeUnreach (.seq (.call none (some 7) [1] none) (.raise 3)))
    (.call none (some 7) [1] none) := by decide +kernel
-- wu_call_ret=Seq (Call (SOME ([1],(LN,LN),Move 0 [(5,1)],2,3)) (SOME 7) [1] (SOME (9,Raise 9,4,5))) Tick
example : same (removeUnreach (.seq (.call (some ([1], (.ln, .ln), .seq .skip (.move 0 [(5, 1)]), 2, 3))
      (some 7) [1] (some (9, .seq (.raise 9) .tick, 4, 5))) .tick))
    (.seq (.call (some ([1], (.ln, .ln), .move 0 [(5, 1)], 2, 3)) (some 7) [1]
      (some (9, .raise 9, 4, 5))) .tick) := by decide +kernel
-- wu_if=Seq (If Equal 1 (Imm 0w) (Break 2) (Move 0 [(5,1)])) Tick
example : same (removeUnreach (.seq (.ite .equal 1 (.imm 0) (.seq .skip (.break 2))
      (.seq (.move 0 [(5, 1)]) .skip)) .tick))
    (.seq (.ite .equal 1 (.imm 0) (.break 2) (.move 0 [(5, 1)])) .tick) := by decide +kernel
-- wu_loop=Seq (Loop LN (Continue 0) LN) (MustTerminate Tick)
example : same (removeUnreach (.seq (.loop .ln (.seq (.continue 0) .tick) .ln)
      (.mustTerminate (.seq .tick .skip))))
    (.seq (.loop .ln (.continue 0) .ln) (.mustTerminate .tick)) := by decide +kernel

end Flapjack.Test.WordUnreachDefParity
