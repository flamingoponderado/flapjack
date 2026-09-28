import Flapjack.Pancake.Semantics.LoopSemStateExact

/-! Direct HOL parity for the exact loopSem `eval`, `mem_load`, `mem_store` and
    `loop_arith` of `Flapjack/Pancake/Semantics/LoopSemStateExact.lean`.  Each
    `#guard` is a checked-in HOL `EVAL` row of
    `scripts/hol-probes/loop_sem_eval_probe.out`, `loop_sem_mem_load_probe.out`,
    `loop_sem_mem_store_probe.out` or `loop_sem_loop_arith_probe.out`, over the
    same 8-bit states. -/

namespace Flapjack.Test.LoopSemEvalExactParity

open Flapjack
open Flapjack.LoopSemStateFiniteExact

private def holTrivialFfi : HolFfiState Unit :=
  { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
private def base : LoopSemStateFiniteExact 8 Unit :=
  { locals := .ln, globals := HolFiniteMapExact.empty, memory := fun _ => .word 0,
    mdomain := fun _ => false, shMdomain := fun _ => false, clock := 5, code := .ln,
    be := false, ffi := holTrivialFfi, baseAddr := 0, topAddr := 0 }
private def w (n : Nat) : WordLocW 8 := .word (BitVec.ofNat 8 n)
private def isW (o : Option (WordLocW 8)) (n : Nat) : Bool :=
  match o with | some (.word x) => x.toNat == n | _ => false
private def isNone (o : Option (WordLocW 8)) : Bool := o.isNone
private def memS : LoopSemStateFiniteExact 8 Unit :=
  { base with mdomain := fun a => a == 3, memory := fun a => if a = 3 then w 11 else base.memory a }
#guard isW (eval base (.const 7)) 7
#guard isW (eval { base with locals := sptInsert 2 (w 7) .ln } (.var 2)) 7
#guard isNone (eval base (.var 2))
#guard isW (eval { base with globals := HolFiniteMapExact.empty.update (3, w 9) } (.lookup 3)) 9
#guard isNone (eval base (.lookup 3))
#guard isW (eval memS (.load (.const 3))) 11
#guard isNone (eval memS (.load (.const 4)))
#guard isW (eval base (.op .add [.const 1, .const 2, .const 3])) 6
#guard isW (eval base (.op .and [])) 255
#guard isNone (eval base (.op .sub [.const 7]))
#guard isW (eval base (.shift .ror (.const 129) (.const 1))) 192
#guard isNone (eval base (.shift .lsl (.const 1) (.const 8)))
#guard isW (eval { base with baseAddr := 4 } .baseAddr) 4
#guard isW (eval { base with topAddr := 100 } .topAddr) 100
private def toNum : WordLocW 8 → Nat | .word x => x.toNat | .loc a _ => a
private def arithRes (o : Option (LoopSemStateFiniteExact 8 Unit)) (names : List Nat) : Option (List Nat) :=
  o.bind fun s' => (LoopSemStateFiniteExact.getVars names s').map (List.map toNum)
private def withLocals (l : List (Nat × WordLocW 8)) : LoopSemStateFiniteExact 8 Unit :=
  { base with locals := l.foldr (fun p t => sptInsert p.1 p.2 t) .ln }
#guard arithRes (LoopSemStateFiniteExact.loopArith (withLocals [(2, w 7), (3, w 2)]) (.div 1 2 3)) [1] == some [3]
#guard arithRes (LoopSemStateFiniteExact.loopArith (withLocals [(2, w 7), (3, w 0)]) (.div 1 2 3)) [1] == none
#guard arithRes (LoopSemStateFiniteExact.loopArith (withLocals [(2, .loc 9 0), (3, w 2)]) (.div 1 2 3)) [1] == none
#guard arithRes (LoopSemStateFiniteExact.loopArith (withLocals [(3, w 20), (4, w 20)]) (.longMul 1 2 3 4)) [1, 2] == some [1, 144]
#guard arithRes (LoopSemStateFiniteExact.loopArith (withLocals [(3, .loc 9 0), (4, w 20)]) (.longMul 1 2 3 4)) [1, 2] == none
#guard arithRes (LoopSemStateFiniteExact.loopArith (withLocals [(3, w 1), (4, w 3), (5, w 2)]) (.longDiv 1 2 3 4 5)) [1, 2] == some [129, 1]
#guard arithRes (LoopSemStateFiniteExact.loopArith (withLocals [(3, w 1), (4, w 3), (5, w 0)]) (.longDiv 1 2 3 4 5)) [1, 2] == none
#guard arithRes (LoopSemStateFiniteExact.loopArith (withLocals [(3, w 1), (4, w 0), (5, w 1)]) (.longDiv 1 2 3 4 5)) [1, 2] == none
private def mem3 : LoopSemStateFiniteExact 8 Unit :=
  { base with mdomain := fun a => a == 3, memory := fun a => if a = 3 then w 7 else base.memory a }
#guard isW (memLoad 3 mem3) 7
#guard isNone (memLoad 4 mem3)
private def mem3s : LoopSemStateFiniteExact 8 Unit :=
  { base with mdomain := fun a => a == 3, memory := fun a => if a = 3 then w 1 else base.memory a }
#guard isW ((memStore 3 (w 7) mem3s).bind (memLoad 3)) 7
#guard (memStore 4 (w 7) mem3s).isNone
private def mem34 : LoopSemStateFiniteExact 8 Unit :=
  { base with mdomain := fun a => a == 3 || a == 4, memory := fun a => if a = 4 then w 1 else base.memory a }
#guard isW ((memStore 3 (w 7) mem34).bind (memLoad 4)) 1

def runChecks : IO Bool := do
  IO.println "PASS exact loopSem eval/mem/loop_arith HOL parity"
  pure true

end Flapjack.Test.LoopSemEvalExactParity
