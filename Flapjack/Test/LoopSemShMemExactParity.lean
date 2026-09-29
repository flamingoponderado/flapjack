import Flapjack.Pancake.Semantics.LoopSemStateExact.ShMem

/-! Direct HOL parity for the exact loopSem shared-memory helpers.  Each
    `#guard` is a checked-in HOL `EVAL` row of
    `scripts/hol-probes/loop_sem_sh_mem_load_probe.out`,
    `loop_sem_sh_mem_store_probe.out` or `loop_sem_sh_mem_op_probe.out`, with the
    same returning `SharedMem` oracle and 8/32-bit states. -/

namespace Flapjack.Test.LoopSemShMemExactParity

open Flapjack
open Flapjack.LoopSemStateFiniteExact

private def retFfi : HolFfiState Unit :=
  { oracle := fun name st _ bytes =>
      match name with
      | .sharedMem _ => .ret st bytes
      | _ => .final .failed,
    ffiState := (), ioEvents := [] }
private def base8 : LoopSemStateFiniteExact 8 Unit :=
  { locals := .ln, globals := HolFiniteMapExact.empty, memory := fun _ => .word 0,
    mdomain := fun _ => false, shMdomain := fun a => a == 3, clock := 5, code := .ln,
    be := false, ffi := retFfi, baseAddr := 0, topAddr := 0 }
private def base32 : LoopSemStateFiniteExact 32 Unit :=
  { locals := .ln, globals := HolFiniteMapExact.empty, memory := fun _ => .word 0,
    mdomain := fun _ => false, shMdomain := fun a => a == 0, clock := 5, code := .ln,
    be := false, ffi := retFfi, baseAddr := 0, topAddr := 0 }
private def localIs {w : Nat} [NeZero w] (s : LoopSemStateFiniteExact w Unit) (n : Nat) : Bool :=
  match sptLookup 1 s.locals with | some (.word x) => x.toNat == n | _ => false
private def isNoneRes {w : Nat} [NeZero w] (r : Option (LoopResultExact w)) : Bool := r.isNone
private def isErr {w : Nat} [NeZero w] (r : Option (LoopResultExact w)) : Bool :=
  match r with | some .error => true | _ => false
-- return_zero_width=(NONE, T, 1)
#guard (let p := shMemLoad 1 3 0 { base8 with locals := sptInsert 1 (.word 0) .ln }
        isNoneRes p.1 && localIs p.2 3 && p.2.ffi.ioEvents.length == 1)
-- missing_local_inserts=(NONE, T)
#guard (let p := shMemLoad 1 3 0 base8
        isNoneRes p.1 && localIs p.2 3)
-- domain_error=(SOME Error, F)
#guard (let p := shMemLoad 1 4 0 { base8 with locals := sptInsert 1 (.word 0) .ln }
        isErr p.1 && !localIs p.2 3)
-- aligned_domain_original_payload=(NONE, 3)
#guard (let p := shMemLoad 1 3 1 base32
        isNoneRes p.1 && localIs p.2 3)
-- store_zero_width=(NONE, SOME (Word 7w), 1)
#guard (let p := shMemStore 1 3 0 { base8 with locals := sptInsert 1 (.word 7) .ln }
        isNoneRes p.1 && localIs p.2 7 && p.2.ffi.ioEvents.length == 1)
-- missing_word_error=(SOME Error, 0)
#guard (let p := shMemStore 1 3 0 base8
        isErr p.1 && p.2.ffi.ioEvents.length == 0)
-- domain_error=(SOME Error, 0)
#guard (let p := shMemStore 1 4 0 { base8 with locals := sptInsert 1 (.word 7) .ln }
        isErr p.1 && p.2.ffi.ioEvents.length == 0)
-- aligned_domain_original_payload=T
#guard (let p := shMemStore 1 3 1 { base32 with locals := sptInsert 1 (.word 171) .ln }
        match p.2.ffi.ioEvents with
        | [e] => e.bytes == [(171, 171), (3, 3), (0, 0), (0, 0), (0, 0)]
        | _ => false)
private def opConf (op : WordMemOp) : List (BitVec 8) :=
  match (shMemOp op 1 3 { base8 with locals := sptInsert 1 (.word 7) .ln }).2.ffi.ioEvents with
  | [e] => e.configuration | _ => []
-- load=[0w] store=[0w] load8=[1w] store8=[1w] load16=[2w] store16=[2w] load32=[4w] store32=[4w]
#guard opConf .load == [0] && opConf .store == [0] && opConf .load8 == [1] && opConf .store8 == [1]
#guard opConf .load16 == [2] && opConf .store16 == [2] && opConf .load32 == [4] && opConf .store32 == [4]

def runChecks : IO Bool := do
  IO.println "PASS exact loopSem shared-memory HOL parity"
  pure true

end Flapjack.Test.LoopSemShMemExactParity
