import Flapjack.Compiler.Backend.Semantics.BviSem.Finalise

/-! Original finalisation observations captured in bvi_sem_state_probe.out. -/
namespace Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem

example : finaliseCons (.number 7) (HolFiniteMapExact.empty : HolFiniteMapExact Nat (Ref Value)) =
    some (.number 7, HolFiniteMapExact.empty) := by
  simp [finaliseCons]

example : finaliseCons (.refPtr false 3) (HolFiniteMapExact.empty : HolFiniteMapExact Nat (Ref Value)) = none := by
  simp [finaliseCons, HolFiniteMapExact.empty]

example : finaliseCons (.refPtr false 1)
    ((HolFiniteMapExact.empty : HolFiniteMapExact Nat (Ref Value)).updateEq
      (1, .mutBlock 2 false [] (.refPtr false 1) [])) = none := by
  simp [finaliseCons, HolFiniteMapExact.lookup_updateEq, HolFiniteMapExact.eraseEq, FDOMSUB_HOL, FUPDATE_HOL]

example : (finaliseCons (.refPtr false 1)
    ((HolFiniteMapExact.empty : HolFiniteMapExact Nat (Ref Value)).updateEq
      (1, .mutBlock 2 false [.number 3] (.number 4) []))).map Prod.fst =
    some (.block 2 [.number 3, .number 4]) := by
  simp [finaliseCons, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
end Flapjack.Compiler.Backend.BviSem
namespace Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem
example : (finaliseCons (.refPtr false 1)
    ((HolFiniteMapExact.empty : HolFiniteMapExact Nat (Ref Value)).updateEq
      (1, .mutBlock 2 false [.number 3] (.number 4) []))).map
      (fun pair => (pair.1, pair.2.lookup 1)) =
    some (.block 2 [.number 3, .number 4], some (.mutBlock 2 true [.number 3] (.number 4) [])) := by
  simp [finaliseCons, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
end Flapjack.Compiler.Backend.BviSem
