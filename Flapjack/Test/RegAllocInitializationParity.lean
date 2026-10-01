import Flapjack.Compiler.Backend.RegAlloc.Initialization

/-! Same-input kernel replay of eight fresh generated-runner observations.
The seed deliberately has inconsistent dimensions and independent lengths. -/
namespace Flapjack.Test.RegAllocInitializationParity
open Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase
private def seed : IraState :=
  { adj_ls := (2,[7,9]), node_tag := (1,.Atemp), degrees := (3,5), dim := 99
    simp_wl := [1], spill_wl := [2], freeze_wl := [3]
    avail_moves_wl := [(8,(1,2))], unavail_moves_wl := [(6,(4,5))]
    coalesced := (4,8), move_related := (5,true), stack := [9,8] }
example : runIraState (fun s => (.success (decide (s.adj_ls = [[7,9],[7,9]])),s)) seed =
    (.success true : Exc Bool Nat) := by rfl
example : runIraState (fun s => (.success (decide (s.node_tag = [.Atemp])),s)) seed =
    (.success true : Exc Bool Nat) := by rfl
example : runIraState (fun s => (.success (decide (s.degrees = [5,5,5])),s)) seed =
    (.success true : Exc Bool Nat) := by rfl
example : runIraState (fun s => (.success (decide (s.coalesced = [8,8,8,8])),s)) seed =
    (.success true : Exc Bool Nat) := by rfl
example : runIraState (fun s => (.success (decide (s.move_related = [true,true,true,true,true])),s)) seed =
    (.success true : Exc Bool Nat) := by rfl
example : runIraState (fun s => (.success (decide (s.dim = 99 ∧ s.simp_wl = [1] ∧
    s.spill_wl = [2] ∧ s.freeze_wl = [3] ∧ s.avail_moves_wl = [(8,(1,2))] ∧
    s.unavail_moves_wl = [(6,(4,5))] ∧ s.stack = [9,8])),s)) seed =
    (.success true : Exc Bool Nat) := by rfl
example : runIraState (fun s => (.failure 23,{s with dim := 123})) seed =
    (.failure 23 : Exc Bool Nat) := by rfl
private def zero : IraState :=
  { seed with adj_ls := (0,[7,9]), node_tag := (0,.Stemp)
              degrees := (0,5), coalesced := (0,8), move_related := (0,true) }
example : runIraState (fun s => (.success (decide (s.adj_ls = [] ∧ s.node_tag = [] ∧
    s.degrees = [] ∧ s.coalesced = [] ∧ s.move_related = [] ∧ s.dim = 99)),s)) zero =
    (.success true : Exc Bool Nat) := by rfl

/-- Flapjack regression infrastructure: no consistency premise appears even
when the result and exception types are independent arbitrary carriers. -/
example {value exception : Type} (value : value) (state : IraState) :
    runIraState (ret value : M State _ exception) state = .success value := rfl
end Flapjack.Test.RegAllocInitializationParity
