module

public import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
@[expose] public section

/-! Direct original HOL observations for the exact total Crep Store clause are
   recorded by `crep_store_eval_probeScript.sml`. -/

namespace Flapjack.Test.CrepSemTotalStoreParity

open Flapjack

def sampleState : CrepSemHOLState 64 Unit where
  locals := HolFiniteMapExact.update HolFiniteMapExact.empty
    (0, .word (BitVec.ofNat 64 7))
  globals := HolFiniteMapExact.empty
  code := HolFiniteMapExact.empty
  memory := fun address => .word (BitVec.ofNat 64 (address.toNat + 1))
  memaddrs := fun address => address = BitVec.ofNat 64 10
  shMemaddrs := fun _ => False
  clock := 5
  be := false
  ffi := { oracle := fun _ _ _ _ => .final .diverged, ffiState := (), ioEvents := [] }
  baseAddr := 0
  topAddr := 100

def memDec (address : BitVec 64) : Decidable (sampleState.memaddrs address) :=
  inferInstanceAs (Decidable (address = BitVec.ofNat 64 10))

def shMemDec (address : BitVec 64) : Decidable (sampleState.shMemaddrs address) :=
  isFalse (by simp [sampleState])

def storeOracleRowsMatch : Bool :=
  let state := sampleState
  let address := BitVec.ofNat 64 10
  let otherAddress := BitVec.ofNat 64 11
  let success := match evalCrepSemHOLProg state memDec shMemDec
      (.store (.const address) (.const 9)) with
    | (none, post) => post.memory address == .word 9 &&
        post.memory otherAddress == state.memory otherAddress &&
        post.locals.lookup 0 == state.locals.lookup 0 && post.clock == state.clock &&
        post.globals.lookup 0 == state.globals.lookup 0 &&
        post.baseAddr == state.baseAddr && post.topAddr == state.topAddr
    | _ => false
  let addressError := match evalCrepSemHOLProg state memDec shMemDec
      (.store (.var 9) (.const 9)) with
    | (some .error, post) => post.memory address == state.memory address &&
        post.clock == state.clock && post.locals.lookup 0 == state.locals.lookup 0
    | _ => false
  let valueError := match evalCrepSemHOLProg state memDec shMemDec
      (.store (.const address) (.var 9)) with
    | (some .error, post) => post.memory address == state.memory address &&
        post.clock == state.clock && post.locals.lookup 0 == state.locals.lookup 0
    | _ => false
  let domainError := match evalCrepSemHOLProg state memDec shMemDec
      (.store (.const otherAddress) (.const 9)) with
    | (some .error, post) => post.memory address == state.memory address &&
        post.memory otherAddress == state.memory otherAddress &&
        post.clock == state.clock && post.locals.lookup 0 == state.locals.lookup 0
    | _ => false
  success && addressError && valueError && domainError

#guard storeOracleRowsMatch

theorem storeSuccessMatchesHolMemStore
    (state : CrepSemHOLState 64 Unit)
    (address value : BitVec 64)
    (hdomain : state.memaddrs address) :
    evalCrepSemHOLProgExact state (.store (.const address) (.const value)) =
      (none, { state with memory := fun current =>
        if current = address then .word value else state.memory current }) := by
  rw [evalCrepSemHOLProgExact_store_holShape]
  simp only [evalCrepSemHOLExp]
  simp [panMemStoreHOL, hdomain]

def runChecks : IO Bool := do
  if storeOracleRowsMatch then
    IO.println "PASS total Crep HOL Store success/address/value/domain clauses match direct oracle"
  else
    IO.println "FAIL total Crep HOL Store success/address/value/domain clauses match direct oracle"
  pure storeOracleRowsMatch

end Flapjack.Test.CrepSemTotalStoreParity
