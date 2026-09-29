import Flapjack.Pancake.Proofs.CrepArith.HOLStateMapc
import Flapjack.Pancake.Semantics.CrepProps

namespace Flapjack.Test.CrepHolStateParity

open Flapjack.Basis.Pure.MlString

private def codeName : MlString := .implode []

private def sampleCode : HolFiniteMapExact MlString
    (List Nat × CrepProgHOL 8) where
  lookup name := if name = codeName then some ([], .skip) else none
  finiteSupport := by
    refine ⟨[codeName], ?_⟩
    intro name hlookup
    by_cases h : name = codeName
    · simp [h]
    · simp [h] at hlookup

private def sampleMapc
    (entry : MlString × (List Nat × CrepProgHOL 8)) :
    List Nat × CrepProgHOL 8 := (entry.2.1, .tick)

theorem mapc_lookup_fixture :
    (sampleCode.map2 sampleMapc).lookup codeName = some ([], .tick) := by
  simp [HolFiniteMapExact.map2, sampleCode, sampleMapc, codeName]

def parityGuard : Bool :=
  match (sampleCode.map2 sampleMapc).lookup codeName with
  | some (parameters, .tick) => parameters.isEmpty
  | _ => false

#eval parityGuard

example : parityGuard = true := by rfl

/-- The source evaluator sees identical observable states across HOL `mapc`.
The direct HOL evidence is in `crep_state_mapc_probe.out`. -/
example {width : Nat} [NeZero width] {ffiState : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width ffiState)
    (expression : CrepExp (Fin width → Bool)) :
    evalCrepHolFiniteWordSourceExp (instFinHolFiniteDimension (width := width))
        (state.mapc f).toExpressionEvaluatorState expression =
      evalCrepHolFiniteWordSourceExp (instFinHolFiniteDimension (width := width))
        state.toExpressionEvaluatorState expression :=
  evalCrepHolFiniteWordSourceExp_mapc_projection f state expression

/-! ## Finite-support map operation rows

Direct rows for `FEMPTY` (`empty`), `FUPDATE` (`update`), `FUPDATE_LIST`
(`updateList`), domain subtraction (`erase`), and `res_var` (`resVar`) on the
finite-support carrier. These pin the observable lookup behavior required by
`crepSemScript.sml:55,61,66,71,163`. -/

private def sampleLocals : HolFiniteMapExact Nat (HolWordLab 8) :=
  HolFiniteMapExact.empty.updateList [(3, .word 7), (5, .word 9)]

example : sampleLocals.lookup 3 = some (.word 7) := by decide

example : sampleLocals.lookup 5 = some (.word 9) := by decide

example : sampleLocals.lookup 4 = none := by decide

example : (sampleLocals.update (3, .word 11)).lookup 3 = some (.word 11) := by decide

example : (sampleLocals.update (3, .word 11)).lookup 5 = some (.word 9) := by decide

example : (sampleLocals.resVar (5, none)).lookup 5 = none := by decide

example : (sampleLocals.resVar (5, some (.word 13))).lookup 5 = some (.word 13) := by
  decide

example :
    (HolFiniteMapExact.empty : HolFiniteMapExact Nat (HolWordLab 8)).lookup 3 = none := rfl

/-! ### HOL-equality (`=`) forms for the polymorphic `res_var_def` port

The tagged `resVarEq`/`updateEq`/`eraseEq` use `DecidableEq` (HOL `=`) rather
than Boolean `BEq`; the rows below mirror the direct HOL rows
`res_var_delete_hit`/`res_var_update_hit` in `crep_res_var_probe.out`. -/

example : (sampleLocals.resVarEq (5, none)).lookup 5 = none := by decide

example : (sampleLocals.resVarEq (5, none)).lookup 3 = some (.word 7) := by decide

example : (sampleLocals.resVarEq (5, some (.word 13))).lookup 5 = some (.word 13) := by
  decide

example : (sampleLocals.updateEq (4, .word 21)).lookup 4 = some (.word 21) := by decide

example : (sampleLocals.eraseEq 3).lookup 3 = none := by decide

example : (sampleLocals.eraseEq 3).lookup 5 = some (.word 9) := by decide

/-! ## Kernel-checked projection bridges

Each finite-support state update projects into the executable `CrepHolState`
helper (`CrepSem.lean`) under `toBitVecEvaluatorState`. The statement-level
examples below apply the bridges; the bridge proofs themselves live beside the
helpers in `CrepSem/HOLState.lean`. -/

example {width : Nat} [NeZero width] {ffiState : Type} (name : Nat)
    (value : HolWordLab width) (state : CrepSemHOLState width ffiState) :
    (CrepSemHOLState.setVar name value state).toBitVecEvaluatorState =
      setCrepHolVarW name value.toPanWordLab state.toBitVecEvaluatorState :=
  CrepSemHOLState.toBitVecEvaluatorState_setVar name value state

example {width : Nat} [NeZero width] {ffiState : Type} (key : BitVec 5)
    (value : HolWordLab width) (state : CrepSemHOLState width ffiState) :
    (CrepSemHOLState.setGlobals key value state).toBitVecEvaluatorState =
      setCrepHolGlobalsW key value.toPanWordLab state.toBitVecEvaluatorState :=
  CrepSemHOLState.toBitVecEvaluatorState_setGlobals key value state

example {width : Nat} [NeZero width] {ffiState : Type}
    (varargs : List (Nat × HolWordLab width)) (state : CrepSemHOLState width ffiState) :
    (CrepSemHOLState.updLocals varargs state).toBitVecEvaluatorState =
      updCrepHolLocalsW (varargs.map (fun entry => (entry.1, entry.2.toPanWordLab)))
        state.toBitVecEvaluatorState :=
  CrepSemHOLState.toBitVecEvaluatorState_updLocals varargs state

example {width : Nat} [NeZero width] {ffiState : Type} (state : CrepSemHOLState width ffiState) :
    (CrepSemHOLState.emptyLocals state).toBitVecEvaluatorState =
      emptyCrepHolLocalsW state.toBitVecEvaluatorState :=
  CrepSemHOLState.toBitVecEvaluatorState_emptyLocals state

example {width : Nat} [NeZero width]
    (map : HolFiniteMapExact Nat (HolWordLab width)) (key : Nat)
    (value : Option (HolWordLab width)) :
    (fun k => ((CrepSemHOLState.resVar map (key, value)).lookup k).map
        HolWordLab.toPanWordLab) =
      resVarW (fun k => (map.lookup k).map HolWordLab.toPanWordLab)
        (key, value.map HolWordLab.toPanWordLab) :=
  CrepSemHOLState.lookup_resVarW map key value

/-- Exact-port fixture for HOL `flookup_res_var_thm`
(`crepPropsScript.sml:257-263`): a `res_var` update exposes the new `SOME`
value at the updated key and leaves other keys to the original map. -/
private def resVarSample : HolFiniteMapExact Nat Nat where
  lookup k := if k = 0 then some 5 else none
  finiteSupport := by
    refine ⟨[0], ?_⟩
    intro k hk
    by_cases h : k = 0
    · simp [h]
    · simp [h] at hk

example :
    (HolFiniteMapExact.resVarEq resVarSample (0, (some 9 : Option Nat))).lookup 0 =
      some 9 := by
  rw [Flapjack.flookupResVarThmHOL]
  simp

example :
    (HolFiniteMapExact.resVarEq resVarSample (0, (some 9 : Option Nat))).lookup 1 =
      none := by
  rw [Flapjack.flookupResVarThmHOL]
  simp [resVarSample]

example :
    (HolFiniteMapExact.resVarEq resVarSample (0, (none : Option Nat))).lookup 0 =
      none := by
  rw [Flapjack.flookupResVarThmHOL]
  simp

/-- Exact-port fixture for HOL `flookup_res_var_diff_eq`
(`crepPropsScript.sml:249-255`): a `res_var` delete/update at key `0` leaves the
lookup at the distinct key `1` equal to the original map's lookup. -/
example :
    (HolFiniteMapExact.resVarEq resVarSample (0, (some 9 : Option Nat))).lookup 1 =
      resVarSample.lookup 1 :=
  Flapjack.flookupResVarDiffEqHOL resVarSample 0 1 (some 9) (by decide)

example :
    (HolFiniteMapExact.resVarEq resVarSample (0, (none : Option Nat))).lookup 1 =
      resVarSample.lookup 1 :=
  Flapjack.flookupResVarDiffEqHOL resVarSample 0 1 none (by decide)

/-! Exact-port fixture for HOL `lookup_locals_eq_map_vars`
(`crepPropsScript.sml:17-27`): collecting local lookups over a name list equals
mapping the exact evaluator over the corresponding `.var` expressions, checked
on a concrete two-local state. -/

private def lookupState : CrepSemHOLState 8 Unit where
  locals := HolFiniteMapExact.empty.updateList
    [(0, .word (BitVec.ofNat 8 7)), (1, .word (BitVec.ofNat 8 8))]
  globals := HolFiniteMapExact.empty
  code := HolFiniteMapExact.empty
  memory := fun _ => .word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 3
  be := false
  ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
  baseAddr := 0
  topAddr := 100

private instance : DecidablePred lookupState.memaddrs :=
  fun _ => isFalse (by simp [lookupState])

private def loadGlobState : CrepSemHOLState 8 Unit :=
  CrepSemHOLState.setGlobals 5 (.word (BitVec.ofNat 8 11)) lookupState

example :
    evalCrepSemHOLExp (loadGlobState.mapc sampleMapc)
        (.loadGlob (BitVec.ofNat 5 5)) =
      evalCrepSemHOLExp loadGlobState (.loadGlob (BitVec.ofNat 5 5)) := by
  simpa [crepSimpExpHOL] using
    (crepSimpExpCorrect1NativeLoadGlobCase sampleMapc loadGlobState
      (BitVec.ofNat 5 5) (HolWordLab.word (BitVec.ofNat 8 11)) (by
        simp [loadGlobState, CrepSemHOLState.setGlobals,
          evalCrepSemHOLExp, lookupState, HolFiniteMapExact.lookup_updateEq,
          FUPDATE_HOL_eq_FUPDATE, FUPDATE]))

private def baseTopState : CrepSemHOLState 8 Unit :=
  { lookupState with
    baseAddr := BitVec.ofNat 8 12
    topAddr := BitVec.ofNat 8 13 }

example :
    evalCrepSemHOLExp (baseTopState.mapc sampleMapc) .baseAddr =
      evalCrepSemHOLExp baseTopState .baseAddr := by
  simpa [crepSimpExpHOL] using
    (crepSimpExpCorrect1NativeBaseAddrCase sampleMapc baseTopState
      (HolWordLab.word (BitVec.ofNat 8 12)) (by
        simp [evalCrepSemHOLExp, baseTopState, lookupState]))

example :
    evalCrepSemHOLExp (baseTopState.mapc sampleMapc) .topAddr =
      evalCrepSemHOLExp baseTopState .topAddr := by
  simpa [crepSimpExpHOL] using
    (crepSimpExpCorrect1NativeTopAddrCase sampleMapc baseTopState
      (HolWordLab.word (BitVec.ofNat 8 13)) (by
        simp [evalCrepSemHOLExp, baseTopState, lookupState]))

private def lookupNames : List Nat := [0, 1]

example :
    lookupNames.mapM lookupState.locals.lookup =
      some [HolWordLab.word (BitVec.ofNat 8 7), HolWordLab.word (BitVec.ofNat 8 8)] := by
  rw [Flapjack.lookupLocalsEqMapVarsHOL]
  simp only [lookupNames, List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil,
    evalCrepSemHOLExp]
  simp only [lookupState, HolFiniteMapExact.lookup_updateList, FUPDATE_LIST_cons]
  decide

example :
    ([0, 1] : List Nat).mapM lookupState.locals.lookup =
      ([CrepExpHOL.var (width := 8) 0, CrepExpHOL.var (width := 8) 1]).mapM
        (Flapjack.evalCrepSemHOLExp lookupState) :=
  Flapjack.lookupLocalsEqMapVarsHOL [0, 1] lookupState

end Flapjack.Test.CrepHolStateParity
