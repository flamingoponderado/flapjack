import Flapjack.RiscV.Link
import Flapjack.Ffi
import Flapjack.PanValueFfiCore

namespace Flapjack

#check @panValueFfiExtCall_returned_ioEvents_prefix

def identityFfiOracle : FfiOracle Unit :=
  fun _ state _ bytes => .returned state bytes

def identityFfiState : FfiState Unit :=
  { oracle := identityFfiOracle, state := (), ioEvents := [] }

example (state : FfiState Unit) (name : FfiName)
    (configuration bytes : List UInt8) (nextState : FfiState Unit)
    (nextBytes : List UInt8)
    (hcall : callFfi state name configuration bytes =
      .returned nextState nextBytes) :
    state.ioEvents <+: nextState.ioEvents :=
  callFfi_return_ioEvents_prefix state name configuration bytes nextState nextBytes hcall

/-! The four observations below are transcribed from
`scripts/hol-probes/ffi_call_probe.out`, generated from
`ffi_call_probeScript.sml`. They cover the source `call_FFI_def` branches in
`cakeml/semantics/ffi/ffiScript.sml:64-79`: a length-preserving return appends
the zipped I/O event, a length mismatch becomes `FFI_failed`, an oracle-final
result is preserved, and `ExtCall ""` is the identity call. -/

def parityFfiState : FfiState Unit :=
  { oracle := fun _ state _ _ => .returned state [5, 6]
    state := ()
    ioEvents := [] }

def parityOracleReturn : Bool :=
  match callFfi parityFfiState (.extCall "foo") [1, 2] [3, 4] with
  | .returned state bytes =>
      bytes == [5, 6] && state.state == () &&
        state.ioEvents ==
          [{ name := .extCall "foo", configuration := [1, 2],
             bytes := [(3, 5), (4, 6)] }]
  | .final _ => false

def parityLengthFailure : Bool :=
  match callFfi
      { parityFfiState with
          oracle := (fun _ state _ _ => .returned state [5]) }
      (.extCall "foo") [1, 2] [3, 4] with
  | .final event => event.outcome == .failed
  | .returned _ _ => false

def parityOracleFinal : Bool :=
  match callFfi
      { parityFfiState with oracle := (fun _ _ _ _ => .final .diverged) }
      (.extCall "foo") [1] [3] with
  | .final event => event.outcome == .diverged
  | .returned _ _ => false

def parityEmptyExtCall : Bool :=
  match callFfi
      { parityFfiState with oracle := (fun _ _ _ _ => .final .diverged) }
      (.extCall "") [1] [3, 4] with
  | .returned state bytes => bytes == [3, 4] && state.ioEvents == []
  | .final _ => false

#guard parityOracleReturn
#guard parityLengthFailure
#guard parityOracleFinal
#guard parityEmptyExtCall

example :
    match callFfi identityFfiState (.extCall "echo") [1, 2] [3, 4] with
    | .returned state bytes =>
        bytes = [3, 4] ∧ state.state = () ∧
          state.ioEvents =
            [{ name := .extCall "echo", configuration := [1, 2],
               bytes := [(3, 3), (4, 4)] }]
    | .final _ => False := by
  simp [callFfi, identityFfiState, identityFfiOracle]

def shortFfiOracle : FfiOracle Unit :=
  fun _ state _ _ => .returned state [7]

example :
    match callFfi { identityFfiState with oracle := shortFfiOracle }
      (.extCall "echo") [1, 2] [3, 4] with
    | .final event =>
        event =
          { name := .extCall "echo", configuration := [1, 2], bytes := [3, 4],
            outcome := .failed }
    | .returned _ _ => False := by
  simp [callFfi, identityFfiState, shortFfiOracle]

def finalFfiOracle : FfiOracle Unit :=
  fun _ _ _ _ => .final .diverged

example :
    match callFfi { identityFfiState with oracle := finalFfiOracle }
      (.extCall "echo") [1] [2] with
    | .final event =>
        event =
          { name := .extCall "echo", configuration := [1], bytes := [2],
            outcome := .diverged }
    | .returned _ _ => False := by
  simp [callFfi, finalFfiOracle]

example :
    match callFfi identityFfiState (.extCall "") [1] [2, 3] with
    | .returned state bytes => bytes = [2, 3] ∧ state.ioEvents = []
    | .final _ => False := by
  simp [callFfi, identityFfiState]

open RiscV

def combinedFfiFunctions : List (Nat × List Nat × WordProg (Word 64)) :=
  [(7, [2], .seq
    (.ffi "inc" 2 3 4 5 ([], []))
    (.return 0 [2]))]

def combinedHandlerFunctions : List (Nat × List Nat × WordProg (Word 64)) :=
  [(8, [3], .raise 3)]

def loopFfiBreakProgram : WordProg (Word 64) :=
  .seq
    (.loop []
      (.seq (.ffi "inc" 2 3 4 5 ([], [])) (.break 0)) [])
    (.return 0 [2])

end Flapjack
