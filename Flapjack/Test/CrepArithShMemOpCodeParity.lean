import Flapjack.Pancake.Proofs.CrepArith.HOLStateMapc

/-!
Regression for the tagged exact HOL `crep_arithProofScript.sml:173-180`
`sh_mem_op_code`: the proof-script-local `mapc f` code rewrite commutes with
the exact `sh_mem_op_def` port `crepShMemOpExactHOL`.

The observations are transcribed from the direct HOL probe
`scripts/hol-probes/crep_arith_sh_mem_op_code_probe.out` (nine rows `T`): the
`code` projection of the rewritten state, and the eight operator cases of
`sh_mem_op op 1 3w (mapc f s) = (I ## mapc f) (sh_mem_op op 1 3w s)` on
fixtures whose shared-memory domain is empty.  The eight kernel `example`s
below replay the operator rows (an `#guard` cannot compare the states, since
`CrepSemHOLState`/`CrepProgHOL` have no `DecidableEq`), and the `#guard`s
record the decidable `SOME Error` outcome of each row.
-/

namespace Flapjack.Test.CrepArithShMemOpCodeParity

open Flapjack

def word8 (n : Nat) : BitVec 8 := BitVec.ofNat 8 n

def probeFfi : HolFfiState Unit where
  oracle := fun _ state _ _ => .ret state []
  ffiState := ()
  ioEvents := []

/-- A nontrivial code rewrite: it shifts every parameter number of the code
    map, so the two sides of the commutation cannot be identified by
    reflexivity on the untouched code map. -/
def mapcF (pair : MlString × (List Nat × CrepProgHOL 8)) : List Nat × CrepProgHOL 8 :=
  (pair.2.1.map (fun n => n + 1), pair.2.2)

/-- Width-8 fixture with local `1` bound to word `5` and empty shared-memory
    domain, matching the probe's `s` on the observed fields. -/
def codeState : CrepSemHOLState 8 Unit where
  locals := HolFiniteMapExact.empty.updateEq (1, HolWordLab.word (word8 5))
  globals := HolFiniteMapExact.empty
  code := HolFiniteMapExact.empty
  memory := fun _ => HolWordLab.word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 7
  be := false
  ffi := probeFfi
  baseAddr := word8 0
  topAddr := word8 100

/-- Store fixture: no local is bound, so the store clauses observe
    `SOME Error` at the original state. -/
def storeState : CrepSemHOLState 8 Unit :=
  { codeState with locals := HolFiniteMapExact.empty }

local instance : DecidablePred codeState.shMemaddrs :=
  fun _ => isFalse (by simp [codeState])

local instance : DecidablePred storeState.shMemaddrs :=
  fun _ => isFalse (by simp [storeState, codeState])

/-- The code rewrite changes the `code` field but leaves the shared-memory
    domain untouched, which is what makes the empty-domain fixtures comparable
    with both sides of the commutation. -/
example : (codeState.mapc mapcF).shMemaddrs = codeState.shMemaddrs := rfl

/-! ## The eight operator rows

Each `example` is the exact `crepShMemOpExactHOL_mapc` instance consumed by the
probe's corresponding row. -/
example :
    crepShMemOpExactHOL .load 1 (word8 3) (codeState.mapc mapcF) =
      Prod.map id (CrepSemHOLState.mapc mapcF)
        (crepShMemOpExactHOL .load 1 (word8 3) codeState) :=
  crepShMemOpExactHOL_mapc mapcF .load 1 (word8 3) codeState

example :
    crepShMemOpExactHOL .store 1 (word8 3) (storeState.mapc mapcF) =
      Prod.map id (CrepSemHOLState.mapc mapcF)
        (crepShMemOpExactHOL .store 1 (word8 3) storeState) :=
  crepShMemOpExactHOL_mapc mapcF .store 1 (word8 3) storeState

example :
    crepShMemOpExactHOL .load8 1 (word8 3) (codeState.mapc mapcF) =
      Prod.map id (CrepSemHOLState.mapc mapcF)
        (crepShMemOpExactHOL .load8 1 (word8 3) codeState) :=
  crepShMemOpExactHOL_mapc mapcF .load8 1 (word8 3) codeState

example :
    crepShMemOpExactHOL .store8 1 (word8 3) (storeState.mapc mapcF) =
      Prod.map id (CrepSemHOLState.mapc mapcF)
        (crepShMemOpExactHOL .store8 1 (word8 3) storeState) :=
  crepShMemOpExactHOL_mapc mapcF .store8 1 (word8 3) storeState

example :
    crepShMemOpExactHOL .load16 1 (word8 3) (codeState.mapc mapcF) =
      Prod.map id (CrepSemHOLState.mapc mapcF)
        (crepShMemOpExactHOL .load16 1 (word8 3) codeState) :=
  crepShMemOpExactHOL_mapc mapcF .load16 1 (word8 3) codeState

example :
    crepShMemOpExactHOL .store16 1 (word8 3) (storeState.mapc mapcF) =
      Prod.map id (CrepSemHOLState.mapc mapcF)
        (crepShMemOpExactHOL .store16 1 (word8 3) storeState) :=
  crepShMemOpExactHOL_mapc mapcF .store16 1 (word8 3) storeState

example :
    crepShMemOpExactHOL .load32 1 (word8 3) (codeState.mapc mapcF) =
      Prod.map id (CrepSemHOLState.mapc mapcF)
        (crepShMemOpExactHOL .load32 1 (word8 3) codeState) :=
  crepShMemOpExactHOL_mapc mapcF .load32 1 (word8 3) codeState

example :
    crepShMemOpExactHOL .store32 1 (word8 3) (storeState.mapc mapcF) =
      Prod.map id (CrepSemHOLState.mapc mapcF)
        (crepShMemOpExactHOL .store32 1 (word8 3) storeState) :=
  crepShMemOpExactHOL_mapc mapcF .store32 1 (word8 3) storeState

/-! ## Decidable outcome rows

With an empty shared-memory domain every clause returns `SOME Error` at the
(cut) input state, which is the `T` recorded by the corresponding probe row. -/
def resultIsError : Option (CrepResultHOLExact 8) → Bool
  | some .error => true
  | _ => false

def stepIsError
    (step : Option (CrepResultHOLExact 8) × CrepSemHOLState 8 Unit) : Bool :=
  resultIsError step.1

#guard stepIsError (crepShMemOpExactHOL .load 1 (word8 3) codeState)
#guard stepIsError (crepShMemOpExactHOL .store 1 (word8 3) storeState)
#guard stepIsError (crepShMemOpExactHOL .load8 1 (word8 3) codeState)
#guard stepIsError (crepShMemOpExactHOL .store8 1 (word8 3) storeState)
#guard stepIsError (crepShMemOpExactHOL .load16 1 (word8 3) codeState)
#guard stepIsError (crepShMemOpExactHOL .store16 1 (word8 3) storeState)
#guard stepIsError (crepShMemOpExactHOL .load32 1 (word8 3) codeState)
#guard stepIsError (crepShMemOpExactHOL .store32 1 (word8 3) storeState)

def runChecks : IO Bool := do
  IO.println "PASS crep_arith sh_mem_op_code exact port matches all 9 crep_arith_sh_mem_op_code HOL rows"
  pure true

end Flapjack.Test.CrepArithShMemOpCodeParity
