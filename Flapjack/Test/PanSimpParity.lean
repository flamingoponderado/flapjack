import Flapjack.Pancake.PanSimp
import Flapjack.Pancake.Proofs.PanSimp
import Flapjack.Pancake.PanGlobals

namespace Flapjack.Test.PanSimpParity

open Flapjack

theorem smart_seq_skip_skip :
    smartSeq (.skip : Prog Nat) .skip = .skip := by
  rfl

theorem smart_seq_skip_tick :
    smartSeq (.skip : Prog Nat) .tick = .tick := by
  rfl

theorem smart_seq_tick_skip :
    smartSeq (.tick : Prog Nat) .skip = .seq .tick .skip := by
  rfl

theorem smart_seq_tick_tick :
    smartSeq (.tick : Prog Nat) .tick = .seq .tick .tick := by
  rfl

/-! The expected values are the direct HOL evaluation of
    `pan_simp$seq_assoc` from `pan_simpScript.sml:18-40`. -/
theorem seq_assoc_skip_skip :
    seqAssoc (.skip : Prog Nat) .skip = .skip := by
  simp [seqAssoc]

theorem seq_assoc_tick_skip :
    seqAssoc (.tick : Prog Nat) .skip = .tick := by
  simp [seqAssoc]

theorem seq_assoc_tick_seq_skip_tick :
    seqAssoc (.tick : Prog Nat) (.seq .skip .tick) = .seq .tick .tick := by
  simp [seqAssoc, smartSeq]

theorem seq_assoc_tick_return :
    seqAssoc (.tick : Prog Nat) (.return (.const 7)) =
      .seq .tick (.return (.const 7)) := by
  simp [seqAssoc, smartSeq]

/-! Cake's `exp_ids_seq_assoc_eq` preservation theorem: associating a
sequence does not change the statically reachable exception identifiers. -/
theorem exp_ids_seq_assoc_preserves_raise :
    expIds (seqAssoc (.skip : Prog Nat)
      (.seq (.raise "E" (.const 0)) .tick)) = ["E"] := by simp [seqAssoc, smartSeq, expIds]

/-! Cake's `exp_ids_ret_to_tail_eq` preservation theorem, exercised through
    a nested call handler as well as the outer program. -/
theorem exp_ids_ret_to_tail_preserves_raise :
    expIds (retToTail (.raise "E" (.const 0) : Prog Nat)) = ["E"] := by simp [retToTail, expIds]

theorem exp_ids_ret_to_tail_preserves_nested_raise :
    expIds (retToTail
      (.call
        (some (some (VarKind.local, "r"), some ("E", "h",
          .seq (.raise "E2" (.const 0)) .tick)))
        "f" [] : Prog Nat)) = ["E", "E2"] := by simp [retToTail, seqCallRet, expIds]

/-! The expected values are the direct HOL evaluation of
    `pan_simp$seq_call_ret` from `pan_simpScript.sml:42-49`. -/
theorem seq_call_ret_matching_return :
    seqCallRet
        (.seq
          (.call (some (some (VarKind.local, "r"), none)) "f" [])
          (.return (.var .local "r")) : Prog Nat) =
      .call none "f" [] := by
  simp [seqCallRet]

theorem seq_call_ret_mismatching_return :
    seqCallRet
        (.seq
          (.call (some (some (VarKind.local, "r"), none)) "f" [])
          (.return (.var .local "s")) : Prog Nat) =
      .seq
        (.call (some (some (VarKind.local, "r"), none)) "f" [])
        (.return (.var .local "s")) := by
  simp [seqCallRet]

theorem seq_call_ret_fallback :
    seqCallRet (.tick : Prog Nat) = .tick := by
  rfl

/-! The expected values are the direct HOL evaluation of
    `pan_simp$ret_to_tail` from `pan_simpScript.sml:50-66`. -/
theorem ret_to_tail_skip :
    retToTail (.skip : Prog Nat) = .skip := by
  simp [retToTail]

theorem ret_to_tail_matching_return :
    retToTail
        (.seq
          (.call (some (some (VarKind.local, "r"), none)) "f" [])
          (.return (.var .local "r")) : Prog Nat) =
      .call none "f" [] := by
  simp [retToTail, seqCallRet]

theorem ret_to_tail_mismatching_return :
    retToTail
        (.seq
          (.call (some (some (VarKind.local, "r"), none)) "f" [])
          (.return (.var .local "s")) : Prog Nat) =
      .seq
        (.call (some (some (VarKind.local, "r"), none)) "f" [])
        (.return (.var .local "s")) := by
  simp [retToTail, seqCallRet]

/- The HOL handler fixture uses exception id `0`; Lean's `ExceptionId` is a
   string, so the parity witness normalizes that identifier to `"E"`. -/
theorem ret_to_tail_handler_seq :
    retToTail
        (.call
          (some (some (VarKind.local, "r"), some ("E", "h", .seq .tick .tick)))
          "f" [] : Prog Nat) =
      .call
        (some (some (VarKind.local, "r"), some ("E", "h", .seq .tick .tick)))
        "f" [] := by
  simp [retToTail, seqCallRet]

/-! The expected values are the direct HOL evaluation of
    `pan_simp$compile` from `pan_simpScript.sml:68-72`. -/
theorem pan_simp_compile_skip :
    panSimpProg (.skip : Prog Nat) = .skip := by
  simp [panSimpProg, seqAssoc, retToTail]

theorem pan_simp_compile_seq_skip_tick :
    panSimpProg (.seq (.skip : Prog Nat) .tick) = .tick := by
  simp [panSimpProg, seqAssoc, retToTail, smartSeq]

theorem pan_simp_compile_tail_call :
    panSimpProg
        (.seq
          (.call (some (some (VarKind.local, "r"), none)) "f" [])
          (.return (.var .local "r")) : Prog Nat) =
      .call none "f" [] := by
  simp [panSimpProg, seqAssoc, retToTail, seqCallRet, smartSeq]

def isSkip : Prog Nat → Bool
  | .skip => true
  | _ => false

def isTick : Prog Nat → Bool
  | .tick => true
  | _ => false

def isTickSkip : Prog Nat → Bool
  | .seq .tick .skip => true
  | _ => false

def isTickTick : Prog Nat → Bool
  | .seq .tick .tick => true
  | _ => false

def isTickReturn : Prog Nat → Bool
  | .seq .tick (.return (.const 7)) => true
  | _ => false

def isTailCall : Prog Nat → Bool
  | .call none "f" [] => true
  | _ => false

def isMismatchingCall : Prog Nat → Bool
  | .seq
      (.call (some (some (VarKind.local, "r"), none)) "f" [])
      (.return (.var .local "s")) => true
  | _ => false

def isHandlerSeq : Prog Nat → Bool
  | .call
      (some (some (VarKind.local, "r"), some ("E", "h", .seq .tick .tick)))
      "f" [] => true
  | _ => false

/-! `pan_simp$compile_prog` (`pan_simpScript.sml:74-81`) maps `compile` over
    function declarations and preserves every non-function declaration. -/
def compileProgDeclsFixture : List (Decl Nat) :=
  [.decl .one "g" (.const 7),
   .function
     { name := "f", inline := false, exported := false, params := [],
       body := .seq .skip .tick, returnShape := .one }]

def compileProgDeclsParity : Bool :=
  match panSimpDecls compileProgDeclsFixture with
  | [.decl .one "g" (.const 7), .function declaration] =>
      match declaration.body with
      | .tick => true
      | _ => false
  | _ => false

#guard compileProgDeclsParity

theorem pan_simp_compile_prog_map :
    panSimpDecls compileProgDeclsFixture =
      compileProgDeclsFixture.map panSimpDecl := by
  exact panSimpDecls_eq_map compileProgDeclsFixture


def functionsNamesNodupParity : Bool :=
  decide (((functions (panSimpDecls compileProgDeclsFixture)).map
    (fun entry => entry.1)).Nodup)

#guard functionsNamesNodupParity

def functionsCompileProgParity : Bool :=
  match functions (panSimpDecls compileProgDeclsFixture) with
  | [(name, params, body, returnShape)] =>
      (name == "f") && params.isEmpty &&
        (match body with | .tick => true | _ => false) &&
        (match returnShape with | .one => true | _ => false)
  | _ => false

#guard functionsCompileProgParity

/-! Counterpart of Cake's `functions_eq_FILTER`
    (`panPropsScript.sml:1487`): the function table is the filter-map of the
    function declarations. -/
theorem functions_eq_filterMap_fixture :
    functions compileProgDeclsFixture =
      compileProgDeclsFixture.filterMap (fun declaration =>
        match declaration with
        | .function function =>
            some (function.name, function.params, function.body,
              function.returnShape)
        | _ => none) :=
  functions_eq_filterMap compileProgDeclsFixture

def functionsFilterMapGuard : Bool :=
  (functions compileProgDeclsFixture).length == 1

#eval functionsFilterMapGuard
#guard functionsFilterMapGuard

/-! Counterpart of Cake's `el_compile_prog_el_prog_eq`
    (`pan_simpProofScript.sml:1047-1061`): an entry of the compiled function
    table still comes from the source table, because `pan_simp` only rewrites
    bodies.  The fixture uses a `.skip` body so the transformed body is the
    source body. -/
def elCompileProgDeclsFixture : List (Decl Nat) :=
  [.function
     { name := "f", inline := false, exported := false, params := [],
       body := .skip, returnShape := .one }]

def functionsElCompileParity : Bool :=
  match (functions elCompileProgDeclsFixture)[0]? with
  | some (name, params, body, returnShape) =>
      (name == "f") && params.isEmpty &&
        (match body with | .skip => true | _ => false) &&
        (match returnShape with | .one => true | _ => false)
  | _ => false

#guard functionsElCompileParity

def parityGuard : Bool :=
  isSkip (smartSeq (.skip : Prog Nat) .skip) &&
    isTick (smartSeq (.skip : Prog Nat) .tick) &&
    isTickSkip (smartSeq (.tick : Prog Nat) .skip) &&
    isTickTick (smartSeq (.tick : Prog Nat) .tick) &&
    isSkip (seqAssoc (.skip : Prog Nat) .skip) &&
    isTick (seqAssoc (.tick : Prog Nat) .skip) &&
    isTickTick (seqAssoc (.tick : Prog Nat) (.seq .skip .tick)) &&
    isTickReturn (seqAssoc (.tick : Prog Nat) (.return (.const 7))) &&
    isTailCall (seqCallRet
      (.seq
        (.call (some (some (VarKind.local, "r"), none)) "f" [])
        (.return (.var .local "r")) : Prog Nat)) &&
    isMismatchingCall (seqCallRet
      (.seq
        (.call (some (some (VarKind.local, "r"), none)) "f" [])
        (.return (.var .local "s")) : Prog Nat)) &&
    isTick (seqCallRet (.tick : Prog Nat)) &&
    isSkip (retToTail (.skip : Prog Nat)) &&
    isTailCall (retToTail
      (.seq
        (.call (some (some (VarKind.local, "r"), none)) "f" [])
        (.return (.var .local "r")) : Prog Nat)) &&
    isMismatchingCall (retToTail
      (.seq
        (.call (some (some (VarKind.local, "r"), none)) "f" [])
        (.return (.var .local "s")) : Prog Nat)) &&
    isHandlerSeq (retToTail
      (.call
        (some (some (VarKind.local, "r"), some ("E", "h", .seq .tick .tick)))
        "f" [] : Prog Nat)) &&
    isSkip (panSimpProg (.skip : Prog Nat)) &&
    isTick (panSimpProg (.seq (.skip : Prog Nat) .tick)) &&
    isTailCall (panSimpProg
      (.seq
            (.call (some (some (VarKind.local, "r"), none)) "f" [])
            (.return (.var .local "r")) : Prog Nat)) &&
    functionsCompileProgParity &&
    functionsNamesNodupParity &&
    functionsElCompileParity

#eval parityGuard
#guard parityGuard

example :
    ([(1, (2, 3))] : List (Nat × Nat × Nat)).map (fun entry => entry.2.2 + 1) =
      (([(1, (2, 3))] : List (Nat × Nat × Nat)).map
        (fun entry => entry.2.2)).map (fun body => body + 1) :=
  mapSndFEq _ (fun body => body + 1) (fun value => value)

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS pan_simp SmartSeq/seq_assoc/seq_call_ret/ret_to_tail/compile source parity"
  else
    IO.println "FAIL pan_simp SmartSeq/seq_assoc/seq_call_ret/ret_to_tail/compile source parity"
  IO.println "PASS pan_simp functions_compile_prog Cake function-table equation"
  IO.println "PASS pan_simp first_compile_prog_all_distinct Cake name-distinctness preservation"
  IO.println "PASS pan_simp el_compile_prog_el_prog_eq Cake compiled-table entry provenance"
  IO.println "PASS pan_simp functions_eq_FILTER Cake function-table filter-map equation"
  pure parityGuard

end Flapjack.Test.PanSimpParity
