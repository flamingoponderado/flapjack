import Flapjack.Pancake.Proofs.PanStructs.ConvertState
import Flapjack.Pancake.PanStructs.CompileExpExact

/-! Rows from `pan_structs_compile_exp_correct_probe.out`,
`pan_structs_compile_correct_probe.out` and `pan_structs_value_validity_probe.out`,
evaluated over finite HOL states and the compiler used by `compileTopExact`. -/
namespace Flapjack.Test.PanStructsExactOracleParity

open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.Proofs.PanStructs.ConvertState

private abbrev ml (s : String) : MlS := Flapjack.Basis.Pure.MlString.ofString s
private def ctx : ContextExact :=
  { structs := [(ml "Pair", [(ml "left", .one), (ml "right", .one)])]
    locals := [(ml "local", .comb [.one, .one])]
    globals := [] }
private def source : PanSemStateFiniteExact 8 Unit where
  locals := (HolFiniteMapExact.empty : HolFiniteMapExact MlS (ValueHOL 8)).update
    (ml "local", .rStruct [.val (.word 3), .val (.word 5)])
  globals := HolFiniteMapExact.empty
  structs := [(ml "Pair", { fields := [(ml "left", .one), (ml "right", .one)], size := 2 })]
  code := HolFiniteMapExact.empty
  eshapes := HolFiniteMapExact.empty
  memory := fun _ => .word 19
  memaddrs := fun address => address = 0
  shMemaddrs := fun _ => False
  clock := 5
  be := false
  ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
  baseAddr := 0
  topAddr := 100

private instance : DecidablePred source.memaddrs := by
  change DecidablePred (fun address : BitVec 8 => address = 0)
  infer_instance

private instance : DecidablePred (convertStateExact ctx source).memaddrs := by
  change DecidablePred (fun address : BitVec 8 => address = 0)
  infer_instance

private def sourceOutside : PanSemStateFiniteExact 8 Unit :=
  { source with memaddrs := fun _ => False }

private instance : DecidablePred sourceOutside.memaddrs := by
  change DecidablePred (fun _ : BitVec 8 => False)
  infer_instance

private def wordNat? : Option (ValueHOL 8) → Option Nat
  | some (.val (.word value)) => some value.toNat
  | _ => none

private def check (expression : ExpHOL 8) (expected : Nat) : Bool :=
  let value : ValueHOL 8 := .val (.word (BitVec.ofNat 8 expected))
  let result := source.evalHOLFinite expression
  let target := (convertStateExact ctx source).evalHOLFinite (compileExpExact ctx expression)
  (match oldExpShapeExact ctx expression with | .one => true | _ => false) &&
  (match shapeOfHOLExact value with | .one => true | _ => false) &&
  valueFldsOkHOLExact source.structs value &&
  wordNat? result == some expected && wordNat? target == some expected

private def nfield : ExpHOL 8 :=
  .nfield (ml "right") (.nstruct (ml "Pair")
    [(ml "left", .const 3), (ml "right", .const 5)])
private def rfield : ExpHOL 8 := .rfield 1 (.var .local (ml "local"))
private def loadByte : ExpHOL 8 := .loadByte (.const 0)

-- compile_exp_correct_const
#guard check (.const 13) 13
-- compile_exp_correct_op
#guard check (.op .add [.const 3, .const 5]) 8
-- compile_exp_correct_panop_mul
#guard check (.panop .mul [.const 3, .const 5]) 15
-- compile_exp_correct_cmp_equal
#guard check (.cmp .equal (.const 3) (.const 3)) 1
-- compile_exp_correct_shift_lsl
#guard check (.shift .lsl (.const 3) (.const 1)) 6
-- compile_exp_correct_base_addr / compile_exp_correct_top_addr: instantiate
-- the symbolic source-state address fields with 0 and 100.
#guard check .baseAddr 0
#guard check .topAddr 100
-- compile_exp_correct_bytes_in_word
#guard check .bytesInWord 1

-- compile_exp_correct_nfield
#guard check nfield 5
-- compile_exp_correct_rfield
#guard check rfield 5
-- compile_exp_correct_load_byte
#guard check loadByte 19
-- compile_exp_correct_load_byte_out_of_domain
#guard (sourceOutside.evalHOLFinite loadByte).isNone

-- compile_exp_correct_shift_asr
#guard check (.shift .asr (.const 128) (.const 1)) 192
-- compile_exp_correct_shift_ror
#guard check (.shift .ror (.const 129) (.const 1)) 192
-- compile_exp_correct_shift_width_cutoff
#guard (source.evalHOLFinite (.shift .lsl (.const 3) (.const 8))).isNone &&
  ((convertStateExact ctx source).evalHOLFinite
    (compileExpExact ctx (.shift .lsl (.const 3) (.const 8)))).isNone
-- convert_named_record
#guard
  match convertV (.nStruct (ml "Pair")
    [(ml "left", .val (.word 3)), (ml "right", .val (.word 5))] : ValueHOL 8) with
  | .rStruct [.val (.word a), .val (.word b)] => a == 3 && b == 5
  | _ => false

/-! The earlier executable fixture selected a field from a named local.
Keep that case alongside the original oracle's inline named record. -/
private def namedLocalCtx : ContextExact :=
  { ctx with locals := [(ml "record", .named (ml "Pair"))] }
private def namedLocalState : PanSemStateFiniteExact 8 Unit :=
  { source with
    locals := (HolFiniteMapExact.empty : HolFiniteMapExact MlS (ValueHOL 8)).update
      (ml "record", .nStruct (ml "Pair") [(ml "left", .val (.word 3)),
        (ml "right", .val (.word 5))]) }
private instance : DecidablePred namedLocalState.memaddrs := by
  change DecidablePred (fun a : BitVec 8 => a = 0)
  infer_instance
private instance : DecidablePred (convertStateExact namedLocalCtx namedLocalState).memaddrs := by
  change DecidablePred (fun a : BitVec 8 => a = 0)
  infer_instance
private def namedLocalExpr : ExpHOL 8 := .nfield (ml "right") (.var .local (ml "record"))
#guard
  (match oldExpShapeExact namedLocalCtx namedLocalExpr with | .one => true | _ => false) &&
  wordNat? (namedLocalState.evalHOLFinite namedLocalExpr) == some 5 &&
  wordNat? ((convertStateExact namedLocalCtx namedLocalState).evalHOLFinite
    (compileExpExact namedLocalCtx namedLocalExpr)) == some 5

/-! Structured loads replay the success, excluded-address and nested-name rows
of `pan_structs_compile_exp_correct_probe.out`. -/
private def loadState : PanSemStateFiniteExact 8 Unit :=
  { source with
    memory := fun a => if a = 0 then .word 3 else if a = 1 then .word 5 else .word 0
    memaddrs := fun a => a = 0 ∨ a = 1 }
private def loadOutside : PanSemStateFiniteExact 8 Unit :=
  { loadState with memaddrs := fun a => a = 1 }
private instance : DecidablePred loadState.memaddrs := by
  change DecidablePred (fun a : BitVec 8 => a = 0 ∨ a = 1)
  infer_instance
private instance : DecidablePred (convertStateExact ctx loadState).memaddrs := by
  change DecidablePred (fun a : BitVec 8 => a = 0 ∨ a = 1)
  infer_instance
private instance : DecidablePred loadOutside.memaddrs := by
  change DecidablePred (fun a : BitVec 8 => a = 1)
  infer_instance
private instance : DecidablePred (convertStateExact ctx loadOutside).memaddrs := by
  change DecidablePred (fun a : BitVec 8 => a = 1)
  infer_instance
private def loadExpr : ExpHOL 8 := .load (.comb [.one, .one]) (.const 0)
private def pairValue : ValueHOL 8 := .rStruct [.val (.word 3), .val (.word 5)]
private def isPair : Option (ValueHOL 8) → Bool
  | some (.rStruct [.val (.word a), .val (.word b)]) => a == 3 && b == 5
  | _ => false
private def isPairShape : ShapeHOL → Bool
  | .comb [.one, .one] => true
  | _ => false

-- compile_exp_correct_mmap_nonempty: the two individual checks cover every
-- member of the concrete expression list, alongside both OPT_MMAP results.
private def isWordList : Option (List (ValueHOL 8)) → Bool
  | some [.val (.word a), .val (.word b)] => a == 3 && b == 5
  | _ => false
#guard
  isWordList (([.const 3, .const 5] : List (ExpHOL 8)).mapM source.evalHOLFinite) &&
  check (.const 3) 3 && check (.const 5) 5 &&
  isWordList ((compileExpsExact ctx [.const 3, .const 5]).mapM
    (convertStateExact ctx source).evalHOLFinite)

-- compile_exp_correct_local_var
#guard isPairShape (oldExpShapeExact ctx (.var .local (ml "local") : ExpHOL 8)) &&
  isPairShape (shapeOfHOLExact pairValue) && valueFldsOkHOLExact source.structs pairValue &&
  isPair (source.evalHOLFinite (.var .local (ml "local"))) &&
  isPair ((convertStateExact ctx source).evalHOLFinite
    (compileExpExact ctx (.var .local (ml "local"))))
-- compile_exp_correct_rstruct / compile_exp_correct_rstruct_eval
#guard isPairShape (oldExpShapeExact ctx (.rstruct [.const 3, .const 5] : ExpHOL 8)) &&
  isPairShape (shapeOfHOLExact pairValue) && valueFldsOkHOLExact source.structs pairValue &&
  isPair (source.evalHOLFinite (.rstruct [.const 3, .const 5])) &&
  isPair ((convertStateExact ctx source).evalHOLFinite
    (compileExpExact ctx (.rstruct [.const 3, .const 5])))
private def namedExpr : ExpHOL 8 :=
  .nstruct (ml "Pair") [(ml "left", .const 3), (ml "right", .const 5)]
private def namedValue : ValueHOL 8 :=
  .nStruct (ml "Pair") [(ml "left", .val (.word 3)), (ml "right", .val (.word 5))]
private def isNamedPair : Option (ValueHOL 8) → Bool
  | some (.nStruct n [(l, .val (.word a)), (r, .val (.word b))]) =>
      n == ml "Pair" && l == ml "left" && r == ml "right" && a == 3 && b == 5
  | _ => false
private def isNamedPairShape : ShapeHOL → Bool
  | .named n => n == ml "Pair"
  | _ => false
-- compile_exp_correct_nstruct
#guard isNamedPairShape (oldExpShapeExact ctx namedExpr) &&
  isNamedPairShape (shapeOfHOLExact namedValue) && valueFldsOkHOLExact source.structs namedValue &&
  isNamedPair (source.evalHOLFinite namedExpr) &&
  isPair ((convertStateExact ctx source).evalHOLFinite (compileExpExact ctx namedExpr))
private def globalCtx : ContextExact := { ctx with globals := [(ml "global", .one)] }
private def globalState : PanSemStateFiniteExact 8 Unit :=
  { source with
    globals := (HolFiniteMapExact.empty : HolFiniteMapExact MlS (ValueHOL 8)).update
      (ml "global", .val (.word 7)) }
private instance : DecidablePred globalState.memaddrs := by
  change DecidablePred (fun a : BitVec 8 => a = 0)
  infer_instance
private instance : DecidablePred (convertStateExact globalCtx globalState).memaddrs := by
  change DecidablePred (fun a : BitVec 8 => a = 0)
  infer_instance
-- compile_exp_correct_global_var
#guard
  (match oldExpShapeExact globalCtx (.var .global (ml "global") : ExpHOL 8) with
    | .one => true | _ => false) &&
  (match shapeOfHOLExact (.val (.word 7) : ValueHOL 8) with | .one => true | _ => false) &&
  valueFldsOkHOLExact globalState.structs (.val (.word 7) : ValueHOL 8) &&
  wordNat? (globalState.evalHOLFinite (.var .global (ml "global"))) == some 7 &&
  wordNat? ((convertStateExact globalCtx globalState).evalHOLFinite
    (compileExpExact globalCtx (.var .global (ml "global")))) == some 7

-- compile_exp_correct_load
#guard isPairShape (oldExpShapeExact ctx loadExpr) &&
  isPairShape (shapeOfHOLExact pairValue) && valueFldsOkHOLExact loadState.structs pairValue &&
  isPair (loadState.evalHOLFinite loadExpr) &&
  isPair ((convertStateExact ctx loadState).evalHOLFinite (compileExpExact ctx loadExpr))
-- compile_exp_correct_load_out_of_domain: the probe requires inequality; this checks the stronger NONE result on both sides.
#guard isPairShape (oldExpShapeExact ctx loadExpr) &&
  isPairShape (shapeOfHOLExact pairValue) && valueFldsOkHOLExact loadOutside.structs pairValue &&
  (loadOutside.evalHOLFinite loadExpr).isNone &&
  ((convertStateExact ctx loadOutside).evalHOLFinite (compileExpExact ctx loadExpr)).isNone

private def nestedCtx : ContextExact :=
  { structs := [(ml "Pair", [(ml "inner", .named (ml "Inner")), (ml "last", .one)]),
      (ml "Inner", [(ml "left", .one), (ml "right", .one)])]
    locals := [], globals := [] }
private def nestedState : PanSemStateFiniteExact 8 Unit :=
  { source with
    structs := [(ml "Pair", { fields := [(ml "inner", .named (ml "Inner")), (ml "last", .one)], size := 3 }),
      (ml "Inner", { fields := [(ml "left", .one), (ml "right", .one)], size := 2 })]
    memory := fun a => if a = 0 then .word 7 else if a = 1 then .word 11
      else if a = 2 then .word 13 else .word 0
    memaddrs := fun a => a = 0 ∨ a = 1 ∨ a = 2 }
private instance : DecidablePred nestedState.memaddrs := by
  change DecidablePred (fun a : BitVec 8 => a = 0 ∨ a = 1 ∨ a = 2)
  infer_instance
private instance : DecidablePred (convertStateExact nestedCtx nestedState).memaddrs := by
  change DecidablePred (fun a : BitVec 8 => a = 0 ∨ a = 1 ∨ a = 2)
  infer_instance
private def nestedExpr : ExpHOL 8 := .load (.named (ml "Pair")) (.const 0)
private def nestedValue : ValueHOL 8 := .nStruct (ml "Pair")
  [(ml "inner", .nStruct (ml "Inner") [(ml "left", .val (.word 7)),
    (ml "right", .val (.word 11))]), (ml "last", .val (.word 13))]
private def isNested : Option (ValueHOL 8) → Bool
  | some (.nStruct n [(i, .nStruct m [(l, .val (.word a)), (r, .val (.word b))]),
      (last, .val (.word c))]) =>
      n == ml "Pair" && i == ml "inner" && m == ml "Inner" && l == ml "left" &&
      r == ml "right" && last == ml "last" && a == 7 && b == 11 && c == 13
  | _ => false
private def isNestedConverted : Option (ValueHOL 8) → Bool
  | some (.rStruct [.rStruct [.val (.word a), .val (.word b)], .val (.word c)]) =>
      a == 7 && b == 11 && c == 13
  | _ => false
private def isPairNamed : ShapeHOL → Bool
  | .named name => name == ml "Pair"
  | _ => false
-- compile_exp_correct_load_nested_named
#guard isPairNamed (oldExpShapeExact nestedCtx nestedExpr) &&
  isPairNamed (shapeOfHOLExact nestedValue) && valueFldsOkHOLExact nestedState.structs nestedValue &&
  isNested (nestedState.evalHOLFinite nestedExpr) &&
  isNestedConverted ((convertStateExact nestedCtx nestedState).evalHOLFinite
    (compileExpExact nestedCtx nestedExpr))

private def load32Ctx : ContextExact := { structs := [], locals := [], globals := [] }
private def load32State : PanSemStateFiniteExact 64 Unit where
  locals := HolFiniteMapExact.empty
  globals := HolFiniteMapExact.empty
  structs := []
  code := HolFiniteMapExact.empty
  eshapes := HolFiniteMapExact.empty
  memory := fun a => if a = 8 then .word 0x8877665544332211 else .word 0
  memaddrs := fun a => a = 8
  shMemaddrs := fun _ => False
  clock := 5
  be := false
  ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
  baseAddr := 0
  topAddr := 100
private instance : DecidablePred load32State.memaddrs := by
  change DecidablePred (fun a : BitVec 64 => a = 8)
  infer_instance
private instance : DecidablePred (convertStateExact load32Ctx load32State).memaddrs := by
  change DecidablePred (fun a : BitVec 64 => a = 8)
  infer_instance
private def load32Expr : ExpHOL 64 := .load32 (.const 8)
private def isLoad32Value : Option (ValueHOL 64) → Bool
  | some (.val (.word w)) => w == 0x44332211
  | _ => false
-- compile_exp_correct_load32_le_success
#guard
  (match oldExpShapeExact load32Ctx load32Expr with | .one => true | _ => false) &&
  (match shapeOfHOLExact (.val (.word (0x44332211 : BitVec 64))) with
    | .one => true | _ => false) &&
  valueFldsOkHOLExact load32State.structs (.val (.word 0x44332211) : ValueHOL 64) &&
  isLoad32Value (load32State.evalHOLFinite load32Expr) &&
  isLoad32Value ((convertStateExact load32Ctx load32State).evalHOLFinite
    (compileExpExact load32Ctx load32Expr))

/-! The original value-validity oracle includes successful and failing named
record lookups, first-match shadowing, and nested fields. -/
private def validityContext : StructContextExact :=
  [(ml "Pair", { fields := [(ml "left", .one), (ml "right", .comb [])], size := 2 })]
private def goodValue : ValueHOL 8 :=
  .nStruct (ml "Pair") [(ml "left", .val (.word 2)), (ml "right", .rStruct [])]
private def badValue : ValueHOL 8 :=
  .nStruct (ml "Pair") [(ml "left", .val (.word 2)), (ml "wrong", .rStruct [])]
private def badFirst : StructContextExact :=
  (ml "Pair", { fields := [(ml "wrong", .one)], size := 1 }) :: validityContext
private def goodFirst : StructContextExact := validityContext ++
  [(ml "Pair", { fields := [(ml "wrong", .one)], size := 1 })]
-- v_flds_ok_word
#guard valueFldsOkHOLExact validityContext (.val (.word 1) : ValueHOL 8)
-- v_flds_ok_named_match
#guard valueFldsOkHOLExact validityContext goodValue
-- v_flds_ok_named_mismatch
#guard !(valueFldsOkHOLExact validityContext badValue)
-- v_flds_ok_named_missing
#guard !(valueFldsOkHOLExact [] goodValue)
-- v_flds_ok_duplicate_first
#guard !(valueFldsOkHOLExact badFirst goodValue)
-- v_flds_ok_duplicate_second
#guard valueFldsOkHOLExact goodFirst goodValue

private def mapState : PanSemStateFiniteExact 8 Unit :=
  { source with
    locals := (HolFiniteMapExact.empty : HolFiniteMapExact MlS (ValueHOL 8)).update
      (ml "local", .val (.word 7))
    globals := (HolFiniteMapExact.empty : HolFiniteMapExact MlS (ValueHOL 8)).update
      (ml "global", .val (.word 11))
    eshapes := (HolFiniteMapExact.empty : HolFiniteMapExact MlS ShapeHOL).update
      (ml "E", .one)
    code := (HolFiniteMapExact.empty : HolFiniteMapExact MlS
      (List (MlS × ShapeHOL) × ProgHOL 8 × ShapeHOL)).update
      (ml "f", ([], .skip, .one)) }

-- convert_s_finite_maps
#guard
  let converted := convertStateExact ctx mapState
  wordNat? (converted.locals.lookup (ml "local")) == some 7 &&
  wordNat? (converted.globals.lookup (ml "global")) == some 11 &&
  (match converted.eshapes.lookup (ml "E") with | some .one => true | _ => false) &&
  (match converted.code.lookup (ml "f") with | some ([], .skip, .one) => true | _ => false)

/-! These state equations replay the original skip, break, continue and tick
rows, with the complete post-state retained in each equality. -/
-- compile_correct_skip_source
example (s : PanSemStateFiniteExact 8 Unit) :
    PanSemStateFiniteExact.evaluateHOLFiniteState s .skip = (none, s) :=
  PanSemStateFiniteExact.evaluateHOLFiniteState_skip s
-- compile_correct_skip_converted
example (s : PanSemStateFiniteExact 8 Unit) :
    PanSemStateFiniteExact.evaluateHOLFiniteState (convertStateExact ctx s) .skip =
      (none, convertStateExact ctx s) :=
  PanSemStateFiniteExact.evaluateHOLFiniteState_skip _
-- compile_correct_break_source
example (s : PanSemStateFiniteExact 8 Unit) :
    PanSemStateFiniteExact.evaluateHOLFiniteState s .break = (some .break, s) :=
  PanSemStateFiniteExact.evaluateHOLFiniteState_break s
-- compile_correct_break_converted
example (s : PanSemStateFiniteExact 8 Unit) :
    PanSemStateFiniteExact.evaluateHOLFiniteState (convertStateExact ctx s) .break =
      (some .break, convertStateExact ctx s) :=
  PanSemStateFiniteExact.evaluateHOLFiniteState_break _
-- compile_correct_continue_source
example (s : PanSemStateFiniteExact 8 Unit) :
    PanSemStateFiniteExact.evaluateHOLFiniteState s .continue = (some .continue, s) :=
  PanSemStateFiniteExact.evaluateHOLFiniteState_continue s
-- compile_correct_continue_converted
example (s : PanSemStateFiniteExact 8 Unit) :
    PanSemStateFiniteExact.evaluateHOLFiniteState (convertStateExact ctx s) .continue =
      (some .continue, convertStateExact ctx s) :=
  PanSemStateFiniteExact.evaluateHOLFiniteState_continue _
-- compile_correct_tick_zero_source
example (s : PanSemStateFiniteExact 8 Unit) :
    PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := 0 } .tick =
      (some .timeOut, PanSemStateFiniteExact.emptyLocalsHOLFinite { s with clock := 0 }) := by
  simp [PanSemStateFiniteExact.evaluateHOLFiniteState_tick]
-- compile_correct_tick_positive_source
example (s : PanSemStateFiniteExact 8 Unit) :
    PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := 1 } .tick =
      (none, { s with clock := 0 }) := by
  simp [PanSemStateFiniteExact.evaluateHOLFiniteState_tick,
    PanSemStateFiniteExact.decClockHOLFinite]
-- compile_correct_tick_zero_converted
example (s : PanSemStateFiniteExact 8 Unit) :
    PanSemStateFiniteExact.evaluateHOLFiniteState
      (convertStateExact ctx { s with clock := 0 }) .tick =
      (some .timeOut, PanSemStateFiniteExact.emptyLocalsHOLFinite
        (convertStateExact ctx { s with clock := 0 })) := by
  simp [PanSemStateFiniteExact.evaluateHOLFiniteState_tick, convertStateExact]
-- compile_correct_tick_positive_converted
example (s : PanSemStateFiniteExact 8 Unit) :
    PanSemStateFiniteExact.evaluateHOLFiniteState
      (convertStateExact ctx { s with clock := 1 }) .tick =
      (none, { convertStateExact ctx { s with clock := 1 } with clock := 0 }) := by
  simp [PanSemStateFiniteExact.evaluateHOLFiniteState_tick, convertStateExact,
    PanSemStateFiniteExact.decClockHOLFinite]

end Flapjack.Test.PanStructsExactOracleParity
