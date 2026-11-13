module

public import Flapjack.Compiler.Backend.StackNames.ProgramNames
public import Flapjack.Compiler.Backend.StackNames.NamesOk

-- Checks below run compiled code from these modules.
public meta import Flapjack.Compiler.Backend.StackNames.ProgramNames
public meta import Flapjack.Compiler.Backend.StackNames.NamesOk
@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Flapjack.Test.StackNamesParity

open Flapjack
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Encoders.Asm

private abbrev W := BitVec 8

private abbrev PT := HolProg 8

/-- Renaming map `3 |-> 7` (HOL oracle `sptree$insert 3 7 (sptree$LN)`). -/
private def names : Spt Nat := sptInsert 3 7 .ln

/-- Empty renaming map. -/
private def emptyNames : Spt Nat := .ln

/-- Colliding map `0 |-> 1`, `1 |-> 1`. -/
private def dupNames : Spt Nat := sptInsert 1 1 (sptInsert 0 1 .ln)

private def isReg7 : Bool :=
  match riFindNameHOL (width := 8) names (.reg 3 : HolRegImm 8) with
  | .reg 7 => true
  | _ => false

private def isConst7 : Bool :=
  match instFindNameHOL (width := 8) names (.const 3 (0 : W) : HolInst 8) with
  | .const 7 _ => true
  | _ => false

private def isHalt7 (p : PT) : Bool :=
  match p with
  | .halt 7 => true
  | _ => false

/-- The reviewed predicate's decidable instance, unfolded once here rather than
restated, so the executable view below is `decide` on `namesOkSptHOL` itself. -/
@[reducible] private def namesOkDecidable (names : Spt Nat) (regCount : Nat)
    (avoidRegs : List Nat) : Decidable (namesOkSptHOL names regCount avoidRegs) := by
  unfold namesOkSptHOL
  infer_instance

/-- Executable view of the reviewed `names_ok` predicate (no restated clauses). -/
@[reducible] private def namesOkB (names : Spt Nat) (regCount : Nat)
    (avoidRegs : List Nat) : Bool :=
  @decide (namesOkSptHOL names regCount avoidRegs) (namesOkDecidable names regCount avoidRegs)

private def mapFstSample : List (Nat × PT) := [(1, .halt 3), (2, .raise 4)]

-- `ri_find_name`
example : riFindNameHOL (width := 8) names (HolRegImm.reg 3) = HolRegImm.reg 7 := by
  simp [riFindNameHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : riFindNameHOL (width := 8) names (HolRegImm.imm (0 : W)) =
    HolRegImm.imm (0 : W) := by
  simp [riFindNameHOL]

-- `inst_find_name`
example : instFindNameHOL (width := 8) names (HolInst.const 3 (0 : W)) =
    HolInst.const 7 (0 : W) := by
  simp [instFindNameHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : instFindNameHOL (width := 8) names (HolInst.arith (HolArith.div 3 4 5)) =
    HolInst.arith (HolArith.div 7 4 5) := by
  simp [instFindNameHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : instFindNameHOL (width := 8) names (HolInst.fp (.fpFma 1 2 3)) =
    HolInst.fp (.fpFma 1 2 3) := by
  simp [instFindNameHOL]
example : instFindNameHOL (width := 8) names
    (HolInst.mem .load 3 (HolAddr.addr 3 (8 : W))) =
    HolInst.mem .load 7 (HolAddr.addr 7 (8 : W)) := by
  simp [instFindNameHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]

-- `dest_find_name`
example : destFindNameHOL names (.inr 3 : Sum Nat Nat) = .inr 7 := by
  simp [destFindNameHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : destFindNameHOL names (.inl 2 : Sum Nat Nat) = .inl 2 := by
  simp [destFindNameHOL]

-- `comp` / `prog_comp` / `compile`
example : progCompHOL names (.seq (.inst (.const 3 0)) (.halt 3) : PT) =
    (.seq (.inst (.const 7 0)) (.halt 7) : PT) := by
  simp [progCompHOL, instFindNameHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : progCompHOL names
    (.call (some (.raise 3, 4, 5, 6)) (.inr 3) (some (.halt 4, 8, 9)) : PT) =
    (.call (some (.raise 7, 4, 5, 6)) (.inr 7) (some (.halt 4, 8, 9)) : PT) := by
  simp [progCompHOL, destFindNameHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : progCompEntryHOL names ((1, .halt 3) : Nat × PT) = (1, .halt 7) := by
  simp [progCompEntryHOL, progCompHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : compileHOL names mapFstSample = [(1, .halt 7), (2, .raise 4)] := by
  simp [compileHOL, progCompEntryHOL, progCompHOL, findNameSpt, mapFstSample, names,
    Flapjack.sptInsert, Flapjack.sptLookup]

-- `names_ok`
example : namesOkB names 4 [0, 1] = false := by
  simp [namesOkB, namesOkSptHOL, findName, names, Flapjack.sptInsert, Flapjack.sptLookup,
    Flapjack.FLOOKUP, List.range_succ]
example : namesOkB emptyNames 8 [] = true := by
  simp [namesOkB, namesOkSptHOL, findName, emptyNames, Flapjack.FLOOKUP,
    List.range_succ]
example : namesOkB dupNames 4 [] = false := by
  simp [namesOkB, namesOkSptHOL, findName, dupNames, Flapjack.sptInsert, Flapjack.sptLookup,
    Flapjack.FLOOKUP, List.range_succ]
example : namesOkSptHOL emptyNames 8 [] := by
  simp [namesOkSptHOL, findName, emptyNames, Flapjack.FLOOKUP, List.range_succ]
example : ¬namesOkSptHOL names 4 [0, 1] := by
  simp [namesOkSptHOL, findName, names, Flapjack.sptInsert, Flapjack.sptLookup,
    Flapjack.FLOOKUP, List.range_succ]

-- `MAP_FST_compile`
example : (compileHOL names mapFstSample).map Prod.fst = mapFstSample.map Prod.fst :=
  map_fst_compileHOL names mapFstSample

private def parityGuard : Bool :=
  isReg7 && isConst7 &&
  (match destFindNameHOL names (.inr 3 : Sum Nat Nat) with | .inr 7 => true | _ => false) &&
  (namesOkB names 4 [0, 1] == false) &&
  (namesOkB emptyNames 8 [] == true) &&
  (namesOkB dupNames 4 [] == false) &&
  ((compileHOL names mapFstSample).map Prod.fst == mapFstSample.map Prod.fst) &&
  (match compileHOL names [(1, .halt 3)] with
   | [(1, p)] => isHalt7 p
   | _ => false)

#guard parityGuard

/-- The `stack_names` renaming port matches every direct HOL EVAL row. -/
def runChecks : IO Bool := do
  IO.println "PASS stack_names ri_find_name/inst_find_name/dest_find_name/comp/compile/names_ok match the HOL oracle"
  pure parityGuard

end Flapjack.Test.StackNamesParity

-- Canonical Spt API replays: absent entries retain their original registers;
-- a collision in the generated names violates ALL_DISTINCT.
example : Flapjack.Compiler.Backend.StackNames.namesOkSptHOL .ln 8 [] := by
  simp [Flapjack.Compiler.Backend.StackNames.namesOkSptHOL,
    Flapjack.Compiler.Backend.StackNames.findName, Flapjack.sptLookup,
    Flapjack.FLOOKUP, List.range_succ]
example : ¬ Flapjack.Compiler.Backend.StackNames.namesOkSptHOL
    (Flapjack.sptInsert 0 1 .ln) 2 [] := by
  simp [Flapjack.Compiler.Backend.StackNames.namesOkSptHOL,
    Flapjack.Compiler.Backend.StackNames.findName, Flapjack.sptLookup,
    Flapjack.FLOOKUP, List.range_succ]
