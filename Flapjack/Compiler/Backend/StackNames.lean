import Flapjack.Compiler.Backend.StackLang
import Flapjack.Compiler.Backend.StackLang.Prog
import Flapjack.Compiler.Encoders.Asm
import Flapjack.Pancake.WordLang
import Flapjack.FiniteMap.Basic
import Flapjack.HolRef

/-!
# StackNames compatibility helpers

Counterpart of `cakeml/compiler/backend/stack_namesScript.sml`. This module
retains untagged lookup-function compatibility APIs. HOL names is `num_map`
(`Spt Nat`), and its `find_name` overload is `misc$tlookup`, with the original
register as the missing-key default. An unrestricted `FiniteMap` lookup function
is not the HOL carrier and matching clauses alone do not justify exact tags.

Reviewed Spt definitions and width-indexed exact operand/instruction/program
ports live in the `StackNames` submodules. `NamesOk.lean` owns the canonical
Spt predicate `namesOkSptHOL` and its source-shaped implication theorems.
The Boolean `namesOk` and function-backed `namesOkHOL` here remain untagged.
-/

namespace Flapjack.Compiler.Backend.StackNames

open Flapjack
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- `misc$tlookup` instantiated at the register map: rename a register when it
is in the domain, otherwise keep it.  HOL writes this overload as
`find_name`. -/
def findName (names : FiniteMap Nat Nat) (register : Nat) : Nat :=
  match FLOOKUP names register with
  | some value => value
  | none => register

/-- HOL `ri_find_name_def` (`stack_namesScript.sml:16-19`), polymorphic in the
word type as in HOL (width-indexed, since HOL's `'a` is an actual word): rename the register of a register-immediate. -/
/- Untagged Flapjack rendering: HOL names uses Spt Nat, while this API
accepts an unrestricted lookup function. Exact carrier migration remains open
under flapjack-pxn.18.5.15.7.7; matching clauses do not justify an exact tag. -/
def riFindName {width : Nat} [NeZero width] (names : FiniteMap Nat Nat) :
    WordRegImm (BitVec width) → WordRegImm (BitVec width)
  | .reg register => .reg (findName names register)
  | .imm value => .imm value

/-- HOL `inst_find_name_def` (`stack_namesScript.sml:21-49`), polymorphic in
the word type as in HOL (width-indexed, since HOL's `'a` is an actual word): rename every register of an instruction. -/
/- Untagged Flapjack rendering: HOL names uses Spt Nat, while this API
accepts an unrestricted lookup function. Exact carrier migration remains open
under flapjack-pxn.18.5.15.7.7; matching clauses do not justify an exact tag. -/
def instFindName {width : Nat} [NeZero width] (names : FiniteMap Nat Nat) :
    WordLangInst (BitVec width) → WordLangInst (BitVec width)
  | .skip => .skip
  | .const destination value => .const (findName names destination) value
  | .arith (.binop operator destination source right) =>
      .arith (.binop operator (findName names destination) (findName names source) (riFindName names right))
  | .arith (.shift operator destination source right) =>
      .arith (.shift operator (findName names destination) (findName names source) (riFindName names right))
  | .arith (.div r1 r2 r3) =>
      .arith (.div (findName names r1) (findName names r2) (findName names r3))
  | .arith (.addCarry r1 r2 r3 r4) =>
      .arith (.addCarry (findName names r1) (findName names r2) (findName names r3) (findName names r4))
  | .arith (.addOverflow r1 r2 r3 r4) =>
      .arith (.addOverflow (findName names r1) (findName names r2) (findName names r3) (findName names r4))
  | .arith (.subOverflow r1 r2 r3 r4) =>
      .arith (.subOverflow (findName names r1) (findName names r2) (findName names r3) (findName names r4))
  | .arith (.longMul r1 r2 r3 r4) =>
      .arith (.longMul (findName names r1) (findName names r2) (findName names r3) (findName names r4))
  | .arith (.longDiv r1 r2 r3 r4 r5) =>
      .arith (.longDiv (findName names r1) (findName names r2) (findName names r3) (findName names r4) (findName names r5))
  | .mem operator register (.addr base offset) =>
      .mem operator (findName names register) (.addr (findName names base) offset)

/-- HOL `dest_find_name_def` (`stack_namesScript.sml:51-54`). -/
/- Untagged Flapjack rendering: HOL names uses Spt Nat, while this API
accepts an unrestricted lookup function. Exact carrier migration remains open
under flapjack-pxn.18.5.15.7.7; matching clauses do not justify an exact tag. -/
def destFindName (names : FiniteMap Nat Nat) : Sum Nat Nat → Sum Nat Nat
  | .inr register => .inr (findName names register)
  | other => other

/-- HOL `comp_def` (`stack_namesScript.sml:56-99`) over the exact
width-indexed `HolProg` carrier: rename every register of every instruction,
leaving the `mlstring` FFI name untouched. -/
/- Untagged Flapjack rendering: HOL names uses Spt Nat, while this API
accepts an unrestricted lookup function. Exact carrier migration remains open
under flapjack-pxn.18.5.15.7.7; matching clauses do not justify an exact tag. -/
def progComp {width : Nat} [NeZero width] (names : FiniteMap Nat Nat) :
    HolProg width → HolProg width
  | .halt register => .halt (findName names register)
  | .raise exception => .raise (findName names exception)
  | .break label => .break label
  | .continue label => .continue label
  | .ret value => .ret (findName names value)
  | .inst instruction =>
      .inst (HolInst.ofWordLangInst (instFindName names (HolInst.toWordLangInst instruction)))
  | .locValue destination label entry => .locValue (findName names destination) label entry
  | .seq first second => .seq (progComp names first) (progComp names second)
  | .ite operator register right thenBranch elseBranch =>
      .ite operator (findName names register)
        (HolRegImm.ofWordRegImm (riFindName names (HolRegImm.toWordRegImm right)))
        (progComp names thenBranch) (progComp names elseBranch)
  | .loop body => .loop (progComp names body)
  | .call returnHandler target handler =>
      .call (match returnHandler with
             | none => none
             | some (returnProgram, linkRegister, l1, l2) =>
                 some (progComp names returnProgram, findName names linkRegister, l1, l2))
        (destFindName names target)
        (match handler with
         | none => none
         | some (handlerProgram, l1, l2) => some (progComp names handlerProgram, l1, l2))
  | .install r1 r2 r3 r4 r5 =>
      .install (findName names r1) (findName names r2) (findName names r3)
        (findName names r4) (findName names r5)
  | .shMemOp operator register (.addr base offset) =>
      .shMemOp operator (findName names register) (.addr (findName names base) offset)
  | .codeBufferWrite r1 r2 => .codeBufferWrite (findName names r1) (findName names r2)
  | .ffi function r1 r2 r3 r4 r5 =>
      .ffi function (findName names r1) (findName names r2) (findName names r3)
        (findName names r4) (findName names r5)
  | .jumpLower r1 r2 target => .jumpLower (findName names r1) (findName names r2) target
  | program => program

/-- HOL `prog_comp_def` (`stack_namesScript.sml:101-103`). -/
/- Untagged Flapjack rendering: HOL names uses Spt Nat, while this API
accepts an unrestricted lookup function. Exact carrier migration remains open
under flapjack-pxn.18.5.15.7.7; matching clauses do not justify an exact tag. -/
def progCompEntry {width : Nat} [NeZero width] (names : FiniteMap Nat Nat)
    (entry : Nat × HolProg width) : Nat × HolProg width :=
  (entry.1, progComp names entry.2)

/-- HOL `compile_def` (`stack_namesScript.sml:105-107`). -/
/- Untagged Flapjack rendering: HOL names uses Spt Nat, while this API
accepts an unrestricted lookup function. Exact carrier migration remains open
under flapjack-pxn.18.5.15.7.7; matching clauses do not justify an exact tag. -/
def compile {width : Nat} [NeZero width] (names : FiniteMap Nat Nat)
    (program : List (Nat × HolProg width)) : List (Nat × HolProg width) :=
  program.map (progCompEntry names)

/-- HOL `MAP_FST_compile` (`stack_namesProofScript.sml:268-272`): renaming
preserves function identifiers. -/
/- Untagged Flapjack rendering: HOL names uses Spt Nat, while this API
accepts an unrestricted lookup function. Exact carrier migration remains open
under flapjack-pxn.18.5.15.7.7; matching clauses do not justify an exact tag. -/
theorem map_fst_compile {width : Nat} [NeZero width] (names : FiniteMap Nat Nat)
    (program : List (Nat × HolProg width)) :
    (compile names program).map Prod.fst = program.map Prod.fst := by
  induction program with
  | nil => rfl
  | cons head tail ih =>
      obtain ⟨n, p⟩ := head
      simp [compile, progCompEntry]

/-- Executable Boolean compatibility check over a lookup-function map. -/
def namesOk (names : FiniteMap Nat Nat) (regCount : Nat) (avoidRegs : List Nat) : Bool :=
  let xs := (List.range (regCount - avoidRegs.length)).map (findName names)
  decide xs.Nodup && xs.all (fun x => x < regCount && !(avoidRegs.contains x))

/-- Untagged proposition-shaped compatibility rendering of HOL `names_ok_def`
(`stack_namesScript.sml:111-116`): generated names are distinct, below the
register bound, and disjoint from the avoided registers. -/
/- Untagged Flapjack rendering: HOL names uses Spt Nat, while this API
accepts an unrestricted lookup function. Exact carrier migration remains open
under flapjack-pxn.18.5.15.7.7; matching clauses do not justify an exact tag. -/
def namesOkHOL (names : FiniteMap Nat Nat) (regCount : Nat)
    (avoidRegs : List Nat) : Prop :=
  let xs := (List.range (regCount - avoidRegs.length)).map (findName names)
  xs.Nodup ∧ xs.all (fun x => x < regCount && !(avoidRegs.contains x)) = true

/-- The executable Boolean check implements the HOL-shaped predicate. -/
theorem namesOkHOL_iff_bool (names : FiniteMap Nat Nat) (regCount : Nat)
    (avoidRegs : List Nat) :
    namesOkHOL names regCount avoidRegs ↔ namesOk names regCount avoidRegs = true := by
  simp [namesOkHOL, namesOk, Bool.and_eq_true]

end Flapjack.Compiler.Backend.StackNames
