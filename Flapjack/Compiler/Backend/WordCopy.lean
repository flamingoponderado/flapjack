import Flapjack.HolRef
import Flapjack.Pancake.WordLang
import Flapjack.Compiler.Backend.RegAlloc
import Flapjack.Misc.Sptree.InterEq

/-!
# `word_copy`: copy propagation

Counterpart of `cakeml/compiler/backend/word_copyScript.sml`. HOL `ALOOKUP` on the
`store_name` association list is Lean core `List.lookup` (first match, `BEq` from
`DecidableEq`), `EVERY`/`MEM` are bounded membership, `FILTER` is `List.filter` of the
decided predicate, `MAX` is `max`, and `lookup`/`insert`/`inter_eq` are the `Spt`
operations. This is a proof-side port; the executed compiler's `RiscV/WordCopyProp.lean` is
a separate untagged implementation whose routing through these definitions is tracked
separately.
-/

namespace Flapjack.Compiler.Backend.WordCopy

open Flapjack

/-- Exact HOL `copy_state` (`word_copyScript.sml:33-42`): `to_eq`/`from_eq` are
`num num_map`s, `store_to_eq` a `(store_name, num) alist`. -/
@[hol "cakeml/compiler/backend/word_copyScript.sml" "copy_state"]
structure CopyState where
  toEq : Spt Nat
  fromEq : Spt Nat
  storeToEq : List (WordStoreHOL × Nat)
  next : Nat

/-- Exact HOL `empty_eq_def` (`word_copyScript.sml:44-48`). -/
@[hol "cakeml/compiler/backend/word_copyScript.sml" "empty_eq_def"]
def emptyEq : CopyState :=
  { toEq := .ln, fromEq := .ln, storeToEq := [], next := 0 }

/-- Exact HOL `lookup_eq_def` (`word_copyScript.sml:52-60`). -/
@[hol "cakeml/compiler/backend/word_copyScript.sml" "lookup_eq_def"]
def lookupEq (cs : CopyState) (v : Nat) : Nat :=
  match sptLookup v cs.toEq with
  | none => v
  | some c =>
    match sptLookup c cs.fromEq with
    | none => v
    | some v' => v'

/-- Exact HOL `lookup_eq_imm_def` (`word_copyScript.sml:62-67`). -/
@[hol "cakeml/compiler/backend/word_copyScript.sml" "lookup_eq_imm_def"
  (words_as_type_indexed_bitvec)]
def lookupEqImm {width : Nat} [NeZero width] (cs : CopyState) (vi : WordRegImm (BitVec width)) :
    WordRegImm (BitVec width) :=
  match vi with
  | .reg v => .reg (lookupEq cs v)
  | _ => vi

/-- Exact HOL `remove_eq_def` (`word_copyScript.sml:73-77`); the commented-out finer
removal is absent, as in HOL. -/
@[hol "cakeml/compiler/backend/word_copyScript.sml" "remove_eq_def"]
def removeEq (cs : CopyState) (v : Nat) : CopyState :=
  match sptLookup v cs.toEq with
  | none => cs
  | some _ => emptyEq

/-- Exact HOL `remove_eqs_def` (`word_copyScript.sml:89-93`). -/
@[hol "cakeml/compiler/backend/word_copyScript.sml" "remove_eqs_def"]
def removeEqs : CopyState → List Nat → CopyState
  | cs, [] => cs
  | cs, v :: vs => removeEqs (removeEq cs v) vs

/-- Exact HOL `copy_prop_inst_def` (`word_copyScript.sml:95-202`). HOL's `LongMul` clause
binds `r3'`/`r4'` without using them, so they are omitted. HOL's final `_ => ARB` clause is
unreachable (every `Arith`, `Mem`-with-`Addr` and `FP` constructor has a clause), so the Lean
match is exhaustive without it. -/
-- riscv-mi: integer-only specialization of the referenced HOL declaration.

def copyPropInst {width : Nat} [NeZero width] :
    WordLangInst (BitVec width) → CopyState → WordLangProgHOL (BitVec width) × CopyState
  | .skip, cs => (.skip, cs)
  | .const reg w, cs => (.inst (.const reg w), removeEq cs reg)
  | .arith (.binop bop r1 r2 ri), cs =>
    let cs' := removeEq cs r1
    let r2' := lookupEq cs r2
    let ri' := lookupEqImm cs ri
    let ri'' := if ri' = .reg r1 then ri else ri'
    (.inst (.arith (.binop bop r1 r2' ri'')), cs')
  | .arith (.shift shift r1 r2 n), cs =>
    let cs' := removeEq cs r1
    let r2' := lookupEq cs r2
    let n' := lookupEqImm cs n
    let n'' := if n' = .reg r1 then n else n'
    (.inst (.arith (.shift shift r1 r2' n'')), cs')
  | .arith (.div r1 r2 r3), cs =>
    let r2' := lookupEq cs r2
    let r3' := lookupEq cs r3
    (.inst (.arith (.div r1 r2' r3')), removeEq cs r1)
  | .arith (.addCarry r1 r2 r3 r4), cs =>
    let cs' := removeEqs cs [r1, r4]
    let r2' := lookupEq cs r2
    let r3' := lookupEq cs r3
    let r3'' := if r3' = r1 then r3 else r3'
    (.inst (.arith (.addCarry r1 r2' r3'' r4)), cs')
  | .arith (.addOverflow r1 r2 r3 r4), cs =>
    let cs' := removeEqs cs [r1, r4]
    let r2' := lookupEq cs r2
    let r3' := lookupEq cs r3
    let r3'' := if r3' = r1 then r3 else r3'
    (.inst (.arith (.addOverflow r1 r2' r3'' r4)), cs')
  | .arith (.subOverflow r1 r2 r3 r4), cs =>
    let cs' := removeEqs cs [r1, r4]
    let r2' := lookupEq cs r2
    let r3' := lookupEq cs r3
    let r3'' := if r3' = r1 then r3 else r3'
    (.inst (.arith (.subOverflow r1 r2' r3'' r4)), cs')
  | .arith (.longMul r1 r2 r3 r4), cs =>
    (.inst (.arith (.longMul r1 r2 r3 r4)), removeEqs cs [r1, r2])
  | .arith (.longDiv r1 r2 r3 r4 r5), cs =>
    let r3' := lookupEq cs r3
    let r4' := lookupEq cs r4
    let r5' := lookupEq cs r5
    (.inst (.arith (.longDiv r1 r2 r3' r4' r5')), removeEqs cs [r2, r1])
  | .mem .load r (.addr a w), cs =>
    let a' := lookupEq cs a
    (.inst (.mem .load r (.addr a' w)), removeEq cs r)
  | .mem .store r (.addr a w), cs =>
    let a' := lookupEq cs a
    let r' := lookupEq cs r
    (.inst (.mem .store r' (.addr a' w)), cs)
  | .mem .load8 r (.addr a w), cs =>
    let a' := lookupEq cs a
    (.inst (.mem .load8 r (.addr a' w)), removeEq cs r)
  | .mem .store8 r (.addr a w), cs =>
    let a' := lookupEq cs a
    let r' := lookupEq cs r
    (.inst (.mem .store8 r' (.addr a' w)), cs)
  | .mem .load16 r (.addr a w), cs =>
    let a' := lookupEq cs a
    (.inst (.mem .load16 r (.addr a' w)), removeEq cs r)
  | .mem .store16 r (.addr a w), cs =>
    let a' := lookupEq cs a
    let r' := lookupEq cs r
    (.inst (.mem .store16 r' (.addr a' w)), cs)
  | .mem .load32 r (.addr a w), cs =>
    let a' := lookupEq cs a
    (.inst (.mem .load32 r (.addr a' w)), removeEq cs r)
  | .mem .store32 r (.addr a w), cs =>
    let a' := lookupEq cs a
    let r' := lookupEq cs r
    (.inst (.mem .store32 r' (.addr a' w)), cs)

/-- Exact HOL `set_eq_def` (`word_copyScript.sml:204-225`). -/
@[hol "cakeml/compiler/backend/word_copyScript.sml" "set_eq_def"]
def setEq (cs : CopyState) (x y : Nat) : CopyState :=
  if isAllocVar x = true ∧ isAllocVar y = true then
    match (match sptLookup y cs.toEq with
      | none => none
      | some c => if sptLookup c cs.fromEq = none then none else some c) with
    | none =>
      { toEq := sptInsert x cs.next (sptInsert y cs.next cs.toEq)
        fromEq := sptInsert cs.next x cs.fromEq
        storeToEq := cs.storeToEq
        next := cs.next + 1 }
    | some c =>
      { toEq := sptInsert x c cs.toEq
        fromEq := sptInsert c x cs.fromEq
        storeToEq := cs.storeToEq
        next := cs.next }
  else
    cs

/-- Exact HOL `set_store_eq_def` (`word_copyScript.sml:233-250`). -/
@[hol "cakeml/compiler/backend/word_copyScript.sml" "set_store_eq_def"]
def setStoreEq (cs : CopyState) (s : WordStoreHOL) (y : Nat) : CopyState :=
  if isAllocVar y = true then
    match (match sptLookup y cs.toEq with
      | none => none
      | some c => if sptLookup c cs.fromEq = none then none else some c) with
    | none =>
      { toEq := sptInsert y cs.next cs.toEq
        fromEq := sptInsert cs.next y cs.fromEq
        storeToEq := (s, cs.next) :: cs.storeToEq
        next := cs.next + 1 }
    | some c => { cs with storeToEq := (s, c) :: cs.storeToEq }
  else emptyEq

/-- Exact HOL `lookup_store_eq_def` (`word_copyScript.sml:252-260`). -/
@[hol "cakeml/compiler/backend/word_copyScript.sml" "lookup_store_eq_def"]
def lookupStoreEq (cs : CopyState) (s : WordStoreHOL) : Option Nat :=
  match cs.storeToEq.lookup s with
  | none => none
  | some c =>
    match sptLookup c cs.fromEq with
    | none => none
    | some v' => some v'

/-- Exact HOL `merge_eqs_def` (`word_copyScript.sml:263-271`). -/
@[hol "cakeml/compiler/backend/word_copyScript.sml" "merge_eqs_def"]
def mergeEqs (cs ds : CopyState) : CopyState :=
  { toEq := sptInterEq cs.toEq ds.toEq
    fromEq := sptInterEq cs.fromEq ds.fromEq
    storeToEq := cs.storeToEq.filter (fun (s, c) =>
      decide (cs.storeToEq.lookup s = some c ∧ ds.storeToEq.lookup s = some c))
    next := max cs.next ds.next }

/-- Exact HOL `copy_prop_move_def` (`word_copyScript.sml:274-281`). -/
@[hol "cakeml/compiler/backend/word_copyScript.sml" "copy_prop_move_def"]
def copyPropMove : List (Nat × Nat) → CopyState → List (Nat × Nat) × CopyState
  | [], cs => ([], cs)
  | (x, y) :: xs, cs =>
    let y' := lookupEq cs y
    let (ms, cs') := copyPropMove xs cs
    let cs'' := setEq (removeEq cs' x) x y
    ((x, y') :: ms, cs'')

/-- Exact HOL `copy_prop_share_def` (`word_copyScript.sml:283-290`). -/
@[hol "cakeml/compiler/backend/word_copyScript.sml" "copy_prop_share_def"
  (words_as_type_indexed_bitvec)]
def copyPropShare {width : Nat} [NeZero width] (exp : WordLangExpHOL (BitVec width))
    (cs : CopyState) : WordLangExpHOL (BitVec width) :=
  match exp with
  | .var r => .var (lookupEq cs r)
  | .op .add [.var r, .const c] => .op .add [.var (lookupEq cs r), .const c]
  | _ => exp

/-- Exact HOL `copy_prop_prog_def` (`word_copyScript.sml:292-384`). HOL's final catch-all
`prog => (prog, empty_eq)` covers exactly `Assign` and `Store`, the constructors without an
earlier clause. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def copyPropProg {width : Nat} [NeZero width] :
    WordLangProgHOL (BitVec width) → CopyState → WordLangProgHOL (BitVec width) × CopyState
  | .skip, cs => (.skip, cs)
  | .move pri xs, cs =>
    let tt := xs.map Prod.fst
    let ss := xs.map Prod.snd
    if ∀ t ∈ tt, t ∉ ss then
      let (xs', cs') := copyPropMove xs cs
      (.move pri xs', cs')
    else (.move pri xs, emptyEq)
  | .inst i, cs => copyPropInst i cs
  | .return v1 v2, cs =>
    let v1' := lookupEq cs v1
    let v2' := v2.map (lookupEq cs)
    (.return v1' v2', cs)
  | .raise v, cs =>
    let v' := lookupEq cs v
    (.raise v', cs)
  | .opCurrHeap b dst src, cs =>
    let src' := lookupEq cs src
    let src'' := if src' = dst then src else src'
    (.opCurrHeap b dst src'', removeEq cs dst)
  | .tick, cs => (.tick, cs)
  | .mustTerminate p1, cs =>
    let (p1', cs') := copyPropProg p1 cs
    (.mustTerminate p1', cs')
  | .seq p1 p2, cs =>
    let (q1, cs') := copyPropProg p1 cs
    let (q2, cs'') := copyPropProg p2 cs'
    (.seq q1 q2, cs'')
  | .ite cmp r ri p1 p2, cs =>
    let r' := lookupEq cs r
    let ri' := lookupEqImm cs ri
    let (q1, cs') := copyPropProg p1 cs
    let (q2, cs'') := copyPropProg p2 cs
    (.ite cmp r' ri' q1 q2, mergeEqs cs' cs'')
  | .set name exp, cs =>
    match exp with
    | .var n =>
      let n' := lookupEq cs n
      (.set name (.var n'), setStoreEq cs name n)
    | _ => (.set name exp, emptyEq)
  | .get n name, cs =>
    match lookupStoreEq cs name with
    | none => (.get n name, setStoreEq (removeEq cs n) name n)
    | some v =>
      if v ≠ n then
        let (xs', cs') := copyPropMove [(n, v)] cs
        (.move 0 xs', cs')
      else (.skip, cs)
  | .call ret dest args handler, _ => (.call ret dest args handler, emptyEq)
  | .alloc r live, _ => (.alloc r live, emptyEq)
  | .storeConsts a b c d ws, cs => (.storeConsts a b c d ws, removeEqs cs [a, b, c, d])
  | .locValue r l1, cs => (.locValue r l1, removeEq cs r)
  | .install r1 r2 r3 r4 live, _ => (.install r1 r2 r3 r4 live, emptyEq)
  | .codeBufferWrite r1 r2, cs =>
    let r1' := lookupEq cs r1
    let r2' := lookupEq cs r2
    (.codeBufferWrite r1' r2', cs)
  | .dataBufferWrite r1 r2, cs =>
    let r1' := lookupEq cs r1
    let r2' := lookupEq cs r2
    (.dataBufferWrite r1' r2', cs)
  | .ffi i r1 r2 r3 r4 live, _ => (.ffi i r1 r2 r3 r4 live, emptyEq)
  | .shareInst op v exp, cs =>
    let exp' := copyPropShare exp cs
    (.shareInst op v exp', removeEq cs v)
  | .loop names c exitNames, _ =>
    let (c', _) := copyPropProg c emptyEq
    (.loop names c' exitNames, emptyEq)
  | .break k, cs => (.break k, cs)
  | .continue k, cs => (.continue k, cs)
  | .assign n e, _ => (.assign n e, emptyEq)
  | .store e n, _ => (.store e n, emptyEq)

/-- Exact HOL `copy_prop_def` (`word_copyScript.sml:386-388`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def copyProp {width : Nat} [NeZero width] (e : WordLangProgHOL (BitVec width)) :
    WordLangProgHOL (BitVec width) :=
  (copyPropProg e emptyEq).1

end Flapjack.Compiler.Backend.WordCopy
