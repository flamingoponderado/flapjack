module

public import Flapjack.Compiler.Backend.WordElim.Definitions
public import Flapjack.Compiler.Backend.FlatElim.Proofs.Reachability
public import Flapjack.Compiler.Backend.Semantics.WordSem.Alloc
public import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors

@[expose] public section

/-!
# Definitions of HOL `word_elimProof`

Counterpart of the `DEFINITIONS` section of
`cakeml/compiler/backend/proofs/word_elimProofScript.sml:43-405`: the
location-collecting helpers `dest_word_loc`, `get_locals`, `get_store`,
`get_num_wordloc_alist`, `get_stack`, `get_memory`, `find_loc_state`, and the
relations `code_rel`, `code_closed`, `gc_no_new_locs`, `word_state_rel`.

The state is the tagged `WordSemStateFiniteExact`, so every word_loc map is a
`Spt (WordLocW width)` and every memory is `BitVec width → WordLocW width`.

**Open rendering decision.** HOL's `get_store` enumerates `SET_TO_LIST (FRANGE
st)` and `get_memory` enumerates `SET_TO_LIST (IMAGE mem mdom)`.  HOL's
`SET_TO_LIST` is choice-based and its order is unspecified; the repository has
no reviewed rendering of it, and `spt` insertion is order-sensitive in tree
shape.  The two definitions below therefore enumerate the finite support /
memory domain in a canonical order, which preserves the *domain* (the only
observation used by every theorem of this script) but not the tree shape.
They are consequently UNTAGGED, as are `find_loc_state` and `word_state_rel`,
which call them.  A faithful port needs the `SET_TO_LIST` rendering decision.
-/

namespace Flapjack.Compiler.Backend.WordElim

open WordSemAllocSupport WordSemStateFiniteExact
open Flapjack.Compiler.Backend.FlatElim

/-! ## Locations in the state -/

/-- Exact HOL `dest_word_loc_def` (`word_elimProofScript.sml:43-47`):
    `dest_word_loc (Loc n _) = SOME n` and `dest_word_loc _ = NONE`. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "dest_word_loc_def"
  (words_as_type_indexed_bitvec)]
def destWordLoc {width : Nat} [NeZero width] : WordLocW width → Option Nat
  | .loc block _ => some block
  | .word _ => none

/-- Exact HOL `dest_result_loc_def` (`word_elimProofScript.sml:49-55`): the
    locations of the returned values, the exception location, and the empty set
    otherwise.  HOL's `num -> bool` sets are predicates here, so `BIGUNION
    (set (MAP ...))` is the pointwise existential. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "dest_result_loc_def"
  (words_as_type_indexed_bitvec)]
def destResultLoc {width : Nat} [NeZero width] :
    Option (WordSemResult width) → Nat → Prop
  | some (.result _ values) =>
      fun location => ∃ value ∈ values, destWordLoc value = some location
  | some (.exception _ (.loc block _)) => fun location => location = block
  | _ => fun _ => False

/-- Exact HOL `get_locals_def` (`word_elimProofScript.sml:58-69`): collect the
    `Loc` blocks stored in a `locals` tree. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "get_locals_def"
  (words_as_type_indexed_bitvec)]
def getLocals {width : Nat} [NeZero width] : Spt (WordLocW width) → NumSet
  | .ln => .ln
  | .ls value =>
      match destWordLoc value with
      | some location => sptInsert location () .ln
      | none => .ln
  | .bn left right => sptUnion (getLocals left) (getLocals right)
  | .bs left value right =>
      let both := sptUnion (getLocals left) (getLocals right)
      match destWordLoc value with
      | some location => sptInsert location () both
      | none => both

/-- HOL `get_store_def` (`word_elimProofScript.sml:130-135`): collect the `Loc`
    blocks in the store range.  UNTAGGED: HOL enumerates `SET_TO_LIST (FRANGE
    st)`, whose order is unspecified, while this definition folds over the
    finite support keys; the domain agrees, the tree shape need not (see the
    module note). -/
noncomputable def getStore {width : Nat} [NeZero width]
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) : NumSet :=
  let keys := Classical.choose store.finiteSupport
  keys.foldl (fun accumulator key =>
    match store.lookup key with
    | none => accumulator
    | some value =>
        match destWordLoc value with
        | some location => sptInsert location () accumulator
        | none => accumulator) .ln

/-- Exact HOL `get_num_wordloc_alist_def` (`word_elimProofScript.sml:160-164`):
    collect the `Loc` blocks in an association list's values.  HOL's `MAP THE
    (FILTER IS_SOME (MAP (dest_word_loc o SND) l))` is `filterMap`. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml"
  "get_num_wordloc_alist_def" (words_as_type_indexed_bitvec)]
def getNumWordlocAlist {width : Nat} [NeZero width] :
    List (Nat × WordLocW width) → NumSet
  | entries =>
      (entries.filterMap (fun entry => destWordLoc entry.2)).foldl
        (fun accumulator location => sptInsert location () accumulator) .ln

/-- Exact HOL `get_stack_def` (`word_elimProofScript.sml:203-208`): collect the
    `Loc` blocks in both cut sets of every stack frame. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "get_stack_def"
  (words_as_type_indexed_bitvec)]
def getStack {width : Nat} [NeZero width] :
    List (WordSemStackFrame width) → NumSet
  | [] => .ln
  | .stackFrame _ nonGcCutset gcCutset _ :: rest =>
      sptUnion
        (sptUnion (getNumWordlocAlist nonGcCutset) (getNumWordlocAlist gcCutset))
        (getStack rest)

/-- HOL `get_memory_def` (`word_elimProofScript.sml:289-295`): collect the
    `Loc` blocks of the memory image of `mdomain`.  UNTAGGED for the same
    `SET_TO_LIST` reason as `getStore`; the enumeration is over the (finite)
    memory domain in a canonical order. -/
noncomputable def getMemory {width : Nat} [NeZero width]
    (memory : BitVec width → WordLocW width) (mdomain : BitVec width → Bool) : NumSet :=
  let addresses := (List.range (2 ^ width)).map (fun index => BitVec.ofNat width index)
  let locations := (addresses.filter (fun address => mdomain address)).map memory
  locations.foldl (fun accumulator value =>
    match destWordLoc value with
    | some location => sptInsert location () accumulator
    | none => accumulator) .ln

/-- HOL `find_loc_state_def` (`word_elimProofScript.sml:335-342`): the union of
    the four location sets.  UNTAGGED because it calls the untagged `getStore`
    and `getMemory` (see the module note). -/
noncomputable def findLocState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (state : WordSemStateFiniteExact width C F) : NumSet :=
  let locals := getLocals state.locals
  let store := getStore state.store
  let stack := getStack state.stack
  let memory := getMemory state.memory state.mdomain
  sptUnion (sptUnion locals store) (sptUnion stack memory)

/-! ## The relations -/

/-- Exact HOL `code_rel_def` (`word_elimProofScript.sml:352-357`): inside the
    reachable set the two code maps agree. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "code_rel_def"
  (words_as_type_indexed_bitvec)]
def codeRel {width : Nat} [NeZero width] (reachable : NumSet)
    (source target : Spt (Nat × WordLangProgHOL (BitVec width))) : Prop :=
  ∀ n, sptMem n reachable → sptLookup n source = sptLookup n target

/-- Exact HOL `code_closed_def` (`word_elimProofScript.sml:359-364`): the code
    is an association list whose dependency closure stays inside `reachable`.
    HOL's `reachable` payload type is free (only its domain is used), so the
    Lean parameter keeps an independent type variable. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "code_closed_def"]
def codeClosed {α β γ : Type} (reachable : Spt γ)
    (code : Spt (α × WordLangProgHOL β)) : Prop :=
  ∃ code1 : List (Nat × α × WordLangProgHOL β),
    code = sptFromAList code1 ∧
      ∀ n m, sptMem n reachable ∧ isReachable (analyseWordCode code1) n m →
        sptMem m reachable

/-- HOL `gc_no_new_locs_def` (`word_elimProofScript.sml:366-373`): the garbage
    collector never adds locations.  UNTAGGED because it calls the untagged
    `getStore`/`getMemory` (see the module note). -/
def gcNoNewLocs {width : Nat} [NeZero width] (gc : WordSemGcFun width) : Prop :=
  ∀ (stack : List (WordSemStackFrame width))
    (memory : BitVec width → WordLocW width) (mdomain : BitVec width → Bool)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (roots : List (WordLocW width)) (memory1 : BitVec width → WordLocW width)
    (store1 : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (stack1 : List (WordSemStackFrame width)),
    gc (wordSemEncStack stack, memory, mdomain, store) = some (roots, memory1, store1) ∧
      wordSemDecStack roots stack = some stack1 →
        (∀ n, sptMem n (getStack stack1) → sptMem n (getStack stack)) ∧
          (∀ n, sptMem n (getMemory memory1 mdomain) → sptMem n (getMemory memory mdomain)) ∧
            ∀ n, sptMem n (getStore store1) → sptMem n (getStore store)

/-- HOL `word_state_rel_def` (`word_elimProofScript.sml:375-403`): the original
    state `t` and the removed state `s` agree on every field, agree on the
    reachable code, and every location of `t` is reachable.  HOL names its two
    state parameters `t` and `s` in that order, which this definition keeps.
    UNTAGGED because it calls the untagged `find_loc_state` (see the module
    note). -/
def wordStateRel {width : Nat} [NeZero width] {C : Type} {F : Type}
    (reachable : NumSet)
    (t s : WordSemStateFiniteExact width C F) : Prop :=
  s.locals = t.locals ∧
    s.fpRegs = t.fpRegs ∧
    s.store = t.store ∧
    s.stack = t.stack ∧
    s.memory = t.memory ∧
    s.mdomain = t.mdomain ∧
    s.shMdomain = t.shMdomain ∧
    s.permute = t.permute ∧
    s.compile = t.compile ∧
    s.compileOracle = t.compileOracle ∧
    s.codeBuffer = t.codeBuffer ∧
    s.dataBuffer = t.dataBuffer ∧
    s.gcFun = t.gcFun ∧
    s.handler = t.handler ∧
    s.clock = t.clock ∧
    s.termdep = t.termdep ∧
    s.be = t.be ∧
    s.ffi = t.ffi ∧
    s.localsSize = t.localsSize ∧
    s.stackMax = t.stackMax ∧
    s.stackLimit = t.stackLimit ∧
    s.stackSize = t.stackSize ∧
    codeRel reachable s.code t.code ∧
    ∀ n, sptMem n (findLocState t) → sptMem n reachable

end Flapjack.Compiler.Backend.WordElim
