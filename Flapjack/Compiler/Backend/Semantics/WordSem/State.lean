import Flapjack.Compiler.Backend.Semantics.WordSem
import Flapjack.Pancake.WordLang
import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Misc.Sptree
import Flapjack.FfiHOL

/-!
# Exact HOL `wordSem` carriers

Counterpart of the carrier declarations of
`cakeml/compiler/backend/semantics/wordSemScript.sml:15-260` (bead
`flapjack-h29l.1`): the `buffer` record with `buffer_flush`/`buffer_write`,
the `stack_frame` datatype, the `gc_fun_type` abbreviation, the `state` record,
the `result` datatype, `isResult`/`isException`, and
`stack_size_frame`/`stack_size`.

Carrier translations, as in the reviewed loopSem `state` port:

* every HOL `'a word` is the positive `BitVec width` (`[NeZero width]`), and
  `word64`/`word8` are `BitVec 64`/`BitVec 8`;
* `'a word_loc` is the tagged `WordLocW width`, `store_name` the tagged
  `WordStoreHOL`, and `'a wordLang$prog` the tagged `WordLangProgHOL` at
  `BitVec width`;
* the `sptree$num_map` fields (`locals`, `stack_size`, `code`) are the exact
  `Spt` carrier, and the two `|->` finite maps (`fp_regs`, `store`) use the
  canonical `HolFiniteMapExact` translation (qualifier
  `fmap_as_finite_support := [fp_regs, store]`);
* the `'a word set` fields (`mdomain`, `sh_mdomain`) use the reviewed
  set-as-Bool rendering of the loopSem state;
* `'c` (the compiler configuration) and `'ffi` are the universe-0 type
  parameters `C` and `F`, and `ffi` is the exact `HolFfiState F`.

This module does not port the evaluator.  `Flapjack/WordSemantics.lean` is a
separate call-aware executable analogue over `RiscV.State` and is not related
to these carriers here.
-/

namespace Flapjack

/-- Exact HOL `wordSem$buffer` (`wordSemScript.sml:15-20`):
    `<| position : 'a word; buffer : 'b word list; space_left : num |>`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "buffer"
  (words_as_type_indexed_bitvec)]
structure WordSemBuffer (aw : Nat) (bw : Nat) [NeZero aw] [NeZero bw] where
  position : BitVec aw
  buffer : List (BitVec bw)
  spaceLeft : Nat

/-- Exact HOL `buffer_flush_def` (`wordSemScript.sml:22-28`).  HOL
    `n2w (dimindex (:'b) DIV 8) : 'a word` is `BitVec.ofNat aw (bw / 8)`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "buffer_flush_def"
  (words_as_type_indexed_bitvec)]
def wordSemBufferFlush {aw : Nat} {bw : Nat} [NeZero aw] [NeZero bw]
    (cb : WordSemBuffer aw bw) (w1 w2 : BitVec aw) :
    Option (List (BitVec bw) × WordSemBuffer aw bw) :=
  if cb.position = w1 ∧
      cb.position + BitVec.ofNat aw (bw / 8) * BitVec.ofNat aw cb.buffer.length = w2 then
    some (cb.buffer, { cb with position := w2, buffer := [] })
  else none

/-- Exact HOL `buffer_write_def` (`wordSemScript.sml:30-35`). -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "buffer_write_def"
  (words_as_type_indexed_bitvec)]
def wordSemBufferWrite {aw : Nat} {bw : Nat} [NeZero aw] [NeZero bw]
    (cb : WordSemBuffer aw bw) (w : BitVec aw) (b : BitVec bw) :
    Option (WordSemBuffer aw bw) :=
  if cb.position + BitVec.ofNat aw (bw / 8) * BitVec.ofNat aw cb.buffer.length = w ∧
      0 < cb.spaceLeft then
    some { cb with buffer := cb.buffer ++ [b], spaceLeft := cb.spaceLeft - 1 }
  else none

/-- Exact HOL `wordSem$stack_frame` (`wordSemScript.sml:186-191`):
    `StackFrame (num option) ((num # 'a word_loc) list) ((num # 'a word_loc) list)
      ((num # num # num) option)`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "stack_frame"
  (words_as_type_indexed_bitvec)]
inductive WordSemStackFrame (width : Nat) [NeZero width] where
  | stackFrame (size : Option Nat) (nonGcCutset : List (Nat × WordLocW width))
      (gcCutset : List (Nat × WordLocW width)) (handler : Option (Nat × Nat × Nat))

/-- Exact HOL `gc_fun_type` (`wordSemScript.sml:193-197`): a function from the
    four-component `(roots, memory, memory-domain, store)` product to an
    optional three-component `(roots, memory, store)` product. Its store maps
    occupy argument slot 4 and result slot 3 and use the same canonical
    `HolFiniteMapExact WordStoreHOL (WordLocW width)` carrier. The finite-map
    function qualifier records this nested pointwise carrier translation; the
    word qualifier records the positive-width translation in all word-bearing
    components. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "gc_fun_type" 193
  (fmap_as_finite_support_function := [argument_4, result_3])
  (words_as_type_indexed_bitvec)]
abbrev WordSemGcFun (width : Nat) [NeZero width] : Type :=
  (List (WordLocW width) × (BitVec width → WordLocW width) × (BitVec width → Bool) ×
      HolFiniteMapExact WordStoreHOL (WordLocW width)) →
    Option (List (WordLocW width) × (BitVec width → WordLocW width) ×
      HolFiniteMapExact WordStoreHOL (WordLocW width))

/-- Broad (unrestricted) counterpart of `WordSemStateFiniteExact`: the two `|->`
    fields `fpRegs` and `store` are plain lookup functions.  It exists only to
    state the canonical finite-map translation witness;
    `WordSemStateBroad.FiniteSupport` cuts out the HOL-image subcarrier. -/
structure WordSemStateBroad (width : Nat) [NeZero width] (C : Type) (F : Type) where
  locals : Spt (WordLocW width)
  localsSize : Option Nat
  fpRegs : Nat → Option (BitVec 64)
  store : WordStoreHOL → Option (WordLocW width)
  stack : List (WordSemStackFrame width)
  stackLimit : Nat
  stackMax : Option Nat
  stackSize : Spt Nat
  memory : BitVec width → WordLocW width
  mdomain : BitVec width → Bool
  shMdomain : BitVec width → Bool
  permute : Nat → Nat → Nat
  compile : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
    Option (List (BitVec 8) × List (BitVec width) × C)
  compileOracle : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))
  codeBuffer : WordSemBuffer width 8
  dataBuffer : WordSemBuffer width width
  gcFun : WordSemGcFun width
  handler : Nat
  clock : Nat
  termdep : Nat
  code : Spt (Nat × WordLangProgHOL (BitVec width))
  be : Bool
  ffi : HolFfiState F

/-- Finite support of the two `|->` fields of `WordSemStateBroad`. -/
def WordSemStateBroad.FiniteSupport {width : Nat} [NeZero width] {C : Type} {F : Type}
    (state : WordSemStateBroad width C F) : Prop :=
  (∃ keys : List Nat, ∀ key, state.fpRegs key ≠ none → key ∈ keys) ∧
    (∃ keys : List WordStoreHOL, ∀ key, state.store key ≠ none → key ∈ keys)

/-- Exact HOL `wordSem$state` (`wordSemScript.sml:203-228`), field for field in
    HOL order.  `locals`, `stack_size` and `code` are `sptree$num_map` over the
    exact `Spt` carrier; `fp_regs` and `store` are the `|->` finite maps, with
    the `fmap_as_finite_support := [fpRegs, store]` qualifier; the word
    dimension is the positive `BitVec width`; `'c` and `'ffi` are `C` and `F`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
structure WordSemStateFiniteExact (width : Nat) [NeZero width] (C : Type) (F : Type) where
  locals : Spt (WordLocW width)
  localsSize : Option Nat
  fpRegs : HolFiniteMapExact Nat (BitVec 64)
  store : HolFiniteMapExact WordStoreHOL (WordLocW width)
  stack : List (WordSemStackFrame width)
  stackLimit : Nat
  stackMax : Option Nat
  stackSize : Spt Nat
  memory : BitVec width → WordLocW width
  mdomain : BitVec width → Bool
  shMdomain : BitVec width → Bool
  permute : Nat → Nat → Nat
  compile : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
    Option (List (BitVec 8) × List (BitVec width) × C)
  compileOracle : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))
  codeBuffer : WordSemBuffer width 8
  dataBuffer : WordSemBuffer width width
  gcFun : WordSemGcFun width
  handler : Nat
  clock : Nat
  termdep : Nat
  code : Spt (Nat × WordLangProgHOL (BitVec width))
  be : Bool
  ffi : HolFfiState F

/-- Forget the finite-support witnesses, reading the maps through `.lookup`. -/
def WordSemStateFiniteExact.toBroad {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : WordSemStateFiniteExact width C F) : WordSemStateBroad width C F where
  locals := s.locals
  localsSize := s.localsSize
  fpRegs := s.fpRegs.lookup
  store := s.store.lookup
  stack := s.stack
  stackLimit := s.stackLimit
  stackMax := s.stackMax
  stackSize := s.stackSize
  memory := s.memory
  mdomain := s.mdomain
  shMdomain := s.shMdomain
  permute := s.permute
  compile := s.compile
  compileOracle := s.compileOracle
  codeBuffer := s.codeBuffer
  dataBuffer := s.dataBuffer
  gcFun := s.gcFun
  handler := s.handler
  clock := s.clock
  termdep := s.termdep
  code := s.code
  be := s.be
  ffi := s.ffi

/-- The projection lands in the finite-support subtype. -/
theorem WordSemStateFiniteExact.toBroad_finiteSupport {width : Nat} [NeZero width]
    {C : Type} {F : Type} (s : WordSemStateFiniteExact width C F) : s.toBroad.FiniteSupport :=
  ⟨s.fpRegs.finiteSupport, s.store.finiteSupport⟩

/-- Rebuild the finite-map carrier from a finite-support broad state. -/
def WordSemStateBroad.ofBroad {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : WordSemStateBroad width C F) (h : s.FiniteSupport) :
    WordSemStateFiniteExact width C F where
  locals := s.locals
  localsSize := s.localsSize
  fpRegs := { lookup := s.fpRegs, finiteSupport := h.1 }
  store := { lookup := s.store, finiteSupport := h.2 }
  stack := s.stack
  stackLimit := s.stackLimit
  stackMax := s.stackMax
  stackSize := s.stackSize
  memory := s.memory
  mdomain := s.mdomain
  shMdomain := s.shMdomain
  permute := s.permute
  compile := s.compile
  compileOracle := s.compileOracle
  codeBuffer := s.codeBuffer
  dataBuffer := s.dataBuffer
  gcFun := s.gcFun
  handler := s.handler
  clock := s.clock
  termdep := s.termdep
  code := s.code
  be := s.be
  ffi := s.ffi

namespace WordSemStateExact

/-- Canonical finite-support witness for the `fmap_as_finite_support` qualifier
    of the tagged `state`: `toBroad` and `ofBroad` are mutually inverse on the
    finite-support subcarrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  ⟨fun _ _ => rfl, fun state => by cases state; rfl⟩

end WordSemStateExact

/-- Exact HOL `wordSem$result` (`wordSemScript.sml:241-249`). -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "result"
  (words_as_type_indexed_bitvec)]
inductive WordSemResult (width : Nat) [NeZero width] where
  | result (value : WordLocW width) (values : List (WordLocW width))
  | exception (value : WordLocW width) (payload : WordLocW width)
  | «break» (label : Nat)
  | «continue» (label : Nat)
  | timeOut
  | notEnoughSpace
  | finalFfi (event : HolFinalEvent)
  | error

/-- Exact HOL `isResult_def` (`wordSemScript.sml:252-254`). -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "isResult_def"
  (words_as_type_indexed_bitvec)]
def wordSemIsResult {width : Nat} [NeZero width] : WordSemResult width → Bool
  | .result _ _ => true
  | _ => false

/-- Exact HOL `isException_def` (`wordSemScript.sml:256-258`). -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "isException_def"
  (words_as_type_indexed_bitvec)]
def wordSemIsException {width : Nat} [NeZero width] : WordSemResult width → Bool
  | .exception _ _ => true
  | _ => false

/-- Exact HOL `stack_size_frame_def` (`wordSemScript.sml:230-233`):
    `stack_size_frame (StackFrame n _ _ NONE) = n` and
    `stack_size_frame (StackFrame n _ _ (SOME _)) = OPTION_MAP ($+ 3) n`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "stack_size_frame_def"
  (words_as_type_indexed_bitvec)]
def wordSemStackSizeFrame {width : Nat} [NeZero width] :
    WordSemStackFrame width → Option Nat
  | .stackFrame n _ _ none => n
  | .stackFrame n _ _ (some _) => n.map (fun m => 3 + m)

/-- HOL `OPTION_MAP2 f (SOME x) (SOME y) = SOME (f x y)`, otherwise `NONE`
    (`optionTheory`), at `$+` on `num`.  Flapjack-only helper. -/
def wordSemOptionAdd : Option Nat → Option Nat → Option Nat
  | some x, some y => some (x + y)
  | _, _ => none

/-- Exact HOL `stack_size_def` (`wordSemScript.sml:235-237`):
    `stack_size = FOLDR (OPTION_MAP2 $+ ∘ stack_size_frame) (SOME 1)`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "stack_size_def"
  (words_as_type_indexed_bitvec)]
def wordSemStackSize {width : Nat} [NeZero width]
    (stack : List (WordSemStackFrame width)) : Option Nat :=
  stack.foldr (fun frame acc => wordSemOptionAdd (wordSemStackSizeFrame frame) acc) (some 1)

end Flapjack
