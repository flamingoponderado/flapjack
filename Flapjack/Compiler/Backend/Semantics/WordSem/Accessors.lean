import Flapjack.Compiler.Backend.Semantics.WordSem.State
import Flapjack.HolArb
import Flapjack.Compiler.Encoders.Asm
import Flapjack.Pancake.Semantics.LoopSemStateExact

/-!
# Exact HOL `wordSem` state accessors

Counterpart of the state accessors of
`cakeml/compiler/backend/semantics/wordSemScript.sml` (bead
`flapjack-h29l.2`), over the tagged `WordSemStateFiniteExact` carrier:

* `is_fwd_ptr`, `isWord`, and `word_cmp` (`:37-66`);
* `dec_clock`, `fix_clock`, `is_word`, `mem_store`, `mem_load`, `get_var`,
  `get_vars`, `set_var`, `unset_var`, `set_vars`, `get_store`, `set_store`,
  `word_exp`, and `flush_state` (`:262-372`);
* `get_fp_var` and `set_fp_var` (`:707-715`), and `get_var_imm` (`:941-944`).

The carrier translations are those of the `state` port. The state's two `|->`
fields, `fp_regs` and `store`, are the canonical `HolFiniteMapExact`
(qualifier `fmap_as_finite_support := [fpRegs, store]`, with the same-module
witness below). `'a word` is `BitVec width` at a positive width.

HOL `theWord_def` (`:42-44`) and `get_word_def` (`:278-280`) are partial:
there is no clause for `Loc`, so HOL leaves their value on `Loc` unspecified.
HOL pattern completion uses the same `ARB` word for both missing clauses,
independent of the location fields. Both accessors use the shared `holArb`
at their result carrier; no concrete value is imposed.
The evaluator accessor paths already pattern-match on `Word`, so their
successful equations do not depend on either unspecified function.
-/

namespace Flapjack

namespace WordSemAccessorsSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged accessors of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemAccessorsSupport

/-- Exact HOL `theWord_def` (`wordSemScript.sml:42-44`): the sole equation is
`theWord (Word w) = w`. Its total carrier has unspecified `Loc` results,
represented by the shared `holArb (BitVec width)`; no concrete value is claimed.
The word/Loc carrier and dimension are the reviewed `WordLocW width` and
positive `BitVec width` translation. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "theWord_def"
  (words_as_type_indexed_bitvec)]
noncomputable def wordSemTheWord {width : Nat} [NeZero width] :
    WordLocW width → BitVec width
  | .word w => w
  | .loc _ _ => holArb (BitVec width)

/-- Exact HOL `get_word_def` (`wordSemScript.sml:278-280`): its sole equation
is `get_word (Word w) = w`. Its missing Loc clause uses the same ARB completion
as `theWord`, independently of the location fields. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "get_word_def"
  (words_as_type_indexed_bitvec)]
noncomputable def wordSemGetWord {width : Nat} [NeZero width] :
    WordLocW width → BitVec width
  | .word w => w
  | .loc _ _ => holArb (BitVec width)

/-- Kernel equation for the original specified Word clause. -/
@[simp] theorem wordSemTheWord_word {width : Nat} [NeZero width] (w : BitVec width) :
    wordSemTheWord (.word w) = w := rfl

/-- Kernel equation for the original specified Word clause. -/
@[simp] theorem wordSemGetWord_word {width : Nat} [NeZero width] (w : BitVec width) :
    wordSemGetWord (.word w) = w := rfl

/-- Exact HOL `is_fwd_ptr_def` (`wordSemScript.sml:37-40`):
    `is_fwd_ptr (Word w) = ((w && 3w) = 0w)` and `is_fwd_ptr _ = F`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "is_fwd_ptr_def"
  (words_as_type_indexed_bitvec)]
def wordSemIsFwdPtr {width : Nat} [NeZero width] : WordLocW width → Bool
  | .word w => decide (w &&& 3 = 0)
  | _ => false

/-- Exact HOL `isWord_def` (`wordSemScript.sml:46-48`):
    `isWord (Word w) = T` and `isWord _ = F`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "isWord_def"
  (words_as_type_indexed_bitvec)]
def wordSemIsWordLoc {width : Nat} [NeZero width] : WordLocW width → Bool
  | .word _ => true
  | _ => false

/-- Kernel agreement of the two identically completed definitions. -/
theorem wordSemTheWord_eq_getWord {width : Nat} [NeZero width]
    (v : WordLocW width) : wordSemTheWord v = wordSemGetWord v := by
  cases v <;> rfl

/-- Compatibility specialization to the specified Word clause. -/
theorem wordSemTheWord_eq_getWord_of_isWord {width : Nat} [NeZero width]
    (v : WordLocW width) (h : wordSemIsWordLoc v = true) :
    wordSemTheWord v = wordSemGetWord v := by
  cases v with
  | word w => rfl
  | loc label offset => simp [wordSemIsWordLoc] at h

/-- Exact HOL `word_cmp_def` (`wordSemScript.sml:56-68`).  On two `Word`s,
    each of HOL's eight clauses is the same comparison as the corresponding
    clause of the tagged `asm$word_cmp` (`wordCmpHOL`).  For example, `Less` is
    the signed `w1 < w2` and `Lower` is the unsigned `w1 <+ w2`. `Test` and
    `NotTest` also accept `Loc _ 0` against `1w`.  Every other combination is
    `NONE`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "word_cmp_def"
  (words_as_type_indexed_bitvec)]
def wordSemWordCmp {width : Nat} [NeZero width] :
    Cmp → WordLocW width → WordLocW width → Option Bool
  | cmp, .word w1, .word w2 => some (Compiler.Encoders.Asm.wordCmpHOL cmp w1 w2)
  | .test, .loc _ n, .word w2 =>
      if n ≠ 0 then none else if w2 = 1 then some true else none
  | .notTest, .loc _ n, .word w2 =>
      if n ≠ 0 then none else if w2 = 1 then some false else none
  | _, _, _ => none

/-- Exact HOL `is_word_def` (`wordSemScript.sml:273-276`):
    `is_word (Word w) = T` and `is_word _ = F`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "is_word_def"
  (words_as_type_indexed_bitvec)]
def wordSemIsWord {width : Nat} [NeZero width] : WordLocW width → Bool
  | .word _ => true
  | _ => false

namespace WordSemStateFiniteExact

/-- Exact HOL `dec_clock_def` (`wordSemScript.sml:262-264`):
    `dec_clock s = s with clock := s.clock - 1`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def decClock {width : Nat} [NeZero width] {C : Type} {F : Type}
    (state : WordSemStateFiniteExact width C F) : WordSemStateFiniteExact width C F :=
  { state with clock := state.clock - 1 }

/-- Exact HOL `fix_clock_def` (`wordSemScript.sml:266-271`): the new clock is
    the smaller of the two clocks, and `termdep` is restored from `old_s`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def fixClock {width : Nat} [NeZero width] {C : Type} {F : Type} {β : Type}
    (old : WordSemStateFiniteExact width C F) (step : β × WordSemStateFiniteExact width C F) :
    β × WordSemStateFiniteExact width C F :=
  (step.1, { step.2 with
    clock := if old.clock < step.2.clock then old.clock else step.2.clock,
    termdep := old.termdep })

/-- Exact HOL `mem_store_def` (`wordSemScript.sml:283-288`):
    `SOME (s with memory := (addr =+ w) s.memory)` when `addr IN s.mdomain`,
    else `NONE`.  `mdomain` uses the reviewed set-as-Bool rendering. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def memStore {width : Nat} [NeZero width] {C : Type} {F : Type}
    (address : BitVec width) (value : WordLocW width)
    (state : WordSemStateFiniteExact width C F) : Option (WordSemStateFiniteExact width C F) :=
  if state.mdomain address then
    some { state with memory := fun a => if a = address then value else state.memory a }
  else none

/-- Exact HOL `mem_load_def` (`wordSemScript.sml:290-295`):
    `SOME (s.memory addr)` when `addr IN s.mdomain`, else `NONE`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def memLoad {width : Nat} [NeZero width] {C : Type} {F : Type}
    (address : BitVec width) (state : WordSemStateFiniteExact width C F) :
    Option (WordLocW width) :=
  if state.mdomain address then some (state.memory address) else none

/-- Exact HOL `get_var_def` (`wordSemScript.sml:305-307`):
    `get_var v s = lookup v s.locals` on the exact `num_map`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def getVar {width : Nat} [NeZero width] {C : Type} {F : Type}
    (name : Nat) (state : WordSemStateFiniteExact width C F) : Option (WordLocW width) :=
  sptLookup name state.locals

/-- Exact HOL `get_vars_def` (`wordSemScript.sml:309-317`): look up each
    variable in turn and fail if any lookup fails. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def getVars {width : Nat} [NeZero width] {C : Type} {F : Type} :
    List Nat → WordSemStateFiniteExact width C F → Option (List (WordLocW width))
  | [], _ => some []
  | v :: vs, state =>
      match getVar v state with
      | none => none
      | some x =>
          match getVars vs state with
          | none => none
          | some xs => some (x :: xs)

/-- Exact HOL `set_var_def` (`wordSemScript.sml:319-322`):
    `set_var v x s = s with locals := insert v x s.locals`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def setVar {width : Nat} [NeZero width] {C : Type} {F : Type}
    (name : Nat) (value : WordLocW width) (state : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact width C F :=
  { state with locals := sptInsert name value state.locals }

/-- Exact HOL `unset_var_def` (`wordSemScript.sml:324-326`):
    `unset_var v s = s with locals := delete v s.locals`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def unsetVar {width : Nat} [NeZero width] {C : Type} {F : Type}
    (name : Nat) (state : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact width C F :=
  { state with locals := sptDelete name state.locals }

/-- Exact HOL `set_vars_def` (`wordSemScript.sml:328-331`):
    `set_vars vs xs s = s with locals := alist_insert vs xs s.locals`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def setVars {width : Nat} [NeZero width] {C : Type} {F : Type}
    (names : List Nat) (values : List (WordLocW width))
    (state : WordSemStateFiniteExact width C F) : WordSemStateFiniteExact width C F :=
  { state with locals := LoopSemStateFiniteExact.sptAlistInsert names values state.locals }

/-- Exact HOL `get_store_def` (`wordSemScript.sml:333-335`):
    `get_store v s = FLOOKUP s.store v`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def getStore {width : Nat} [NeZero width] {C : Type} {F : Type}
    (name : WordStoreHOL) (state : WordSemStateFiniteExact width C F) :
    Option (WordLocW width) :=
  state.store.lookup name

/-- Exact HOL `set_store_def` (`wordSemScript.sml:337-339`):
    `set_store v x s = s with store := s.store |+ (v,x)`, with `FUPDATE` at
    HOL equality (`updateEq`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def setStore {width : Nat} [NeZero width] {C : Type} {F : Type}
    (name : WordStoreHOL) (value : WordLocW width) (state : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact width C F :=
  { state with store := state.store.updateEq (name, value) }

/-- Exact HOL `word_exp_def` (`wordSemScript.sml:341-362`) for the tagged
    `wordLang$exp`:
    * `Const` gives `Word w`, `Var` is `get_var`, and `Lookup` is `get_store`;
    * `Load` uses `mem_load` on a `Word` address;
    * `Op` is `the_words (MAP (word_exp s) ...)` followed by `word_op`;
    * `Shift` is `word_sh sh w (w2n w1)` on two `Word`s.

    HOL's termination measure is `exp_size`; Lean uses the structural size of
    the nested `List`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def wordExp {width : Nat} [NeZero width] {C : Type} {F : Type}
    (state : WordSemStateFiniteExact width C F) :
    WordLangExpHOL (BitVec width) → Option (WordLocW width)
  | .const w => some (.word w)
  | .var v => getVar v state
  | .lookup name => getStore name state
  | .load address =>
      match wordExp state address with
      | some (.word w) => memLoad w state
      | _ => none
  | .op operator args =>
      match theWords (args.attach.map fun ⟨e, _⟩ => wordExp state e) with
      | some ws => (wordOpHOL operator ws).map WordLocW.word
      | none => none
  | .shift sh e1 e2 =>
      match wordExp state e1, wordExp state e2 with
      | some (.word w), some (.word w1) => (wordShiftHOL sh w w1.toNat).map WordLocW.word
      | _, _ => none

/-- Exact HOL `flush_state_def` (`wordSemScript.sml:365-372`).  `flush_state T`
    empties `locals`, `stack` and `store` and sets `locals_size := SOME 0`.
    `flush_state F` empties only `locals` and sets `locals_size := SOME 0`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def flushState {width : Nat} [NeZero width] {C : Type} {F : Type} :
    Bool → WordSemStateFiniteExact width C F → WordSemStateFiniteExact width C F
  | true, state =>
      { state with locals := .ln, stack := [], store := HolFiniteMapExact.empty,
                   localsSize := some 0 }
  | false, state => { state with locals := .ln, localsSize := some 0 }

/-- Exact HOL `get_fp_var_def` (`wordSemScript.sml:707-709`):
    `get_fp_var v s = FLOOKUP s.fp_regs v`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def getFpVar {width : Nat} [NeZero width] {C : Type} {F : Type}
    (name : Nat) (state : WordSemStateFiniteExact width C F) : Option (BitVec 64) :=
  state.fpRegs.lookup name

/-- Exact HOL `set_fp_var_def` (`wordSemScript.sml:711-714`):
    `set_fp_var v x s = s with fp_regs := s.fp_regs |+ (v,x)`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def setFpVar {width : Nat} [NeZero width] {C : Type} {F : Type}
    (name : Nat) (value : BitVec 64) (state : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact width C F :=
  { state with fpRegs := state.fpRegs.updateEq (name, value) }

/-- Exact HOL `get_var_imm_def` (`wordSemScript.sml:941-944`):
    `get_var_imm (Reg n) s = get_var n s` and `get_var_imm (Imm w) s = SOME
    (Word w)`.  The `asm$reg_imm` argument uses the carrier `WordRegImm (BitVec
    width)`, the `If` payload of the tagged `WordLangProgHOL` that the evaluator
    passes here.  It has the same two constructors, `Reg num | Imm ('a word)`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def getVarImm {width : Nat} [NeZero width] {C : Type} {F : Type} :
    WordRegImm (BitVec width) → WordSemStateFiniteExact width C F → Option (WordLocW width)
  | .reg n, state => getVar n state
  | .imm w, _ => some (.word w)

end WordSemStateFiniteExact

end Flapjack
