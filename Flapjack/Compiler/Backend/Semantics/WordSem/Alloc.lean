import Flapjack.Compiler.Backend.Semantics.WordSem.Env

/-!
# Exact HOL `wordSem` code lookup, garbage collection and allocation

Counterpart of `cakeml/compiler/backend/semantics/wordSemScript.sml:614-705`
(bead `flapjack-h29l.5`): `find_code`, `enc_stack`, `dec_stack`, `gc`,
`has_space`, `alloc`, and `assign`.  The state operations are over the tagged
`WordSemStateFiniteExact`, with the carrier translations of its `state`
port (qualifier `fmap_as_finite_support := [fpRegs, store]` and the
same-module witness below).

HOL `LAST`/`FRONT` on a non-empty list are `List.getLast`/`List.dropLast`, and
`TAKE`/`DROP`/`ZIP` are `List.take`/`List.drop`/`List.zip`.  `ZIP` is only
applied to lists of equal length here.  The garbage collector is the
state's `gcFun` field (the untagged `WordSemGcFun` abbreviation, bead
`flapjack-h29l.11`), called exactly as in HOL.
-/

namespace Flapjack

namespace WordSemAllocSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged state helpers of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemAllocSupport

/-- Exact HOL `find_code_def` (`wordSemScript.sml:614-630`).
    HOL independently quantifies the code payload and stack-size payload;
    neither is inspected. Evaluator callers instantiate these at the source
    program carrier and Nat, while this definition retains the full type.
    * `find_code (SOME p) args code ssize`: look `p` up in `code`, check the
      arity, and return `(args, exp, lookup p ssize)`.
    * `find_code NONE args code ssize`: fail on `[]`.  Otherwise the last
      argument must be `Loc loc 0`, whose entry must have arity `LENGTH args -
      1`, and the result is `(FRONT args, exp, lookup loc ssize)`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "find_code_def"
  (words_as_type_indexed_bitvec)]
def wordSemFindCode {width : Nat} [NeZero width] {Code StackSize : Type} :
    Option Nat → List (WordLocW width) → Spt (Nat × Code) →
      Spt StackSize → Option (List (WordLocW width) × Code × Option StackSize)
  | some p, args, code, ssize =>
      match sptLookup p code with
      | none => none
      | some (arity, exp) =>
          if args.length = arity then some (args, exp, sptLookup p ssize) else none
  | none, args, code, ssize =>
      if h : args = [] then none
      else
        match args.getLast h with
        | .loc loc 0 =>
            (match sptLookup loc code with
             | none => none
             | some (arity, exp) =>
                 if args.length = arity + 1 then some (args.dropLast, exp, sptLookup loc ssize)
                 else none)
        | _ => none

/-- Exact HOL `enc_stack_def` (`wordSemScript.sml:632-635`):
    `enc_stack [] = []` and
    `enc_stack (StackFrame n _ l handler :: st) = MAP SND l ++ enc_stack st`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "enc_stack_def"
  (words_as_type_indexed_bitvec)]
def wordSemEncStack {width : Nat} [NeZero width] :
    List (WordSemStackFrame width) → List (WordLocW width)
  | [] => []
  | .stackFrame _ _ l _ :: st => l.map Prod.snd ++ wordSemEncStack st

/-- Exact HOL `dec_stack_def` (`wordSemScript.sml:637-646`): refill each
    frame's GC list `l` with the next `LENGTH l` values, keeping its keys.
    Fail if too few values remain or if values are left over. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "dec_stack_def"
  (words_as_type_indexed_bitvec)]
def wordSemDecStack {width : Nat} [NeZero width] :
    List (WordLocW width) → List (WordSemStackFrame width) →
      Option (List (WordSemStackFrame width))
  | [], [] => some []
  | xs, .stackFrame n l0 l handler :: st =>
      if xs.length < l.length then none
      else
        match wordSemDecStack (xs.drop l.length) st with
        | none => none
        | some s =>
            some (.stackFrame n l0 ((l.map Prod.fst).zip (xs.take l.length)) handler :: s)
  | _, _ => none

namespace WordSemStateFiniteExact

/-- Exact HOL `gc_def` (`wordSemScript.sml:648-661`).  Run `s.gc_fun` on
    `(enc_stack s.stack, s.memory, s.mdomain, s.store)`.  Then `dec_stack` the
    returned roots into `s.stack` and install the new `stack`, `store` and
    `memory`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def gc {width : Nat} [NeZero width] {C : Type} {F : Type}
    (state : WordSemStateFiniteExact width C F) : Option (WordSemStateFiniteExact width C F) :=
  let wlList := wordSemEncStack state.stack
  match state.gcFun (wlList, state.memory, state.mdomain, state.store) with
  | none => none
  | some (wl, m, st) =>
      match wordSemDecStack wl state.stack with
      | none => none
      | some stack => some { state with stack := stack, store := st, memory := m }

/-- Exact HOL `has_space_def` (`wordSemScript.sml:663-668`):
    `case (wl, get_store NextFree s, get_store TriggerGC s) of (Word w, SOME
    (Word n), SOME (Word l)) => SOME (w2n w <= w2n (l - n)) | _ => NONE`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def hasSpace {width : Nat} [NeZero width] {C : Type} {F : Type}
    (wl : WordLocW width) (state : WordSemStateFiniteExact width C F) : Option Bool :=
  match wl, getStore .nextFree state, getStore .triggerGC state with
  | .word w, some (.word n), some (.word l) => some (decide (w.toNat ≤ (l - n).toNat))
  | _, _, _ => none

/-- Exact HOL `alloc_def` (`wordSemScript.sml:671-698`).  The steps are:
    1. cut the locals with `cut_envs names`;
    2. `push_env` them (no handler) over `set_store AllocSize (Word w) s`;
    3. run `gc` and then `pop_env`;
    4. read `AllocSize` back and test `has_space`.
    A failed cut, `gc` or `pop_env` gives `(SOME Error, flush_state T s)`.
    A missing `AllocSize` or `has_space = NONE` gives `SOME Error` on the
    current state.  `SOME F` gives `(SOME NotEnoughSpace, flush_state T s)`,
    and `SOME T` gives `(NONE, s)`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def alloc {width : Nat} [NeZero width] {C : Type} {F : Type}
    (w : BitVec width) (names : WordLangCutsetsHOL) (state : WordSemStateFiniteExact width C F) :
    Option (WordSemResult width) × WordSemStateFiniteExact width C F :=
  match wordSemCutEnvs names state.locals with
  | none => (some .error, flushState true state)
  | some envs =>
      match gc (pushEnv envs none (setStore .allocSize (.word w) state)) with
      | none => (some .error, flushState true state)
      | some s =>
          match popEnv s with
          | none => (some .error, flushState true s)
          | some s =>
              match getStore .allocSize s with
              | none => (some .error, s)
              | some w =>
                  match hasSpace w s with
                  | none => (some .error, s)
                  | some true => (none, s)
                  | some false => (some .notEnoughSpace, flushState true s)

/-- Exact HOL `assign_def` (`wordSemScript.sml:700-705`):
    `case word_exp s exp of NONE => NONE | SOME w => SOME (set_var reg w s)`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def assign {width : Nat} [NeZero width] {C : Type} {F : Type}
    (reg : Nat) (exp : WordLangExpHOL (BitVec width)) (state : WordSemStateFiniteExact width C F) :
    Option (WordSemStateFiniteExact width C F) :=
  match wordExp state exp with
  | none => none
  | some w => some (setVar reg w state)

end WordSemStateFiniteExact

end Flapjack
