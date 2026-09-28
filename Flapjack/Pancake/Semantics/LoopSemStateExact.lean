import Flapjack.Pancake.Semantics.LoopSemState
import Flapjack.Pancake.Semantics.LoopProps
import Flapjack.Pancake.LoopLang
import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Misc.Sptree
import Flapjack.FfiBridge
import Flapjack.Compiler.Backend.Semantics.WordSem

/-!
# Exact finite-support HOL `loopSem$state` carrier

Counterpart of the `state` datatype in
`cakeml/pancake/semantics/loopSemScript.sml:13-27`:

```
state =
  <| locals  : ('a word_loc) num_map
   ; globals : 5 word  |-> 'a word_loc
   ; memory  : 'a word -> 'a word_loc
   ; mdomain : ('a word) set
   ; sh_mdomain : ('a word) set
   ; clock   : num
   ; code    : (num list # ('a loopLang$prog)) num_map
   ; be      : bool
   ; ffi     : 'ffi ffi_state
   ; base_addr   : 'a word
   ; top_addr    : 'a word |>
```

`LoopSemStateFiniteExact` is the source-shaped carrier.  HOL `locals` and
`code` are `sptree$num_map` (`'a word_loc spt` and
`(num list # 'a loopLang$prog) spt`), rendered by the exact `Spt` datatype
(`Flapjack/Misc/Sptree.lean`, whose `num_set` abbreviation is the tagged exact
port of HOL `misc$num_set`); `globals : 5 word |-> 'a word_loc` is the only
`|->` finite map and uses the reviewed canonical `HolFiniteMapExact`
translation, recorded by the `fmap_as_finite_support := [globals]` qualifier on
the tagged `state`.  `code` entries use the exact `HolLoopProg` carrier and the
`ffi` field uses the exact `HolFfiState`.  The word dimension is the nonzero
`BitVec width` model; `memory` is total and the domains are Lean sets, both
matching HOL.

The production `LoopMachineState` bridge and the `get_var_imm`/`get_vars`
carrier-level statements live in `LoopSemState.lean`; the bridge to the
production state over this exact carrier is tracked separately on
`flapjack-pxn.18.5.17.1`.
-/

namespace Flapjack

/-- Broad (unrestricted) counterpart of `LoopSemStateFiniteExact`: `globals` is
    a plain lookup function, a strict superset of HOL's `|->` finite map.  The
    `locals`/`code` `sptree` maps are already concrete/finite and are shared
    verbatim.  It exists only to state the canonical finite-map translation
    witness `holFmapAsFiniteSupportWitness`; `FiniteSupport` cuts out the
    HOL-image subcarrier. -/
structure LoopSemStateBroad (width : Nat) [NeZero width] (F : Type) where
  locals : Spt (WordLocW width)
  globals : BitVec 5 → Option (WordLocW width)
  memory : BitVec width → WordLocW width
  mdomain : BitVec width → Bool
  shMdomain : BitVec width → Bool
  clock : Nat
  code : Spt (List Nat × HolLoopProg width)
  be : Bool
  ffi : HolFfiState F
  baseAddr : BitVec width
  topAddr : BitVec width

/-- Finite support of the `globals` field of `LoopSemStateBroad`, matching
    HOL's `|->` view. -/
def LoopSemStateBroad.FiniteSupport {width : Nat} [NeZero width] {F : Type}
    (state : LoopSemStateBroad width F) : Prop :=
  ∃ keys : List (BitVec 5), ∀ key, state.globals key ≠ none → key ∈ keys

/-- Source-shaped rendering of HOL `loopSem$state`
    (`loopSemScript.sml:13-27`): `locals`/`code` are `sptree$num_map` over the
    exact `Spt` carrier; `globals` is the only `|->` finite map and carries the
    `fmap_as_finite_support := [globals]` qualifier.  Every HOL `'a word`
    occurrence (the `memory`/`mdomain`/`sh_mdomain`/`base_addr`/`top_addr`
    fields and the `WordLocW` payloads) is rendered as the positive
    `BitVec width` with the `[NeZero width]` discharge of
    `dimindex (:α) ≥ 1`, and the FFI host is the universe-0 Lean type `F`, so
    the `state` tag also carries `(words_as_type_indexed_bitvec)` under the
    combined status.  The fixed `BitVec 5` globals key is HOL's `5 word`,
    whose dimension is a literal rather than `dimindex (:α)`. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "state"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
structure LoopSemStateFiniteExact (width : Nat) [NeZero width] (F : Type) where
  locals : Spt (WordLocW width)
  globals : HolFiniteMapExact (BitVec 5) (WordLocW width)
  memory : BitVec width → WordLocW width
  mdomain : BitVec width → Bool
  shMdomain : BitVec width → Bool
  clock : Nat
  code : Spt (List Nat × HolLoopProg width)
  be : Bool
  ffi : HolFfiState F
  baseAddr : BitVec width
  topAddr : BitVec width

/-- Forget the finite-support witness of `globals`, reading it through
    `.lookup`. -/
def LoopSemStateFiniteExact.toBroad {width : Nat} [NeZero width] {F : Type}
    (state : LoopSemStateFiniteExact width F) : LoopSemStateBroad width F where
  locals := state.locals
  globals := state.globals.lookup
  memory := state.memory
  mdomain := state.mdomain
  shMdomain := state.shMdomain
  clock := state.clock
  code := state.code
  be := state.be
  ffi := state.ffi
  baseAddr := state.baseAddr
  topAddr := state.topAddr

/-- The projection lands in the finite-support subtype. -/
theorem LoopSemStateFiniteExact.toBroad_finiteSupport {width : Nat} [NeZero width]
    {F : Type} (state : LoopSemStateFiniteExact width F) :
    state.toBroad.FiniteSupport :=
  state.globals.finiteSupport

/-- Rebuild the finite-map carrier from a broad state together with a
    finite-support proof; the inverse of `toBroad` on the finite-support
    subtype. -/
def LoopSemStateBroad.ofBroad {width : Nat} [NeZero width] {F : Type}
    (state : LoopSemStateBroad width F) (h : state.FiniteSupport) :
    LoopSemStateFiniteExact width F where
  locals := state.locals
  globals := { lookup := state.globals, finiteSupport := h }
  memory := state.memory
  mdomain := state.mdomain
  shMdomain := state.shMdomain
  clock := state.clock
  code := state.code
  be := state.be
  ffi := state.ffi
  baseAddr := state.baseAddr
  topAddr := state.topAddr

/-- `toBroad` after `ofBroad` is the identity on a finite-support broad state. -/
theorem LoopSemStateBroad.toBroad_ofBroad {width : Nat} [NeZero width] {F : Type}
    (state : LoopSemStateBroad width F) (h : state.FiniteSupport) :
    (ofBroad state h).toBroad = state := rfl

/-- `ofBroad` after `toBroad` is the identity on the finite-map carrier. -/
theorem LoopSemStateBroad.ofBroad_toBroad {width : Nat} [NeZero width] {F : Type}
    (state : LoopSemStateFiniteExact width F) :
    ofBroad state.toBroad state.toBroad_finiteSupport = state := by
  cases state
  rfl

namespace LoopSemStateFiniteExact

/-- Canonical kernel witness for the `fmap_as_finite_support` `@[hol]`
    qualifier on `LoopSemStateFiniteExact`: the finite-map carrier is
    invertibly related to the broad one. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  ⟨fun state h => LoopSemStateBroad.toBroad_ofBroad state h,
    fun state => LoopSemStateBroad.ofBroad_toBroad state⟩

/-- Source-shaped `get_var_imm_def`
    (`cakeml/pancake/semantics/loopSemScript.sml:165-167`):

    ```
    (get_var_imm ((Reg n):'a reg_imm) ^s = sptree$lookup n s.locals) /\
    (get_var_imm (Imm w) s = SOME(Word w))
    ```

    Exact HOL port: the Lean statement is operand-first as in HOL and reads the
    `locals` `sptree$num_map` through the exact `Spt` carrier
    (`sptLookup`, the tagged `Flapjack/Misc/Sptree.lean` rendering of
    `sptree$lookup`).  It returns the exact `WordLocW` carrier (tagged
    `word_loc`) with no extra hypotheses beyond `[NeZero width]`.  No
    `fmap_as_finite_support` qualifier applies: `locals` is a `num_map`, not a
    `|->` field.  The only carrier translation is HOL's type-indexed `'a word`
    (the `RegImm`, `WordLocW` and `BitVec width` dimensions) to the positive
    `BitVec width`, so the tag carries `(words_as_type_indexed_bitvec)`. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "get_var_imm_def"
  (words_as_type_indexed_bitvec)]
def getVarImm {width : Nat} [NeZero width] {F : Type}
    (operand : RegImm (BitVec width)) (state : LoopSemStateFiniteExact width F) :
    Option (WordLocW width) :=
  match operand with
  | .reg name => sptLookup name state.locals
  | .imm value => some (.word value)

@[simp] theorem getVarImm_reg {width : Nat} [NeZero width] {F : Type}
    (state : LoopSemStateFiniteExact width F) (name : Nat) :
    getVarImm (.reg name) state = sptLookup name state.locals := rfl

@[simp] theorem getVarImm_imm {width : Nat} [NeZero width] {F : Type}
    (state : LoopSemStateFiniteExact width F) (value : BitVec width) :
    getVarImm (.imm value) state = some (.word value) := rfl

/-- Exact HOL `get_vars_def` (`loopSemScript.sml:98-107`), state second as in
    HOL: `get_vars [] s = SOME []`; `get_vars (v::vs) s` looks `v` up in the
    `locals` `num_map` and conses it onto `get_vars vs s`, failing if either
    fails. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "get_vars_def" (words_as_type_indexed_bitvec)]
def getVars {width : Nat} [NeZero width] {F : Type} :
    List Nat → LoopSemStateFiniteExact width F → Option (List (WordLocW width))
  | [], _ => some []
  | name :: names, state =>
      (sptLookup name state.locals).bind
        (fun value => (getVars names state).map (fun values => value :: values))

@[simp] theorem getVars_nil {width : Nat} [NeZero width] {F : Type}
    (state : LoopSemStateFiniteExact width F) :
    getVars [] state = some [] := rfl

theorem getVars_cons {width : Nat} [NeZero width] {F : Type}
    (name : Nat) (names : List Nat) (state : LoopSemStateFiniteExact width F) :
    getVars (name :: names) state =
      (sptLookup name state.locals).bind
        (fun value => (getVars names state).map (fun values => value :: values)) :=
  rfl


/-- Exact HOL `loopSem$result` (`cakeml/pancake/semantics/loopSemScript.sml:30-38`):

    ```
    result = Result (('w word_loc) list) | Exception ('w word_loc)
           | Break num | Continue num | TimeOut | FinalFFI final_event | Error
    ```

    over the exact `word_loc` carrier `WordLocW` and HOL `final_event`
    (`HolFinalEvent`). -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "result" (words_as_type_indexed_bitvec)]
inductive LoopResultExact (width : Nat) [NeZero width] where
  | result (values : List (WordLocW width))
  | exception (value : WordLocW width)
  | break (label : Nat)
  | continue (label : Nat)
  | timeOut
  | finalFfi (event : HolFinalEvent)
  | error

/-- Exact HOL `dec_clock_def` (`loopSemScript.sml:42-44`):
    `dec_clock s = s with clock := s.clock - 1`. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "dec_clock_def" (words_as_type_indexed_bitvec)]
def decClock {width : Nat} [NeZero width] {F : Type}
    (state : LoopSemStateFiniteExact width F) : LoopSemStateFiniteExact width F :=
  { state with clock := state.clock - 1 }

/-- Exact HOL `fix_clock_def` (`loopSemScript.sml:46-50`):
    `fix_clock old_s (res,new_s) = (res, new_s with clock := if old_s.clock <
    new_s.clock then old_s.clock else new_s.clock)`. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "fix_clock_def" (words_as_type_indexed_bitvec)]
def fixClock {width : Nat} [NeZero width] {F : Type} {β : Type}
    (old : LoopSemStateFiniteExact width F) (step : β × LoopSemStateFiniteExact width F) :
    β × LoopSemStateFiniteExact width F :=
  (step.1, { step.2 with
    clock := if old.clock < step.2.clock then old.clock else step.2.clock })

/-- Exact HOL `set_globals_def` (`loopSemScript.sml:52-55`):
    `set_globals gv w s = s with globals := s.globals |+ (gv,w)`. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "set_globals_def"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
def setGlobals {width : Nat} [NeZero width] {F : Type}
    (global : BitVec 5) (value : WordLocW width) (state : LoopSemStateFiniteExact width F) :
    LoopSemStateFiniteExact width F :=
  { state with globals := state.globals.update (global, value) }

/-- Exact HOL `set_var_def` (`loopSemScript.sml:108-111`):
    `set_var v x s = s with locals := insert v x s.locals`. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "set_var_def" (words_as_type_indexed_bitvec)]
def setVar {width : Nat} [NeZero width] {F : Type}
    (name : Nat) (value : WordLocW width) (state : LoopSemStateFiniteExact width F) :
    LoopSemStateFiniteExact width F :=
  { state with locals := sptInsert name value state.locals }

/-- Rendering of HOL `sptree$alist_insert` (`HOL/src/finite_maps/sptreeScript.sml`):
    `alist_insert [] xs t = t`, `alist_insert vs [] t = t`,
    `alist_insert (v::vs) (x::xs) t = insert v x (alist_insert vs xs t)`.  HOL
    standard library, outside `cakeml/`, so untagged. -/
def sptAlistInsert {α : Type} : List Nat → List α → Spt α → Spt α
  | [], _, t => t
  | _ :: _, [], t => t
  | v :: vs, x :: xs, t => sptInsert v x (sptAlistInsert vs xs t)

/-- Exact HOL `set_vars_def` (`loopSemScript.sml:113-116`):
    `set_vars vs xs s = s with locals := alist_insert vs xs s.locals`. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "set_vars_def" (words_as_type_indexed_bitvec)]
def setVars {width : Nat} [NeZero width] {F : Type}
    (names : List Nat) (values : List (WordLocW width)) (state : LoopSemStateFiniteExact width F) :
    LoopSemStateFiniteExact width F :=
  { state with locals := sptAlistInsert names values state.locals }

/-- Rendering of HOL `sptree$fromList` (`HOL/src/finite_maps/sptreeScript.sml`):
    `fromList l = SND (FOLDL (\(i,t) a. (i + 1, insert i a t)) (0,LN) l)`.
    HOL standard library, untagged. -/
def sptFromList {α : Type} (values : List α) : Spt α :=
  (values.foldl (fun (acc : Nat × Spt α) value => (acc.1 + 1, sptInsert acc.1 value acc.2))
    (0, .ln)).2

/-- Exact HOL `call_env_def` (`loopSemScript.sml:177-180`):
    `call_env args s = s with locals := fromList args`. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "call_env_def" (words_as_type_indexed_bitvec)]
def callEnv {width : Nat} [NeZero width] {F : Type}
    (arguments : List (WordLocW width)) (state : LoopSemStateFiniteExact width F) :
    LoopSemStateFiniteExact width F :=
  { state with locals := sptFromList arguments }

/-- Exact HOL `find_code_def` (`loopSemScript.sml:147-163`).  A direct call looks
    up `p`; an indirect call uses the last argument, which must be `Loc loc 0`,
    and drops it (`FRONT`).  Both check the argument count and bind the
    parameters with `fromAList (ZIP ...)`. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "find_code_def" (words_as_type_indexed_bitvec)]
def findCode {width : Nat} [NeZero width] :
    Option Nat → List (WordLocW width) → Spt (List Nat × HolLoopProg width) →
      Option (Spt (WordLocW width) × HolLoopProg width)
  | some target, arguments, code =>
      match sptLookup target code with
      | none => none
      | some (parameters, body) =>
          if arguments.length = parameters.length then
            some (sptFromAList (parameters.zip arguments), body)
          else none
  | none, [], _ => none
  | none, argument :: rest, code =>
      match (argument :: rest).getLast (by simp) with
      | .loc location 0 =>
          match sptLookup location code with
          | none => none
          | some (parameters, body) =>
              if (argument :: rest).length = parameters.length + 1 then
                some (sptFromAList (parameters.zip (argument :: rest).dropLast), body)
              else none
      | _ => none

/-- Exact HOL `mem_store_def` (`loopSemScript.sml:57-62`): store `w` at `addr`
    (`(addr =+ w) s.memory`) when `addr IN s.mdomain`, else `NONE`. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "mem_store_def" (words_as_type_indexed_bitvec)]
def memStore {width : Nat} [NeZero width] {F : Type}
    (address : BitVec width) (value : WordLocW width) (state : LoopSemStateFiniteExact width F) :
    Option (LoopSemStateFiniteExact width F) :=
  if state.mdomain address then
    some { state with memory := fun a => if a = address then value else state.memory a }
  else none

/-- Exact HOL `mem_load_def` (`loopSemScript.sml:64-69`): `SOME (s.memory addr)`
    when `addr IN s.mdomain`, else `NONE`. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "mem_load_def" (words_as_type_indexed_bitvec)]
def memLoad {width : Nat} [NeZero width] {F : Type}
    (address : BitVec width) (state : LoopSemStateFiniteExact width F) : Option (WordLocW width) :=
  if state.mdomain address then some (state.memory address) else none

/-- Exact HOL `eval_def` (`loopSemScript.sml:71-96`) for loopLang expressions:
    `Const`, `Var` (`lookup` in the `locals` num_map), `Lookup` (`FLOOKUP
    s.globals`), `Load` (through `mem_load`), `Op` (`the_words (MAP (eval s)
    ...)` then `word_op`), `Shift` (`word_sh sh w1 (w2n w2)`), `BaseAddr`,
    `TopAddr`. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "eval_def" (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
def eval {width : Nat} [NeZero width] {F : Type} (state : LoopSemStateFiniteExact width F) :
    HolLoopExp width → Option (WordLocW width)
  | .const w => some (.word w)
  | .var v => sptLookup v state.locals
  | .lookup name => state.globals.lookup name
  | .load address =>
      match eval state address with
      | some (.word w) => memLoad w state
      | _ => none
  | .op operator args =>
      match theWords (args.attach.map fun ⟨e, _⟩ => eval state e) with
      | some ws => (wordOpHOL operator ws).map WordLocW.word
      | none => none
  | .shift sh e1 e2 =>
      match eval state e1, eval state e2 with
      | some (.word w1), some (.word w2) => (wordShiftHOL sh w1 w2.toNat).map WordLocW.word
      | _, _ => none
  | .baseAddr => some (.word state.baseAddr)
  | .topAddr => some (.word state.topAddr)

/-- Exact HOL `loop_arith_def` (`loopSemScript.sml:118-146`): `LDiv` (unsigned
    word division, failing on a zero divisor), `LLongMul` (low and high halves of
    the natural product, `dimword` = `2 ^ width`) and `LLongDiv` (quotient and
    remainder of the two-word numerator, failing on a zero divisor or a quotient
    `>= dimword`), all through `set_var`. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "loop_arith_def" (words_as_type_indexed_bitvec)]
def loopArith {width : Nat} [NeZero width] {F : Type} (state : LoopSemStateFiniteExact width F) :
    LoopArith → Option (LoopSemStateFiniteExact width F)
  | .div r1 r2 r3 =>
      match sptLookup r3 state.locals, sptLookup r2 state.locals with
      | some (.word q), some (.word w2) =>
          if q ≠ 0 then some (setVar r1 (.word (w2 / q)) state) else none
      | _, _ => none
  | .longMul r1 r2 r3 r4 =>
      match sptLookup r3 state.locals, sptLookup r4 state.locals with
      | some (.word w3), some (.word w4) =>
          let r := w3.toNat * w4.toNat
          some (setVar r2 (.word (BitVec.ofNat width r))
            (setVar r1 (.word (BitVec.ofNat width (r / 2 ^ width))) state))
      | _, _ => none
  | .longDiv r1 r2 r3 r4 r5 =>
      match sptLookup r3 state.locals, sptLookup r4 state.locals, sptLookup r5 state.locals with
      | some (.word w3), some (.word w4), some (.word w5) =>
          let n := w3.toNat * 2 ^ width + w4.toNat
          let d := w5.toNat
          let q := n / d
          if d ≠ 0 ∧ q < 2 ^ width then
            some (setVar r1 (.word (BitVec.ofNat width q)) (setVar r2 (.word (BitVec.ofNat width (n % d))) state))
          else none
      | _, _, _ => none

end LoopSemStateFiniteExact

/-- Observational bridge from the exact `LoopSemStateFiniteExact` to the
    production `LoopMachineState`.  Word-location payloads compare through
    `loopValueOfWordLocW`; the total `memory` is option-valued on the production
    side (always present); the address sets are `Bool` predicates on both
    sides; the code table is related by the production association list
    enumerating entries of the exact finite map (`num_map` has no enumeration
    order), with the executable program the `loopProgExecRel` image of the
    faithful one; and the FFI state by `FfiStateRel`. -/
def LoopSemStateFiniteExact.prodRel {width : Nat} [NeZero width] {F : Type}
    (state : LoopSemStateFiniteExact width F)
    (machine : LoopMachineState (BitVec width) F) : Prop :=
  (∀ name, machine.locals name = (sptLookup name state.locals).map loopValueOfWordLocW) ∧
  (∀ global, machine.globals global = (state.globals.lookup global).map loopValueOfWordLocW) ∧
  (∀ address, machine.memory address = some (loopValueOfWordLocW (state.memory address))) ∧
  machine.mdomain = state.mdomain ∧
  machine.shMdomain = state.shMdomain ∧
  machine.clock = state.clock ∧
  machine.be = state.be ∧
  FfiStateRel machine.ffi state.ffi ∧
  machine.baseAddr = state.baseAddr ∧
  machine.topAddr = state.topAddr ∧
  (∀ entry, entry ∈ machine.code →
    ∃ program, sptLookup entry.1 state.code = some (entry.2.1, program) ∧
      loopProgExecRel entry.2.2 program)

/-- Register reads through `get_var_imm` on the production state agree with the
    exact carrier's local lookup under `prodRel`. -/
theorem LoopSemStateFiniteExact.getVarImm_map_eq_of_prodRel {width : Nat} [NeZero width]
    {F : Type} {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (h : state.prodRel machine) (operand : RegImm (BitVec width)) :
    (LoopSemStateFiniteExact.getVarImm operand state).map loopValueOfWordLocW =
      Flapjack.getVarImm machine operand := by
  cases operand with
  | reg name => exact (h.1 name).symm
  | imm value => rfl

/-- Variable reads through `get_vars` on the production state agree with the
    exact carrier's recursive read under `prodRel`. -/
theorem LoopSemStateFiniteExact.getVars_map_eq_of_prodRel {width : Nat} [NeZero width]
    {F : Type} {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (h : state.prodRel machine) (names : List Nat) :
    (LoopSemStateFiniteExact.getVars names state).map (List.map loopValueOfWordLocW) =
      Flapjack.getVars names machine := by
  induction names with
  | nil => rfl
  | cons name names ih =>
      rw [LoopSemStateFiniteExact.getVars_cons, Flapjack.getVars, h.1 name]
      cases hlookup : sptLookup name state.locals with
      | none => rfl
      | some value =>
          simp only [Option.bind_some, Option.map_some, Option.map_map]
          rw [← ih]
          cases hg : LoopSemStateFiniteExact.getVars names state <;> rfl

end Flapjack
