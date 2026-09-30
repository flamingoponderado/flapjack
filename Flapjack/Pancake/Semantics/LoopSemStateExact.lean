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
    `sptree$lookup`). It returns the exact `WordLocW` carrier (tagged
    `word_loc`) with no extra hypotheses beyond `[NeZero width]`. The lookup is
    over `locals`, a `num_map` rather than a `|->` field, but the full state
    carrier also contains `globals : 5 word |-> word_loc`; therefore the tag
    records the carrier's `fmap_as_finite_support := [globals]` translation.
    The same-module `holFmapAsFiniteSupportWitness` checks the canonical
    roundtrip. HOL's type-indexed `'a word` is translated to positive
    `BitVec width`, recorded by `(words_as_type_indexed_bitvec)`. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "get_var_imm_def"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
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
    fails. The state carrier's `globals` `|->` representation is recorded by
    the finite-support qualifier and same-module canonical witness. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "get_vars_def"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
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
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "dec_clock_def"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
def decClock {width : Nat} [NeZero width] {F : Type}
    (state : LoopSemStateFiniteExact width F) : LoopSemStateFiniteExact width F :=
  { state with clock := state.clock - 1 }

/-- Exact HOL `fix_clock_def` (`loopSemScript.sml:46-50`):
    `fix_clock old_s (res,new_s) = (res, new_s with clock := if old_s.clock <
    new_s.clock then old_s.clock else new_s.clock)`. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "fix_clock_def"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
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
    `set_var v x s = s with locals := insert v x s.locals`. `locals` is the
    exact `num_map`; the full state carrier's sole `|->` field, `globals`, is
    recorded by the finite-support qualifier and canonical witness. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "set_var_def"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
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
    `set_vars vs xs s = s with locals := alist_insert vs xs s.locals`. The
    `locals` map remains the exact `num_map`; the full state carrier's only
    `|->` field `globals` is recorded by the finite-support qualifier and
    canonical witness. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "set_vars_def"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
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
    `call_env args s = s with locals := fromList args`. The replacement is
    the exact `num_map` `fromList` rendering; the full state carrier's sole
    `|->` field `globals` is recorded by the finite-support qualifier and
    canonical witness. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "call_env_def"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
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
    (`(addr =+ w) s.memory`) when `addr IN s.mdomain`, else `NONE`. `memory`
    is a total function, not a finite map; the full state carrier's distinct
    `globals` `|->` field is recorded by the finite-support qualifier and
    same-module canonical witness. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "mem_store_def"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
def memStore {width : Nat} [NeZero width] {F : Type}
    (address : BitVec width) (value : WordLocW width) (state : LoopSemStateFiniteExact width F) :
    Option (LoopSemStateFiniteExact width F) :=
  if state.mdomain address then
    some { state with memory := fun a => if a = address then value else state.memory a }
  else none

/-- Exact HOL `mem_load_def` (`loopSemScript.sml:64-69`): `SOME (s.memory addr)`
    when `addr IN s.mdomain`, else `NONE`. `memory` is total; the state
    carrier's separate `globals` `|->` field is recorded by the finite-support
    qualifier and same-module canonical witness. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "mem_load_def"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
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

/-- Exact HOL `loop_arith_def` (`loopSemScript.sml:118-146`): `LDiv` (signed
    truncating word quotient, failing on a zero divisor), `LLongMul` (low and high halves of
    the natural product, `dimword` = `2 ^ width`) and `LLongDiv` (quotient and
    remainder of the two-word numerator, failing on a zero divisor or a quotient
    `>= dimword`), all through `set_var`. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "loop_arith_def" (words_as_type_indexed_bitvec)]
def loopArith {width : Nat} [NeZero width] {F : Type} (state : LoopSemStateFiniteExact width F) :
    LoopArith → Option (LoopSemStateFiniteExact width F)
  | .div r1 r2 r3 =>
      match sptLookup r3 state.locals, sptLookup r2 state.locals with
      | some (.word q), some (.word w2) =>
          if q ≠ 0 then some (setVar r1 (.word (w2.sdiv q)) state) else none
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

/-- Exact HOL `exit_loop_def` (`loopSemScript.sml:272-276`):

    ```
    exit_loop (SOME (Break n)) = SOME (Break (n - 1)) ∧
    exit_loop (SOME (Continue n)) = SOME (Continue (n - 1)) ∧
    exit_loop res = res
    ```
-/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "exit_loop_def"
  (words_as_type_indexed_bitvec)]
def exitLoop {width : Nat} [NeZero width] :
    Option (LoopResultExact width) → Option (LoopResultExact width)
  | some (.break n) => some (.break (n - 1))
  | some (.continue n) => some (.continue (n - 1))
  | res => res

/-- Exact HOL `loop_primop_def` (`loopSemScript.sml:242-253`) over the exact
    `word_loc` carrier `WordLocW`:

    ```
    loop_primop AddCarry args =
      if LENGTH args = 3 ∧ EVERY isWord args then
        let l = theWord (EL 0 args); r = theWord (EL 1 args);
            ci = theWord (EL 2 args); (res, co) = word_add_carry l r ci
        in SOME [Word res; Word co]
      else NONE
    ```

    The length-three, all-`Word` guard is the single list pattern. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "loop_primop_def"
  (words_as_type_indexed_bitvec)]
def loopPrimop {width : Nat} [NeZero width] :
    PrimOp → List (WordLocW width) → Option (List (WordLocW width))
  | .addCarry, [.word l, .word r, .word ci] =>
      let (res, co) := wordAddCarryHOL l r ci
      some [.word res, .word co]
  | _, _ => none

/-- Computable subset test on the exact spt carrier: enumerate the keys of
    `left` through an absolute-key map `g` and check each is present in
    `right`.  Untagged Flapjack infrastructure. -/
def sptSubsetAux {α β : Type} (right : Spt β) (g : Nat → Nat) : Spt α → Bool
  | .ln => true
  | .ls _ => (sptLookup (g 0) right).isSome
  | .bn first second =>
      sptSubsetAux right (fun m => g (2 * m + 2)) first &&
        sptSubsetAux right (fun m => g (2 * m + 1)) second
  | .bs first _ second =>
      (sptLookup (g 0) right).isSome &&
        (sptSubsetAux right (fun m => g (2 * m + 2)) first &&
          sptSubsetAux right (fun m => g (2 * m + 1)) second)

/-- Correctness of `sptSubsetAux`: the Boolean test accepts exactly when every
    key of `left`, mapped by `g`, lies in `right`. -/
theorem sptSubsetAux_eq_true {α β : Type} (right : Spt β) :
    ∀ (g : Nat → Nat) (left : Spt α),
      sptSubsetAux right g left = true ↔ ∀ key, sptMem key left → sptMem (g key) right := by
  intro g left
  induction left generalizing g with
  | ln => simp [sptSubsetAux]
  | ls value =>
      simp only [sptSubsetAux]
      constructor
      · intro h key hk
        have hk0 : key = 0 := (sptMem_ls key value).mp hk
        subst hk0
        exact (sptMem_iff_lookup _ _).mpr (Option.isSome_iff_exists.mp h)
      · intro h
        exact Option.isSome_iff_exists.mpr
          ((sptMem_iff_lookup _ _).mp (h 0 ((sptMem_ls 0 value).mpr rfl)))
  | bn first second ihl ihr =>
      simp only [sptSubsetAux, Bool.and_eq_true, sptMem_bn]
      rw [ihl (fun m => g (2 * m + 2)), ihr (fun m => g (2 * m + 1))]
      constructor
      · rintro ⟨hl, hr⟩ key (⟨m, hm, hk⟩ | ⟨m, hm, hk⟩)
        · subst hk; exact hl m hm
        · subst hk; exact hr m hm
      · intro h
        exact ⟨fun m hm => h (2 * m + 2) (Or.inl ⟨m, hm, rfl⟩),
          fun m hm => h (2 * m + 1) (Or.inr ⟨m, hm, rfl⟩)⟩
  | bs first value second ihl ihr =>
      simp only [sptSubsetAux, Bool.and_eq_true, sptMem_bs]
      rw [ihl (fun m => g (2 * m + 2)), ihr (fun m => g (2 * m + 1))]
      constructor
      · rintro ⟨h0, hl, hr⟩ key (h0' | ⟨m, hm, hk⟩ | ⟨m, hm, hk⟩)
        · subst h0'
          exact (sptMem_iff_lookup _ _).mpr (Option.isSome_iff_exists.mp h0)
        · subst hk; exact hl m hm
        · subst hk; exact hr m hm
      · intro h
        exact ⟨Option.isSome_iff_exists.mpr ((sptMem_iff_lookup _ _).mp (h 0 (Or.inl rfl))),
          fun m hm => h (2 * m + 2) (Or.inr (Or.inl ⟨m, hm, rfl⟩)),
          fun m hm => h (2 * m + 1) (Or.inr (Or.inr ⟨m, hm, rfl⟩))⟩

/-- Predicate rendering of HOL set inclusion on `sptree$num_set`
    (`domain live SUBSET domain s.locals`, `loopSemScript.sml:186`): HOL sets are
    rendered as membership predicates (`sptMem`), so subset is the pointwise
    implication.  Used by the exact `cut_state` guard.  Untagged Flapjack
    infrastructure (HOL `SUBSET` over `num_set` is outside the carrier
    translation). -/
def sptSubsetLive {α β : Type} (left : Spt α) (right : Spt β) : Prop :=
  ∀ key, sptMem key left → sptMem key right

/-- The computable subset test decides `sptSubsetLive`. -/
theorem sptSubsetAux_id_eq_true {α β : Type} (left : Spt α) (right : Spt β) :
    sptSubsetAux right id left = true ↔ sptSubsetLive left right :=
  sptSubsetAux_eq_true right id left

/-- Decision procedure for the `cut_state` guard: enumerate the finite live set
    and look each key up in the local map. -/
instance sptSubsetLiveDecidable {α β : Type} (left : Spt α) (right : Spt β) :
    Decidable (sptSubsetLive left right) :=
  decidable_of_iff (sptSubsetAux right id left = true) (sptSubsetAux_id_eq_true left right)

/-- Exact HOL `cut_state_def`
    (`cakeml/pancake/semantics/loopSemScript.sml:182-187`):
    `cut_state live s = if domain live SUBSET domain s.locals then
    SOME (s with locals := inter s.locals live) else NONE`.  The set inclusion
    `domain live SUBSET domain s.locals` is rendered as `sptSubsetLive`, and the
    restricted local map uses the heterogeneous `sptInter`.  The guard is a
    finite-set inclusion decided by the computable `sptSubsetAux` enumeration
    (`sptSubsetLiveDecidable`), so the definition is executable; the production
    executable counterpart is `Flapjack.cutLoopState`. The full state carrier's
    sole `|->` field `globals` is recorded by the finite-support qualifier and
    same-module canonical witness. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "cut_state_def"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
def cutState {width : Nat} [NeZero width] {F : Type} (live : NumSet)
    (state : LoopSemStateFiniteExact width F) :
    Option (LoopSemStateFiniteExact width F) :=
  if sptSubsetLive live state.locals then
    some { state with locals := sptInter state.locals live }
  else none

/-- `cutState` succeeds exactly when the live keys are all locals, returning the
    state with `locals` restricted to the live keys. -/
theorem cutState_of_subset {width : Nat} [NeZero width] {F : Type}
    (live : NumSet) (state : LoopSemStateFiniteExact width F)
    (h : sptSubsetLive live state.locals) :
    cutState live state = some { state with locals := sptInter state.locals live } := by
  unfold cutState
  rw [if_pos h]

/-- `cutState` fails exactly when some live key is not a local. -/
theorem cutState_eq_none_of_not_subset {width : Nat} [NeZero width] {F : Type}
    (live : NumSet) (state : LoopSemStateFiniteExact width F)
    (h : ¬ sptSubsetLive live state.locals) :
    cutState live state = none := by
  unfold cutState
  rw [if_neg h]

/-- `cut_state` preserves the clock (HOL's `s with locals := inter s.locals live`
    updates only `locals`). -/
theorem cutState_some_clock {width : Nat} [NeZero width] {F : Type}
    {live : NumSet} {state cut : LoopSemStateFiniteExact width F}
    (h : cutState live state = some cut) : cut.clock = state.clock := by
  by_cases hsub : sptSubsetLive live state.locals
  · rw [cutState_of_subset live state hsub] at h
    injection h with h
    subst h
    rfl
  · rw [cutState_eq_none_of_not_subset live state hsub] at h
    exact absurd h (by simp)

/-- `cut_state` preserves every field except `locals`. -/
theorem cutState_some_frame {width : Nat} [NeZero width] {F : Type}
    {live : NumSet} {state cut : LoopSemStateFiniteExact width F}
    (h : cutState live state = some cut) :
    cut.globals = state.globals ∧ cut.memory = state.memory ∧
      cut.mdomain = state.mdomain ∧ cut.shMdomain = state.shMdomain ∧
      cut.clock = state.clock ∧ cut.code = state.code ∧ cut.be = state.be ∧
      cut.ffi = state.ffi ∧ cut.baseAddr = state.baseAddr ∧
      cut.topAddr = state.topAddr := by
  by_cases hsub : sptSubsetLive live state.locals
  · rw [cutState_of_subset live state hsub] at h
    injection h with h
    subst h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [cutState_eq_none_of_not_subset live state hsub] at h
    exact absurd h (by simp)

/-- Exact HOL `cut_res_def`
    (`cakeml/pancake/semantics/loopSemScript.sml:189-197`):
    `cut_res live (res,s) = if res ≠ NONE then (res,s) else
    case cut_state live s of NONE => (SOME Error,s)
    | SOME s => if s.clock = 0 then (SOME TimeOut, s with locals := LN)
                else (res, dec_clock s)`.  The `SOME` branch rebinds `s` to the
    cut state and `res` is `NONE`, so the final branch returns
    `(NONE, dec_clock cut)`. The state carrier's `globals` `|->` field is
    recorded by the finite-support qualifier and same-module canonical witness. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "cut_res_def"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
def cutRes {width : Nat} [NeZero width] {F : Type} (live : NumSet)
    (step : Option (LoopResultExact width) × LoopSemStateFiniteExact width F) :
    Option (LoopResultExact width) × LoopSemStateFiniteExact width F :=
  match step.1 with
  | some result => (some result, step.2)
  | none =>
      match cutState live step.2 with
      | none => (some .error, step.2)
      | some cut =>
          if cut.clock = 0 then
            (some .timeOut, { cut with locals := .ln })
          else (none, decClock cut)

end LoopSemStateFiniteExact

/-- Reverse/coverage direction of the exact/production code-table relation:
    every successful HOL `sptree$lookup` on the exact `code` `sptree$num_map`
    has a matching association-list entry in the production state, with the
    executable program the `loopProgExecRel` image of the faithful one.  This
    is the two-way counterpart of the forward code conjunct of `prodRel`
    (below), which maps each production entry back to a successful exact
    lookup: together they pin down the exact finite support of `code` as
    exactly the labels occurring in `machine.code`.  A raw lookup-level
    statement avoids needing an enumeration (`toAList`/`fold`) lemma for the
    `Spt` carrier.  Flapjack bridge infrastructure (no `@[hol]` tag). -/
def LoopCodeTableCoverage {width : Nat} [NeZero width] {F : Type}
    (state : LoopSemStateFiniteExact width F)
    (machine : LoopMachineState (BitVec width) F) : Prop :=
  ∀ label parameters program,
    sptLookup label state.code = some (parameters, program) →
      ∃ entry ∈ machine.code,
        entry.1 = label ∧ entry.2.1 = parameters ∧
          loopProgExecRel entry.2.2 program

/-- Observational bridge from the exact `LoopSemStateFiniteExact` to the
    production `LoopMachineState`.  Word-location payloads compare through
    `loopValueOfWordLocW`; the total `memory` is option-valued on the production
    side (always present); the address sets are `Bool` predicates on both
    sides; the code table is related in BOTH directions: the forward conjunct
    maps each production association-list entry to a successful exact
    `sptLookup` (with the executable program the `loopProgExecRel` image of the
    faithful one), and `LoopCodeTableCoverage` supplies the reverse direction,
    so the exact finite support of `code` is exactly the labels listed in
    `machine.code`; and the FFI state by `FfiStateRel`. -/
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
      loopProgExecRel entry.2.2 program) ∧
  LoopCodeTableCoverage state machine

/-- Construct the production state carrier observed by `prodRel` from an
    exact HOL-shaped state, while keeping the production FFI carrier and code
    table explicit. This is Flapjack-only carrier infrastructure: HOL defines
    one `loopSem$state` datatype and has no conversion to the production
    association-list / `FfiState` representation. -/
def LoopSemStateFiniteExact.toProductionState {width : Nat} [NeZero width]
    {F : Type} (state : LoopSemStateFiniteExact width F)
    (code : LoopCode (BitVec width)) (ffi : FfiState F) :
    LoopMachineState (BitVec width) F where
  locals := fun name => (sptLookup name state.locals).map loopValueOfWordLocW
  globals := fun address => (state.globals.lookup address).map loopValueOfWordLocW
  memory := fun address => some (loopValueOfWordLocW (state.memory address))
  mdomain := state.mdomain
  shMdomain := state.shMdomain
  clock := state.clock
  code := code
  be := state.be
  ffi := ffi
  baseAddr := state.baseAddr
  topAddr := state.topAddr

/-- The state constructor satisfies the observational production relation when
    the caller supplies the two genuinely non-structural obligations: related
    FFI states and both directions of the production-list/exact-Spt code
    relation. This does not identify any actual CLI state constructor or prove
    an evaluator simulation; its purpose is to make those remaining premises
    explicit for subsequent source-route proofs. Flapjack-only infrastructure,
    with no separate HOL theorem for a carrier conversion. -/
theorem LoopSemStateFiniteExact.toProductionState_prodRel {width : Nat}
    [NeZero width] {F : Type} (state : LoopSemStateFiniteExact width F)
    (code : LoopCode (BitVec width)) (ffi : FfiState F)
    (hFfi : FfiStateRel ffi state.ffi)
    (hRows : ∀ entry, entry ∈ code →
      ∃ program, sptLookup entry.1 state.code = some (entry.2.1, program) ∧
        loopProgExecRel entry.2.2 program)
    (hCoverage : ∀ label parameters program,
      sptLookup label state.code = some (parameters, program) →
        ∃ entry ∈ code, entry.1 = label ∧ entry.2.1 = parameters ∧
          loopProgExecRel entry.2.2 program) :
    state.prodRel (state.toProductionState code ffi) := by
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl, hFfi, rfl, rfl, ?_, ?_⟩
  · intro name
    rfl
  · intro global
    rfl
  · intro address
    rfl
  · intro entry hEntry
    exact hRows entry hEntry
  · intro label parameters program hLookup
    exact hCoverage label parameters program hLookup

/-- Exact and production Loop states preserve `prodRel` when the source
    `set_var` update is paired with the executable `loopSetVar` update. The
    local-map lookup proof uses the exact `sptInsert` lookup equations; every
    other state field is unchanged by both updates. This is a Flapjack-only
    cross-carrier transition lemma for evaluator-case proofs, not a separate
    HOL declaration or a whole-evaluator simulation theorem. -/
theorem LoopSemStateFiniteExact.setVar_prodRel {width : Nat} [NeZero width]
    {F : Type} {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hrel : state.prodRel machine) (name : Nat) (value : WordLocW width) :
    (setVar name value state).prodRel
      {machine with locals := loopSetVar machine.locals name (loopValueOfWordLocW value)} := by
  rcases hrel with
    ⟨hlocals, hglobals, hmemory, hmdomain, hshMdomain, hclock, hbe, hffi,
      hbaseAddr, htopAddr, hcode, hcoverage⟩
  refine ⟨?_, hglobals, hmemory, hmdomain, hshMdomain, hclock, hbe, hffi,
    hbaseAddr, htopAddr, hcode, hcoverage⟩
  intro key
  by_cases hkey : key = name
  · subst key
    simp [setVar, loopSetVar, sptLookup_sptInsert_same]
  · calc
      loopSetVar machine.locals name (loopValueOfWordLocW value) key =
          machine.locals key := by simp [loopSetVar, hkey]
      _ = (sptLookup key state.locals).map loopValueOfWordLocW := hlocals key
      _ = (sptLookup key (sptInsert name value state.locals)).map
            loopValueOfWordLocW := by
              rw [sptLookup_sptInsert_ne name key value state.locals hkey]

private theorem loopSetVars_sptAlistInsert_map {α β : Type} (f : α → β)
    (names : List Nat) (values : List α) (tree : Spt α) :
    loopSetVars (fun key => (sptLookup key tree).map f) names (values.map f) =
      fun key => (sptLookup key
        (LoopSemStateFiniteExact.sptAlistInsert names values tree)).map f := by
  induction names generalizing values tree with
  | nil =>
      funext key
      simp [loopSetVars, lookupFirst, LoopSemStateFiniteExact.sptAlistInsert]
  | cons name names ih =>
      cases values with
      | nil =>
          funext key
          simp [loopSetVars, lookupFirst, LoopSemStateFiniteExact.sptAlistInsert]
      | cons value values =>
          funext key
          by_cases hkey : key = name
          · subst key
            simp [loopSetVars, lookupFirst, List.zip_cons_cons,
              LoopSemStateFiniteExact.sptAlistInsert,
              sptLookup_sptInsert_same]
          · have htail := ih values tree
            calc
              loopSetVars (fun k => (sptLookup k tree).map f)
                  (name :: names) (f value :: values.map f) key =
                loopSetVars (fun k => (sptLookup k tree).map f)
                  names (values.map f) key := by
                    simp [loopSetVars, lookupFirst, List.zip_cons_cons, hkey]
              _ = (sptLookup key
                    (LoopSemStateFiniteExact.sptAlistInsert names values tree)).map f :=
                    congrFun htail key
              _ = (sptLookup key
                    (LoopSemStateFiniteExact.sptAlistInsert (name :: names)
                      (value :: values) tree)).map f := by
                    simp only [LoopSemStateFiniteExact.sptAlistInsert]
                    rw [sptLookup_sptInsert_ne name key value
                      (LoopSemStateFiniteExact.sptAlistInsert names values tree) hkey]

/-- Production Loop state update paired with a WordLoc-valued exact
    `set_vars`. Flapjack-only bridge helper; HOL's `set_vars` operates on its
    single exact state carrier and does not define this production conversion. -/
def loopMachineSetVarsWordLoc {width : Nat} [NeZero width] {F : Type}
    (machine : LoopMachineState (BitVec width) F) (names : List Nat)
    (values : List (WordLocW width)) : LoopMachineState (BitVec width) F :=
  { machine with locals :=
      loopSetVars machine.locals names (values.map loopValueOfWordLocW) }

/-- Exact and production Loop states preserve `prodRel` when the source
    `set_vars` alist insertion is paired with the production overlay. The proof
    retains HOL's first-occurrence-wins duplicate behavior and `ZIP` truncation
    for unequal list lengths. This is a Flapjack-only cross-carrier transition
    lemma for call/return case proofs, not a full evaluator simulation. -/
theorem LoopSemStateFiniteExact.setVars_prodRel {width : Nat} [NeZero width]
    {F : Type} {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hrel : state.prodRel machine) (names : List Nat)
    (values : List (WordLocW width)) :
    (LoopSemStateFiniteExact.setVars names values state).prodRel
      (loopMachineSetVarsWordLoc machine names values) := by
  rcases hrel with
    ⟨hlocals, hglobals, hmemory, hmdomain, hshMdomain, hclock, hbe, hffi,
      hbaseAddr, htopAddr, hcode, hcoverage⟩
  refine ⟨?_, hglobals, hmemory, hmdomain, hshMdomain, hclock, hbe, hffi,
    hbaseAddr, htopAddr, hcode, hcoverage⟩
  intro key
  change loopSetVars machine.locals names (values.map loopValueOfWordLocW) key =
    (sptLookup key (LoopSemStateFiniteExact.sptAlistInsert names values state.locals)).map
      loopValueOfWordLocW
  have hlocalsEq : machine.locals =
      (fun key => (sptLookup key state.locals).map loopValueOfWordLocW) := by
    funext localName
    exact hlocals localName
  rw [hlocalsEq]
  exact congrFun (loopSetVars_sptAlistInsert_map loopValueOfWordLocW names
    values state.locals) key

/-- Source-shaped `find_code` (`loopSemScript.sml:147-163`) reading the exact
    `code` `sptree$num_map` through `sptLookup`.  The code-table representation
    (`Spt` versus the production association list) and the program carrier
    (`HolLoopProg` versus `LoopProg`) are the only differences from
    `Flapjack.findLoopCode`; the argument and local-environment word-location
    values are the executable `LoopValue` mirror on both sides, so the shared
    `loopSetVars` overlay is used verbatim.  Flapjack bridge infrastructure
    (no `@[hol]` tag): it is the exact `code`-table reading used to relate the
    production association-list lookup to the HOL `num_map` lookup. -/
def findLoopCodeSpt {width : Nat} [NeZero width]
    (label : Option Nat) (args : List (LoopValue (BitVec width)))
    (code : Spt (List Nat × HolLoopProg width)) :
    Option ((Nat → Option (LoopValue (BitVec width))) × HolLoopProg width) :=
  match label with
  | some entry =>
      match sptLookup entry code with
      | none => none
      | some (parameters, body) =>
          if args.length = parameters.length then
            some (loopSetVars (fun _ => none) parameters args, body)
          else none
  | none =>
      if args = [] then none
      else
        match args.getLast? with
        | some (.loc identifier 0) =>
            match sptLookup identifier code with
            | none => none
            | some (parameters, body) =>
                if args.length = parameters.length + 1 then
                  some (loopSetVars (fun _ => none) parameters args.dropLast, body)
                else none
        | _ => none

/-- Result correspondence for the production `findLoopCode` and the exact
    `findLoopCodeSpt`: both succeed with the same local environment and
    `loopProgExecRel`-related bodies, or both fail.  Flapjack bridge
    infrastructure (no `@[hol]` tag). -/
def loopFindCodeResultRel {width : Nat} [NeZero width] :
    Option ((Nat → Option (LoopValue (BitVec width))) × LoopProg (BitVec width)) →
    Option ((Nat → Option (LoopValue (BitVec width))) × HolLoopProg width) → Prop
  | some (executableEnv, executableBody), some (holEnv, holBody) =>
      executableEnv = holEnv ∧ loopProgExecRel executableBody holBody
  | none, none => True
  | _, _ => False

namespace LoopSemStateFiniteExact

/-- Under the forward code conjunct, a successful production
    `lookupLoopFunction` always lands on a successful exact lookup.  Used to
    show that an absent exact entry stays absent from production.  Flapjack
    bridge infrastructure (no `@[hol]` tag). -/
theorem lookupLoopFunction_eq_none_of_rel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F} {code : LoopCode (BitVec width)}
    (hcode : ∀ entry, entry ∈ code →
      ∃ program, sptLookup entry.1 state.code = some (entry.2.1, program) ∧
        loopProgExecRel entry.2.2 program)
    {label : Nat} (hlookup : sptLookup label state.code = none) :
    lookupLoopFunction label code = none := by
  revert hcode
  induction code with
  | nil => intro _; rfl
  | cons head rest ih =>
      intro hcode
      rcases head with ⟨candidate, headParameters, headBody⟩
      by_cases hc : (label == candidate) = true
      · simp only [lookupLoopFunction, hc, if_true]
        obtain ⟨program, hlookup', _⟩ :=
          hcode (candidate, headParameters, headBody) (by simp)
        have hcand : label = candidate := by simpa [beq_iff_eq] using hc
        rw [← hcand, hlookup] at hlookup'
        exact absurd hlookup' (by simp)
      · simp only [lookupLoopFunction, hc]
        exact ih (fun entry hentry => hcode entry (List.mem_cons_of_mem _ hentry))

/-- Under both code conjuncts, a successful exact `sptLookup` is realised by
    the FIRST production association-list entry with that label, with the
    executable program related to the faithful one.  First-occurrence-wins in
    `lookupLoopFunction` is handled by the forward conjunct forcing every
    duplicate entry back to the same exact lookup.  Flapjack bridge
    infrastructure (no `@[hol]` tag). -/
theorem lookupLoopFunction_eq_of_rel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F} {code : LoopCode (BitVec width)}
    (hcode : ∀ entry, entry ∈ code →
      ∃ program, sptLookup entry.1 state.code = some (entry.2.1, program) ∧
        loopProgExecRel entry.2.2 program)
    {label : Nat} {parameters : List Nat} {program : HolLoopProg width}
    (hex : ∃ entry, entry ∈ code ∧ entry.1 = label)
    (hlookup : sptLookup label state.code = some (parameters, program)) :
    ∃ executableProgram,
      lookupLoopFunction label code = some (parameters, executableProgram) ∧
        loopProgExecRel executableProgram program := by
  revert hcode hex
  induction code with
  | nil =>
      intro hcode hex
      obtain ⟨entry, hentry, _⟩ := hex
      simp at hentry
  | cons head rest ih =>
      intro hcode hex
      rcases head with ⟨candidate, headParameters, headBody⟩
      simp only [lookupLoopFunction]
      by_cases hc : (label == candidate) = true
      · simp only [hc, if_true]
        obtain ⟨program', hlookup', hrel'⟩ :=
          hcode (candidate, headParameters, headBody) (by simp)
        have hcand : label = candidate := by simpa [beq_iff_eq] using hc
        rw [← hcand, hlookup] at hlookup'
        simp only [Option.some.injEq] at hlookup'
        have hparams : parameters = headParameters := congrArg Prod.fst hlookup'
        have hprog : program = program' := congrArg Prod.snd hlookup'
        refine ⟨headBody, ?_, ?_⟩
        · rw [← hparams]
        · rwa [← hprog] at hrel'
      · simp only [hc]
        obtain ⟨entry, hentry, hentryLabel⟩ := hex
        rcases List.mem_cons.mp hentry with hhead | hrest
        · have hcand : candidate = label := by
            rw [hhead] at hentryLabel
            simpa using hentryLabel
          exact absurd (beq_iff_eq.mpr hcand.symm) hc
        · exact ih
            (fun entry hentry => hcode entry (List.mem_cons_of_mem _ hentry))
            ⟨entry, hrest, hentryLabel⟩

/-- Production lookup correspondence under the full state bridge.  Flapjack
    bridge infrastructure (no `@[hol]` tag). -/
theorem lookupLoopFunction_eq_of_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (h : state.prodRel machine)
    {label : Nat} {parameters : List Nat} {program : HolLoopProg width}
    (hlookup : sptLookup label state.code = some (parameters, program)) :
    ∃ executableProgram,
      lookupLoopFunction label machine.code = some (parameters, executableProgram) ∧
        loopProgExecRel executableProgram program := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hcode, hcov⟩ := h
  obtain ⟨entry, hentry, hlabel, _, _⟩ := hcov label parameters program hlookup
  exact lookupLoopFunction_eq_of_rel hcode ⟨entry, hentry, hlabel⟩ hlookup

/-- Production lookup absence under the full state bridge.  Flapjack bridge
    infrastructure (no `@[hol]` tag). -/
theorem lookupLoopFunction_eq_none_of_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (h : state.prodRel machine)
    {label : Nat} (hlookup : sptLookup label state.code = none) :
    lookupLoopFunction label machine.code = none := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hcode, _⟩ := h
  exact lookupLoopFunction_eq_none_of_rel hcode hlookup

/-- `find_code` correspondence: under `prodRel`, the production executable
    `findLoopCode` on the association-list code table and the exact
    source-shaped `findLoopCodeSpt` on the `sptree$num_map` code table produce
    corresponding results.  Both the labelled (`some entry`) and link
    (`.loc _ 0` trailing argument) cases are handled, including the
    duplicate-label first-occurrence-wins order of `lookupLoopFunction`.
    Flapjack bridge infrastructure (no `@[hol]` tag): it proves the compiled
    executable lookup agrees with the faithful `loopSem$find_code` reading. -/
theorem findLoopCode_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (h : state.prodRel machine) (label : Option Nat)
    (args : List (LoopValue (BitVec width))) :
    loopFindCodeResultRel (findLoopCode label args machine.code)
      (findLoopCodeSpt label args state.code) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hcode, hcov⟩ := h
  cases label with
  | some entry =>
      simp only [findLoopCode, findLoopCodeSpt]
      cases hlookup : sptLookup entry state.code with
      | none =>
          have hprod := lookupLoopFunction_eq_none_of_rel hcode hlookup
          simp only [hprod, loopFindCodeResultRel]
      | some pair =>
          obtain ⟨parameters, holBody⟩ := pair
          obtain ⟨codeEntry, hentry, hlabel, _, _⟩ :=
            hcov entry parameters holBody hlookup
          obtain ⟨execBody, hprod, hrel⟩ :=
            lookupLoopFunction_eq_of_rel hcode ⟨codeEntry, hentry, hlabel⟩ hlookup
          simp only [hprod]
          by_cases hlen : args.length = parameters.length
          · simp only [hlen, if_true]
            exact ⟨rfl, hrel⟩
          · simp only [hlen, if_false, loopFindCodeResultRel]
  | none =>
      simp only [findLoopCode, findLoopCodeSpt]
      by_cases hempty : args = []
      · simp only [hempty, if_true, loopFindCodeResultRel]
      · simp only [hempty, if_false]
        cases hlast : args.getLast? with
        | none => simp only [loopFindCodeResultRel]
        | some last =>
            cases last with
            | word value => simp only [loopFindCodeResultRel]
            | loc identifier offset =>
                cases offset with
                | zero =>
                    by_cases hlookup : sptLookup identifier state.code = none
                    · have hprod := lookupLoopFunction_eq_none_of_rel hcode hlookup
                      simp only [loopFindCodeResultRel]
                      rw [hlookup, hprod]
                      trivial
                    · obtain ⟨pair, hsome⟩ : ∃ pair, sptLookup identifier state.code = some pair := by
                        cases h : sptLookup identifier state.code with
                        | none => exact absurd h hlookup
                        | some p => exact ⟨p, rfl⟩
                      obtain ⟨parameters, holBody⟩ := pair
                      obtain ⟨codeEntry, hentry, hlabel, _, _⟩ :=
                        hcov identifier parameters holBody hsome
                      obtain ⟨execBody, hprod, hrel⟩ :=
                        lookupLoopFunction_eq_of_rel hcode
                          ⟨codeEntry, hentry, hlabel⟩ hsome
                      simp only [loopFindCodeResultRel]
                      rw [hsome, hprod]
                      by_cases hlen : args.length = parameters.length + 1
                      · simp only [hlen, if_true]
                        exact ⟨trivial, hrel⟩
                      · simp only [hlen, if_false]
                | succ offset => simp only [loopFindCodeResultRel]

end LoopSemStateFiniteExact

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
