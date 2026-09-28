import Flapjack.Pancake.Semantics.LoopSem

/-!
# Properties of the Lean `loopSem` machine state

Counterpart module for `cakeml/pancake/semantics/loopPropsScript.sml`.

The HOL script states properties of `loopSem$get_vars` / `set_vars` and of
`get_var_imm` over the word-length-indexed `loopSem$state`.

PRECISE STATE-CARRIER GAP (why the declarations in this module are UNTAGGED):
HOL quantifies over the full `loopSem$state` (`loopSemScript.sml:13-27`) with an
`sptree$num_map` code/locals, a finite-map `5 word |-> word_loc` globals, a TOTAL
`'a word -> 'a word_loc` memory, `mdomain`/`sh_mdomain` sets and the HOL FFI
state. The Lean carrier `LoopMachineState` represents `code` as an association
list, `memory` as `Option`-valued, `globals`/`locals` as functions and the
domains as Boolean maps, so it is not the exact HOL state carrier; a whole-state
signature over it must not carry an exact `@[hol]` tag. The exact width-indexed
`loopSem$state` carrier and its observational bridge are tracked in bead
`flapjack-pxn.18.5.17.1`. These lemmas stay untagged support until then; the
generic proofs are already width/word-polymorphic.
-/

namespace Flapjack

/-! ## `survives`

The exact width-indexed port of HOL `survives_def` from
`cakeml/pancake/semantics/loopPropsScript.sml:25-38`. Its HOL `bool` result is
kept as `Bool`; each `n IN domain` check is the `isSome` bit of exact
`Spt Unit` lookup. -/

/-- Exact HOL `survives_def`: live-set domain checks apply to If/Loop/Call/FFI;
    Mark and Seq recurse, and every other program constructor survives. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "survives_def"
  (words_as_type_indexed_bitvec)]
def survivesHOLExact {width : Nat} [NeZero width] (name : Nat) :
    HolLoopProg width → Bool
  | .ite _ _ _ thenBranch elseBranch live =>
      survivesHOLExact name thenBranch && survivesHOLExact name elseBranch &&
        (sptLookup name live).isSome
  | .loop liveIn body liveOut =>
      (sptLookup name liveIn).isSome && (sptLookup name liveOut).isSome &&
        survivesHOLExact name body
  | .call (some (_, returns)) _ _ none => (sptLookup name returns).isSome
  | .call (some (_, returns)) _ _ (some (_, first, second, post)) =>
      (sptLookup name returns).isSome && (sptLookup name post).isSome &&
        survivesHOLExact name first && survivesHOLExact name second
  | .ffi _ _ _ _ _ live => (sptLookup name live).isSome
  | .mark body => survivesHOLExact name body
  | .seq first second => survivesHOLExact name first && survivesHOLExact name second
  | _ => true
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/-! ## `get_vars`

Faithful port of HOL `loopSem$get_vars` (`loopSemScript.sml:98-106`): read the
listed variables from the machine state's local map in order, failing as soon
as one is absent:

```
(get_vars [] s = SOME []) /\
(get_vars (v::vs) s =
   case lookup v s.locals of
   | NONE => NONE
   | SOME x => case get_vars vs s of
               | NONE => NONE
               | SOME xs => SOME (x::xs))
```

HOL's `s.locals` is an `sptree$num_map` rendered extensionally here as
`LoopMachineState.locals : Nat → Option (LoopValue W)`. -/
def getVars (names : List Nat) (state : LoopMachineState W F) :
    Option (List (LoopValue W)) :=
  match names with
  | [] => some []
  | name :: names =>
      match state.locals name with
      | none => none
      | some value =>
          match getVars names state with
          | none => none
          | some values => some (value :: values)

@[simp] theorem getVars_nil (state : LoopMachineState W F) :
    getVars [] state = some [] := rfl

/-- Untagged width-indexed companion of `get_vars_def` (`loopSemScript.sml:98`);
    see the module header for the state-carrier gap (bead .18.5.17.1). -/
def getVarsHOL {width : Nat} [NeZero width]
    (names : List Nat) (state : LoopMachineState (BitVec width) F) :
    Option (List (LoopValue (BitVec width))) :=
  getVars names state

theorem getVarsHOL_eq_getVars {width : Nat} [NeZero width]
    (names : List Nat) (state : LoopMachineState (BitVec width) F) :
    getVarsHOL names state = getVars names state := rfl

/-! ## Clock and locals transport properties

These are the `loopPropsScript.sml` lemmas that only observe how `get_vars` and
`get_var_imm` read the local map / clock. All declarations here are untagged
support (see the module header); the width-indexed ones are companions of the
HOL statements. -/

theorem getVars_local_clock_upd_eq (names : List Nat) (state : LoopMachineState W F)
    (locals : Nat → Option (LoopValue W)) (ck : Nat) :
    getVars names { state with locals := locals, clock := ck } =
      getVars names { state with locals := locals } := by
  induction names with
  | nil => rfl
  | cons name names ih =>
      simp only [getVars]
      cases h : locals name with
      | none => rfl
      | some value => rw [ih]

theorem getVars_clock_upd_eq (names : List Nat) (state : LoopMachineState W F)
    (ck : Nat) :
    getVars names { state with clock := ck } = getVars names state := by
  induction names with
  | nil => rfl
  | cons name names ih =>
      simp only [getVars]
      rw [ih]

/-- Untagged companion of HOL `get_var_imm_add_clk_eq`
    (`cakeml/pancake/semantics/loopPropsScript.sml:251-255`). -/
theorem getVarImmHOL_add_clock_eq {width : Nat} [NeZero width]
    (operand : RegImm (BitVec width)) (state : LoopMachineState (BitVec width) F)
    (ck : Nat) :
    getVarImmHOL operand { state with clock := ck } = getVarImmHOL operand state := by
  cases operand <;> rfl

/-- Untagged companion of HOL `get_vars_local_clock_upd_eq`
    (`cakeml/pancake/semantics/loopPropsScript.sml:260-266`). -/
theorem getVarsHOL_local_clock_upd_eq {width : Nat} [NeZero width]
    (names : List Nat) (state : LoopMachineState (BitVec width) F)
    (locals : Nat → Option (LoopValue (BitVec width))) (ck : Nat) :
    getVarsHOL names { state with locals := locals, clock := ck } =
      getVarsHOL names { state with locals := locals } :=
  getVars_local_clock_upd_eq names state locals ck

/-- Untagged companion of HOL `get_vars_clock_upd_eq`
    (`cakeml/pancake/semantics/loopPropsScript.sml:269-275`). -/
theorem getVarsHOL_clock_upd_eq {width : Nat} [NeZero width]
    (names : List Nat) (state : LoopMachineState (BitVec width) F) (ck : Nat) :
    getVarsHOL names { state with clock := ck } = getVarsHOL names state :=
  getVars_clock_upd_eq names state ck

end Flapjack
