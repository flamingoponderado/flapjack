import Flapjack.Pancake.Semantics.LoopSemState
import Flapjack.Pancake.Semantics.LoopProps
import Flapjack.Pancake.LoopLang
import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Misc.Sptree
import Flapjack.FfiBridge

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

/-- Exact `get_vars_def` (`loopSemScript.sml:98-107`), state second as in HOL. -/
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
