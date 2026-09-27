import Flapjack.Pancake.PanLang.Decl
import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Pancake.Semantics.PanSem.ValueHOL
import Flapjack.Pancake.Proofs.PanToCrep.StateRelFiniteSupport
import Flapjack.Pancake.Proofs.PanToCrep.CompileExpValRel

/-!
Direct carrier checks paired with `pan_to_crep_state_rel_carrier_probe.out`.
HOL `state_rel_def` (`pan_to_crepProofScript.sml:45-56`) consumes
`panSem$state.structs : (mlstring # struct_info) list` and requires it empty;
`state_rel_globals` (`:65-68`) requires its `mlstring |-> 'a v` globals map to
be `FEMPTY`. The exact source-side names and struct metadata below use
`MlString`, `ShapeHOL`, and `StructInfoHOLExact`; the value map uses
`HolFiniteMapExact MlString (ValueHOL width)`. These are source-carrier checks,
not an implementation of `state_rel` and not evidence that production
`String`/`Shape` states are exact HOL carriers. The HOL EVAL row for equality
against `FEMPTY` remains an unevaluated function equality; the adjacent
lookup rows pin the nonempty and empty observations without claiming HOL
decides extensional function inequality.
-/

namespace Flapjack.Test.PanToCrepStateRelCarrierParity

open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

private abbrev ExactStructContext := List (MlS × StructInfoHOLExact)

private def ml (name : String) : MlS := ofString name

private def exactPairStruct : StructInfoHOLExact :=
  { fields := [(ml "left", .one)], size := 1 }

private def exactNamedStructs : ExactStructContext :=
  [(ml "Pair", exactPairStruct)]

private def exactGlobalMap : HolFiniteMapExact MlS (ValueHOL 8) :=
  (HolFiniteMapExact.empty).update
    (ml "global", ValueHOL.val (.word (3 : BitVec 8)))

private def exactEmptyGlobalMap : HolFiniteMapExact MlS (ValueHOL 8) :=
  HolFiniteMapExact.empty

private def exactEmptyStructs : ExactStructContext := []

theorem exact_named_struct_carrier_row :
    exactNamedStructs =
      [(ml "Pair", { fields := [(ml "left", ShapeHOL.one)], size := 1 })] := rfl

theorem exact_nonempty_global_lookup_row :
    exactGlobalMap.lookup (ml "global") =
      some (ValueHOL.val (.word (3 : BitVec 8))) := by
  simp [exactGlobalMap, HolFiniteMapExact.update, FUPDATE]

theorem exact_empty_global_lookup_row :
    exactEmptyGlobalMap.lookup (ml "global") = none := rfl

private def matchingFieldsOracleCase : Bool :=
  exactEmptyStructs.isEmpty && (exactEmptyGlobalMap.lookup (ml "global")).isNone

private def nonemptyStructsOracleCase : Bool :=
  exactNamedStructs.length == 1

private def nonemptyGlobalLookupOracleCase : Bool :=
  match exactGlobalMap.lookup (ml "global") with
  | some (.val (.word value)) => value == (3 : BitVec 8)
  | _ => false

private def emptyGlobalLookupOracleCase : Bool :=
  (exactEmptyGlobalMap.lookup (ml "global")).isNone

/-- Kernel-checked row: the exact `state_rel_structs` projection applies to any
    related exact carrier pair, returning the empty source struct context. -/
example {width : Nat} [NeZero width] {σ : Type}
    (source : PanSemStateFiniteExact width σ) (target : CrepSemHOLState width σ)
    (hrel : panToCrepStateRelFiniteExact source target) :
    source.structs = [] :=
  panToCrepStateRelFiniteExact_structs source target hrel

/-- Kernel-checked row: the exact `state_rel_globals` projection applies to any
    related exact carrier pair, returning the pointwise-empty globals map. -/
example {width : Nat} [NeZero width] {σ : Type}
    (source : PanSemStateFiniteExact width σ) (target : CrepSemHOLState width σ)
    (hrel : panToCrepStateRelFiniteExact source target) :
    source.globals.lookup = (fun _ => none) :=
  panToCrepStateRelFiniteExact_globals source target hrel

private def tlcSlots : List Nat := [0, 1]

private def tlcArguments : List (ValueHOL 8) :=
  [.val (.word (5 : BitVec 8)), .val (.word (7 : BitVec 8))]

/- Concrete exact `tlcHOL` rows for `slots = [0,1]` and two `Val` arguments:
    `flatten` maps each argument to its single word, so the finite map stores
    `0 |-> 5` and `1 |-> 7` and is undefined elsewhere (mirroring HOL
    `FEMPTY |++ ZIP (ns, FLAT (MAP flatten args))`).  Paired with the direct
    original-HOL oracle `scripts/hol-probes/pan_to_crep_slc_tlc_probe.out`
    (rows `slc_tlc_tlc_0=SOME (Word 5w)`, `slc_tlc_tlc_1=SOME (Word 7w)`,
    `slc_tlc_tlc_absent=NONE`). -/
theorem tlcHOL_zero : (tlcHOL tlcSlots tlcArguments).lookup 0 =
    some (.word (5 : BitVec 8)) := by
  simp only [tlcHOL, tlcSlots, tlcArguments, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, flattenHOL,
    HolFiniteMapExact.updateListEq, HolFiniteMapExact.empty, FUPDATE_LIST_HOL]
  decide

theorem tlcHOL_one : (tlcHOL tlcSlots tlcArguments).lookup 1 =
    some (.word (7 : BitVec 8)) := by
  simp only [tlcHOL, tlcSlots, tlcArguments, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, flattenHOL,
    HolFiniteMapExact.updateListEq, HolFiniteMapExact.empty, FUPDATE_LIST_HOL]
  decide

theorem tlcHOL_absent : (tlcHOL tlcSlots tlcArguments).lookup 2 = none := by
  simp only [tlcHOL, tlcSlots, tlcArguments, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, flattenHOL,
    HolFiniteMapExact.updateListEq, HolFiniteMapExact.empty, FUPDATE_LIST_HOL]
  decide

def tlcHOLGuard : Bool :=
  ((tlcHOL tlcSlots tlcArguments).lookup 0 == some (.word (5 : BitVec 8))) &&
  ((tlcHOL tlcSlots tlcArguments).lookup 1 == some (.word (7 : BitVec 8))) &&
  ((tlcHOL tlcSlots tlcArguments).lookup 2 == none)

private def slcVariables : List (MlS × ShapeHOL) :=
  [(ml "x", .one), (ml "y", .one)]

private def slcArguments : List (ValueHOL 8) :=
  [.val (.word (5 : BitVec 8)), .val (.word (7 : BitVec 8))]

/- Concrete exact `slcHOL` rows for `vshs = [(x,One),(y,One)]` and two `Val`
    arguments: `ZIP (MAP FST vshs, args)` pairs the `varname`s with the argument
    values, so the finite map stores `x |-> 5` and `y |-> 7` and is undefined
    elsewhere (mirroring HOL `FEMPTY |++ ZIP (MAP FST vshs, args)`).  Paired with
    the direct original-HOL oracle `scripts/hol-probes/pan_to_crep_slc_tlc_probe.out`
    (rows `slc_tlc_slc_x=SOME (ValWord 5w)`, `slc_tlc_slc_y=SOME (ValWord 7w)`,
    `slc_tlc_slc_absent=NONE`). -/
theorem slcHOL_x : (slcHOL slcVariables slcArguments).lookup (ml "x") =
    some (.val (.word (5 : BitVec 8))) := by
  simp only [slcHOL, slcVariables, slcArguments, HolFiniteMapExact.updateListEq,
    HolFiniteMapExact.empty, FUPDATE_LIST_HOL]
  rfl

theorem slcHOL_y : (slcHOL slcVariables slcArguments).lookup (ml "y") =
    some (.val (.word (7 : BitVec 8))) := by
  simp only [slcHOL, slcVariables, slcArguments, HolFiniteMapExact.updateListEq,
    HolFiniteMapExact.empty, FUPDATE_LIST_HOL]
  rfl

theorem slcHOL_absent : (slcHOL slcVariables slcArguments).lookup (ml "z") = none := by
  simp only [slcHOL, slcVariables, slcArguments, HolFiniteMapExact.updateListEq,
    HolFiniteMapExact.empty, FUPDATE_LIST_HOL]
  rfl

def slcHOLGuard : Bool :=
  (match (slcHOL slcVariables slcArguments).lookup (ml "x") with
   | some (.val (.word value)) => value == (5 : BitVec 8)
   | _ => false) &&
  (match (slcHOL slcVariables slcArguments).lookup (ml "y") with
   | some (.val (.word value)) => value == (7 : BitVec 8)
   | _ => false) &&
  (match (slcHOL slcVariables slcArguments).lookup (ml "z") with
   | none => true
   | _ => false)

/- Exact `slc_tlc_rw` rewrite rows: applying each conjunct of `slcTlcRwHOL`
    turns the raw HOL `FEMPTY |++ ...` update into the named `slcHOL`/`tlcHOL`
    map, so the raw lookup agrees with the stored entries.  Paired with the
    original-HOL oracle rows `slc_tlc_rw_slc_holds=T`, `slc_tlc_rw_tlc_holds=T`,
    `slc_tlc_slc_rhs_lookup=SOME (ValWord 5w)`, `slc_tlc_tlc_rhs_lookup=SOME (Word 7w)`
    in `scripts/hol-probes/pan_to_crep_slc_tlc_probe.out`. -/
theorem slcTlcRwHOL_raw_slc :
    (HolFiniteMapExact.updateListEq HolFiniteMapExact.empty
        ((slcVariables.map Prod.fst).zip slcArguments)).lookup (ml "x") =
      some (.val (.word (5 : BitVec 8))) := by
  rw [(slcTlcRwHOL slcVariables tlcSlots slcArguments).1]
  exact slcHOL_x

theorem slcTlcRwHOL_raw_tlc :
    (HolFiniteMapExact.updateListEq HolFiniteMapExact.empty
        (tlcSlots.zip ((tlcArguments.map flattenHOL).flatten))).lookup 1 =
      some (.word (7 : BitVec 8)) := by
  rw [(slcTlcRwHOL slcVariables tlcSlots tlcArguments).2]
  exact tlcHOL_one

def slcTlcRwHOLGuard : Bool :=
  (match (HolFiniteMapExact.updateListEq HolFiniteMapExact.empty
      ((slcVariables.map Prod.fst).zip slcArguments)).lookup (ml "x") with
   | some (.val (.word value)) => value == (5 : BitVec 8)
   | _ => false) &&
  (match (HolFiniteMapExact.updateListEq HolFiniteMapExact.empty
      (tlcSlots.zip ((tlcArguments.map flattenHOL).flatten))).lookup 1 with
   | some (.word value) => value == (7 : BitVec 8)
   | _ => false)

/-! Exact-carrier regression for the `Const` case of HOL `compile_exp_val_rel`
(`pan_to_crepProofScript.sml:143-150`), exercised over the exact carriers with
the finite-support source evaluator and the exact target evaluator. The state
relation, code relation, locals relation, and localisation premises of the
enclosing HOL theorem are irrelevant to `Const` and are not needed here. -/
example {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [ht : DecidablePred targetState.memaddrs]
    (word : BitVec width) :
    ([CrepExpHOL.const word].map (evalCrepSemHOLExp targetState)) =
      (flattenHOL (ValueHOL.val (HolWordLab.word word))).map some :=
  (compileExpValRelHOL_const state context targetState word
    (ValueHOL.val (HolWordLab.word word)) [CrepExpHOL.const word] ShapeHOL.one
    rfl (by simp only [compileExpExactHOLW])).1

example {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [ht : DecidablePred targetState.memaddrs]
    (word : BitVec width) :
    shapeOfHOLExact (ValueHOL.val (HolWordLab.word word)) = ShapeHOL.one :=
  (compileExpValRelHOL_const state context targetState word
    (ValueHOL.val (HolWordLab.word word)) [CrepExpHOL.const word] ShapeHOL.one
    rfl (by simp only [compileExpExactHOLW])).2.2.1
/- Exact `locals_rel_lookup_ctxt` (`pan_to_crepProofScript.sml:527-534`)
    regression over the exact carriers. The fixture is the exact-carrier
    counterpart of the production `localsRelLookupCtxt_fixture`
    (`Flapjack/Test/PanToCrepStateRelParity.lean`): one local `x = ValWord 5`
    at slot `0`, with `shape_of = One` and `flatten = [5]`. No HOL-EVAL oracle
    exists for `locals_rel_lookup_ctxt` itself (the nearest oracle evidence is
    the production fixture plus the `pan_upd_locals`/`pan_empty_locals` probe
    rows), so this row records the exact-carrier derivation and exposes the
    same slot, flattened value, and shape the production row checks. -/

private def lookupCtxtName : MlS := ml "x"

private def lookupCtxtValue : ValueHOL 8 := .val (.word (5 : BitVec 8))

private def lookupCtxtVars : HolFiniteMapExact MlS (ShapeHOL × List Nat) :=
  HolFiniteMapExact.empty.update (lookupCtxtName, (ShapeHOL.one, [0]))

private def lookupCtxtContext : PanToCrepContextExact 8 :=
  { vars := lookupCtxtVars
    funcs := HolFiniteMapExact.empty
    eids := HolFiniteMapExact.empty
    vmax := 0 }

private def lookupCtxtSourceLocals : HolFiniteMapExact MlS (ValueHOL 8) :=
  HolFiniteMapExact.empty.update (lookupCtxtName, lookupCtxtValue)

private def lookupCtxtTargetLocals : HolFiniteMapExact Nat (HolWordLab 8) :=
  HolFiniteMapExact.empty.update (0, HolWordLab.word (5 : BitVec 8))

private theorem lookupCtxtVars_lookup (key : MlS) :
    lookupCtxtVars.lookup key =
      (if lookupCtxtName == key then some (ShapeHOL.one, [0]) else none) := by
  unfold lookupCtxtVars HolFiniteMapExact.update HolFiniteMapExact.empty FUPDATE
  rfl

private theorem lookupCtxtSource_lookup (key : MlS) :
    lookupCtxtSourceLocals.lookup key =
      (if lookupCtxtName == key then some lookupCtxtValue else none) := by
  unfold lookupCtxtSourceLocals HolFiniteMapExact.update HolFiniteMapExact.empty FUPDATE
  rfl

private theorem lookupCtxtSource_lookup_self :
    lookupCtxtSourceLocals.lookup lookupCtxtName = some lookupCtxtValue := by
  rw [lookupCtxtSource_lookup]
  simp

private theorem lookupCtxtTarget_lookup (key : Nat) :
    lookupCtxtTargetLocals.lookup key =
      (if (0 : Nat) == key then some (HolWordLab.word (5 : BitVec 8)) else none) := by
  unfold lookupCtxtTargetLocals HolFiniteMapExact.update HolFiniteMapExact.empty FUPDATE
  rfl

private theorem lookupCtxtLocalsRel :
    panToCrepLocalsRelFiniteExact lookupCtxtContext lookupCtxtSourceLocals
      lookupCtxtTargetLocals := by
  refine ⟨?_, ?_, ?_⟩
  · unfold noOverlapFiniteExact
    constructor
    · intro key shape slots hlookup
      change lookupCtxtVars.lookup key = some (shape, slots) at hlookup
      rw [lookupCtxtVars_lookup] at hlookup
      split at hlookup
      · rcases Option.some.inj hlookup with hpair
        rcases Prod.mk.inj hpair with ⟨_, hslots⟩
        subst hslots
        simp
      · simp at hlookup
    · intro key key' shape shape' slots slots' hkey hkey' _hshared
      change lookupCtxtVars.lookup key = some (shape, slots) at hkey
      change lookupCtxtVars.lookup key' = some (shape', slots') at hkey'
      rw [lookupCtxtVars_lookup] at hkey
      rw [lookupCtxtVars_lookup] at hkey'
      split at hkey
      · rename_i hkeycond
        split at hkey'
        · rename_i hkey'cond
          exact (beq_iff_eq.mp hkeycond).symm.trans (beq_iff_eq.mp hkey'cond)
        · simp at hkey'
      · simp at hkey
  · unfold ctxtMaxFiniteExact
    refine ⟨Nat.zero_le 0, ?_⟩
    intro key shape slots hlookup slot hslot
    change lookupCtxtVars.lookup key = some (shape, slots) at hlookup
    rw [lookupCtxtVars_lookup] at hlookup
    split at hlookup
    · rcases Option.some.inj hlookup with hpair
      rcases Prod.mk.inj hpair with ⟨_, hslots⟩
      subst hslots
      simp only [List.mem_singleton] at hslot
      subst hslot
      omega
    · simp at hlookup
  · intro name value hlookup
    rw [lookupCtxtSource_lookup] at hlookup
    split at hlookup
    · rename_i hcond
      have hname : name = lookupCtxtName := (beq_iff_eq.mp hcond).symm
      have hvalue : value = lookupCtxtValue := (Option.some.inj hlookup).symm
      subst hvalue
      subst hname
      refine ⟨[0], [.word (5 : BitVec 8)], ?_, ?_, ?_, ?_⟩
      · change lookupCtxtVars.lookup lookupCtxtName =
          some (shapeOfHOLExact lookupCtxtValue, [0])
        rw [lookupCtxtVars_lookup]
        simp [shapeOfHOLExact, lookupCtxtValue]
      · simp [lookupCtxtTarget_lookup]
      · simp [flattenHOL, lookupCtxtValue]
      · simp [shapeOfHOLExact, lookupCtxtValue]
    · simp at hlookup

/-- Kernel-checked row: the exact `locals_rel_lookup_ctxt` port applies to any
    related exact carrier triple; the existential exposes the four HOL
    conjuncts. -/
example {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (sourceLocals : HolFiniteMapExact MlS (ValueHOL width))
    (targetLocals : HolFiniteMapExact Nat (HolWordLab width))
    (name : MlS) (value : ValueHOL width)
    (hrel : panToCrepLocalsRelFiniteExact context sourceLocals targetLocals)
    (hlookup : sourceLocals.lookup name = some value) :
    ∃ slots, context.vars.lookup name = some (shapeOfHOLExact value, slots) ∧
      slots.length = (flattenHOL value).length ∧
      slots.mapM targetLocals.lookup = some (flattenHOL value) ∧
      isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true :=
  panToCrepLocalsRelLookupCtxtFiniteExact context sourceLocals targetLocals
    name value hrel hlookup

/-- Concrete exact-carrier derivations recovering the slot `[0]`, shape `One`,
    flattened word `5`, and well-formedness for the one-word local. -/
private theorem lookupCtxtExactFixture :
    lookupCtxtContext.vars.lookup lookupCtxtName = some (ShapeHOL.one, [0]) ∧
    (flattenHOL lookupCtxtValue) = [.word (5 : BitVec 8)] ∧
    ([0] : List Nat).mapM lookupCtxtTargetLocals.lookup =
      some (flattenHOL lookupCtxtValue) ∧
    isWfShapeExactHOL ([] : StructContextExact)
      (shapeOfHOLExact lookupCtxtValue) = true := by
  have hextract := panToCrepLocalsRelLookupCtxtFiniteExact lookupCtxtContext
    lookupCtxtSourceLocals lookupCtxtTargetLocals lookupCtxtName lookupCtxtValue
    lookupCtxtLocalsRel lookupCtxtSource_lookup_self
  obtain ⟨slots, hcontext, _hlen, hmap, hwf⟩ := hextract
  have hslots : slots = [0] := by
    have h := congrArg (fun option => option.map Prod.snd) hcontext
    simp only [lookupCtxtContext] at h
    rw [lookupCtxtVars_lookup] at h
    simpa using h.symm
  refine ⟨?_, ?_, ?_, hwf⟩
  · rw [hslots] at hcontext
    simpa [shapeOfHOLExact, lookupCtxtValue] using hcontext
  · simp [flattenHOL, lookupCtxtValue]
  · rw [hslots] at hmap
    exact hmap

/-- Kernel-checked row: the exact `ctxt_max_el_leq` port applies to any exact
    context satisfying `ctxtMaxFiniteExact`; the selected in-range slot is
    bounded by `vmax`. -/
example {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (name : MlS) (shape : ShapeHOL)
    (slots : List Nat) (n : Nat)
    (hmax : ctxtMaxFiniteExact context.vmax context.vars)
    (hlookup : context.vars.lookup name = some (shape, slots))
    (hindex : n < slots.length) :
    slots[n] ≤ context.vmax :=
  ctxtMaxElLeqFiniteExact context name shape slots n hmax hlookup hindex

/-- Concrete exact-carrier instance: the one-slot `lookupCtxtContext` fixture
    (`vars` maps `x` to `(One, [0])`, `vmax = 0`) bounds its selected slot. -/
private theorem ctxtMaxElLeqFixture :
    ([0] : List Nat)[0]'(by simp) ≤ lookupCtxtContext.vmax := by
  have hmax : ctxtMaxFiniteExact lookupCtxtContext.vmax lookupCtxtContext.vars :=
    lookupCtxtLocalsRel.2.1
  have hlookup : lookupCtxtContext.vars.lookup lookupCtxtName =
      some (ShapeHOL.one, [0]) := by
    change lookupCtxtVars.lookup lookupCtxtName = some (ShapeHOL.one, [0])
    rw [lookupCtxtVars_lookup]
    simp
  exact ctxtMaxElLeqFiniteExact lookupCtxtContext lookupCtxtName ShapeHOL.one
    [0] 0 hmax hlookup (by simp)

private def lookupCtxtGuard : Bool :=
  (match lookupCtxtContext.vars.lookup lookupCtxtName with
   | some (.one, [0]) => true
   | _ => false) &&
    (match flattenHOL lookupCtxtValue with
     | [.word value] => value == (5 : BitVec 8)
     | _ => false)

private def ctxtMaxElLeqGuard : Bool :=
  match lookupCtxtContext.vars.lookup lookupCtxtName with
  | some (.one, [slot]) => decide (slot ≤ lookupCtxtContext.vmax)
  | _ => false

/-! Exact `compile_exp_val_rel` `Var Local` case
    (`pan_to_crepProofScript.sml:151-165`). The kernel-checked application below
    confirms the exact-carrier statement and the shape conclusion; it takes the
    HOL case's hypotheses (successful source evaluation, `locals_rel`, and the
    exact `compile_exp` result) directly. -/

example {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [ht : DecidablePred targetState.memaddrs]
    (name : MlS) (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (heval : state.evalHOLFinite (.var .local name) = some value)
    (hlocals : panToCrepLocalsRelFiniteExact context state.locals targetState.locals)
    (hcompile : compileExpExactHOLW context (.var .local name) = (expressions, shape)) :
    shapeOfHOLExact value = shape :=
  (compileExpValRelHOL_var_local state context targetState name value expressions shape
    heval hlocals hcompile).2.2.1

/-- The global-variable localisation premise of the `Var Global` case is
    unreachable: `localised_exp` rejects global variables. -/
example {width : Nat} [NeZero width] (name : MlS) :
    localisedExpHOL (width := width) (.var .global name) = false := by
  simp only [localisedExpHOL, everyExpHOL]

example {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [ht : DecidablePred targetState.memaddrs]
    (name : MlS) (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (heval : state.evalHOLFinite (.var .global name) = some value)
    (hlocalised : localisedExpHOL (width := width) (.var .global name) = true)
    (hcompile : compileExpExactHOLW context (.var .global name) = (expressions, shape)) :
    shapeOfHOLExact value = shape :=
  (compileExpValRelHOL_var_global state context targetState name value expressions shape
    heval hlocalised hcompile).2.2.1

/-- Kernel regression for the list-level companion `compileExpListValRelHOL`:
    under the HOL premises it yields the `RStruct` shape conclusion. -/
example {width : Nat} [NeZero width]
    (state : PanSemStateFiniteExact width Unit) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width Unit) [ht : DecidablePred targetState.memaddrs]
    (fields : List (ExpHOL width)) (values : List (ValueHOL width))
    (compiled : List (List (CrepExpHOL width) × ShapeHOL))
    (hrel : ∀ (expression : ExpHOL width), expression ∈ fields →
        (value : ValueHOL width) → (expressions : List (CrepExpHOL width)) →
        (shape : ShapeHOL) →
        state.evalHOLFinite expression = some value →
        localisedExpHOL expression = true →
        compileExpExactHOLW context expression = (expressions, shape) →
        expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
        expressions.length = sizeOfShapeHOL shape ∧
        shapeOfHOLExact value = shape ∧
        isWfShapeExactHOL ([] : StructContextExact) shape = true)
    (heval : state.evalListHOLFinite fields = some values)
    (hlocalised : everyExpListHOL (width := width) localisedExpPredHOL fields = true)
    (hcompile : compileExpExactHOLWList context fields = compiled) :
    shapeOfHOLExact (.rStruct values) = .comb (compiled.map Prod.snd) :=
  (compileExpListValRelHOL state context targetState fields hrel values compiled
    heval hlocalised hcompile).2.2.1

/-- Kernel regression for the exact `RStruct` case `compileExpValRelHOL_rstruct`
    (HOL `pan_to_crepProofScript.sml:171-198`). -/
example {width : Nat} [NeZero width]
    (state : PanSemStateFiniteExact width Unit) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width Unit) [ht : DecidablePred targetState.memaddrs]
    (fields : List (ExpHOL width)) (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (hrel : ∀ (expression : ExpHOL width), expression ∈ fields →
        (value : ValueHOL width) → (expressions : List (CrepExpHOL width)) →
        (shape : ShapeHOL) →
        state.evalHOLFinite expression = some value →
        localisedExpHOL expression = true →
        compileExpExactHOLW context expression = (expressions, shape) →
        expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
        expressions.length = sizeOfShapeHOL shape ∧
        shapeOfHOLExact value = shape ∧
        isWfShapeExactHOL ([] : StructContextExact) shape = true)
    (heval : state.evalHOLFinite (.rstruct fields) = some value)
    (hlocalised : localisedExpHOL (.rstruct fields) = true)
    (hcompile : compileExpExactHOLW context (.rstruct fields) = (expressions, shape)) :
    shapeOfHOLExact value = shape :=
  (compileExpValRelHOL_rstruct state context targetState fields value expressions shape
    hrel heval hlocalised hcompile).2.2.1


/-- Kernel regression for the exact `BaseAddr` case `compileExpValRelHOL_baseAddr`
    (HOL `pan_to_crepProofScript.sml:130-396`). -/
example {width : Nat} [NeZero width]
    (state : PanSemStateFiniteExact width Unit) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width Unit) [_ht : DecidablePred targetState.memaddrs]
    (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (heval : state.evalHOLFinite .baseAddr = some value)
    (hstate : panToCrepStateRelFiniteExact state targetState)
    (hcompile : compileExpExactHOLW context .baseAddr = (expressions, shape)) :
    shapeOfHOLExact value = shape :=
  (compileExpValRelHOL_baseAddr state context targetState value expressions shape
    heval hstate hcompile).2.2.1

/-- Kernel regression for the exact `TopAddr` case `compileExpValRelHOL_topAddr`
    (HOL `pan_to_crepProofScript.sml:130-396`). -/
example {width : Nat} [NeZero width]
    (state : PanSemStateFiniteExact width Unit) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width Unit) [_ht : DecidablePred targetState.memaddrs]
    (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (heval : state.evalHOLFinite .topAddr = some value)
    (hstate : panToCrepStateRelFiniteExact state targetState)
    (hcompile : compileExpExactHOLW context .topAddr = (expressions, shape)) :
    shapeOfHOLExact value = shape :=
  (compileExpValRelHOL_topAddr state context targetState value expressions shape
    heval hstate hcompile).2.2.1

/-- Kernel regression for the exact `BytesInWord` case
    `compileExpValRelHOL_bytesInWord` (HOL `pan_to_crepProofScript.sml:130-396`). -/
example {width : Nat} [NeZero width]
    (state : PanSemStateFiniteExact width Unit) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width Unit) [_ht : DecidablePred targetState.memaddrs]
    (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (heval : state.evalHOLFinite .bytesInWord = some value)
    (hcompile : compileExpExactHOLW context .bytesInWord = (expressions, shape)) :
    shapeOfHOLExact value = shape :=
  (compileExpValRelHOL_bytesInWord state context targetState value expressions shape
    heval hcompile).2.2.1

/-- Kernel regression for the vacuous `NStruct` case
    `compileExpValRelHOL_nstruct` (HOL `pan_to_crepProofScript.sml:130-396`). -/
example {width : Nat} [NeZero width]
    (state : PanSemStateFiniteExact width Unit) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width Unit) [_ht : DecidablePred targetState.memaddrs]
    (name : MlS) (fields : List (MlS × ExpHOL width))
    (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (heval : state.evalHOLFinite (.nstruct name fields) = some value)
    (hstate : panToCrepStateRelFiniteExact state targetState)
    (hcompile : compileExpExactHOLW context (.nstruct name fields) = (expressions, shape)) :
    shapeOfHOLExact value = shape :=
  (compileExpValRelHOL_nstruct state context targetState name fields value expressions shape
    heval hstate hcompile).2.2.1

/-- Kernel regression for the vacuous `NField` case
    `compileExpValRelHOL_nfield` (HOL `pan_to_crepProofScript.sml:130-396`). -/
example {width : Nat} [NeZero width]
    (state : PanSemStateFiniteExact width Unit) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width Unit) [_ht : DecidablePred targetState.memaddrs]
    (name : MlS) (value' : ExpHOL width)
    (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (heval : state.evalHOLFinite (.nfield name value') = some value)
    (hstate : panToCrepStateRelFiniteExact state targetState)
    (hcompile : compileExpExactHOLW context (.nfield name value') = (expressions, shape)) :
    shapeOfHOLExact value = shape :=
  (compileExpValRelHOL_nfield state context targetState name value' value expressions shape
    heval hstate hcompile).2.2.1

/-- Kernel regression for the `RField` case `compileExpValRelHOL_rfield`
    (HOL `pan_to_crepProofScript.sml:187-214`). -/
example {width : Nat} [NeZero width]
    (state : PanSemStateFiniteExact width Unit) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width Unit) [_ht : DecidablePred targetState.memaddrs]
    (index : Nat) (subExpression : ExpHOL width)
    (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (hsub : ∀ (subValue : ValueHOL width)
        (subExpressions : List (CrepExpHOL width)) (subShape : ShapeHOL),
        state.evalHOLFinite subExpression = some subValue →
        panToCrepStateRelFiniteExact state targetState →
        codeRelExactHOLW context state.code targetState.code →
        panToCrepLocalsRelFiniteExact context state.locals targetState.locals →
        localisedExpHOL subExpression = true →
        compileExpExactHOLW context subExpression = (subExpressions, subShape) →
        subExpressions.map (evalCrepSemHOLExp targetState) = (flattenHOL subValue).map some ∧
        subExpressions.length = sizeOfShapeHOL subShape ∧
        shapeOfHOLExact subValue = subShape ∧
        isWfShapeExactHOL ([] : StructContextExact) subShape = true)
    (heval : state.evalHOLFinite (.rfield index subExpression) = some value)
    (hlocalised : localisedExpHOL (.rfield index subExpression) = true)
    (hstate : panToCrepStateRelFiniteExact state targetState)
    (hcode : codeRelExactHOLW context state.code targetState.code)
    (hlocals : panToCrepLocalsRelFiniteExact context state.locals targetState.locals)
    (hcompile : compileExpExactHOLW context (.rfield index subExpression) = (expressions, shape)) :
    shapeOfHOLExact value = shape :=
  (compileExpValRelHOL_rfield state context targetState index subExpression value expressions shape
    hsub heval hlocalised hstate hcode hlocals hcompile).2.2.1

/-- Kernel regression for the `Load32` case `compileExpValRelHOL_load32`. -/
example {width : Nat} [NeZero width]
    (state : PanSemStateFiniteExact width Unit) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width Unit) [_ht : DecidablePred targetState.memaddrs]
    (subExpression : ExpHOL width)
    (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (hsub : ∀ (subValue : ValueHOL width)
        (subExpressions : List (CrepExpHOL width)) (subShape : ShapeHOL),
        state.evalHOLFinite subExpression = some subValue →
        panToCrepStateRelFiniteExact state targetState →
        codeRelExactHOLW context state.code targetState.code →
        panToCrepLocalsRelFiniteExact context state.locals targetState.locals →
        localisedExpHOL subExpression = true →
        compileExpExactHOLW context subExpression = (subExpressions, subShape) →
        subExpressions.map (evalCrepSemHOLExp targetState) = (flattenHOL subValue).map some ∧
        subExpressions.length = sizeOfShapeHOL subShape ∧
        shapeOfHOLExact subValue = subShape ∧
        isWfShapeExactHOL ([] : StructContextExact) subShape = true)
    (heval : state.evalHOLFinite (.load32 subExpression) = some value)
    (hlocalised : localisedExpHOL (.load32 subExpression) = true)
    (hstate : panToCrepStateRelFiniteExact state targetState)
    (hcode : codeRelExactHOLW context state.code targetState.code)
    (hlocals : panToCrepLocalsRelFiniteExact context state.locals targetState.locals)
    (hcompile : compileExpExactHOLW context (.load32 subExpression) = (expressions, shape)) :
    shapeOfHOLExact value = shape :=
  (compileExpValRelHOL_load32 state context targetState subExpression value expressions shape
    hsub heval hlocalised hstate hcode hlocals hcompile).2.2.1

/-- Kernel regression for the `LoadByte` case `compileExpValRelHOL_loadByte`. -/
example {width : Nat} [NeZero width]
    (state : PanSemStateFiniteExact width Unit) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width Unit) [_ht : DecidablePred targetState.memaddrs]
    (subExpression : ExpHOL width)
    (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (hsub : ∀ (subValue : ValueHOL width)
        (subExpressions : List (CrepExpHOL width)) (subShape : ShapeHOL),
        state.evalHOLFinite subExpression = some subValue →
        panToCrepStateRelFiniteExact state targetState →
        codeRelExactHOLW context state.code targetState.code →
        panToCrepLocalsRelFiniteExact context state.locals targetState.locals →
        localisedExpHOL subExpression = true →
        compileExpExactHOLW context subExpression = (subExpressions, subShape) →
        subExpressions.map (evalCrepSemHOLExp targetState) = (flattenHOL subValue).map some ∧
        subExpressions.length = sizeOfShapeHOL subShape ∧
        shapeOfHOLExact subValue = subShape ∧
        isWfShapeExactHOL ([] : StructContextExact) subShape = true)
    (heval : state.evalHOLFinite (.loadByte subExpression) = some value)
    (hlocalised : localisedExpHOL (.loadByte subExpression) = true)
    (hstate : panToCrepStateRelFiniteExact state targetState)
    (hcode : codeRelExactHOLW context state.code targetState.code)
    (hlocals : panToCrepLocalsRelFiniteExact context state.locals targetState.locals)
    (hcompile : compileExpExactHOLW context (.loadByte subExpression) = (expressions, shape)) :
    shapeOfHOLExact value = shape :=
  (compileExpValRelHOL_loadByte state context targetState subExpression value expressions shape
    hsub heval hlocalised hstate hcode hlocals hcompile).2.2.1

/-- Kernel regression for the `Cmp` case `compileExpValRelHOL_cmp`. -/
example {width : Nat} [NeZero width]
    (state : PanSemStateFiniteExact width Unit) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width Unit) [_ht : DecidablePred targetState.memaddrs]
    (operator : Cmp) (left right : ExpHOL width)
    (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (hleft : ∀ (subValue : ValueHOL width)
        (subExpressions : List (CrepExpHOL width)) (subShape : ShapeHOL),
        state.evalHOLFinite left = some subValue →
        panToCrepStateRelFiniteExact state targetState →
        codeRelExactHOLW context state.code targetState.code →
        panToCrepLocalsRelFiniteExact context state.locals targetState.locals →
        localisedExpHOL left = true →
        compileExpExactHOLW context left = (subExpressions, subShape) →
        subExpressions.map (evalCrepSemHOLExp targetState) = (flattenHOL subValue).map some ∧
        subExpressions.length = sizeOfShapeHOL subShape ∧
        shapeOfHOLExact subValue = subShape ∧
        isWfShapeExactHOL ([] : StructContextExact) subShape = true)
    (hright : ∀ (subValue : ValueHOL width)
        (subExpressions : List (CrepExpHOL width)) (subShape : ShapeHOL),
        state.evalHOLFinite right = some subValue →
        panToCrepStateRelFiniteExact state targetState →
        codeRelExactHOLW context state.code targetState.code →
        panToCrepLocalsRelFiniteExact context state.locals targetState.locals →
        localisedExpHOL right = true →
        compileExpExactHOLW context right = (subExpressions, subShape) →
        subExpressions.map (evalCrepSemHOLExp targetState) = (flattenHOL subValue).map some ∧
        subExpressions.length = sizeOfShapeHOL subShape ∧
        shapeOfHOLExact subValue = subShape ∧
        isWfShapeExactHOL ([] : StructContextExact) subShape = true)
    (heval : state.evalHOLFinite (.cmp operator left right) = some value)
    (hlocalised : localisedExpHOL (.cmp operator left right) = true)
    (hstate : panToCrepStateRelFiniteExact state targetState)
    (hcode : codeRelExactHOLW context state.code targetState.code)
    (hlocals : panToCrepLocalsRelFiniteExact context state.locals targetState.locals)
    (hcompile : compileExpExactHOLW context (.cmp operator left right) = (expressions, shape)) :
    shapeOfHOLExact value = shape :=
  (compileExpValRelHOL_cmp state context targetState operator left right value expressions shape
    hleft hright heval hlocalised hstate hcode hlocals hcompile).2.2.1

/-- Kernel regression for the `Shift` case `compileExpValRelHOL_shift`. -/
example {width : Nat} [NeZero width]
    (state : PanSemStateFiniteExact width Unit) [_hs : DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width Unit) [_ht : DecidablePred targetState.memaddrs]
    (operator : Shift) (left right : ExpHOL width)
    (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL)
    (hleft : ∀ (subValue : ValueHOL width)
        (subExpressions : List (CrepExpHOL width)) (subShape : ShapeHOL),
        state.evalHOLFinite left = some subValue →
        panToCrepStateRelFiniteExact state targetState →
        codeRelExactHOLW context state.code targetState.code →
        panToCrepLocalsRelFiniteExact context state.locals targetState.locals →
        localisedExpHOL left = true →
        compileExpExactHOLW context left = (subExpressions, subShape) →
        subExpressions.map (evalCrepSemHOLExp targetState) = (flattenHOL subValue).map some ∧
        subExpressions.length = sizeOfShapeHOL subShape ∧
        shapeOfHOLExact subValue = subShape ∧
        isWfShapeExactHOL ([] : StructContextExact) subShape = true)
    (hright : ∀ (subValue : ValueHOL width)
        (subExpressions : List (CrepExpHOL width)) (subShape : ShapeHOL),
        state.evalHOLFinite right = some subValue →
        panToCrepStateRelFiniteExact state targetState →
        codeRelExactHOLW context state.code targetState.code →
        panToCrepLocalsRelFiniteExact context state.locals targetState.locals →
        localisedExpHOL right = true →
        compileExpExactHOLW context right = (subExpressions, subShape) →
        subExpressions.map (evalCrepSemHOLExp targetState) = (flattenHOL subValue).map some ∧
        subExpressions.length = sizeOfShapeHOL subShape ∧
        shapeOfHOLExact subValue = subShape ∧
        isWfShapeExactHOL ([] : StructContextExact) subShape = true)
    (heval : state.evalHOLFinite (.shift operator left right) = some value)
    (hlocalised : localisedExpHOL (.shift operator left right) = true)
    (hstate : panToCrepStateRelFiniteExact state targetState)
    (hcode : codeRelExactHOLW context state.code targetState.code)
    (hlocals : panToCrepLocalsRelFiniteExact context state.locals targetState.locals)
    (hcompile : compileExpExactHOLW context (.shift operator left right) = (expressions, shape)) :
    shapeOfHOLExact value = shape :=
  (compileExpValRelHOL_shift state context targetState operator left right value expressions shape
    hleft hright heval hlocalised hstate hcode hlocals hcompile).2.2.1

def runChecks : IO Bool := do
  let checks := [
    ("HOL state_rel matching empty carrier fields", matchingFieldsOracleCase),
    ("HOL state_rel nonempty struct violates empty-field clause",
      nonemptyStructsOracleCase),
    ("HOL state_rel exact MlString named struct carrier", true),
    ("HOL state_rel nonempty globals lookup is present",
      nonemptyGlobalLookupOracleCase),
    ("HOL state_rel empty globals lookup is absent",
      emptyGlobalLookupOracleCase),
    ("HOL tlc_def exact Nat->word_lab finite map", tlcHOLGuard),
    ("HOL slc_def exact varname->value finite map", slcHOLGuard),
    ("HOL slc_tlc_rw exact finite-map rewrite", slcTlcRwHOLGuard),
    ("HOL locals_rel_lookup_ctxt exact slot, flattened value, and shape",
      lookupCtxtGuard),
    ("HOL ctxt_max_el_leq exact selected slot within vmax", ctxtMaxElLeqGuard)]
  for (name, passed) in checks do
    IO.println s!"{if passed then "PASS" else "FAIL"} {name}"
  pure (checks.all Prod.snd)

end Flapjack.Test.PanToCrepStateRelCarrierParity
