import Flapjack.Ffi
import Flapjack.Misc.LList

/-!
# CakeML generic behavior semantics

This is the generic behavior carrier and resource-limit extension from
`cakeml/semantics/ffi/ffiScript.sml` and
`cakeml/semantics/proofs/semanticsPropsScript.sml:204-225`.

The existing Pancake and Loop observational wrappers are program-specific
views; the backend `semantics_compile` theorem instead composes sets of these
generic Cake behaviors. `CakeLazyList` represents HOL `llist` values as
possibly finite sequences with no gaps.
-/

namespace Flapjack

/- Port status: these definitions follow the HOL constructor and relation
   clauses, but they are not tagged as exact ports. The Lean `CakeLazyList`
   representation below has no checked bridge to HOL's `llist`, and there is
   no verified source-to-Lean representation relation for this behavior
   carrier. `cakeImplements'_trans` is therefore a kernel-checked structural
   analogue until those carrier correspondences are established. -/
/-- A HOL lazy list (`llist`): a finite prefix may end, after which all reads
    are absent, or the list may continue indefinitely. -/
structure CakeLazyList (α : Type u) where
  get? : Nat → Option α
  none_suffix : ∀ index, get? index = none → ∀ later, index ≤ later → get? later = none

/-- `LPREFIX (fromList xs) trace` from HOL: every element of the finite list
    agrees with the same position in the lazy list. -/
def cakeLprefix (xs : List α) (trace : CakeLazyList α) : Prop :=
  ∀ index, index < xs.length → trace.get? index = xs[index]?

/-- The finite-list prefix relation used by Cake's `≼`. -/
def cakeListPrefix (xs ys : List α) : Prop :=
  xs.length ≤ ys.length ∧ ∀ index, index < xs.length → xs[index]? = ys[index]?

theorem cakeListPrefix_trans {xs ys zs : List α}
    (hxy : cakeListPrefix xs ys) (hyz : cakeListPrefix ys zs) :
    cakeListPrefix xs zs := by
  have hlenxy := hxy.1
  have hlenyz := hyz.1
  constructor
  · omega
  · intro index hindex
    rw [hxy.2 index hindex]
    exact hyz.2 index (by omega)

theorem cakeListPrefix_lprefix_trans {xs ys : List α}
    {trace : CakeLazyList α} (hxy : cakeListPrefix xs ys)
    (htrace : cakeLprefix ys trace) : cakeLprefix xs trace := by
  have hlenxy := hxy.1
  intro index hindex
  rw [hxy.2 index hindex]
  exact htrace index (by omega)

/-- `outcome` from Cake's generic semantics, where a terminal FFI event is
    distinct from successful completion and resource exhaustion. -/
inductive CakeOutcome where
  | success
  | resourceLimitHit
  | ffi (event : FfiFinalEvent)
  deriving DecidableEq, Repr

/-- The three constructors of Cake's generic `behaviour` datatype. -/
inductive CakeBehaviour where
  | diverge (trace : CakeLazyList FfiEvent)
  | terminate (outcome : CakeOutcome) (events : List FfiEvent)
  | fail

/-- HOL sets are represented by their membership predicates. -/
abbrev CakeBehaviourSet := CakeBehaviour → Prop

/-- Membership in HOL `extend_with_resource_limit`: retain existing
    behaviors, allow finite prefixes of terminating traces, and allow finite
    prefixes of divergent traces as resource-limit termination. -/
def cakeExtendWithResourceLimit (behaviours : CakeBehaviourSet)
    (result : CakeBehaviour) : Prop :=
  behaviours result ∨
    (∃ events outcome complete,
        result = .terminate .resourceLimitHit events ∧
        behaviours (.terminate outcome complete) ∧
        cakeListPrefix events complete) ∨
    (∃ events trace,
        result = .terminate .resourceLimitHit events ∧
        behaviours (.diverge trace) ∧ cakeLprefix events trace)

/-- The precise flag chooses either the original behavior set or its
    resource-limit extension, matching `extend_with_resource_limit'`. -/
def cakeExtendWithResourceLimit' (precise : Bool)
    (behaviours : CakeBehaviourSet) : CakeBehaviourSet :=
  if precise then behaviours else cakeExtendWithResourceLimit behaviours

/-- Cake's `implements' precise x y`: compiled behavior `x` refines source
    behavior `y`, modulo the resource-limit extension. This remains an
    untagged carrier analogue until the HOL/Lean behavior relation is checked. -/
def cakeImplements' (precise : Bool) (compiled source : CakeBehaviourSet) : Prop :=
  ¬ source .fail → ∀ result, compiled result →
    cakeExtendWithResourceLimit' precise source result

theorem cakeExtend_not_fail (behaviours : CakeBehaviourSet)
    (result : CakeBehaviour) (hresult : cakeExtendWithResourceLimit behaviours result)
    (hfail : ¬ behaviours .fail) : result ≠ .fail := by
  rcases hresult with hresult | hresult | hresult
  · intro heq
    subst result
    exact hfail hresult
  · rcases hresult with ⟨events, outcome, complete, heq, _, _⟩
    cases heq <;> simp
  · rcases hresult with ⟨events, trace, heq, _, _⟩
    cases heq <;> simp

/-- Extending behaviors twice adds no new resource-limit observations: list
    prefix and lazy-list prefix are transitive. This is the set-inclusion core
    needed by Cake's `implements'_trans`. -/
theorem cakeExtendWithResourceLimit_idempotent (behaviours : CakeBehaviourSet)
    (result : CakeBehaviour)
    (hresult : cakeExtendWithResourceLimit
      (cakeExtendWithResourceLimit behaviours) result) :
    cakeExtendWithResourceLimit behaviours result := by
  rcases hresult with hresult | hresult | hresult
  · exact hresult
  · rcases hresult with ⟨events, outcome, complete, rfl, hcomplete, hpref⟩
    change cakeExtendWithResourceLimit behaviours (.terminate outcome complete) at hcomplete
    rcases hcomplete with hcomplete | hcomplete | hcomplete
    · exact Or.inr (Or.inl ⟨events, outcome, complete, rfl, hcomplete, hpref⟩)
    · rcases hcomplete with ⟨middle, middleOutcome, middleComplete, hmid, hmiddle, hmidPrefix⟩
      cases hmid
      exact Or.inr (Or.inl ⟨events, middleOutcome, middleComplete, rfl, hmiddle,
        cakeListPrefix_trans hpref hmidPrefix⟩)
    · rcases hcomplete with ⟨middle, trace, hmid, hmiddle, hmidPrefix⟩
      cases hmid
      exact Or.inr (Or.inr ⟨events, trace, rfl, hmiddle,
        cakeListPrefix_lprefix_trans hpref hmidPrefix⟩)
  · rcases hresult with ⟨events, trace, rfl, htrace, hpref⟩
    change cakeExtendWithResourceLimit behaviours (.diverge trace) at htrace
    rcases htrace with htrace | htrace | htrace
    · exact Or.inr (Or.inr ⟨events, trace, rfl, htrace, hpref⟩)
    · rcases htrace with ⟨_, _, _, hdiverge, _⟩
      cases hdiverge
    · rcases htrace with ⟨_, _, hdiverge, _⟩
      cases hdiverge

theorem cakeExtendWithResourceLimit'_idempotent (precise : Bool)
    (behaviours : CakeBehaviourSet) (result : CakeBehaviour)
    (hresult : cakeExtendWithResourceLimit' precise
      (cakeExtendWithResourceLimit' precise behaviours) result) :
    cakeExtendWithResourceLimit' precise behaviours result := by
  cases precise with
  | true => exact hresult
  | false => exact cakeExtendWithResourceLimit_idempotent behaviours result hresult

theorem cakeExtendWithResourceLimit_mono {left right : CakeBehaviourSet}
    (hsubset : ∀ result, left result → right result) (result : CakeBehaviour)
    (hresult : cakeExtendWithResourceLimit left result) :
    cakeExtendWithResourceLimit right result := by
  rcases hresult with hresult | hresult | hresult
  · exact Or.inl (hsubset result hresult)
  · rcases hresult with ⟨events, outcome, complete, rfl, hcomplete, hpref⟩
    exact Or.inr (Or.inl ⟨events, outcome, complete, rfl,
      hsubset (.terminate outcome complete) hcomplete, hpref⟩)
  · rcases hresult with ⟨events, trace, rfl, htrace, hpref⟩
    exact Or.inr (Or.inr ⟨events, trace, rfl, hsubset (.diverge trace) htrace, hpref⟩)

theorem cakeExtendWithResourceLimit'_mono (precise : Bool)
    {left right : CakeBehaviourSet} (hsubset : ∀ result, left result → right result)
    (result : CakeBehaviour)
    (hresult : cakeExtendWithResourceLimit' precise left result) :
    cakeExtendWithResourceLimit' precise right result := by
  cases precise with
  | false => exact cakeExtendWithResourceLimit_mono hsubset result hresult
  | true => exact hsubset result hresult

/-- Structural analogue of HOL `implements'_trans` from
    `semanticsPropsScript.sml:285-295`, with the representation gap noted at
    `CakeLazyList`. -/
theorem cakeImplements'_trans {compiled intermediate source : CakeBehaviourSet}
    {precise : Bool} (hintermediate : cakeImplements' precise intermediate source)
    (hcompiled : cakeImplements' precise compiled intermediate) :
    cakeImplements' precise compiled source := by
  intro hsourceFail result hresult
  have hintermediateSubset := hintermediate hsourceFail
  have hintermediateFail : ¬ intermediate .fail := by
    intro hfail
    have hfailExtended : cakeExtendWithResourceLimit' precise source .fail :=
      hintermediateSubset .fail hfail
    cases precise with
    | false => exact cakeExtend_not_fail source .fail hfailExtended hsourceFail rfl
    | true => exact hsourceFail hfailExtended
  have hcompiledSubset := hcompiled hintermediateFail
  have hcompiledExtended := cakeExtendWithResourceLimit'_mono precise hintermediateSubset result
    (hcompiledSubset result hresult)
  exact cakeExtendWithResourceLimit'_idempotent precise source
    result hcompiledExtended

/-! ## Representation bridge to HOL `llist`

The Cake generic behavior carrier `CakeLazyList` reads through its `get?`
function with a downward-closed `none` suffix. HOL's `llist` carrier
(`Flapjack.HolLList`, the `llist_abs` subtype with the `lrep_ok` invariant)
reads through its `rep` function with the same downward-closed `none` property
`HolLrepOk`. They are related by the identity on reads
(`CakeLazyListRepresents`); this section records that correspondence and the
fact that `cakeLprefix` matches `HolLList.lprefix (fromList events)` of the
related representation. These declarations
remain untagged as local representation/transport infrastructure: there is no
independently reviewed exact HOL declaration with these statements, and the
mapping of the `FfiEvent` carrier still awaits review (tracked by
`flapjack-pxn.18.5.15.10.1`). -/

/-- The reviewed representation relation: a `CakeLazyList` represents a HOL
    `llist` when both read the same values at every index. -/
def CakeLazyListRepresents (t : CakeLazyList α) (ll : HolLList α) : Prop :=
  t.get? = ll.rep

/-- A `CakeLazyList` viewed as the HOL `llist` subtype: its `get?` function is
    `HolLrepOk` (downward-closed `none` reads). -/
def CakeLazyList.toHolLList (t : CakeLazyList α) : HolLList α :=
  ⟨t.get?, fun n h => by
    rw [Option.isSome_iff_ne_none] at h ⊢
    intro hnone
    exact h (t.none_suffix n hnone (n + 1) (Nat.le_succ n))⟩

/-- A HOL `llist` viewed as a `CakeLazyList`. -/
def cakeLazyListOfHolLList (ll : HolLList α) : CakeLazyList α :=
  ⟨ll.rep, fun _i h _later hle => HolLList.rep_none_of_le ll h hle⟩

/-- `CakeLazyList` extensionality: equal reads give equal carriers. -/
theorem CakeLazyList.ext {a b : CakeLazyList α} (h : a.get? = b.get?) : a = b := by
  cases a with
  | mk ga pa =>
    cases b with
    | mk gb pb =>
      simp only at h
      subst h
      exact congrArg (fun p => (⟨ga, p⟩ : CakeLazyList α)) (Subsingleton.elim pa pb)

theorem cakeLazyListRepresents_toHolLList (t : CakeLazyList α) :
    CakeLazyListRepresents t t.toHolLList := rfl

theorem cakeLazyListRepresents_ofHolLList (ll : HolLList α) :
    CakeLazyListRepresents (cakeLazyListOfHolLList ll) ll := rfl

theorem cakeLazyListOfHolLList_toHolLList (ll : HolLList α) :
    (cakeLazyListOfHolLList ll).toHolLList = ll :=
  HolLList.ext_of_rep (fun _ => rfl)

theorem toHolLList_cakeLazyListOfHolLList (t : CakeLazyList α) :
    cakeLazyListOfHolLList t.toHolLList = t :=
  CakeLazyList.ext rfl

/-- `CakeLazyList` is a total, functional representation of HOL `llist`. -/
theorem cakeLazyListRepresents_iff_eq (t : CakeLazyList α) (ll : HolLList α) :
    CakeLazyListRepresents t ll ↔ t = cakeLazyListOfHolLList ll := by
  constructor
  · intro h
    apply CakeLazyList.ext
    exact h
  · intro h
    rw [h]
    exact cakeLazyListRepresents_ofHolLList ll

/-- Flapjack representation fact: `cakeLprefix xs t` holds exactly when
    `HolLList.fromList xs` is an `lprefix` of the related lazy list.  Untagged
    local representation/transport infrastructure (no independently reviewed
    exact HOL declaration for this statement); whether the external
    `LPREFIX`/`extend_with_resource_limit` correspondence holds is the
    follow-up review tracked by `flapjack-pxn.18.5.15.10.1`. -/
theorem cakeLprefix_iff_lprefix {xs : List α} {t : CakeLazyList α} :
    cakeLprefix xs t ↔ HolLList.lprefix (HolLList.fromList xs) t.toHolLList := by
  constructor
  · intro h
    refine HolLList.lprefix_of_rep_agree (fun n x hx => ?_)
    have hn : n < xs.length := HolLList.fromList_rep_lt hx
    rw [HolLList.fromList_rep] at hx
    show t.get? n = some x
    rw [h n hn, hx]
  · intro h i hi
    have hrep : (HolLList.fromList xs).rep i = some xs[i] := by
      rw [HolLList.fromList_rep, List.getElem?_eq_getElem hi]
    have hreads := HolLList.lprefix_rep h hrep
    show t.get? i = xs[i]?
    rw [List.getElem?_eq_getElem hi]
    exact hreads

/-- The finite-list prefix relation `cakeListPrefix` is HOL's `isPREFIX`
    (`≼` on event lists in `extend_with_resource_limit`). -/
theorem cakeListPrefix_iff_prefix {xs ys : List α} :
    cakeListPrefix xs ys ↔ xs <+: ys := by
  constructor
  · intro h
    rw [List.prefix_iff_getElem?]
    intro i hi
    rw [← h.2 i hi, List.getElem?_eq_getElem hi]
  · intro h
    refine ⟨h.length_le, fun i hi => ?_⟩
    rw [List.getElem?_eq_getElem hi, (List.prefix_iff_getElem?.mp h) i hi]

end Flapjack
