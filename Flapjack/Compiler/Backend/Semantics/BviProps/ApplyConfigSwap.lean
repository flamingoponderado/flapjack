module

public import Flapjack.Compiler.Backend.Semantics.BviProps.ApplyFields
public import Flapjack.Compiler.Backend.Semantics.BviSem.ApplyRuntimeFrame
public import Flapjack.Compiler.Backend.Semantics.BvlProps.ApplyFallbackFrame
public import Flapjack.Compiler.Backend.WordElim.Proofs.Locations
public import Flapjack.HolRef

@[expose] public section

/-!
# Swapping runtime fields across configurations in HOL `bviProps`

Counterpart of `cakeml/compiler/backend/semantics/bviPropsScript.sml:768-835`:
`do_app_cfg_swap`, `do_app_cfg_swap_Rval` and `do_app_cfg_swap_Rerr`.

HOL writes the type-changing record update `t with <| refs := s.refs;
clock := s.clock; global := s.global; ffi := s.ffi |>`, which moves the ffi
type parameter from `('g,'d) state` to `('g,'f) state`. Lean record update
cannot change a structure's type parameter, so the source-shaped update is
rendered with the reviewed `runtimeFrame source target`, which takes the
runtime fields (refs, clock, global, ffi) from the source and the compiler
fields and code tree from the target.
-/

namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.Compiler.Backend.WordElim
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)

namespace ConfigSwapCarrier
/-- Canonical BVI reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end ConfigSwapCarrier

/-- Flapjack helper: a handled result transfers across configurations when the
source code domain is contained in the target's. -/
theorem doAppAux_frame_growth {C D F G : Type} (op : ClosLang.Op) (args : List Value)
    (source : BviState C F) (target : BviState D G) (next : BviState C F) (value : Value)
    (run : doAppAux op args source = some (some (value, next)))
    (growth : sptDomainSet source.code ⊆ sptDomainSet target.code) :
    doAppAux op args (runtimeFrame source target) =
      some (some (value, runtimeFrame next target)) := by
  by_cases hlabel : ∃ name, op = .label name
  · obtain ⟨name, rfl⟩ := hlabel
    cases args with
    | cons arg rest => simp [doAppAux] at run
    | nil =>
      simp only [doAppAux] at run ⊢
      split at run
      · rename_i found
        simp at run
        obtain ⟨rfl, rfl⟩ := run
        have present : (sptLookup name target.code).isSome = true := by
          apply growth
          show (sptLookup name source.code).isSome = true
          exact found
        simp [runtimeFrame, present]
      · simp_all
  · have notLabel : ∀ name, op ≠ .label name := by
      intro name eq
      exact hlabel ⟨name, eq⟩
    have frame := doAppAux_frame op args source target (Or.inr notLabel)
    rw [frame, run]
    rfl

/-- Flapjack helper: an unhandled operation stays unhandled when the target
code domain is contained in the source's. -/
theorem doAppAux_frame_none {C D F G : Type} (op : ClosLang.Op) (args : List Value)
    (source : BviState C F) (target : BviState D G)
    (run : doAppAux op args source = none)
    (shrink : sptDomainSet target.code ⊆ sptDomainSet source.code) :
    doAppAux op args (runtimeFrame source target) = none := by
  by_cases hlabel : ∃ name, op = .label name
  · obtain ⟨name, rfl⟩ := hlabel
    cases args with
    | cons arg rest => simp [doAppAux]
    | nil =>
      simp only [doAppAux] at run ⊢
      split at run
      · simp_all
      · rename_i missing
        split
        · rename_i found
          have present : (sptLookup name source.code).isSome = true := by
            apply shrink
            show (sptLookup name target.code).isSome = true
            exact found
          simp [missing] at present
        · rfl
  · have notLabel : ∀ name, op ≠ .label name := by
      intro name eq
      exact hlabel ⟨name, eq⟩
    have frame := doAppAux_frame op args source target (Or.inr notLabel)
    rw [frame, run]
    rfl

/-- Flapjack helper: a delegated operation stays delegated across
configurations. -/
theorem doAppAux_frame_some_none {C D F G : Type} (op : ClosLang.Op) (args : List Value)
    (source : BviState C F) (target : BviState D G)
    (run : doAppAux op args source = some none) :
    doAppAux op args (runtimeFrame source target) = some none := by
  by_cases hlabel : ∃ name, op = .label name
  · obtain ⟨name, rfl⟩ := hlabel
    cases args with
    | nil => simp [doAppAux] at run
    | cons arg rest => simp [doAppAux] at run
  · have notLabel : ∀ name, op ≠ .label name := by
      intro name eq
      exact hlabel ⟨name, eq⟩
    have frame := doAppAux_frame op args source target (Or.inr notLabel)
    rw [frame, run]
    rfl

/-- Flapjack helper: a delegated successful result transfers across
configurations when the source code domain is contained in the target's. -/
theorem doAppFallback_frame_growth {C D F G : Type} (op : ClosLang.Op) (args : List Value)
    (source : BviState C F) (target : BviState D G) (next : BviState C F) (value : Value)
    (run : doAppFallback op args source = .val (value, next))
    (notInstall : op ≠ .install)
    (growth : sptDomainSet source.code ⊆ sptDomainSet target.code) :
    doAppFallback op args (runtimeFrame source target) =
      .val (value, runtimeFrame next target) := by
  unfold doAppFallback at run ⊢
  cases aux : doAppAux op args source with
  | none => simp [aux] at run
  | some result =>
    cases result with
    | some pair =>
      obtain ⟨v, t⟩ := pair
      simp [aux] at run
      obtain ⟨rfl, rfl⟩ := run
      rw [doAppAux_frame_growth op args source target t v aux growth]
    | none =>
      simp only [aux] at run ⊢
      have notGlobal : ∀ operation, op ≠ .globOp operation := by
        intro operation eq
        subst op
        exact doAppAux_delegates_not_global operation args source aux
      rw [toBvl_runtimeFrame]
      cases original : BvlSem.doApp op args (toBvl source) with
      | err error => cases error <;> simp [original] at run
      | val pair =>
        obtain ⟨v, t⟩ := pair
        simp [original] at run
        obtain ⟨rfl, rfl⟩ := run
        have domainBvl : ∀ key, sptDomain (toBvl source).code key →
            sptDomain (toBvl (runtimeFrame source target)).code key := by
          intro key present
          rw [toBvl_domain] at present
          rw [toBvl_domain]
          exact growth present
        have swapped := BvlProps.doAppFallbackRvalSwap op args (toBvl source) t v
          (toBvl (runtimeFrame source target)) notGlobal ⟨original, notInstall, domainBvl⟩
        rw [doAppAux_frame_some_none op args source target aux]
        rw [swapped]
        simp only [fromBvl_runtimeFrame]

/-- Flapjack helper: a delegated error transfers across configurations when the
target code domain is contained in the source's, or the error is not a type
error. -/
theorem doAppFallback_frame_shrink {C D F G : Type} (op : ClosLang.Op) (args : List Value)
    (source : BviState C F) (target : BviState D G) (error : ErrorResult ExnOrRet)
    (run : doAppFallback op args source = .err error)
    (notInstall : op ≠ .install)
    (guard : sptDomainSet target.code ⊆ sptDomainSet source.code ∨
      error ≠ .abort .typeError) :
    doAppFallback op args (runtimeFrame source target) = .err error := by
  unfold doAppFallback at run ⊢
  cases aux : doAppAux op args source with
  | none =>
    simp only [aux] at run ⊢
    obtain ⟨rfl⟩ := run.symm
    rcases guard with shrink | notType
    · rw [doAppAux_frame_none op args source target aux shrink]
    · exact absurd rfl notType
  | some result =>
    cases result with
    | some pair => simp [aux] at run
    | none =>
      simp only [aux] at run ⊢
      have notGlobal : ∀ operation, op ≠ .globOp operation := by
        intro operation eq
        subst op
        exact doAppAux_delegates_not_global operation args source aux
      have notLabel : ∀ n, op ≠ .label n := by
        intro n eq
        subst eq
        cases args with
        | nil => simp [doAppAux] at aux
        | cons arg rest => simp [doAppAux] at aux
      rw [toBvl_runtimeFrame]
      cases original : BvlSem.doApp op args (toBvl source) with
      | val pair => simp [original] at run
      | err error' =>
        rw [original] at run
        cases error' with
        | raise value =>
          have run' : error = .raise (.exn value) := by simpa using run.symm
          have bvlGuard : ((∀ key, sptDomain (toBvl (runtimeFrame source target)).code key →
              sptDomain (toBvl source).code key) ∨
              (ErrorResult.raise value : ErrorResult Value) ≠ .abort .typeError) ∨
              ∀ n, op ≠ .label n := by
            left
            right
            intro eq
            cases eq
          have swapped := BvlProps.doAppFallbackRerrSwap op args (toBvl source)
            (.raise value) (toBvl (runtimeFrame source target)) notGlobal
            ⟨original, notInstall, bvlGuard⟩
          rw [doAppAux_frame_some_none op args source target aux]
          rw [swapped]
          simp [run']
        | abort reason =>
          have run' : error = .abort reason := by simpa using run.symm
          have bvlGuard : ((∀ key, sptDomain (toBvl (runtimeFrame source target)).code key →
              sptDomain (toBvl source).code key) ∨
              (ErrorResult.abort reason : ErrorResult Value) ≠ .abort .typeError) ∨
              ∀ n, op ≠ .label n := by
            left
            rcases guard with shrink | notType
            · left
              intro key present
              rw [toBvl_domain] at present
              rw [toBvl_domain]
              exact shrink present
            · right
              intro eq
              cases eq
              exact notType run'
          have swapped := BvlProps.doAppFallbackRerrSwap op args (toBvl source)
            (.abort reason) (toBvl (runtimeFrame source target)) notGlobal
            ⟨original, notInstall, bvlGuard⟩
          rw [doAppAux_frame_some_none op args source target aux]
          rw [swapped]
          simp [run']

/-- A non-install primitive application transfers across configurations when
the source code domain is contained in the target's (successful case), or the
target's is contained in the source's or the error is not a type error (error
case). -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "do_app_cfg_swap"
  (fmap_as_finite_support := [refs])]
theorem doApp_cfg_swap {C D F G : Type} (op : ClosLang.Op) (args : List Value)
    (source : BviState C F) (value : Value) (next : BviState C F)
    (target : BviState D G) (error : ErrorResult ExnOrRet)
    (notInstall : op ≠ .install) :
    ((doApp op args source = .val (value, next) ∧
        sptDomainSet source.code ⊆ sptDomainSet target.code →
        doApp op args (runtimeFrame source target) = .val (value, runtimeFrame next target)) ∧
      (doApp op args source = .err error ∧
        (sptDomainSet target.code ⊆ sptDomainSet source.code ∨
          error ≠ .abort .typeError) →
        doApp op args (runtimeFrame source target) = .err error)) := by
  constructor
  · intro h
    obtain ⟨run, growth⟩ := h
    simp only [doApp] at run ⊢
    exact doAppFallback_frame_growth op args source target next value run notInstall growth
  · intro h
    obtain ⟨run, guard⟩ := h
    simp only [doApp] at run ⊢
    exact doAppFallback_frame_shrink op args source target error run notInstall guard

/-- A successful non-install application transfers across configurations with
equal code domains. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "do_app_cfg_swap_Rval"
  (fmap_as_finite_support := [refs])]
theorem doApp_cfg_swap_Rval {C D F : Type} (op : ClosLang.Op) (args : List Value)
    (source : BviState C F) (next : BviState C F) (target : BviState D F) (value : Value)
    (premise : op ≠ .install ∧ sptDomainSet source.code = sptDomainSet target.code ∧
      doApp op args source = .val (value, next)) :
    doApp op args (runtimeFrame source target) = .val (value, runtimeFrame next target) := by
  obtain ⟨notInstall, domains, run⟩ := premise
  have growth : sptDomainSet source.code ⊆ sptDomainSet target.code := by
    intro key present
    rwa [domains] at present
  exact (doApp_cfg_swap op args source value next target (.abort .typeError)
    notInstall).1 ⟨run, growth⟩

/-- A non-install error transfers across configurations with equal code
domains. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "do_app_cfg_swap_Rerr"
  (fmap_as_finite_support := [refs])]
theorem doApp_cfg_swap_Rerr {C D F : Type} (op : ClosLang.Op) (args : List Value)
    (source : BviState C F) (target : BviState D F) (error : ErrorResult ExnOrRet)
    (premise : op ≠ .install ∧ sptDomainSet source.code = sptDomainSet target.code ∧
      doApp op args source = .err error) :
    doApp op args (runtimeFrame source target) = .err error := by
  obtain ⟨notInstall, domains, run⟩ := premise
  have shrink : sptDomainSet target.code ⊆ sptDomainSet source.code := by
    intro key present
    rwa [← domains] at present
  exact (doApp_cfg_swap op args source BvlSem.unitValue source target error
    notInstall).2 ⟨run, Or.inl shrink⟩

end Flapjack.Compiler.Backend.BviProps
