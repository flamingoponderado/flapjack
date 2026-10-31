import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.Semantics.BvlProps.ApplyRuntimeFrame
import Aesop

/-! Runtime-field transfer for BVI primitive application. -/
namespace Flapjack.Compiler.Backend.BviSem
open BvlSem

/-- Keep the target's compiler and code while taking the source's runtime
fields. This is Flapjack infrastructure for polymorphic state transfer. -/
def runtimeFrame {C D F G : Type} (source : BviState C F) (target : BviState D G) : BviState D F :=
  ⟨source.refs, source.clock, source.global, target.compile, target.compileOracle, target.code, source.ffi⟩

set_option maxHeartbeats 1200000 in
/-- Transfer the handled part of the dispatcher between states with equal
code domains. This helper has no standalone HOL declaration. -/
theorem doAppAux_frame {C D F G : Type} (op : ClosLang.Op) (args : List Value)
    (source : BviState C F) (target : BviState D G)
    (domains : sptDomain source.code = sptDomain target.code) :
    doAppAux op args (runtimeFrame source target) =
      (doAppAux op args source).map (fun result =>
        result.map fun (value, next) => (value, runtimeFrame next target)) := by
  cases op with
  | label name =>
    cases args with
    | nil =>
      have present : (sptLookup name source.code).isSome = (sptLookup name target.code).isSome := by
        have same := congrFun domains name
        cases h1 : sptLookup name source.code <;> cases h2 : sptLookup name target.code <;>
          simp_all [sptDomain]
      simp [doAppAux, runtimeFrame, ← present]
    | cons value rest => simp [doAppAux]
  | _ =>
    unfold doAppAux runtimeFrame
    repeat' split
    all_goals simp_all [Option.map_bind, Function.comp_def]
    all_goals try (cases h : source.global <;> simp_all)
    all_goals try (rename_i ptr; cases h : source.refs.lookup ptr <;>
      simp_all)
    all_goals try (split <;> simp_all)
    all_goals (expose_names; first
      | (cases val <;> simp_all <;> split <;> simp_all)
      | exact h_1 tag left a_2 right rfl rfl rfl rfl)

/-- Converting a framed BVI state is the same as framing the corresponding
BVL states. This helper has no standalone HOL declaration. -/
theorem toBvl_runtimeFrame {C D F G : Type} (source : BviState C F) (target : BviState D G) :
    toBvl (runtimeFrame source target) =
      BvlProps.runtimeFrame (toBvl source) (toBvl target) := by
  cases source
  cases target
  rfl

/-- The BVL conversion preserves a BVI code tree's domain. -/
theorem toBvl_domain {C F : Type} (source : BviState C F) :
    sptDomain (toBvl source).code = sptDomain source.code := by
  exact sptDomain_sptMap _ _

/-- Returning from a framed BVL state commutes with the BVI runtime frame. -/
theorem fromBvl_runtimeFrame {C D F G : Type} (source : BvlSem.State C F)
    (target : BvlSem.State D G) (original : BviState C F) (other : BviState D G) :
    fromBvl (BvlProps.runtimeFrame source target) (runtimeFrame original other) =
      runtimeFrame (fromBvl source original) other := by
  cases source
  cases target
  cases original
  cases other
  rfl

/-- A non-install fallback operation commutes with runtime framing when code
domains agree. This Flapjack helper combines the BVI and BVL dispatchers. -/
theorem doAppFallback_frame {C D F G : Type} (op : ClosLang.Op) (args : List Value)
    (source : BviState C F) (target : BviState D G)
    (notInstall : op ≠ .install) (domains : sptDomain source.code = sptDomain target.code) :
    doAppFallback op args (runtimeFrame source target) =
      match doAppFallback op args source with
      | .err error => .err error
      | .val (value, next) => .val (value, runtimeFrame next target) := by
  have domainBvl : sptDomain (toBvl source).code = sptDomain (toBvl target).code := by
    rw [toBvl_domain, toBvl_domain, domains]
  unfold doAppFallback
  rw [doAppAux_frame op args source target domains]
  cases aux : doAppAux op args source with
  | none => rfl
  | some result =>
    cases result with
    | some pair =>
      obtain ⟨value, next⟩ := pair
      rfl
    | none =>
      simp only [Option.map_some, Option.map_none]
      rw [toBvl_runtimeFrame]
      cases original : BvlSem.doApp op args (toBvl source) with
      | err error =>
        have swapped := BvlProps.doAppRerrSwap op args (toBvl source) error (toBvl target)
          ⟨original, notInstall, by intro key present; rwa [domainBvl]⟩
        rw [swapped]
        cases error <;> rfl
      | val pair =>
        obtain ⟨value, next⟩ := pair
        have swapped := BvlProps.doAppRvalSwap op args (toBvl source) next value (toBvl target)
          ⟨original, notInstall, by intro key present; rwa [← domainBvl]⟩
        rw [swapped]
        simp only [fromBvl_runtimeFrame]

/-- A handled operation never changes the compiler, oracle, or code. -/
theorem doAppAux_compiler_fields {C F : Type} (op : ClosLang.Op) (args : List Value)
    (source next : BviState C F) (value : Value)
    (run : doAppAux op args source = some (some (value, next))) :
    next.compile = source.compile ∧ next.compileOracle = source.compileOracle ∧ next.code = source.code := by
  unfold doAppAux at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals aesop

/-- Successful non-install fallback operations leave compiler fields and
code unchanged. This helper has no standalone HOL declaration. -/
theorem doAppFallback_compiler_fields {C F : Type} (op : ClosLang.Op) (args : List Value)
    (source next : BviState C F) (value : Value)
    (run : doAppFallback op args source = .val (value, next)) :
    next.compile = source.compile ∧ next.compileOracle = source.compileOracle ∧ next.code = source.code := by
  unfold doAppFallback at run
  cases aux : doAppAux op args source with
  | none => simp [aux] at run
  | some result =>
    cases result with
    | some pair =>
      have eq : pair = (value, next) := by simpa [aux] using run
      subst pair
      exact doAppAux_compiler_fields op args source next value aux
    | none =>
      simp only [aux] at run
      cases original : BvlSem.doApp op args (toBvl source) with
      | err error => cases error <;> simp [original] at run
      | val pair =>
        obtain ⟨originalValue, originalState⟩ := pair
        simp only [original, Flapjack.SemanticPrimitivesHOL.Result.val.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        exact ⟨rfl, rfl, rfl⟩

end Flapjack.Compiler.Backend.BviSem
