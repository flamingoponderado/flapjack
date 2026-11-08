import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ThunkRel
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedArray
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ListConversion
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PrimitiveData

/-! Bounded vector and string primitive simulation over preliminary relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- strlen expressions compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_strlen {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .strlen [body]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by decide) (by decide) (by decide) (by decide)
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst expr
  assumption

/-- vfromList expressions compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_vfromList {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .vfromList [body]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by decide) (by decide) (by decide) (by decide)
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst expr
  assumption

/-- strcat expressions compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_strcat {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .strcat [body]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by decide) (by decide) (by decide) (by decide)
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst expr
  assumption

/-- implode expressions compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_implode {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .implode [body]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by decide) (by decide) (by decide) (by decide)
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst expr
  assumption

/-- explode expressions compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_explode {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .explode [body]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by decide) (by decide) (by decide) (by decide)
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst expr
  assumption

/-- vlength expressions compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_vlength {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .vlength [body]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by decide) (by decide) (by decide) (by decide)
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst expr
  assumption

/-- Compose vsub operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_vsub {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .vsub [left, right]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by decide) (by decide) (by decide) (by decide)
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> assumption

/-- Compose vsubUnsafe operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_vsubUnsafe {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .vsubUnsafe [left, right]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by decide) (by decide) (by decide) (by decide)
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> assumption

/-- Compose strsub operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_strsub {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .strsub [left, right]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by decide) (by decide) (by decide) (by decide)
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> assumption

/-- Compose listAppend operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_listAppend {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .listAppend [left, right]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by decide) (by decide) (by decide) (by decide)
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> assumption

/-- Compose configGC operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_configGC {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .configGC [left, right]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by decide) (by decide) (by decide) (by decide)
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> assumption

/-- The environment-ID operation leaves any related, well-formed operand
unchanged; source environment values themselves have no related flat value in
the factored value relation. -/
theorem envId_related_identity {F : Type} (genv : GlobalEnv) (source : State F)
    (value : Value) (flatValue : FlatSem.Value) (related : ValueRel genv value flatValue)
    (successful : doApp (source.refs, source.ffi) .envId [value] ≠ none) :
    doApp (source.refs, source.ffi) .envId [value] = some ((source.refs, source.ffi), .val value) := by
  cases related <;> simp [doApp, doAppNumericCore, doAppBasic] at successful ⊢
  case tuple sources flats h =>
    cases sources with
    | nil => simp at successful
    | cons first tail =>
      cases tail with
      | nil => simp at successful
      | cons second rest =>
        cases rest with
        | nil => rfl
        | cons third rest => simp at successful

/-- Environment-ID applications compose operand simulations in a local environment. -/
theorem localEnvBounded_envId {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp) (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .envId [body]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .envId [body]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, bad]
  obtain ⟨nextGenv, bodySim, post⟩ := bodyIH genv start finish other source flat baseEnv sourceLocal flatEnv traces
    trace baseMap gen clockBound localRel envInv tracesLen invariant generation bodySafe
  unfold ExprSim at bodySim
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [body] = sourceResult at bodySim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap body] = flatResult at bodySim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := bodySim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      trivial
  | raise valueRel =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [flatRun]
      exact ⟨.raise valueRel, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [flatRun]
      exact post
  | @value sourceValues flatValues valuesRel =>
    obtain ⟨value, rfl⟩ := EvaluateProps.evaluateSingFull source sourceEnv body nextSource sourceValues sourceRun
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | nil =>
        rename_i flatValue
        obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
        have successful : doApp (nextSource.refs, nextSource.ffi) .envId [value] ≠ none := by
          intro failed
          apply safe nextSource
          change EvaluateHOL.evaluate source sourceEnv [.app .envId [body]] = _
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp [getOpClass, failed, EvaluateHOL.typeError]
        have sourceApp := envId_related_identity nextGenv nextSource value flatValue valueRel successful
        refine ⟨nextGenv, ?_, ?_⟩
        · unfold ExprSim
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
          rw [flatRun]
          simp [getOpClass, sourceApp, EvaluateHOL.listResult]
          exact ⟨.value (.cons valueRel .nil), states⟩
        · rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
          rw [flatRun]
          simpa [getOpClass, sourceApp, EvaluateHOL.listResult] using
            And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))

/-- String slicing composes operand simulations in a local environment. -/
theorem localEnvBounded_copyStrStr {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right third : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right)
    (thirdIH : LocalEnvBoundedIH (F := F) interp transform limit third) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .copyStrStr [left, right, third]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by decide) (by decide) (by decide) (by decide)
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> assumption

/-- Fused multiply-add composes bounded operand simulations. -/
theorem localEnvBounded_floatFma {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right third : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right)
    (thirdIH : LocalEnvBoundedIH (F := F) interp transform limit third) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith .fma .float64T) [left, right, third]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by decide) (by decide) (by decide) (by decide)
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> assumption

/-- Byte-array slicing composes operand simulations in a local environment. -/
theorem localEnvBounded_copyAw8Str {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right third : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right)
    (thirdIH : LocalEnvBoundedIH (F := F) interp transform limit third) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .copyAw8Str [left, right, third]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by decide) (by decide) (by decide) (by decide)
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> assumption

/-- Byte-array XOR preserves related stores in arbitrary local environments. -/
theorem localEnvBounded_xorAw8StrUnsafe {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .xorAw8StrUnsafe [left, right]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by decide) (by decide) (by decide) (by decide)
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> assumption

/-- Thunk allocation composes the operand simulation with a related store allocation. -/
theorem localEnvBounded_allocThunk {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (mode : ThunkMode) (body : AstHOL.Exp)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.thunkOp (.allocThunk mode)) [body]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by simp) (by simp) (by simp) (by simp [getOpClass])
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst expr
  assumption

/-- Explicit thunk update preserves related stores in arbitrary local environments. -/
theorem localEnvBounded_updateThunk {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (mode : ThunkMode) (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.thunkOp (.updateThunk mode)) [left, right]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by simp) (by simp) (by simp) (by simp [getOpClass])
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> assumption

/-- String-to-byte-array copy composes operand simulations in a local environment. -/
theorem localEnvBounded_copyStrAw8 {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right third fourth fifth : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right)
    (thirdIH : LocalEnvBoundedIH (F := F) interp transform limit third)
    (fourthIH : LocalEnvBoundedIH (F := F) interp transform limit fourth)
    (fifthIH : LocalEnvBoundedIH (F := F) interp transform limit fifth) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .copyStrAw8 [left, right, third, fourth, fifth]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by decide) (by decide) (by decide) (by decide)
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> assumption

/-- Byte-array copy composes operand simulations in a local environment. -/
theorem localEnvBounded_copyAw8Aw8 {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right third fourth fifth : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right)
    (thirdIH : LocalEnvBoundedIH (F := F) interp transform limit third)
    (fourthIH : LocalEnvBoundedIH (F := F) interp transform limit fourth)
    (fifthIH : LocalEnvBoundedIH (F := F) interp transform limit fifth) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .copyAw8Aw8 [left, right, third, fourth, fifth]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by decide) (by decide) (by decide) (by decide)
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> assumption

/-- External calls preserve related stores and the shared FFI state in arbitrary local environments. -/
theorem localEnvBounded_ffi {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (name : Basis.Pure.MlString.MlString) (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.ffi name) [left, right]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by simp) (by simp) (by simp) (by simp [getOpClass])
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> assumption

end Flapjack.Compiler.Backend.SourceToFlat
