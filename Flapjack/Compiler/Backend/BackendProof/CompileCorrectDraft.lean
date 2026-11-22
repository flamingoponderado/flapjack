import Flapjack.Compiler.Backend.Backend.Compile
import Flapjack.Compiler.Backend.BackendProof.AddEvalState
import Flapjack.Compiler.Backend.BackendProof.ConfigOk
import Flapjack.Compiler.Backend.BackendProof.MachineInit
import Flapjack.Compiler.Backend.BackendProof.SafeForSpace
import Flapjack.Compiler.Backend.BackendProof.ReadLimits
import Flapjack.Compiler.Backend.BackendProof.CompileCorrect
import Flapjack.Compiler.Backend.LabToTarget.InitializationContracts
import Flapjack.Compiler.Backend.Semantics.TargetSem.Installed
import Flapjack.Compiler.Backend.Semantics.TargetSem.MachineSem
import Flapjack.Compiler.Backend.Semantics.TargetProps.EvaluateAddClockIoEventsMono
import Flapjack.SemanticsProps.Implements
import Flapjack.SemanticsProps.Clock
import Flapjack.PrimSemEnv
import Flapjack.Misc.Option

set_option autoImplicit false

/-! Draft (untagged) statements of the final theorems of
`backendProofScript.sml` (`compile_correct'`, `compile_correct`,
`compile_correct_is_safe_for_space`, `compile_correct_eval`), and the derivation
of the last three from `compile_correct'`, following HOL's proofs
(`backendProofScript.sml:4429-4498`).

Nothing here carries an `@[hol]` tag: `compile_correct'` itself is not yet
proved, so each derived theorem takes the corresponding instance of the
`compile_correct'` statement as an explicit hypothesis
(`..._of_compileCorrectPrime`). The statements are written with HOL's shape so
that they can be tagged once `compile_correct'` is proved. -/
namespace Flapjack.Compiler.Backend.BackendProof.Draft

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.BackendDefs
open Flapjack.SemanticsHOL Flapjack.SemanticPrimitivesHOL Flapjack.PrimTypesHOL
open Flapjack.SemanticsPropsHOL Flapjack.Compiler.Backend.SourceEval.Proofs

/-- Inhabitant of HOL's `'ffi semanticPrimitives$state # v sem_env`, the type
of `THE (prim_sem_env ffi)`. Flapjack infrastructure for the `holThe`
rendering of HOL `THE` (no correctness content): every HOL type is inhabited,
and the instance is derived from an inhabitant of the FFI state type. -/
instance primSemEnvCarrier_nonempty {F : Type} [Nonempty F] :
    Nonempty (State F × SemEnv Value) := by
  obtain ⟨f⟩ := ‹Nonempty F›
  let ffi : HolFfiState F :=
    { oracle := fun _ _ _ _ => .ret f [], ffiState := f, ioEvents := [] }
  exact ⟨({ clock := 0, refs := [], ffi := ffi, nextTypeStamp := 0, nextExnStamp := 0,
            evalState := none }, { v := NamespaceHOL.nsEmpty, c := NamespaceHOL.nsEmpty })⟩

/-- The statement of HOL `compile_correct'` (`backendProofScript.sml:3547-3559`)
for fixed free variables. HOL's `'a asm_config` is `AsmConfigExact width`,
`'ffi` is `F`, `(α,β,γ) machine_config` is `MachineConfig width state
projection`, `THE` is `holThe`, the behaviour sets are predicates and
`machine_sem mc ffi ms ⊆ X` is `∀ b, machineSemHOL mc ffi ms b → X b`. The
boolean `is_safe_for_space ...` flag is the classical decision of the Prop. -/
noncomputable def compileCorrectPrimeStmt {width : Nat} [NeZero width]
    {state projection F : Type} [Nonempty F]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (bytes : List (BitVec 8)) (bitmaps : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) (ffi : HolFfiState F)
    (ev : Option (CompilerInstance Flapjack.Compiler.Backend.Backend.Config))
    (mc : MachineConfig width state projection) (cbspace dataSp : Nat) (ms : state) : Prop :=
  open Classical in
  BackendDefs.compile asmConf c prog = some (bytes, bitmaps, c') →
    match holThe (primSemEnv ffi) with
    | (s0, env) =>
      let s := addEvalState ev s0
      ¬ semanticsProg s env prog .fail ∧ backendConfigOk asmConf c ∧
          LabToTarget.mcConfOk mc ∧ mcInitOk asmConf c mc ∧
          optEvalConfigWf asmConf c' ev ∧
          installed bytes cbspace bitmaps dataSp c'.labConf.ffiNames
            (heapRegs c.stackConf.regNames) mc c'.labConf.shmemExtra ms →
        ∀ b, machineSemHOL mc ffi ms b →
          extendWithResourceLimitPrimeHOL
            (decide (isSafeForSpace ffi asmConf c prog (readLimits asmConf c mc ms)))
            (semanticsProg s env prog) b

/-- The statement of HOL `compile_correct` (`backendProofScript.sml:4433-4443`). -/
noncomputable def compileCorrectStmt {width : Nat} [NeZero width]
    {state projection F : Type} [Nonempty F]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (bytes : List (BitVec 8)) (bitmaps : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) (ffi : HolFfiState F)
    (mc : MachineConfig width state projection) (cbspace dataSp : Nat) (ms : state) : Prop :=
  BackendDefs.compile asmConf c prog = some (bytes, bitmaps, c') →
    match holThe (primSemEnv ffi) with
    | (s, env) =>
      ¬ semanticsProg s env prog .fail ∧ backendConfigOk asmConf c ∧
          LabToTarget.mcConfOk mc ∧ mcInitOk asmConf c mc ∧
          installed bytes cbspace bitmaps dataSp c'.labConf.ffiNames
            (heapRegs c.stackConf.regNames) mc c'.labConf.shmemExtra ms →
        ∀ b, machineSemHOL mc ffi ms b →
          extendWithResourceLimitHOL (semanticsProg s env prog) b

/-- The statement of HOL `compile_correct_is_safe_for_space`
(`backendProofScript.sml:4459-4471`). -/
noncomputable def compileCorrectIsSafeForSpaceStmt {width : Nat} [NeZero width]
    {state projection F : Type} [Nonempty F]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (bytes : List (BitVec 8)) (bitmaps : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) (ffi : HolFfiState F)
    (stackLimit heapLimit : Nat)
    (mc : MachineConfig width state projection) (cbspace dataSp : Nat) (ms : state) : Prop :=
  BackendDefs.compile asmConf c prog = some (bytes, bitmaps, c') →
  isSafeForSpace ffi asmConf c prog (stackLimit, heapLimit) →
  readLimits asmConf c mc ms = (stackLimit, heapLimit) →
    match holThe (primSemEnv ffi) with
    | (s, env) =>
      ¬ semanticsProg s env prog .fail ∧ backendConfigOk asmConf c ∧
          LabToTarget.mcConfOk mc ∧ mcInitOk asmConf c mc ∧
          installed bytes cbspace bitmaps dataSp c'.labConf.ffiNames
            (heapRegs c.stackConf.regNames) mc c'.labConf.shmemExtra ms →
        machineSemHOL mc ffi ms = semanticsProg s env prog

/-- The statement of HOL `compile_correct_eval` (`backendProofScript.sml:4486-4497`). -/
noncomputable def compileCorrectEvalStmt {width : Nat} [NeZero width]
    {state projection F : Type} [Nonempty F]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (bytes : List (BitVec 8)) (bitmaps : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) (ffi : HolFfiState F)
    (ev : Option (CompilerInstance Flapjack.Compiler.Backend.Backend.Config))
    (mc : MachineConfig width state projection) (cbspace dataSp : Nat) (ms : state) : Prop :=
  BackendDefs.compile asmConf c prog = some (bytes, bitmaps, c') →
    match holThe (primSemEnv ffi) with
    | (s0, env) =>
      ¬ semanticsProg (addEvalState ev s0) env prog .fail ∧ backendConfigOk asmConf c ∧
          LabToTarget.mcConfOk mc ∧ mcInitOk asmConf c mc ∧
          optEvalConfigWf asmConf c' ev ∧
          installed bytes cbspace bitmaps dataSp c'.labConf.ffiNames
            (heapRegs c.stackConf.regNames) mc c'.labConf.shmemExtra ms →
        ∀ b, machineSemHOL mc ffi ms b →
          extendWithResourceLimitHOL (semanticsProg (addEvalState ev s0) env prog) b

/-- HOL `extend_with_resource_limit'_SUBSET` (`semanticsPropsScript.sml:312-318`),
pointwise. Draft helper; to be tagged in the semanticsProps counterpart. -/
theorem extendWithResourceLimitPrime_subset (b : Bool) (s : BehaviourSetHOL) (x : HolBehaviour)
    (h : extendWithResourceLimitPrimeHOL b s x) : extendWithResourceLimitHOL s x := by
  cases b
  · exact h
  · exact Or.inl h

/-- HOL `targetProps$machine_sem_total` (`targetPropsScript.sml:1138-1165`).
Draft helper; to be tagged in the targetProps counterpart. -/
theorem machineSem_total {width : Nat} [NeZero width] {state projection σ : Type}
    (mc : MachineConfig width state projection) (st : HolFfiState σ) (ms : state) :
    ∃ b, machineSemHOL mc st ms b := by
  by_cases hhalt : ∃ k t, (evaluateTargetHOL mc st k ms).1 = .halt t
  · obtain ⟨k, t, hk⟩ := hhalt
    refine ⟨.terminate t (evaluateTargetHOL mc st k ms).2.2.ioEvents, ?_⟩
    refine ⟨k, (evaluateTargetHOL mc st k ms).2.1, (evaluateTargetHOL mc st k ms).2.2, ?_, rfl⟩
    rw [← hk]
  by_cases herr : ∃ k, (evaluateTargetHOL mc st k ms).1 = .error
  · exact ⟨.fail, herr⟩
  refine ⟨.diverge (HolLList.buildLprefixLub
      (fun ll => ∃ k : Nat,
        HolLList.fromList (evaluateTargetHOL mc st k ms).2.2.ioEvents = ll)), ?_, ?_⟩
  · intro k
    refine ⟨(evaluateTargetHOL mc st k ms).2.1, (evaluateTargetHOL mc st k ms).2.2, ?_⟩
    rcases hres : (evaluateTargetHOL mc st k ms).1 with t | _ | _
    · exact absurd ⟨k, t, hres⟩ hhalt
    · exact absurd ⟨k, hres⟩ herr
    · rw [← hres]
  · apply HolLList.buildLprefixLub_thm
    have hchain := HolLList.prefixChain_lprefixChain
      (ls := fun l => ∃ k : Nat, (evaluateTargetHOL mc st k ms).2.2.ioEvents = l) ?_
    · intro l1 l2 hl
      apply hchain l1 l2
      obtain ⟨⟨k1, h1⟩, ⟨k2, h2⟩⟩ := hl
      exact ⟨⟨_, ⟨k1, rfl⟩, h1⟩, ⟨_, ⟨k2, rfl⟩, h2⟩⟩
    · intro l1 l2 ⟨⟨k1, h1⟩, ⟨k2, h2⟩⟩
      subst h1 h2
      rcases Nat.le_total k1 k2 with h | h
      · exact Or.inl (evaluateTargetAddClockIoEventsMono mc st k1 ms k2 h)
      · exact Or.inr (evaluateTargetAddClockIoEventsMono mc st k2 ms k1 h)

/-- HOL `compile_correct` (`backendProofScript.sml:4433-4449`), from the
`ev = NONE` instance of `compile_correct'` (HOL's local
`compile_correct_no_eval`). -/
theorem compileCorrect_of_compileCorrectPrime {width : Nat} [NeZero width]
    {state projection F : Type} [Nonempty F]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (bytes : List (BitVec 8)) (bitmaps : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) (ffi : HolFfiState F)
    (mc : MachineConfig width state projection) (cbspace dataSp : Nat) (ms : state)
    (hprime : compileCorrectPrimeStmt asmConf c prog bytes bitmaps c' ffi none mc
      cbspace dataSp ms) :
    compileCorrectStmt asmConf c prog bytes bitmaps c' ffi mc cbspace dataSp ms := by
  intro hcomp
  have h := hprime hcomp
  revert h
  rcases holThe (primSemEnv ffi) with ⟨s, env⟩
  intro h ⟨hfail, hok, hmc, hinit, hinst⟩ b hb
  exact extendWithResourceLimitPrime_subset _ _ _
    (h ⟨hfail, hok, hmc, hinit, trivial, hinst⟩ b hb)

/-- HOL `compile_correct_is_safe_for_space` (`backendProofScript.sml:4459-4480`),
from the `ev = NONE` instance of `compile_correct'`. -/
theorem compileCorrectIsSafeForSpace_of_compileCorrectPrime {width : Nat} [NeZero width]
    {state projection F : Type} [Nonempty F]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (bytes : List (BitVec 8)) (bitmaps : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) (ffi : HolFfiState F)
    (stackLimit heapLimit : Nat)
    (mc : MachineConfig width state projection) (cbspace dataSp : Nat) (ms : state)
    (hprime : compileCorrectPrimeStmt asmConf c prog bytes bitmaps c' ffi none mc
      cbspace dataSp ms) :
    compileCorrectIsSafeForSpaceStmt asmConf c prog bytes bitmaps c' ffi stackLimit heapLimit
      mc cbspace dataSp ms := by
  intro hcomp hsafe hlim
  have h := hprime hcomp
  revert h
  rw [hlim]
  rcases holThe (primSemEnv ffi) with ⟨s, env⟩
  intro h ⟨hfail, hok, hmc, hinit, hinst⟩
  have hsub := h ⟨hfail, hok, hmc, hinit, trivial, hinst⟩
  simp only [addEvalState, extendWithResourceLimitPrimeHOL, hsafe, decide_true,
    if_true] at hsub
  obtain ⟨x, hx⟩ := semanticsProg_sing s env prog
  have hxeq : ∀ y, semanticsProg s env prog y ↔ y = x := fun y => by
    have := Set.ext_iff.mp hx y
    exact this
  funext y
  apply propext
  constructor
  · exact hsub y
  · intro hy
    obtain ⟨z, hz⟩ := machineSem_total mc ffi ms
    have hzx := (hxeq z).1 (hsub z hz)
    have hyx := (hxeq y).1 hy
    rw [hyx, ← hzx]
    exact hz

/-- HOL `compile_correct_eval` (`backendProofScript.sml:4486-4503`), from
`compile_correct'` at the same `ev`. -/
theorem compileCorrectEval_of_compileCorrectPrime {width : Nat} [NeZero width]
    {state projection F : Type} [Nonempty F]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (bytes : List (BitVec 8)) (bitmaps : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) (ffi : HolFfiState F)
    (ev : Option (CompilerInstance Flapjack.Compiler.Backend.Backend.Config))
    (mc : MachineConfig width state projection) (cbspace dataSp : Nat) (ms : state)
    (hprime : compileCorrectPrimeStmt asmConf c prog bytes bitmaps c' ffi ev mc
      cbspace dataSp ms) :
    compileCorrectEvalStmt asmConf c prog bytes bitmaps c' ffi ev mc cbspace dataSp ms := by
  intro hcomp
  have h := hprime hcomp
  revert h
  rcases holThe (primSemEnv ffi) with ⟨s0, env⟩
  intro h hpre b hb
  exact extendWithResourceLimitPrime_subset _ _ _ (h hpre b hb)

end Flapjack.Compiler.Backend.BackendProof.Draft
