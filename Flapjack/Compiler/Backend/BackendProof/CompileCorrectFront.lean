import Flapjack.Compiler.Backend.BackendProof.CompileCorrectPrereqs
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.NoMat

set_option autoImplicit false

/-! Draft (untagged) front half of HOL `compile_correct'`
(`backendProofScript.sml:3560-3700`): from the source semantics down to the
data-language semantics. Each lemma is one block of HOL's proof. -/
namespace Flapjack.Compiler.Backend.BackendProof.Draft

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.BackendDefs
open Flapjack.SemanticsHOL Flapjack.SemanticPrimitivesHOL Flapjack.PrimTypesHOL
open Flapjack.Compiler.Backend.SourceEval.Proofs Flapjack.Compiler.Backend.BackendProps

/-- `s0.ffi = ffi` for `THE (prim_sem_env ffi) = (s0, env)` (HOL's
`prim_sem_env_eq` step, `backendProofScript.sml:3576`). -/
theorem primSemEnv_the_ffi {F : Type} [Nonempty F] (ffi : HolFfiState F) (s0 : State F)
    (env : SemEnv Value) (h : holThe (primSemEnv ffi) = (s0, env)) : s0.ffi = ffi := by
  rw [PrimSemEnv.primSemEnvEq] at h
  simp only [holThe, Prod.mk.injEq] at h
  rw [← h.1]

/-- A non-failing source program has exactly one behaviour, so a behaviour of it
determines its whole behaviour set (HOL's `semantics_prog_deterministic` step,
`backendProofScript.sml:3587-3592`). -/
theorem semanticsProg_eq_singleton {F : Type} (s : State F) (env : SemEnv Value)
    (prog : List AstHOL.Dec) (b : HolBehaviour) (hb : semanticsProg s env prog b) :
    semanticsProg s env prog = (fun b' => b' = b) := by
  funext b'
  apply propext
  constructor
  · intro hb'
    exact SemanticsProps.semanticsProg_deterministic s env prog b' b ⟨hb', hb⟩
  · rintro rfl
    exact hb

/-- The source-to-closure block of HOL `compile_correct'`
(`backendProofScript.sml:3570-3612`): `source_eval_to_flat_semantics`, then
`flat_semantics`. The source behaviour set is the singleton of the closure
semantics of the compiled program under the `cake_orac` flat oracle. -/
theorem compileCorrectPrime_sourceToClos {width : Nat} [NeZero width] {F : Type} [Nonempty F]
    (hsrc : SourceEvalToFlatSemanticsStmt width F)
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (bytes : List (BitVec 8)) (bitmaps : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) (ffi : HolFfiState F)
    (ev : Option (CompilerInstance Flapjack.Compiler.Backend.Backend.Config))
    (s0 : State F) (env : SemEnv Value)
    (hcomp : BackendDefs.compile asmConf c prog = some (bytes, bitmaps, c'))
    (hprim : holThe (primSemEnv ffi) = (s0, env))
    (hnf : ¬ semanticsProg (addEvalState ev s0) env prog .fail)
    (hok : backendConfigOk asmConf c) (hwf : optEvalConfigWf asmConf c' ev) :
    ∃ syn : Nat → (Nat × Nat) × List AstHOL.Dec,
      semanticsProg (addEvalState ev s0) env prog =
        (fun b => b = ClosSem.semantics ffi c.closConf.maxApp HolFiniteMapExact.holEmpty
          (pureCo FlatToClos.incCompileDecs ∘
            cakeOrac asmConf c' syn (Prod.snd ∘ configTuple1) (fun ps => ps.flatProg))
          (ClosToBvl.compileCommonInc c.closConf
            (pureCc (ClosToBvl.compileInc c.closConf.maxApp)
              (BvlToBvi.Proofs.fullCc c.bvlConf (pureCc BviToData.compileProg
                (backendFromDataTupleCc asmConf c)))))
          (FlatToClos.compileProg
            (SourceToFlat.compileTotal Flapjack.Compiler.Backend.Backend.primSrcConfig
              (SourceToSource.compile prog)).2)) := by
  have hsrcConf : c.sourceConf = Flapjack.Compiler.Backend.Backend.primSrcConfig := hok.1
  have hmax : 0 < c.closConf.maxApp := hok.2.1
  have hperf : c.stackConf.perfCalls = false := hok.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨syn, hsem⟩ := hsrc ev s0 env prog asmConf c bytes bitmaps c'
    (SourceToFlat.compileTotal Flapjack.Compiler.Backend.Backend.primSrcConfig
      (SourceToSource.compile prog)).1
    (SourceToFlat.compileTotal Flapjack.Compiler.Backend.Backend.primSrcConfig
      (SourceToSource.compile prog)).2 ffi
    ⟨hnf, hcomp, rfl, hprim, hwf, hperf, hsrcConf⟩
  have hffi := primSemEnv_the_ffi ffi s0 env hprim
  rw [hffi] at hsem
  refine ⟨syn, ?_⟩
  rw [semanticsProg_eq_singleton _ _ _ _ hsem]
  have hflat := flatSemantics asmConf c' syn
    (ClosToBvl.compileCommonInc c.closConf
      (pureCc (ClosToBvl.compileInc c.closConf.maxApp)
        (BvlToBvi.Proofs.fullCc c.bvlConf (pureCc BviToData.compileProg
          (backendFromDataTupleCc asmConf c)))))
    ffi (SourceToFlat.compileTotal Flapjack.Compiler.Backend.Backend.primSrcConfig
      (SourceToSource.compile prog)).2 c.closConf
  simp only at hflat
  have hnfFlat : FlatSem.semantics
      (FlatProps.mkFlatInstallConf (backendFromFlatTupleCc asmConf c)
        (cakeOrac asmConf c' syn (Prod.snd ∘ configTuple1) (fun ps => ps.flatProg))) ffi
      (SourceToFlat.compileTotal Flapjack.Compiler.Backend.Backend.primSrcConfig
        (SourceToSource.compile prog)).2 ≠ .fail := by
    intro hfail
    rw [hfail] at hsem
    exact hnf hsem
  rw [hflat ⟨hnfFlat, hmax, SourceToFlat.noMat_compileTotal _ _⟩]
  rfl

end Flapjack.Compiler.Backend.BackendProof.Draft
