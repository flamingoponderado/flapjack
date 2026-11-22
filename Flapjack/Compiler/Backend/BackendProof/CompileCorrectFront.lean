import Flapjack.Compiler.Backend.BackendProof.CompileCorrectPrereqs
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.NoMat
import Flapjack.Compiler.Backend.BackendProof.FromConfEx
import Flapjack.Compiler.Backend.BackendProof.CakeOracEqs
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.WholeSemantics
import Flapjack.Compiler.Backend.BackendProof.BvlToBviSemantics2
import Flapjack.Compiler.Backend.BackendProof.NameDistinct
import Flapjack.Compiler.Backend.BackendProof.StateOracle

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

/-- `from_bvi` keeps the closure, BVL, data and stack configurations (the
`from_EXS` chain `from_bvi_conf_EX` ... `from_lab_conf_EX`). -/
theorem fromBvi_confs {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Flapjack.Compiler.Backend.Backend.Config) (names : Spt Basis.Pure.MlString.MlString)
    (p : List (Nat × Nat × Bvi.Exp)) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config)
    (h : fromBvi asmConf c names p = some (b, bm, c')) :
    c'.closConf = c.closConf ∧ c'.bvlConf = c.bvlConf ∧ c'.dataConf = c.dataConf ∧
      c'.stackConf = c.stackConf ∧ c'.sourceConf = c.sourceConf := by
  obtain ⟨p1, h1⟩ := fromBvi_confEx asmConf c names p _ h
  obtain ⟨wcu, p2, h2⟩ := fromData_confEx asmConf c names p1 _ h1
  obtain ⟨wc, p3, bm3, h3⟩ := fromWord_confEx asmConf _ names p2 _ h2
  obtain ⟨p4, h4⟩ := fromStack_confEx asmConf _ names p3 bm3 _ h3
  obtain ⟨lc, rfl⟩ := fromLab_confEx asmConf _ names p4 bm3 b bm c' h4
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The source-to-closure unfolding of `compile` (`compile_eq_from_source`,
`from_source_def`, `from_flat_def`, `from_clos_def`). -/
theorem compile_fromBvl {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Flapjack.Compiler.Backend.Backend.Config) (prog : List AstHOL.Dec) :
    BackendDefs.compile asmConf c prog =
      let cs := { c with sourceConf :=
        (SourceToFlat.compileTotal c.sourceConf (SourceToSource.compile prog)).1 }
      let r := ClosToBvl.compileSource c.closConf
        (FlatToClos.compileProg
          (SourceToFlat.compileTotal c.sourceConf (SourceToSource.compile prog)).2)
      fromBvl asmConf { cs with closConf := r.1 } r.2.2 r.2.1 := by
  rw [compile_eq_fromSource]
  rfl

/-- The closure-to-BVL block of HOL `compile_correct'`
(`backendProofScript.sml:3614-3650`): `clos_to_bvlProof$compile_semantics`
at the `cake_orac` closure oracle (`cake_orac_eqs`), with its syntactic oracle
premise from `cake_orac_clos_syntax_oracle_ok` (hypothesis). -/
theorem compileCorrectPrime_closToBvl {width : Nat} [NeZero width] {F : Type}
    (hclos : CakeOracClosSyntaxOracleOkStmt width)
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (bytes : List (BitVec 8)) (bitmaps : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) (ffi : HolFfiState F)
    (syn : Nat → (Nat × Nat) × List AstHOL.Dec)
    (hcomp : BackendDefs.compile asmConf c prog = some (bytes, bitmaps, c'))
    (hok : backendConfigOk asmConf c)
    (cc : BvlSem.Compiler (Spt (Nat × Bvl.Exp) × Nat × Nat × Nat × Spt (Nat × Bvi.Exp) × Nat ×
      LabToTarget.Config)) :
    let es := FlatToClos.compileProg
      (SourceToFlat.compileTotal Flapjack.Compiler.Backend.Backend.primSrcConfig
        (SourceToSource.compile prog)).2
    let r := ClosToBvl.compileSource c.closConf es
    ClosSem.semantics ffi c.closConf.maxApp HolFiniteMapExact.holEmpty
        (pureCo FlatToClos.incCompileDecs ∘
          cakeOrac asmConf c' syn (Prod.snd ∘ configTuple1) (fun ps => ps.flatProg))
        (ClosToBvl.compileCommonInc c.closConf
          (pureCc (ClosToBvl.compileInc c.closConf.maxApp) cc)) es ≠ .fail →
    BvlSem.semantics ffi (sptFromAList r.2.1)
        (cakeOrac asmConf c' syn configTuple2 (fun ps => ps.bvlProg)) cc r.1.start =
      ClosSem.semantics ffi c.closConf.maxApp HolFiniteMapExact.holEmpty
        (pureCo FlatToClos.incCompileDecs ∘
          cakeOrac asmConf c' syn (Prod.snd ∘ configTuple1) (fun ps => ps.flatProg))
        (ClosToBvl.compileCommonInc c.closConf
          (pureCc (ClosToBvl.compileInc c.closConf.maxApp) cc)) es := by
  intro es r hnf
  have hsrcConf : c.sourceConf = Flapjack.Compiler.Backend.Backend.primSrcConfig := hok.1
  have hmax : 0 < c.closConf.maxApp := hok.2.1
  have eqs := cakeOrac_eqs (β := Nat × Spt ClosKnown.ValApprox × NumSet × _) asmConf c' syn
    (Prod.snd ∘ configTuple1) c prog bytes bitmaps c.closConf c.bvlConf
    (Prod.snd ∘ configTuple1) c.dataConf false 0 0 (Prod.snd ∘ configTuple1)
    c.stackConf.regNames false 0 (0, 0) (Prod.snd ∘ configTuple1)
  have hco := eqs.2.1
  have hbvl := eqs.2.2.1 ⟨hcomp, rfl⟩
  rw [hco] at hnf ⊢
  -- the final closure configuration is the compiled one with a new start
  have hfin : ∃ st, c'.closConf = { r.1 with start := st } := by
    have h := hcomp
    rw [compile_fromBvl] at h
    simp only at h
    rw [hsrcConf] at h
    obtain ⟨st, bvlcu, names, p, hb⟩ := fromBvl_confEx asmConf _ _ _ _ h
    exact ⟨st, (fromBvi_confs asmConf _ names p bytes bitmaps c' hb).1⟩
  have hsyn := hclos asmConf c prog bytes bitmaps c' c.closConf r.1 es r.2 syn
    ⟨hcomp, rfl, hfin, rfl, by simp [es, Backend.toClos, Backend.toFlat, hsrcConf], hmax, hsrcConf⟩
  have hsem := ClosToBvl.compile_semantics ffi c.closConf r.1
    (cakeOrac asmConf c' syn (Prod.snd ∘ configTuple1) (fun ps => ps.closProg)) cc es r.2.1 r.2.2
    ⟨hnf, rfl, hsyn⟩
  rw [← hsem, hbvl]

/-- The BVL-to-BVI block of HOL `compile_correct'`
(`backendProofScript.sml:3652-3690`): `bvl_to_bvi_compile_semantics2` at the
`cake_orac` BVL oracle, then `bvl_to_bvi_orac_eq` (`cake_orac_eqs`). -/
theorem compileCorrectPrime_bvlToBvi {width : Nat} [NeZero width] {F : Type}
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (bytes : List (BitVec 8)) (bitmaps : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) (ffi : HolFfiState F)
    (syn : Nat → (Nat × Nat) × List AstHOL.Dec)
    (hcomp : BackendDefs.compile asmConf c prog = some (bytes, bitmaps, c'))
    (hok : backendConfigOk asmConf c)
    (cc : BviSem.Compiler (Nat × LabToTarget.Config))
    (rc : ClosToBvl.Config) (rp : List (Nat × Nat × Bvl.Exp))
    (rn : Spt Basis.Pure.MlString.MlString)
    (hr : ClosToBvl.compileSource c.closConf (FlatToClos.compileProg
      (SourceToFlat.compileTotal Flapjack.Compiler.Backend.Backend.primSrcConfig
        (SourceToSource.compile prog)).2) = (rc, rp, rn))
    (s : Nat) (q' : List (Nat × Nat × Bvi.Exp)) (l : Spt (Nat × Bvl.Exp))
    (bl : Spt (Nat × Bvi.Exp)) (n1 n2 n3 : Nat) (names1 : Spt Basis.Pure.MlString.MlString)
    (hq : BvlToBvi.compileSource rc.start c.bvlConf rn rp = (s, q', l, bl, n1, n2, n3, names1))
    (hnf : BvlSem.semantics ffi (sptFromAList rp)
        (cakeOrac asmConf c' syn configTuple2 (fun ps => ps.bvlProg))
        (BvlToBvi.Proofs.fullCc c.bvlConf cc) rc.start ≠ .fail) :
    BviSem.semantics ffi (sptFromAList q')
        (cakeOrac asmConf c' syn
          (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ configTuple2)
          (fun ps => ps.bviProg)) cc s =
      BvlSem.semantics ffi (sptFromAList rp)
        (cakeOrac asmConf c' syn configTuple2 (fun ps => ps.bvlProg))
        (BvlToBvi.Proofs.fullCc c.bvlConf cc) rc.start := by
  have hsrcConf : c.sourceConf = Flapjack.Compiler.Backend.Backend.primSrcConfig := hok.1
  have eqs := cakeOrac_eqs (β := Nat) asmConf c' syn (fun _ => 0) c prog bytes bitmaps
    c.closConf c.bvlConf (fun _ => 0) c.dataConf false 0 0 (fun _ => 0)
    c.stackConf.regNames false 0 (0, 0) (fun _ => 0)
  rw [← eqs.2.2.2.1 ⟨hcomp, rfl⟩]
  have h := hcomp
  rw [compile_fromBvl] at h
  simp only [hsrcConf, hr] at h
  simp only [fromBvl, hq] at h
  have hbvlConf := (fromBvi_confs asmConf _ _ _ bytes bitmaps c' h).2.1
  have hco0 : ∃ v, (cakeOrac asmConf c' syn configTuple2 (fun ps => ps.bvlProg) 0).1 =
      (l, n1, n2, n3, bl, v) := by
    refine ⟨(c'.wordConf.bitmapsLength, c'.labConf), ?_⟩
    rw [cakeOrac_zero]
    simp only [configTuple2, hbvlConf]
  have hdist := ClosToBvl.compileSource_allDistinct c.closConf _ rc rp rn hr
  exact bvlToBvi_compileSemantics2 rc.start c.bvlConf rn rp s q' l bl n1 n2 n3
    names1 (cakeOrac asmConf c' syn configTuple2 (fun ps => ps.bvlProg)) ffi cc
    ⟨hq, hco0, fun n => cakeOrac_bvl_allDistinct asmConf c prog bytes bitmaps c' syn
        configTuple2 n hcomp, hdist,
      isStateOracle_tailrec_cakeOrac asmConf c prog bytes bitmaps c' syn hcomp,
      isStateOracle_tmc_cakeOrac asmConf c prog bytes bitmaps c' syn hcomp⟩ hnf

end Flapjack.Compiler.Backend.BackendProof.Draft
