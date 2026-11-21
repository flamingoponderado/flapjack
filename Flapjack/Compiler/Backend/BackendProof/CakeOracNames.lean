module

public import Flapjack.Compiler.Backend.BackendProof.CakeOrac
public import Flapjack.Compiler.Backend.BackendProof.CakeOracConfig
public import Flapjack.Compiler.Backend.BackendProof.ConfigOk
public import Flapjack.Compiler.Backend.BackendProps.Pure
public import Flapjack.Compiler.Backend.BviTailrec.Proofs.CodeLabels
public import Flapjack.Compiler.Backend.BviTmc.Proofs.CodeRelation
public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileIncLemma
public import Flapjack.Compiler.Backend.BviInline.Proofs.CodeLabels

@[expose] public section

/-! backendProofScript.sml 735-1001: projections and invariants of the
incremental oracle `cake_orac`, and the fresh-name and stub-bound facts for
the BVL-to-BVI names it produces. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.Backend
open Flapjack.Compiler.Backend.BackendDefs Flapjack.Compiler.Backend.BackendProps

/-- Exact HOL `cake_orac_eq_I` (`backendProofScript.sml:735-739`). HOL
`f ## g` is `Prod.map f g` and `I` is `id`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "cake_orac_eq_I"
  (words_as_type_indexed_bitvec)]
theorem cakeOrac_eq_id {width : Nat} [NeZero width] {α γ : Type}
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (syn : Nat → (Nat × Nat) × List AstHOL.Dec) :
    ∀ (f : Flapjack.Compiler.Backend.Backend.Config → α) (g : BackendProgs width → γ),
      cakeOrac asmConf c syn f g = Prod.map f g ∘ cakeOrac asmConf c syn id id := by
  intro f g
  funext i
  rfl

/-- Exact HOL `cake_orac_invariant` (`backendProofScript.sml:741-750`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "cake_orac_invariant"
  (words_as_type_indexed_bitvec)]
theorem cakeOrac_invariant {width : Nat} [NeZero width] {α γ : Type}
    (P : α → Prop) (f : Flapjack.Compiler.Backend.Backend.Config → α)
    (c : Flapjack.Compiler.Backend.Backend.Config) (asmConf : AsmConfigExact width)
    (syn : Nat → (Nat × Nat) × List AstHOL.Dec) (g : BackendProgs width → γ) :
    P (f c) ∧
      (∀ (c : Flapjack.Compiler.Backend.Backend.Config) (prog : (Nat × Nat) × List AstHOL.Dec),
        P (f c) → P (f (compileIncProgs true asmConf c prog).1)) →
      ∀ i, P (cakeOrac asmConf c syn f g i).1 := by
  intro ⟨h0, hstep⟩ i
  show P (f (cakeConfigs asmConf c syn i))
  induction i with
  | zero => exact h0
  | succ n ih => exact hstep _ _ ih

/-- Exact HOL `compile_no_stubs_wrap_pure_co` (`backendProofScript.sml:822-830`).
The oracle index, configuration and bitmap types are independent, as
captured; the unused third component is discarded as in HOL. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "compile_no_stubs_wrap_pure_co"
  (words_as_type_indexed_bitvec)]
theorem compileNoStubs_wrapPureCo {width : Nat} [NeZero width] {α β δ : Type}
    (coracle : α → β × List (Nat × StackLang.HolProg width) × δ) (rn : Spt Nat) (j : Bool)
    (offs : BitVec width × BitVec width) (sp : Nat) :
    (fun n => let (c, p, _b) := coracle n
      (c, StackToLab.compileNoStubs rn j offs sp p)) =
      pureCo (StackToLab.compileNoStubs rn j offs sp ∘ Prod.fst) ∘ coracle := by
  funext n
  rfl

/-- Flapjack helper: threading a fresh-name pass keeps every state at least
its initial value. -/
private theorem stateOracStates_tailrec_ge (doIt : Bool) (nn2 : Nat)
    (orac : Nat → List (Nat × Nat × Bvi.Exp)) (n : Nat) :
    nn2 ≤ stateOracStates (BviTailrec.compileProgSource doIt) nn2 orac n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
      simp only [stateOracStates]
      rcases hc : BviTailrec.compileProgSource doIt
          (stateOracStates (BviTailrec.compileProgSource doIt) nn2 orac n) (orac n) with ⟨n1, ys⟩
      obtain ⟨k, hk⟩ := BviTailrec.Proofs.compileProg_nextMono doIt _ _ n1 ys hc
      simp only
      omega

/-- Exact HOL `data_num_stubs_LE_tailrec_compile` (`backendProofScript.sml:835-859`).
HOL `EVERY ($<= d) l` is `∀ x ∈ l, d ≤ x`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "data_num_stubs_LE_tailrec_compile"]
theorem dataNumStubs_le_tailrecCompile (nn2 : Nat) (orac : Nat → List (Nat × Nat × Bvi.Exp))
    (n : Nat) (doIt : Bool) :
    dataNumStubs ≤ nn2 ∧ (∀ x ∈ (orac n).map Prod.fst, dataNumStubs ≤ x) →
      ∀ x ∈ (stateCoProgs (BviTailrec.compileProgSource doIt) nn2 orac n).map Prod.fst,
        dataNumStubs ≤ x := by
  intro ⟨hnn, horac⟩ x hx
  simp only [stateCoProgs] at hx
  rcases hc : BviTailrec.compileProgSource doIt
      (stateOracStates (BviTailrec.compileProgSource doIt) nn2 orac n) (orac n) with ⟨n1, ys⟩
  rw [hc] at hx
  rcases BviTailrec.Proofs.compileProg_mem doIt _ _ n1 ys x ⟨hc, hx⟩ with h | ⟨hle, -, -⟩
  · exact horac x h
  · have := stateOracStates_tailrec_ge doIt nn2 orac n
    omega

/-- Exact HOL `data_num_stubs_LE_bvl_bvi_compile` (`backendProofScript.sml:861-874`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "data_num_stubs_LE_bvl_bvi_compile"]
theorem dataNumStubs_le_bvlBviCompile (nn1 : Nat) (orac : Nat → List (Nat × Nat × Bvl.Exp))
    (n : Nat) :
    ∀ x ∈ (stateCoProgs BvlToBvi.compileIncSource nn1 orac n).map Prod.fst,
      dataNumStubs ≤ x := by
  intro x hx
  simp only [stateCoProgs] at hx
  rcases hc : BvlToBvi.compileIncSource
      (stateOracStates BvlToBvi.compileIncSource nn1 orac n) (orac n) with ⟨n2, ys⟩
  rw [hc] at hx
  have hr := BvlToBvi.Proofs.compileInc_nextRange _ _ n2 ys x ⟨hc, hx⟩
  have hd : dataNumStubs ≤ bvlNumStubs := by unfold bvlNumStubs; omega
  split at hr
  · omega
  · omega

/-- Flapjack helper: the BVL configuration after one incremental compilation. -/
private theorem compileIncProgs_bvlConf {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (p : (Nat × Nat) × List AstHOL.Dec) :
    ∃ q, (compileIncProgs true asmConf c p).1.bvlConf =
      (BvlToBvi.bvlToBviCompileIncAll c.bvlConf q).1 := by
  obtain ⟨e, d⟩ := p
  exact ⟨_, rfl⟩

/-- Exact HOL `configs_nn2_MULT_namespaces` (`backendProofScript.sml:876-888`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "configs_nn2_MULT_namespaces"
  (words_as_type_indexed_bitvec)]
theorem configs_nn2_mulNamespaces {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c' : Flapjack.Compiler.Backend.Backend.Config)
    (syn : Nat → (Nat × Nat) × List AstHOL.Dec) (n : Nat) :
    ∃ k, (cakeConfigs asmConf c' syn n).bvlConf.nextName2 =
      c'.bvlConf.nextName2 + k * bvlToBviNamespaces := by
  induction n with
  | zero => exact ⟨0, by simp [cakeConfigs, stateOracStates]⟩
  | succ n ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨q, hq⟩ := compileIncProgs_bvlConf asmConf (cakeConfigs asmConf c' syn n)
        (syn n)
      have hstep : (cakeConfigs asmConf c' syn (n + 1)).bvlConf =
          (BvlToBvi.bvlToBviCompileIncAll (cakeConfigs asmConf c' syn n).bvlConf q).1 := hq
      have h2 : ∃ r, (BvlToBvi.bvlToBviCompileIncAll
            (cakeConfigs asmConf c' syn n).bvlConf q).1.nextName2 =
          (BviTailrec.compileProgSource (cakeConfigs asmConf c' syn n).bvlConf.doTailrec
            (cakeConfigs asmConf c' syn n).bvlConf.nextName2 r).1 := ⟨_, rfl⟩
      obtain ⟨r, hr⟩ := h2
      rcases hc : BviTailrec.compileProgSource (cakeConfigs asmConf c' syn n).bvlConf.doTailrec
          (cakeConfigs asmConf c' syn n).bvlConf.nextName2 r with ⟨n1, ys⟩
      obtain ⟨j, hj⟩ := BviTailrec.Proofs.compileProg_nextMono _ _ _ n1 ys hc
      rw [hc] at hr
      refine ⟨k + j, ?_⟩
      rw [hstep, hr, hj, hk, Nat.add_mul]
      simp only [Flapjack.bvlToBviNamespaces]
      omega

/-- Exact HOL `configs_nn2_MOD_namespaces` (`backendProofScript.sml:890-898`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "configs_nn2_MOD_namespaces"
  (words_as_type_indexed_bitvec)]
theorem configs_nn2_modNamespaces {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c' : Flapjack.Compiler.Backend.Backend.Config)
    (syn : Nat → (Nat × Nat) × List AstHOL.Dec) (n : Nat) :
    (cakeConfigs asmConf c' syn n).bvlConf.nextName2 % bvlToBviNamespaces =
      c'.bvlConf.nextName2 % bvlToBviNamespaces := by
  obtain ⟨k, hk⟩ := configs_nn2_mulNamespaces asmConf c' syn n
  rw [hk, Nat.add_mul_mod_self_right]

/-- Exact HOL `configs_nn3_MULT_namespaces` (`backendProofScript.sml:900-912`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "configs_nn3_MULT_namespaces"
  (words_as_type_indexed_bitvec)]
theorem configs_nn3_mulNamespaces {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c' : Flapjack.Compiler.Backend.Backend.Config)
    (syn : Nat → (Nat × Nat) × List AstHOL.Dec) (n : Nat) :
    ∃ k, (cakeConfigs asmConf c' syn n).bvlConf.nextName3 =
      c'.bvlConf.nextName3 + k * bvlToBviNamespaces := by
  induction n with
  | zero => exact ⟨0, by simp [cakeConfigs, stateOracStates]⟩
  | succ n ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨q, hq⟩ := compileIncProgs_bvlConf asmConf (cakeConfigs asmConf c' syn n)
        (syn n)
      have hstep : (cakeConfigs asmConf c' syn (n + 1)).bvlConf =
          (BvlToBvi.bvlToBviCompileIncAll (cakeConfigs asmConf c' syn n).bvlConf q).1 := hq
      have h3 : ∃ r, (BvlToBvi.bvlToBviCompileIncAll
            (cakeConfigs asmConf c' syn n).bvlConf q).1.nextName3 =
          (BviTmc.compileProgSource (cakeConfigs asmConf c' syn n).bvlConf.doTmc
            (cakeConfigs asmConf c' syn n).bvlConf.nextName3 r).1 := ⟨_, rfl⟩
      obtain ⟨r, hr⟩ := h3
      rcases hc : BviTmc.compileProgSource (cakeConfigs asmConf c' syn n).bvlConf.doTmc
          (cakeConfigs asmConf c' syn n).bvlConf.nextName3 r with ⟨n1, ys⟩
      obtain ⟨j, hj⟩ := BviTmc.compileProgSource_next_mono _ _ n1 r ys hc
      rw [hc] at hr
      refine ⟨k + j, ?_⟩
      rw [hstep, hr, hj, hk, Nat.add_mul]
      simp only [Flapjack.bvlToBviNamespaces]
      omega

/-- Exact HOL `configs_nn3_MOD_namespaces` (`backendProofScript.sml:914-922`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "configs_nn3_MOD_namespaces"
  (words_as_type_indexed_bitvec)]
theorem configs_nn3_modNamespaces {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c' : Flapjack.Compiler.Backend.Backend.Config)
    (syn : Nat → (Nat × Nat) × List AstHOL.Dec) (n : Nat) :
    (cakeConfigs asmConf c' syn n).bvlConf.nextName3 % bvlToBviNamespaces =
      c'.bvlConf.nextName3 % bvlToBviNamespaces := by
  obtain ⟨k, hk⟩ := configs_nn3_mulNamespaces asmConf c' syn n
  rw [hk, Nat.add_mul_mod_self_right]

/-- Flapjack helper: the fresh-name counters left by a successful compilation
are the outputs of the whole-program tail-recursion and tail-modulo-cons
passes started at `bvl_num_stubs + 2` and `bvl_num_stubs + 3`. -/
theorem compile_nextNames {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config)
    (h : BackendDefs.compile asmConf c prog = some (b, bm, c')) :
    (∃ r, c'.bvlConf.nextName2 =
        (BviTailrec.compileProgSource c.bvlConf.doTailrec (bvlNumStubs + 2) r).1) ∧
      (∃ r, c'.bvlConf.nextName3 =
        (BviTmc.compileProgSource c.bvlConf.doTmc (bvlNumStubs + 3) r).1) := by
  simp only [BackendDefs.compile] at h
  obtain ⟨bytes, lc, -, hr⟩ := attachBitmaps_some _ _ _ _ _ h
  simp only [Prod.mk.injEq] at hr
  obtain ⟨-, -, rfl⟩ := hr
  exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- Exact HOL `configs_nn2_MOD_namespaces_ok` (`backendProofScript.sml:924-936`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "configs_nn2_MOD_namespaces_ok"
  (words_as_type_indexed_bitvec)]
theorem configs_nn2_modNamespacesOk {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) :
    BackendDefs.compile asmConf c prog = some (b, bm, c') ∧ backendConfigOk asmConf c →
      c'.bvlConf.nextName2 % bvlToBviNamespaces = 2 := by
  intro ⟨h, _⟩
  obtain ⟨⟨r, hr⟩, -⟩ := compile_nextNames asmConf c prog b bm c' h
  rcases hc : BviTailrec.compileProgSource c.bvlConf.doTailrec (bvlNumStubs + 2) r with ⟨n1, ys⟩
  obtain ⟨k, hk⟩ := BviTailrec.Proofs.compileProg_nextMono _ _ _ n1 ys hc
  rw [hr, hc]
  simp only [hk, bvlNumStubs, dataNumStubs, wordNumStubs, stackNumStubs,
    Flapjack.bvlToBviNamespaces]
  omega

/-- Exact HOL `configs_nn3_MOD_namespaces_ok` (`backendProofScript.sml:938-950`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "configs_nn3_MOD_namespaces_ok"
  (words_as_type_indexed_bitvec)]
theorem configs_nn3_modNamespacesOk {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) :
    BackendDefs.compile asmConf c prog = some (b, bm, c') ∧ backendConfigOk asmConf c →
      c'.bvlConf.nextName3 % bvlToBviNamespaces = 3 := by
  intro ⟨h, _⟩
  obtain ⟨-, ⟨r, hr⟩⟩ := compile_nextNames asmConf c prog b bm c' h
  rcases hc : BviTmc.compileProgSource c.bvlConf.doTmc (bvlNumStubs + 3) r with ⟨n1, ys⟩
  obtain ⟨k, hk⟩ := BviTmc.compileProgSource_next_mono _ _ n1 r ys hc
  rw [hr, hc]
  simp only [hk, bvlNumStubs, dataNumStubs, wordNumStubs, stackNumStubs,
    Flapjack.bvlToBviNamespaces]
  omega

/-- Exact HOL `bvl_to_bvi_compile_inc_all_num_stubs_LE`
(`backendProofScript.sml:952-976`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml"
  "bvl_to_bvi_compile_inc_all_num_stubs_LE"]
theorem bvlToBviCompileIncAll_numStubsLe (c : BvlToBvi.Config)
    (bvl : List (Nat × Nat × Bvl.Exp)) (c' : BvlToBvi.Config)
    (bvi : List (Nat × Nat × Bvi.Exp)) :
    BvlToBvi.bvlToBviCompileIncAll c bvl = (c', bvi) →
      bvlNumStubs ≤ c.nextName2 ∧ bvlNumStubs ≤ c.nextName3 →
        ∀ x ∈ bvi.map Prod.fst, bvlNumStubs ≤ x := by
  intro h ⟨h2, h3⟩ x hx
  simp only [BvlToBvi.bvlToBviCompileIncAll] at h
  rcases h0 : BvlInline.compileInc c.inlineSizeLimit c.splitMainAtSeq c.expCut c.inlines bvl with
    ⟨inl, p0⟩
  rcases h1 : BvlToBvi.compileIncSource c.nextName1 p0 with ⟨nn1, p1⟩
  rcases ht : BviTailrec.compileProgSource c.doTailrec c.nextName2 p1 with ⟨nn2, p2⟩
  rcases hm : BviTmc.compileProgSource c.doTmc c.nextName3 p2 with ⟨nn3, p3⟩
  rcases hi : BviInline.compileIncSource c.bviInlines p3 with ⟨bl, p4⟩
  simp only [h0, h1, ht, hm, hi, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rw [BviInline.Proofs.compileInc_mapFst _ _ _ _ hi] at hx
  rcases BviTmc.compileProgSource_mem _ _ nn3 x p2 p3 hm hx with hm2 | ⟨hle, -, -⟩
  · rcases BviTailrec.Proofs.compileProg_mem _ _ _ nn2 p2 x ⟨ht, hm2⟩ with hm1 | ⟨hle, -, -⟩
    · have hr := BvlToBvi.Proofs.compileInc_nextRange _ _ nn1 p1 x ⟨h1, hm1⟩
      split at hr <;> omega
    · omega
  · omega

/-- Exact HOL `bvl_num_stubs_LE_bvi_prog` (`backendProofScript.sml:978-1001`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "bvl_num_stubs_LE_bvi_prog"
  (words_as_type_indexed_bitvec)]
theorem bvlNumStubs_le_bviProg {width : Nat} [NeZero width] {β : Type}
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config)
    (syn : Nat → (Nat × Nat) × List AstHOL.Dec)
    (f : Flapjack.Compiler.Backend.Backend.Config → β) (n : Nat) :
    BackendDefs.compile asmConf c prog = some (b, bm, c') →
      ∀ x ∈ (cakeOrac asmConf c' syn f (fun ps => ps.bviProg) n).2.map Prod.fst,
        bvlNumStubs ≤ x := by
  intro h
  obtain ⟨⟨r2, hr2⟩, ⟨r3, hr3⟩⟩ := compile_nextNames asmConf c prog b bm c' h
  rcases hc2 : BviTailrec.compileProgSource c.bvlConf.doTailrec (bvlNumStubs + 2) r2 with
    ⟨n2, ys2⟩
  obtain ⟨k2, hk2⟩ := BviTailrec.Proofs.compileProg_nextMono _ _ _ n2 ys2 hc2
  rcases hc3 : BviTmc.compileProgSource c.bvlConf.doTmc (bvlNumStubs + 3) r3 with ⟨n3, ys3⟩
  obtain ⟨k3, hk3⟩ := BviTmc.compileProgSource_next_mono _ _ n3 r3 ys3 hc3
  rw [hc2] at hr2
  rw [hc3] at hr3
  obtain ⟨j2, hj2⟩ := configs_nn2_mulNamespaces asmConf c' syn n
  obtain ⟨j3, hj3⟩ := configs_nn3_mulNamespaces asmConf c' syn n
  have hq : ∃ q, (cakeOrac asmConf c' syn f (fun ps => ps.bviProg) n).2 =
      keepProgs true
        (BvlToBvi.bvlToBviCompileIncAll (cakeConfigs asmConf c' syn n).bvlConf q).2 := by
    exact ⟨_, rfl⟩
  obtain ⟨q, hq⟩ := hq
  rw [hq]
  simp only [keepProgs, if_true]
  apply bvlToBviCompileIncAll_numStubsLe _ q _ _ rfl
  constructor <;> omega

end Flapjack.Compiler.Backend.BackendProof
