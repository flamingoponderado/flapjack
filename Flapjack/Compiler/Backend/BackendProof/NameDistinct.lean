module

public import Flapjack.Compiler.Backend.BackendProof.CakeOrac
public import Flapjack.Compiler.Backend.BackendProof.ConfigTuple
public import Flapjack.Compiler.Backend.BackendProof.CakeOracNames
public import Flapjack.Compiler.Backend.BackendProof.CakeOracConfig
public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.FullOracleDistinct
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.BvlOracle
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.MtiInvariants
public import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileKeys
public import Flapjack.Compiler.Backend.BviTailrec.Proofs.CodeLabels
public import Flapjack.Compiler.Backend.BviTmc.Proofs.CodeRelation

@[expose] public section

set_option autoImplicit false

/-! backendProofScript.sml 1197-1282: function names of the BVL, BVI and
stack programs produced by `cake_orac` are distinct, and the per-function word
optimiser is an instance of `word_to_word$compile`. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.BackendDefs
open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.ClosKnown

/-- Exact HOL `bvl_to_bvi_compile_inc_all_DISTINCT` (`backendProofScript.sml:1223-1238`).
`bvl_to_bvi_compile_inc_all` is the reviewed `BvlToBvi.bvlToBviCompileIncAll`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "bvl_to_bvi_compile_inc_all_DISTINCT"]
theorem bvlToBviCompileIncAll_distinct (c : BvlToBvi.Config) (p : List (Nat × Nat × Bvl.Exp))
    (c' : BvlToBvi.Config) (p' : List (Nat × Nat × Bvi.Exp)) :
    BvlToBvi.bvlToBviCompileIncAll c p = (c', p') ∧ (p.map Prod.fst).Nodup ∧
      c.nextName2 % bvlToBviNamespaces = 2 ∧ c.nextName3 % bvlToBviNamespaces = 3 →
      (p'.map Prod.fst).Nodup := by
  rintro ⟨h, hd, h2, h3⟩
  have := BvlToBvi.Proofs.fullCo_distinctNames c
    (fun _ : Unit => ((c.inlines, c.nextName1, c.nextName2, c.nextName3, c.bviInlines, ()), p))
    () ⟨hd, h2, h3⟩
  have hp : (BvlToBvi.bvlToBviCompileIncAll c p).2 = p' := by rw [h]
  rw [← hp]
  exact this

/-- Exact HOL `MAP_full_compile_single_to_compile` (`backendProofScript.sml:1269-1282`).
HOL `Abbrev P` is `P` (`markerTheory.Abbrev_def`); free variables explicit. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "MAP_full_compile_single_to_compile"
  (words_as_type_indexed_bitvec)]
theorem mapFullCompileSingle_to_compile {width : Nat} [NeZero width]
    (pp pp0 : List (Nat × Nat × WordLangProgHOL (BitVec width))) (asmC : AsmConfigExact width)
    (regCount regAlg : Nat) :
    pp = pp0.map (fun p => WordToWord.fullCompileSingle asmC.twoRegArith regCount regAlg asmC
        (p, none)) ∧
      regCount = asmC.regCount - (asmC.avoidRegs.length + 5) →
    ∃ (wc : WordToWord.Config) (ign : List (Option (Spt Nat))),
      WordToWord.compile wc asmC pp0 = (ign, pp) := by
  rintro ⟨rfl, rfl⟩
  refine ⟨⟨regAlg, []⟩, (WordToWord.compile ⟨regAlg, []⟩ asmC pp0).1, Prod.ext rfl ?_⟩
  simp only [WordToWord.compile, WordToWord.nextNOracle, List.length_nil]
  have hz : ∀ l : List (Nat × Nat × WordLangProgHOL (BitVec width)),
      l.zip (List.replicate l.length (none : Option (Spt Nat))) = l.map (fun p => (p, none)) := by
    intro l; induction l with
    | nil => rfl
    | cons a t ih => simp [List.replicate_succ, ih]
  have hk : asmC.regCount - (5 + asmC.avoidRegs.length) =
      asmC.regCount - (asmC.avoidRegs.length + 5) := by omega
  by_cases h0 : pp0.length ≤ 0
  · have : pp0 = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rfl
  · simp only [if_neg h0, hz, List.map_map, hk]
    rfl

/-- Exact HOL `cake_orac_bvl_ALL_DISTINCT` (`backendProofScript.sml:1197-1213`).
HOL's free `asm_conf c prog b bm c' syntax f n` are explicit (`syntax` is
`syntaxOrac`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "cake_orac_bvl_ALL_DISTINCT"
  (words_as_type_indexed_bitvec)]
theorem cakeOrac_bvl_allDistinct {width : Nat} [NeZero width] {β : Type}
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config)
    (syntaxOrac : Nat → (Nat × Nat) × List AstHOL.Dec)
    (f : Flapjack.Compiler.Backend.Backend.Config → β) (n : Nat) :
    BackendDefs.compile asmConf c prog = some (b, bm, c') →
      ((cakeOrac asmConf c' syntaxOrac f (fun ps => ps.bvlProg) n).2.map Prod.fst).Nodup := by
  intro _
  rw [cakeOrac_eq_pair]
  generalize hC : cakeConfigs asmConf c' syntaxOrac n = C
  let flat := (SourceToFlat.incCompile (syntaxOrac n).1 C.sourceConf
    (SourceToSource.compile (syntaxOrac n).2)).2
  let orac : Nat → (Nat × Spt ClosKnown.ValApprox × Unit) × ClosSem.Program := fun _ =>
    ((C.closConf.nextLoc, ClosKnown.optionValApproxSpt C.closConf.knownConf, ()),
      ClosMti.condCompileInc C.closConf.doMti C.closConf.maxApp
        (FlatToClos.incCompileDecs (α := Nat × Nat × ClosLang.Exp) flat))
  have hempty : (orac 0).2.2 = [] := by
    simp only [orac, ClosToBvl.snd_condMtiCompileInc]
    split <;> rfl
  have key := ClosToBvl.compileInc_phases_allDistinct orac 0 C.closConf.maxApp
    C.closConf.doCall C.closConf.callState.1 C.closConf.knownConf hempty
  rw [knownCo_eq_stateCo_inc] at key
  exact key

/-- The word-to-word optimiser keeps function names (Flapjack infrastructure). -/
theorem map_fst_fullCompileSingle {width : Nat} [NeZero width] (t : Bool) (rc alg : Nat)
    (ac : AsmConfigExact width) (l : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    (l.map fun p => WordToWord.fullCompileSingle t rc alg ac (p, none)).map Prod.fst =
      l.map Prod.fst := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    obtain ⟨x, y, z⟩ := a
    simp only [List.map_cons, ih]
    rfl

/-- Data-to-word part compilation keeps function names (Flapjack infrastructure). -/
theorem map_fst_compilePart {width : Nat} [NeZero width] (dc : DataToWord.Config)
    (l : List (Nat × Nat × DataLang.Prog)) :
    (l.map (DataToWord.compilePart (width := width) dc)).map Prod.fst = l.map Prod.fst := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, ih]; rfl

/-- BVI-to-data compilation keeps function names (Flapjack infrastructure). -/
theorem map_fst_bviToDataCompileProg (l : List (Nat × Nat × Bvi.Exp)) :
    (BviToData.compileProg l).map Prod.fst = l.map Prod.fst := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [BviToData.compileProg, List.map_cons] at ih ⊢; rw [ih]; rfl

/-- Exact HOL `cake_orac_stack_ALL_DISTINCT` (`backendProofScript.sml:1240-1267`).
The configuration projection `SND ∘ SND ∘ SND ∘ SND ∘ SND ∘ SND ∘ config_tuple2`
is written as the composite of `Prod.snd` with `configTuple2`; `syntax` is
`syntaxOrac`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "cake_orac_stack_ALL_DISTINCT"
  (words_as_type_indexed_bitvec)]
theorem cakeOrac_stack_allDistinct {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config)
    (syntaxOrac : Nat → (Nat × Nat) × List AstHOL.Dec) (n : Nat) :
    BackendDefs.compile asmConf c prog = some (b, bm, c') →
      ((cakeOrac asmConf c' syntaxOrac
          (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ configTuple2)
          (fun ps => (ps.stackProg, ps.curBm)) n).2.1.map Prod.fst).Nodup := by
  intro h
  have hbvl := cakeOrac_bvl_allDistinct asmConf c prog b bm c' syntaxOrac id n h
  rw [cakeOrac_eq_pair] at hbvl ⊢
  generalize hC : cakeConfigs asmConf c' syntaxOrac n = C at hbvl ⊢
  obtain ⟨⟨r2, hr2⟩, ⟨r3, hr3⟩⟩ := compile_nextNames asmConf c prog b bm c' h
  have m2 : C.bvlConf.nextName2 % bvlToBviNamespaces = 2 := by
    rw [← hC, configs_nn2_modNamespaces]
    rcases hc : BviTailrec.compileProgSource c.bvlConf.doTailrec (bvlNumStubs + 2) r2 with ⟨n1, ys⟩
    obtain ⟨k, hk⟩ := BviTailrec.Proofs.compileProg_nextMono _ _ _ n1 ys hc
    rw [hr2, hc]
    simp only [hk, bvlNumStubs, dataNumStubs, wordNumStubs, stackNumStubs,
      Flapjack.bvlToBviNamespaces]
    omega
  have m3 : C.bvlConf.nextName3 % bvlToBviNamespaces = 3 := by
    rw [← hC, configs_nn3_modNamespaces]
    rcases hc : BviTmc.compileProgSource c.bvlConf.doTmc (bvlNumStubs + 3) r3 with ⟨n1, ys⟩
    obtain ⟨k, hk⟩ := BviTmc.compileProgSource_next_mono _ _ n1 r3 ys hc
    rw [hr3, hc]
    simp only [hk, bvlNumStubs, dataNumStubs, wordNumStubs, stackNumStubs,
      Flapjack.bvlToBviNamespaces]
    omega
  have hd := bvlToBviCompileIncAll_distinct C.bvlConf
    (compileIncProgs true asmConf C (syntaxOrac n)).2.bvlProg _ _ ⟨rfl, hbvl, m2, m3⟩
  show (((compileIncProgs true asmConf C (syntaxOrac n)).2.stackProg).map Prod.fst).Nodup
  revert hd
  generalize hP : (compileIncProgs true asmConf C (syntaxOrac n)).2.bvlProg = P
  intro hd
  unfold compileIncProgs at hP ⊢
  simp only [keepProgs_true, id] at hP ⊢
  subst hP
  rw [WordToStackProofs.mapFstCompileWordToStack _ _ _ _ _ _ _ (Prod.mk.eta).symm]
  rw [map_fst_fullCompileSingle, map_fst_compilePart, map_fst_bviToDataCompileProg]
  exact hd

end Flapjack.Compiler.Backend.BackendProof
