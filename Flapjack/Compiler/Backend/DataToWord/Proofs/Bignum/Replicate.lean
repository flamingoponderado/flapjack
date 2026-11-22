module

public import Flapjack.Compiler.Backend.DataToWord.Stubs
public import Flapjack.Compiler.Backend.DataToWord.Control
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StoreList
public import Flapjack.Compiler.Backend.BackendProps
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate

@[expose] public section

/-! Correctness of the generated word-replication loop `Replicate_code`. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace ReplicateWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end ReplicateWitness

private theorem repSeqAssign {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (k : Nat) (e : WordLangExpHOL (BitVec width))
    (v : WordLocW width) (p : WordLangProgHOL (BitVec width))
    (read : t.wordExp e = some v) :
    WordSemStateFiniteExact.evaluate (.seq (.assign k e) p) t =
      WordSemStateFiniteExact.evaluate p (t.setVar k v) := by
  simp [WordSemStateFiniteExact.evaluate, read, WordSemStateFiniteExact.fixClock,
    WordSemStateFiniteExact.setVar]

private theorem repSeqStore {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (e : WordLangExpHOL (BitVec width)) (v : Nat)
    (a : BitVec width) (w : WordLocW width) (p : WordLangProgHOL (BitVec width))
    (read : t.wordExp e = some (.word a)) (hv : WordSemStateFiniteExact.getVar v t = some w)
    (dom : t.mdomain a = true) :
    WordSemStateFiniteExact.evaluate (.seq (.store e v) p) t =
      WordSemStateFiniteExact.evaluate p
        { t with memory := fun x => if x = a then w else t.memory x } := by
  simp [WordSemStateFiniteExact.evaluate, read, hv, WordSemStateFiniteExact.memStore, dom,
    WordSemStateFiniteExact.fixClock]

private theorem repEvalCall {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (loc arity : Nat) (prog : WordLangProgHOL (BitVec width))
    (args : List Nat) (vals : List (WordLocW width))
    (hcode : sptLookup loc t.code = some (arity, prog)) (hclock : t.clock ≠ 0)
    (hvals : WordSemStateFiniteExact.getVars args t = some vals) (hlen : vals.length = arity)
    (res : WordSemResult width) (s : WordSemStateFiniteExact width C F)
    (hrun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv vals (sptLookup loc t.stackSize)
        (WordSemStateFiniteExact.decClock t)) = (some res, s))
    (hres : wordSemBadFunReturn (some res) = false) :
    WordSemStateFiniteExact.evaluate (.call none (some loc) args none) t = (some res, s) := by
  simp [WordSemStateFiniteExact.evaluate, hvals, wordSemBadDestArgs, wordSemAddRetLoc,
    wordSemFindCode, hcode, hlen, hclock, hrun, hres]

private theorem optMax (x y : Option Nat) : wordSemOptionMax x y = Option.map₂ max x y := by
  cases x <;> cases y <;> rfl

private theorem optAdd (x y : Option Nat) : wordSemOptionAdd x y = Option.map₂ (· + ·) x y := by
  cases x <;> cases y <;> rfl

private theorem maxIdem (x y : Option Nat) :
    Option.map₂ max (Option.map₂ max x y) y = Option.map₂ max x y := by
  cases x <;> cases y <;> simp [Option.map₂]

private theorem optionLe_max_left (x y : Option Nat) : optionLe x (Option.map₂ max x y) := by
  cases x <;> cases y <;> simp [optionLe, Option.map₂]

/-- The loop body, entered with its five registers: Flapjack infrastructure for
`Replicate_code_thm` and `Replicate_code_alt_thm`, with no separate HOL declaration. -/
private theorem replicateBody {width : Nat} [NeZero width] {C F : Type}
    (v : WordLocW width) (l1 l2 : Nat) (ret_val : WordLocW width) :
    ∀ (n : Nat) (a : BitVec width) (s0 : WordSemStateFiniteExact width C F)
      (m1 : BitVec width → WordLocW width),
      sptLookup replicateLocation s0.code = some (5, replicateCode) →
      storeList (a + wordSemBytesInWord) (List.replicate n v) s0.memory s0.mdomain = some m1 →
      sptLookup 0 s0.locals = some (.loc l1 l2) →
      sptLookup 2 s0.locals = some (.word a) →
      sptLookup 4 s0.locals = some v →
      sptLookup 6 s0.locals = some (.word (BitVec.ofNat width (4 * n))) →
      sptLookup 8 s0.locals = some ret_val →
      4 * n < 2 ^ width → n ≤ s0.clock →
      ∃ m : Option Nat,
        WordSemStateFiniteExact.evaluate replicateCode s0 =
          (some (.result (.loc l1 l2) [ret_val]),
            { s0 with memory := m1, clock := s0.clock - n, locals := .ln,
                      localsSize := some 0, stackMax := m }) ∧
        optionLe m (Option.map₂ max s0.stackMax
          (Option.map₂ (· + ·) (wordSemStackSize s0.stack)
            (sptLookup replicateLocation s0.stackSize))) := by
  intro n
  induction n with
  | zero =>
    intro a s0 m1 hcode hstore h0 h2 h4 h6 h8 _ _
    simp only [List.replicate, storeList, Option.some.injEq] at hstore
    subst hstore
    refine ⟨s0.stackMax, ?_, optionLe_max_left _ _⟩
    rw [replicateCode, WordSemStateFiniteExact.evaluate]
    simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.getVars,
      WordSemStateFiniteExact.getVarImm, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL,
      WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.flushState, h0, h6, h8]
  | succ n ih =>
    intro a s0 m1 hcode hstore h0 h2 h4 h6 h8 hbound hclock
    simp only [List.replicate, storeList] at hstore
    split at hstore
    case isFalse => simp at hstore
    rename_i dom
    let B : BitVec width := wordSemBytesInWord
    let s1 := s0.setVar 2 (.word (a + B))
    let s2 := { s1 with memory := fun x => if x = a + B then v else s1.memory x }
    let s3 := s2.setVar 6 (.word (BitVec.ofNat width (4 * n)))
    have sub4 : BitVec.ofNat width (4 * (n + 1)) - 4 = BitVec.ofNat width (4 * n) := by
      rw [show 4 * (n + 1) = 4 * n + 4 by ring, ← BitVec.ofNat_add_ofNat]
      exact BitVec.add_sub_cancel _ _
    have ne0 : (BitVec.ofNat width (4 * (n + 1)) == 0#width) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound] at this
      simp at this
    let vals : List (WordLocW width) :=
      [.loc l1 l2, .word (a + B), v, .word (BitVec.ofNat width (4 * n)), ret_val]
    let s4 := WordSemStateFiniteExact.callEnv vals (sptLookup replicateLocation s3.stackSize)
      (WordSemStateFiniteExact.decClock s3)
    obtain ⟨m, hrun, hle⟩ := ih (a + B) s4 m1 hcode hstore
      (by simp [s4, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup])
      (by simp [s4, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup])
      (by simp [s4, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup])
      (by simp [s4, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup])
      (by simp [s4, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup])
      (by omega)
      (by simp [s4, s3, s2, s1, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.callEnv,
        WordSemStateFiniteExact.decClock]; omega)
    have top : WordSemStateFiniteExact.evaluate replicateCode s0 =
        WordSemStateFiniteExact.evaluate (wordListSeq [
          .assign 2 (.op .add [.var 2, .const (BitVec.ofNat width (width / 8))]),
          .store (.var 2) 4,
          .assign 6 (.op .sub [.var 6, .const 4]),
          .call none (some replicateLocation) [0, 2, 4, 6, 8] none]) s0 := by
      conv_lhs => rw [replicateCode]
      rw [WordSemStateFiniteExact.evaluate]
      simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.getVarImm, wordSemWordCmp,
        Compiler.Encoders.Asm.wordCmpHOL, h6, ne0]
    refine ⟨m, ?_, ?_⟩
    · rw [top]
      simp only [wordListSeq.eq_3, wordListSeq.eq_2]
      rw [repSeqAssign s0 2 _ (.word (a + B)) _ (by
        simp [B, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar, h2, theWords,
          wordOpHOL, wordOp, wordSemBytesInWord])]
      rw [repSeqStore s1 _ 4 (a + B) v _ (by
        simp [s1, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]) (by
        simp [s1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
          sptLookup_sptInsert_ne, h4]) (by simpa [s1, WordSemStateFiniteExact.setVar] using dom)]
      rw [repSeqAssign s2 6 _ (.word (BitVec.ofNat width (4 * n))) _ (by
        simp [s2, s1, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, h6, theWords, wordOpHOL, wordOp]
        exact sub4)]
      rw [repEvalCall s3 replicateLocation 5 replicateCode [0, 2, 4, 6, 8] vals
        (by simpa [s3, s2, s1, WordSemStateFiniteExact.setVar] using hcode)
        (by simp [s3, s2, s1, WordSemStateFiniteExact.setVar]; omega)
        (by simp [s3, s2, s1, vals, WordSemStateFiniteExact.getVars,
          WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
          sptLookup_sptInsert_ne, sptLookup_sptInsert_same, h0, h4, h8])
        rfl _ _ hrun rfl]
      simp [s4, s3, s2, s1, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
        WordSemStateFiniteExact.setVar]
      omega
    · simpa [s4, s3, s2, s1, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
        WordSemStateFiniteExact.setVar, optMax, optAdd, maxIdem] using hle

/-- Running the generated replication loop writes `n` copies of a value after
`a`, returning to the caller's location. HOL's free `v`, `l1`, `l2` and
`ret_val` are explicit leading binders. The evaluator inherits the real-model
assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "Replicate_code_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem replicateCode_thm {width : Nat} [NeZero width] {C F : Type}
    (v : WordLocW width) (l1 l2 : Nat) (ret_val : WordLocW width) :
    ∀ (n : Nat) (a : BitVec width) (r : WordSemStateFiniteExact width C F)
      (m1 : BitVec width → WordLocW width) (a1 a2 a3 a4 a5 : Nat),
      sptLookup replicateLocation r.code = some (5, replicateCode) ∧
      storeList (a + wordSemBytesInWord) (List.replicate n v) r.memory r.mdomain = some m1 ∧
      WordSemStateFiniteExact.getVar a1 r = some (.loc l1 l2) ∧
      WordSemStateFiniteExact.getVar a2 r = some (.word a) ∧
      WordSemStateFiniteExact.getVar a3 r = some v ∧
      WordSemStateFiniteExact.getVar a4 r = some (.word (BitVec.ofNat width (4 * n))) ∧
      WordSemStateFiniteExact.getVar a5 r = some ret_val ∧
      4 * n < 2 ^ width ∧ n < r.clock →
      ∃ m : Option Nat,
        WordSemStateFiniteExact.evaluate
            (.call none (some replicateLocation) [a1, a2, a3, a4, a5] none) r =
          (some (.result (.loc l1 l2) [ret_val]),
            { r with memory := m1, clock := r.clock - n - 1, locals := .ln,
                     localsSize := some 0, stackMax := m }) ∧
        optionLe m (Option.map₂ max r.stackMax
          (Option.map₂ (· + ·) (wordSemStackSize r.stack)
            (sptLookup replicateLocation r.stackSize))) := by
  intro n a r m1 a1 a2 a3 a4 a5 ⟨hcode, hstore, h1, h2, h3, h4, h5, hbound, hclock⟩
  let vals : List (WordLocW width) :=
    [.loc l1 l2, .word a, v, .word (BitVec.ofNat width (4 * n)), ret_val]
  let s0 := WordSemStateFiniteExact.callEnv vals (sptLookup replicateLocation r.stackSize)
    (WordSemStateFiniteExact.decClock r)
  obtain ⟨m, hrun, hle⟩ := replicateBody v l1 l2 ret_val n a s0 m1 hcode hstore
    (by simp [s0, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup])
    (by simp [s0, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup])
    (by simp [s0, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup])
    (by simp [s0, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup])
    (by simp [s0, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup])
    hbound (by simp [s0, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock]; omega)
  refine ⟨m, ?_, ?_⟩
  · rw [repEvalCall r replicateLocation 5 replicateCode [a1, a2, a3, a4, a5] vals hcode
      (by omega) (by simp [vals, WordSemStateFiniteExact.getVars, h1, h2, h3, h4, h5]) rfl _ _
      hrun rfl]
    simp [s0, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock]
    omega
  · simpa [s0, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock, optMax, optAdd,
      maxIdem] using hle

private theorem sptInter_ls_of_lookup {α : Type} (t : Spt α) (x : α)
    (h : sptLookup 0 t = some x) : sptInter t (.ls ()) = .ls x := by
  cases t with
  | ln => simp [sptLookup] at h
  | ls y => simp [sptLookup] at h; subst h; simp [sptInter]
  | bn a b => simp [sptLookup] at h
  | bs a y b => simp [sptLookup] at h; subst h; simp [sptInter]

private theorem sptInter_ln {α : Type} (t : Spt α) : sptInter t (.ln : Spt Unit) = .ln := by
  cases t <;> simp [sptInter]

/-- The returning call into the replication loop: the loop runs as in
`Replicate_code_thm`, then the caller's register 0 is restored. HOL's free `v`,
`l1`, `l2` and `ret_val` are explicit leading binders; its unused universals
`a1 : 'b`, `a5 : 'd` and `var : 'e` are kept over independent types. The
evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "Replicate_code_alt_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem replicateCode_alt_thm {width : Nat} [NeZero width] {C F β δ ε : Type}
    (v : WordLocW width) (l1 l2 : Nat) (ret_val : WordLocW width) :
    ∀ (n : Nat) (a : BitVec width) (r : WordSemStateFiniteExact width C F)
      (m1 : BitVec width → WordLocW width) (_a1 : β) (a2 a3 a4 : Nat) (_a5 : δ) (_var : ε),
      sptLookup replicateLocation r.code = some (5, replicateCode) ∧
      storeList (a + wordSemBytesInWord) (List.replicate n v) r.memory r.mdomain = some m1 ∧
      WordSemStateFiniteExact.getVar a2 r = some (.word a) ∧
      WordSemStateFiniteExact.getVar a3 r = some v ∧
      WordSemStateFiniteExact.getVar a4 r = some (.word (BitVec.ofNat width (4 * n))) ∧
      WordSemStateFiniteExact.getVar 0 r = some ret_val ∧
      4 * n < 2 ^ width ∧ n < r.clock →
      ∃ maxStack : Option Nat,
        WordSemStateFiniteExact.evaluate
            (.call (some ([0], (sptFromList [()], .ln), .skip, l1, l2))
              (some replicateLocation) [a2, a3, a4, 0] none) r =
          (none,
            { r with memory := m1, clock := r.clock - n - 1,
                     locals := sptInsert 0 ret_val .ln, stackMax := maxStack,
                     permute := fun n => r.permute (n + 1) }) := by
  intro n a r m1 _ a2 a3 a4 _ _ ⟨hcode, hstore, h2, h3, h4, h0, hbound, hclock⟩
  have l0 : sptLookup 0 r.locals = some ret_val := h0
  have fl : sptFromList [()] = (.ls () : Spt Unit) := by simp [sptFromList]
  have cut : wordSemCutEnvs (sptFromList [()], (.ln : Spt Unit)) r.locals =
      some (.ls ret_val, .ln) := by
    have sub1 : LoopSemStateFiniteExact.sptSubsetLive (sptFromList [()]) r.locals := by
      intro key hk
      rw [fl, sptMem_ls] at hk
      subst hk
      exact (sptMem_iff_lookup _ _).2 ⟨_, l0⟩
    have sub2 : LoopSemStateFiniteExact.sptSubsetLive (.ln : Spt Unit) r.locals := by
      intro key hk; simp at hk
    rw [fl] at sub1
    simp only [wordSemCutEnvs, wordSemCutNames, fl, sub1, sub2, if_true,
      sptInter_ls_of_lookup _ _ l0, sptInter_ln]
  let vals : List (WordLocW width) :=
    [.loc l1 l2, .word a, v, .word (BitVec.ofNat width (4 * n)), ret_val]
  let pushed := WordSemStateFiniteExact.pushEnv (.ls ret_val, .ln) none
    (WordSemStateFiniteExact.decClock r)
  let s0 := WordSemStateFiniteExact.callEnv vals (sptLookup replicateLocation r.stackSize) pushed
  obtain ⟨m, hrun, _⟩ := replicateBody v l1 l2 ret_val n a s0 m1 hcode
    (by simpa [s0, pushed, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
      WordSemStateFiniteExact.decClock] using hstore)
    (by simp [s0, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup])
    (by simp [s0, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup])
    (by simp [s0, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup])
    (by simp [s0, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup])
    (by simp [s0, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup])
    hbound
    (by simp [s0, pushed, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
      WordSemStateFiniteExact.decClock]; omega)
  refine ⟨m, ?_⟩
  have c0 : r.clock ≠ 0 := by omega
  change sptLookup a2 r.locals = some (.word a) at h2
  change sptLookup a3 r.locals = some v at h3
  change sptLookup a4 r.locals = some (.word (BitVec.ofNat width (4 * n))) at h4
  have nonempty : ¬ sptDomainEmpty (sptFromList [()]) := by
    intro e; exact e 0 (by rw [fl, sptMem_ls])
  have envl : wordSemEnvToList (.ln : Spt (WordLocW width)) r.permute =
      ([], fun n => r.permute (n + 1)) := by
    have e1 : sptToAList (.ln : Spt (WordLocW width)) = [] := by simp [sptToAList, sptFoldi]
    have e2 : Basis.Pure.MlList.sort wordSemKeyValCompare
        ([] : List (Nat × WordLocW width)) = [] := by
      simp [Basis.Pure.MlList.sort, Basis.Pure.MlList.mergesortTail,
        Basis.Pure.MlList.mergesortNTail]
    simp [wordSemEnvToList, e1, e2, wordSemListRearrange]
  have al : sptToAList (.ls ret_val) = [(0, ret_val)] := by simp [sptToAList, sptFoldi]
  simp only [s0, pushed, vals] at hrun
  rw [WordSemStateFiniteExact.evaluate]
  simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, h2, h3, h4, l0,
    wordSemBadDestArgs, wordSemAddRetLoc, wordSemFindCode, hcode, cut, c0, nonempty]
  have hfc := congrArg (fun p => WordSemStateFiniteExact.fixClock
    (WordSemStateFiniteExact.callEnv
      [WordLocW.loc l1 l2, WordLocW.word a, v, WordLocW.word (BitVec.ofNat width (4 * n)), ret_val]
      (sptLookup replicateLocation r.stackSize)
      (WordSemStateFiniteExact.pushEnv (Spt.ls ret_val, Spt.ln) none r.decClock)) p) hrun
  have un : sptUnion (sptFromAList ([] : List (Nat × WordLocW width)))
      (sptFromAList [(0, ret_val)]) = .ls ret_val := by
    simp [sptFromAList, sptUnion]
  have deu : sptDomainEqUnion (.ls ret_val) (.ls ret_val) (.ln : Spt (WordLocW width)) := by
    intro k; simp
  split
  case h_6 =>
    exfalso
    rename_i n1 n2 n3 n4 n5
    exact n1 _ _ _ hfc
  all_goals rename_i heq
  all_goals rw [hrun] at heq
  all_goals simp only [WordSemStateFiniteExact.fixClock, Prod.mk.injEq] at heq
  case h_1 x ys s2 =>
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
    simp [WordSemStateFiniteExact.popEnv,
      WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv, envl, al,
      WordSemStateFiniteExact.decClock, un, deu, WordSemStateFiniteExact.setVars,
      LoopSemStateFiniteExact.sptAlistInsert, WordSemStateFiniteExact.evaluate, sptInsert]
    by_cases hc : r.clock - 1 < r.clock - 1 - n <;> simp only [hc, if_true, if_false] <;> omega
  all_goals simp at heq

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
