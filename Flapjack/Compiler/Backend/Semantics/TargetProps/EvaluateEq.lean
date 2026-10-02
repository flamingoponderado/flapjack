import Flapjack.Compiler.Backend.Semantics.TargetProps.Interference
import Flapjack.Compiler.Backend.Semantics.TargetProps.FindNextInterference
import Flapjack.Compiler.Backend.Semantics.TargetSem.Evaluate
import Flapjack.Compiler.Encoders.AsmProps.Assertions.Iteration
import Flapjack.Compiler.Encoders.AsmProps.PcCoverage
import Flapjack.Compiler.Encoders.AsmProps.Interference

namespace Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmProps Classical

/-- Internal guard derivation from the original encoded region; no separate HOL
original is claimed for this extracted proof step. -/
private theorem encodedRegion {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (i : HolAsm width) (pc : BitVec width) (k : Nat)
    (memory : BitVec width → BitVec 8) (domain subdomain : BitVec width → Prop)
    (hsub : ∀ a, subdomain a → domain a)
    (hk : k * 2 ^ c.codeAlignment < (c.encode i).length)
    (hmem : bytesInMemoryHOL pc (c.encode i) memory subdomain) :
    encodedBytesInMemHOL c (pc + BitVec.ofNat width (k * 2 ^ c.codeAlignment)) memory domain := by
  let offset := k * 2 ^ c.codeAlignment
  have hsplit := (bytesInMemory_append ((c.encode i).take offset)
    ((c.encode i).drop offset) pc memory subdomain).mp
      (by simpa using hmem)
  have hlen : ((c.encode i).take offset).length = offset := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk), offset]
  rw [hlen] at hsplit
  exact ⟨i, k, hk, bytesInMemory_subset _ _ _ _ _ ⟨hsub, hsplit.2⟩⟩

/-- Extract the remaining assertion trajectory after fixing its first oracle.
This is local proof infrastructure for the original successor argument, not a
separately claimed HOL declaration. -/
private theorem assertsAfterFirst {S Q : Type} (n : Nat) (next : S → S)
    (proj : S → Q) (first : S → S) (s : S) (P R : S → Prop)
    (hfirst : ∀ ms, proj (first ms) = proj ms)
    (h : ∀ env, interferenceOk env proj →
      asserts (n + 1) (fun k ms => env k (next ms)) s P R)
    (env : Nat → S → S) (henv : interferenceOk env proj) :
    asserts n (fun k ms => env k (next ms)) (first (next s)) P R := by
  let patched := fun k ms => if k = n + 1 then first ms else env k ms
  have hp : interferenceOk patched proj := by
    intro k ms
    by_cases hk : k = n + 1
    · simpa [patched, hk] using hfirst ms
    · simpa [patched, hk] using henv k ms
  have ha := h patched hp
  have ht : asserts n (fun k ms => patched k (next ms)) (first (next s)) P R := by
    simpa only [asserts, patched, if_pos rfl] using ha.2
  apply asserts_weaken n (fun k ms => patched k (next ms))
    (fun k ms => env k (next ms)) (first (next s)) P P R _ ht
  intro k hk
  constructor
  · funext ms
    have hne : k ≠ n + 1 := by omega
    simp [patched, hne]
  · exact fun hx => hx

/-- Transport the original reversed-index frame assertion after its first
step. This extracts the source successor proof's asserts2_change_interfer use;
it is local infrastructure with no independent HOL original claimed. -/
private theorem frameAfterFirst {S : Type} (n : Nat) (oracle : Nat → S → S)
    (next : S → S) (s : S) (P : S → S → Prop)
    (h : asserts2 (n + 2) (fun k => oracle (n + 2 - k)) next s P) :
    asserts2 (n + 1) (fun k => holShiftSeq 1 oracle (n + 1 - k))
      next (oracle 0 (next s)) P := by
  have ht : asserts2 (n + 1) (fun k => oracle (n + 2 - k))
      next (oracle 0 (next s)) P := by
    simpa only [asserts2, Nat.sub_self] using h.2
  apply asserts2_changeInterfer (n + 1) (fun k => oracle (n + 2 - k))
    (fun k => holShiftSeq 1 oracle (n + 1 - k)) next (oracle 0 (next s)) P
  refine ⟨ht, ?_⟩
  intro k hk
  have he : n + 2 - k = (n + 1 - k) + 1 := by omega
  simp only [holShiftSeq, he]

/-- Original evaluate_EQ_evaluate_lemma base case. All original hypotheses are
retained, including the universal environment assertion and full frame condition.
Inherited total holEl/holHd semantics are unchanged: out-of-range names remain
shared opaque holHdNil/holArb, with no additional bounds premise or fallback. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml"
  "evaluate_EQ_evaluate_lemma" (words_as_type_indexed_bitvec)]
theorem evaluateEqEvaluate_base {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (ms1 : S) (c : MachineConfig width S Q)
    (io : HolFfiState σ) (dm : BitVec width → Prop)
    (i : HolAsm width) (initPc : BitVec width) (s2 : AsmState width)
    (h : (c.progAddresses (c.target.getPc ms1) ∧ c.target.getPc ms1 ∉ c.ffiEntryPcs) ∧
      c.target.stateOk ms1 = true ∧ c.progAddresses = dm ∧
      interferenceOk c.nextInterfer (c.target.proj dm) ∧
      (∀ s ms, targetStateRel c.target s ms → c.target.stateOk ms = true) ∧
      (∀ ms ms', c.target.proj dm ms = c.target.proj dm ms' →
        c.target.stateOk ms = c.target.stateOk ms' ∧
        c.target.getPc ms = c.target.getPc ms' ∧
        ∀ a, dm a → c.target.getByte ms a = c.target.getByte ms' a) ∧
      (∀ env, interferenceOk env (c.target.proj dm) →
        asserts 0 (fun k s => env k (c.target.next s)) ms1
          (fun ms => c.target.stateOk ms = true ∧
            (∀ pc, pc ∈ allPcs (c.target.config.encode i).length initPc 0 →
              c.target.getByte ms pc = c.target.getByte ms1 pc) ∧
            c.target.getPc ms ∈ allPcs (c.target.config.encode i).length initPc c.target.config.codeAlignment)
          (fun ms => targetStateRel c.target s2 ms)) ∧
      asserts2 1 (fun k => c.nextInterfer (1 - k)) c.target.next ms1
        (fun ms ms' => ∀ x, ¬ dm x → c.target.getByte ms x = c.target.getByte ms' x) ∧
      (∃ k, c.target.getPc ms1 = initPc + BitVec.ofNat width (k * 2 ^ c.target.config.codeAlignment) ∧
        k * 2 ^ c.target.config.codeAlignment < (c.target.config.encode i).length ∧
        bytesInMemoryHOL initPc (c.target.config.encode i) (c.target.getByte ms1)
          (fun a => c.progAddresses a ∧ a ∉ c.ffiEntryPcs))) :
    ∃ ms2, ∀ k,
      evaluateTargetHOL c io (k + 1) ms1 = evaluateTargetHOL (shiftInterfer 1 c) io k ms2 ∧
      findNextInterference c io (k + 1) ms1 = findNextInterference (shiftInterfer 1 c) io k ms2 ∧
      targetStateRel c.target s2 ms2 := by
  rcases h with ⟨hn, hok, hdm, hinter, hvalid, hobs, ha, hframe, k0, hpc, hk, hmem⟩
  let ms2 := c.nextInterfer 0 (c.target.next ms1)
  have hrel : targetStateRel c.target s2 ms2 :=
    ha (fun _ => c.nextInterfer 0) (fun _ ms => hinter 0 ms)
  have hok2 : c.target.stateOk ms2 = true := hvalid s2 ms2 hrel
  have hproj : c.target.proj dm ms2 = c.target.proj dm (c.target.next ms1) :=
    hinter 0 (c.target.next ms1)
  have hoknext : c.target.stateOk (c.target.next ms1) = true :=
    (hobs ms2 (c.target.next ms1) hproj).1.symm.trans hok2
  have he : encodedBytesInMemHOL c.target.config (c.target.getPc ms1)
      (c.target.getByte ms1) c.progAddresses := by
    rw [hpc]
    exact encodedRegion _ _ _ _ _ _ _ (fun _ ha => ha.1) hk hmem
  have hf : ∀ x, ¬ c.progAddresses x →
      c.target.getByte (c.target.next ms1) x = c.target.getByte ms1 x := by
    intro x hx
    exact (hframe.1 x (by simpa [← hdm] using hx)).symm
  refine ⟨ms2, ?_⟩
  intro k
  constructor
  · simp only [evaluateTargetHOL]
    rw [if_pos hn, if_pos he]
    split
    · rfl
    · rename_i hbad
      exact False.elim (hbad (by simpa only [applyOracleHOL] using
        (show c.target.stateOk ms1 = true ∧ c.target.stateOk (c.target.next ms1) = true ∧
          c.target.stateOk ms2 = true ∧ _ from ⟨hok, hoknext, hok2, hf⟩)))
  · constructor
    · simp only [findNextInterference]
      rw [if_pos hn, if_pos he]
      split
      · rfl
      · rename_i hbad
        exact False.elim (hbad (by simpa only [applyOracleHOL] using
          (show c.target.stateOk ms1 = true ∧ c.target.stateOk (c.target.next ms1) = true ∧
            c.target.stateOk ms2 = true ∧ _ from ⟨hok, hoknext, hok2, hf⟩)))
    · exact hrel

end Flapjack.Compiler.Backend.Semantics.TargetProps
