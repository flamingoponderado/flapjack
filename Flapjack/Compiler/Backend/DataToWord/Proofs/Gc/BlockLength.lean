import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Block

/-! Relating compiled block-header accesses to the memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- The generated address expression agrees with the memory relation's
address decoder when the configured shift is within the machine word. -/
theorem wordExp_realAddr64 {C F : Type} (conf : Config) (state : WordSemStateFiniteExact 64 C F)
    (reg : Nat) (word address : BitVec 64)
    (shiftBound : shiftLength conf < 64)
    (varRun : WordSemStateFiniteExact.getVar reg state = some (.word word))
    (addressEq : Memory.getRealAddr conf state.store word = some address) :
    WordSemStateFiniteExact.wordExp state (realAddr conf reg) = some (.word address) := by
  unfold Memory.getRealAddr at addressEq
  cases curr : state.store.lookup .currHeap with
  | none => simp [curr] at addressEq
  | some value =>
    cases value with
    | loc a b => simp [curr] at addressEq
    | word base =>
      have k : wordShiftAmount 64 = 3 := by rfl
      have large : (64 : Nat) < 2 ^ 64 := by norm_num
      have shiftSmall : (BitVec.ofNat 64 (shiftLength conf)).toNat = shiftLength conf := by
        simp only [BitVec.toNat_ofNat]
        apply Nat.mod_eq_of_lt
        norm_num at large ⊢
        omega
      have shortSmall : (BitVec.ofNat 64 (shiftLength conf - 3)).toNat = shiftLength conf - 3 := by
        simp only [BitVec.toNat_ofNat]
        apply Nat.mod_eq_of_lt
        norm_num at large ⊢
        omega
      by_cases fast : wordShiftAmount 64 = shiftLength conf ∧ conf.lenBits = 0 ∧ conf.tagBits = 0
      · simp [curr, fast] at addressEq
        subst address
        simp [realAddr, fast, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore,
          varRun, curr, wordOpHOL, wordOp, theWords]
        bv_decide
      · by_cases short : wordShiftAmount 64 ≤ conf.padBits + 1
        · simp [curr, fast, short] at addressEq
          subst address
          have small : shiftLength conf - 3 < 64 := by omega
          have fast' : ¬ (3 = shiftLength conf ∧ conf.lenBits = 0 ∧ conf.tagBits = 0) := by simpa [k] using fast
          have short' : 3 ≤ conf.padBits + 1 := by simpa [k] using short
          simp only [realAddr, k, if_neg fast', if_pos short']
          have notBig : ¬ 64 ≤ shiftLength conf - 3 := by omega
          simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore,
            varRun, curr, wordOpHOL, wordOp, wordShiftHOL, theWords, shortSmall, notBig]
        · simp [curr, fast, short] at addressEq
          subst address
          have fast' : ¬ (3 = shiftLength conf ∧ conf.lenBits = 0 ∧ conf.tagBits = 0) := by simpa [k] using fast
          have short' : ¬ 3 ≤ conf.padBits + 1 := by simpa [k] using short
          simp only [realAddr, k, if_neg fast', if_neg short']
          have notBig : ¬ 64 ≤ shiftLength conf := by omega
          simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore,
            varRun, curr, wordOpHOL, wordOp, wordShiftHOL, theWords, shiftSmall, notBig]

/-- For a related nonempty constructor, the generated heap-header load
succeeds and returns a header with the source field count. -/
theorem stateRel64_loadBlockHeader {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (name stamp tag : Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVar name source.locals = some (.block stamp tag values))
    (nonempty : values ≠ []) :
    ∃ (word header : BitVec 64),
      WordSemStateFiniteExact.getVar (adjustVar name) target = some (.word word) ∧
      word.getLsbD 0 = true ∧
      WordSemStateFiniteExact.wordExp target (.load (realAddr conf (adjustVar name))) = some (.word header) ∧
      WordGcFunctions.decodeLength conf header = BitVec.ofNat 64 values.length ∧
      values.length < 2 ^ (64 - 4) := by
  obtain ⟨word, address, header, variableRun, bit, real, mem, domain, decoded, bound⟩ :=
    stateRel64_getBlockHeader conf l1 l2 source target locs related name stamp tag values sourceRun nonempty
  have shiftBound : shiftLength conf < 64 := by
    rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, memory⟩
    obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, rest⟩ := memory
    exact heapMem.2.2.2.2.2.1
  have addressRun := wordExp_realAddr64 conf target (adjustVar name) word address shiftBound variableRun real
  refine ⟨word, header, variableRun, bit, ?_, decoded, bound⟩
  simp [WordSemStateFiniteExact.wordExp, addressRun, WordSemStateFiniteExact.memLoad, domain, mem]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
