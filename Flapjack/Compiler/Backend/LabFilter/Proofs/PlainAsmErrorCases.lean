import Flapjack.Compiler.Backend.LabFilter.Proofs.BufferTerminalCases

namespace Flapjack.Compiler.Backend.LabFilter.Proofs
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip

/-- Flapjack proof factoring of the four literal default evaluator branches;
there is no separately named HOL declaration for this constructor predicate. -/
private def plainAsmError {width : Nat} [NeZero width] : HolAsm width → Prop
  | .jump _ | .jumpCmp _ _ _ _ | .call _ | .loc _ _ => True
  | _ => False

/-- Flapjack factoring of the original `same_inst_tac` default-error argument.
The constructor predicate only selects the four actual native Error branches;
no target execution, induction hypothesis or reachability assumption is supplied. -/
private theorem plainAsmErrorCase {width : Nat} [NeZero width] {C F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (instruction : HolAsm width) (bytes : List (BitVec 8)) (len : Nat)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (hfailed : t1.failed = false)
    (hfetch : asmFetch s1 = some (.asm (.asmi instruction) bytes len))
    (hplain : plainAsmError instruction) :
    ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧
      s2.ffi = t2.ffi := by
  by_cases hc : s1.clock = 0
  · exact filterCorrectClockZero s1 t1 res s2 heval hrel hfailed hc
  have hsclock : s1.clock = t1.clock := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    rw [hs]
  have htclock : t1.clock ≠ 0 := by omega
  have hf : asmFetchAux (adjustPc t1.pc t1.code) (filterSkip t1.code) =
      some (.asm (.asmi instruction) bytes len) := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    simpa only [hs, asmFetch] using hfetch
  obtain ⟨count, halign, hskips⟩ := asmFetchAuxEq2 t1.pc t1.code _ hf
  cases instruction <;> simp only [plainAsmError] at hplain
  all_goals
    have he := heval
    conv at he => lhs; rw [evaluate]
    simp only [hc, ↓reduceIte, hfetch] at he
    cases he
    have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
    refine ⟨count, {t1 with pc := t1.pc + count}, ?_, ?_⟩
    · simp only [Nat.add_zero] at hrun
      rw [hsclock, hrun]
      conv => lhs; rw [evaluate]
      simp only [htclock, ↓reduceIte, asmFetch, halign]
    · rcases hrel with ⟨⟨_, hs, _⟩, _⟩
      rw [hs]

/-- Original plain ASM Jump default-error case, not the labAsm Jump branch.
Retains all original simulation premises and derives the skipped target run. -/
@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "filter_correct"
  (words_as_type_indexed_bitvec)]
theorem filterCorrectPlainJump {width : Nat} [NeZero width] {C F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (offset : BitVec width) (bytes : List (BitVec 8)) (len : Nat)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (hfailed : t1.failed = false)
    (hfetch : asmFetch s1 = some (.asm (.asmi (.jump offset)) bytes len)) :
    ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧
      s2.ffi = t2.ffi :=
  plainAsmErrorCase s1 t1 res s2 (.jump offset) bytes len heval hrel hfailed hfetch trivial

/-- Original plain ASM JumpCmp default-error case; no source branch is excluded. -/
@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "filter_correct"
  (words_as_type_indexed_bitvec)]
theorem filterCorrectPlainJumpCmp {width : Nat} [NeZero width] {C F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (operator : HolCmp) (register : Nat) (right : HolRegImm width)
    (offset : BitVec width) (bytes : List (BitVec 8)) (len : Nat)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (hfailed : t1.failed = false)
    (hfetch : asmFetch s1 = some (.asm (.asmi (.jumpCmp operator register right offset)) bytes len)) :
    ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧
      s2.ffi = t2.ffi :=
  plainAsmErrorCase s1 t1 res s2 (.jumpCmp operator register right offset) bytes len
    heval hrel hfailed hfetch trivial

/-- Original plain ASM Call default-error case, not the labAsm Call branch. -/
@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "filter_correct"
  (words_as_type_indexed_bitvec)]
theorem filterCorrectPlainCall {width : Nat} [NeZero width] {C F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (offset : BitVec width) (bytes : List (BitVec 8)) (len : Nat)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (hfailed : t1.failed = false)
    (hfetch : asmFetch s1 = some (.asm (.asmi (.call offset)) bytes len)) :
    ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧
      s2.ffi = t2.ffi :=
  plainAsmErrorCase s1 t1 res s2 (.call offset) bytes len heval hrel hfailed hfetch trivial

/-- Original plain ASM Loc default-error case, not the labAsm LocValue branch. -/
@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "filter_correct"
  (words_as_type_indexed_bitvec)]
theorem filterCorrectPlainLoc {width : Nat} [NeZero width] {C F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (register : Nat) (offset : BitVec width) (bytes : List (BitVec 8)) (len : Nat)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (hfailed : t1.failed = false)
    (hfetch : asmFetch s1 = some (.asm (.asmi (.loc register offset)) bytes len)) :
    ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧
      s2.ffi = t2.ffi :=
  plainAsmErrorCase s1 t1 res s2 (.loc register offset) bytes len heval hrel hfailed hfetch trivial

end Flapjack.Compiler.Backend.LabFilter.Proofs
