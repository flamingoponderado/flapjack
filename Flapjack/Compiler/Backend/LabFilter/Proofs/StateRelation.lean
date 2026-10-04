import Flapjack.Compiler.Backend.LabFilter.Proofs.Navigation

namespace Flapjack.Compiler.Backend.LabFilter.Proofs
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip

/-- The original unused inst binder is retained on an independent arbitrary carrier,
without constraining its type or specializing it to an instruction datatype. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem asmFetchNotSkipAdjustPc {width : Nat} [NeZero width] {I : Type u} (pc : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)))) (_inst : I) :
    (∀ bytes len, asmFetchAux pc code ≠ some (.asm (.asmi (.inst .skip)) bytes len)) →
    asmFetchAux pc code = asmFetchAux (adjustPc pc code) (filterSkip code) := by
  intro hn
  obtain ⟨count, he, hs⟩ := asmFetchAuxEq pc code
  have hz : count = 0 := by
    by_contra h
    obtain ⟨bytes, len, hf⟩ := hs.2 0 (by omega)
    exact hn bytes len (by simpa only [Nat.add_zero] using hf)
  simpa only [hz, Nat.add_zero] using he

/-- Full source filter simulation relation, retaining the actual compiler/oracle
transformations and original nonfailed guard. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def stateRel {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s t : Flapjack.Compiler.Backend.LabSem.State width C F) : Prop :=
  (∃ sourceCompile,
    s = { t with
      code := filterSkip t.code
      pc := adjustPc t.pc t.code
      compileOracle := (fun n => ((t.compileOracle n).1, filterSkip (t.compileOracle n).2))
      compile := sourceCompile } ∧
    t.compile = fun config program => sourceCompile config (filterSkip program)) ∧
  t.failed = false

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem asmFetchAuxEq2 {width : Nat} [NeZero width] (pc : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width))))
    (x : Option (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width))) :
    asmFetchAux (adjustPc pc code) (filterSkip code) = x →
    ∃ count, asmFetchAux (pc + count) code = x ∧ allSkips pc code count := by
  intro h
  obtain ⟨count, he, hs⟩ := asmFetchAuxEq pc code
  exact ⟨count, he.trans h, hs⟩

/-- Entire result-pair equality from the original skipped-run clock accounting.
Evaluation inherits the real rendering assumption of SOUNDNESS item 8. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem allSkipsEvaluateRw {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) (count clock : Nat)
    (t : Flapjack.Compiler.Backend.LabSem.State width C F) :
    allSkips s.pc s.code count ∧ s.failed = false ∧ s.clock = clock + count ∧
      t = { s with pc := s.pc + count, clock := clock } →
    evaluate s = evaluate t := by
  rintro ⟨hs, hf, hc, rfl⟩
  have h := allSkipsEvaluate count {s with clock := clock} ⟨hs, hf⟩ 0
  simpa only [Nat.add_zero, ← hc] using h

end Flapjack.Compiler.Backend.LabFilter.Proofs
