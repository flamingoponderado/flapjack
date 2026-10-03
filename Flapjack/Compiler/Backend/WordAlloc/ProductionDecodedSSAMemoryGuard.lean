import Flapjack.Compiler.Backend.WordAlloc.ProductionNormalizedMemoryGuard
import Flapjack.Compiler.Backend.WordAlloc.ProductionFullSSAMemoryGuard
import Flapjack.Compiler.Backend.WordAlloc.ProductionFullSSAMetadata

namespace Flapjack.WordAlloc
open Compiler.Backend.WordAlloc

/-- The actual decoded native SSA metadata result retains the native input
memory guard. The producer equation identifies its returned program; it is
not a target evaluation or assumed support result. This is Flapjack production
correspondence with no HOL original. -/
theorem decodedSsaMemoryGuard {width : Nat} [NeZero width]
    (count : Nat) (native : WordLangProgHOL (BitVec width))
    (output : WordSsaState × List Nat × WordProg (BitVec width))
    (produced : wordFullSsaCcTransNativeWithStateFromHOL count native = some output) :
    RiscV.allocatorMemorySupported output.2.2 = nativeMemorySupported native := by
  unfold wordFullSsaCcTransNativeWithStateFromHOL at produced
  cases decoded : wordLangProgFromHOL (fullSsaCcTransWithMetadata count native).program with
  | none => simp [decoded] at produced
  | some body =>
      simp only [decoded, Option.map_some, Option.some.injEq] at produced
      subst output
      have guard := decodedMemoryGuard _ body decoded
      simpa only [fullSsaCcTransWithMetadata_program, fullSsaProgramMemoryGuard] using guard

/-- Accepted source encoding discharges the decoded SSA output guard from
exactly the source guard, without assuming output support. No HOL theorem is
narrowed by the additional production-domain predicate. -/
theorem decodedSsaMemoryGuard_production {width : Nat} [NeZero width]
    (count : Nat) (actual : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL actual = some native)
    (output : WordSsaState × List Nat × WordProg (BitVec width))
    (produced : wordFullSsaCcTransNativeWithStateFromHOL count native = some output) :
    RiscV.allocatorMemorySupported output.2.2 = RiscV.allocatorMemorySupported actual := by
  rw [decodedSsaMemoryGuard count native output produced,
    memoryGuardProgram_production actual native encoded]

end Flapjack.WordAlloc
