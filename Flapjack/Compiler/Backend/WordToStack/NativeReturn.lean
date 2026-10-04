import Flapjack.Compiler.Backend.WordToStack.NativeInstructions

/-! Native return-slot lowering for the literal Word-to-Stack compiler.
The source list_Seq clauses (stackLangScript.sml:86-90) are reproduced by the
existing structural listSeq at the native carrier specialization. Production
compiler routing and return simulation remain open under the parent compiler bead.
-/
namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang

/-- Literal zero/nonzero stack-free sequence on the native program carrier. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def seqStackFreeNative {width : Nat} [NeZero width]
    (n : Nat) (p : HolProg width) : HolProg width :=
  if n = 0 then p else .seq (.stackFree n) p

/-- Literal descending return-slot copies, preserving the source list_Seq tree. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def copyRetAuxNative {width : Nat} [NeZero width] (k f : Nat) : Nat → HolProg width
  | 0 => .skip
  | n + 1 => listSeq [.stackLoad k n, .stackStore k (n + f), copyRetAuxNative k f n]

/-- Literal return copy/free wrapper. The unused third frame component has its own
independent carrier, as confirmed by the original full HOL type. The return-value
list element carrier is independent of the native continuation carrier, as in
the source length operation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def copyRetNative {width : Nat} [NeZero width] {β γ : Type}
    (perf isHandle : Bool) (kf : Nat × Nat × γ)
    (vs : List β) (kont : HolProg width) : HolProg width :=
  let n := WordToStack.numStackRet kf.1 vs
  if n = 0 then kont
  else .seq
    (copyRetAuxNative kf.1
      (if isHandle then kf.2.1 + WordToStack.handlerSlots perf else kf.2.1) n)
    (seqStackFreeNative n kont)

/-- Flapjack-only representation transport for every native body and count. -/
theorem toGeneric_seqStackFreeNative {width : Nat} [NeZero width]
    (n : Nat) (p : HolProg width) :
    toGeneric (seqStackFreeNative n p) = WordToStack.seqStackFree n (toGeneric p) := by
  simp only [seqStackFreeNative, WordToStack.seqStackFree]
  split <;> simp [toGeneric, Prog.map]

/-- Flapjack-only universal return-slot payload transport, not an evaluation theorem. -/
theorem toGeneric_copyRetAuxNative {width : Nat} [NeZero width] (k f n : Nat) :
    toGeneric (copyRetAuxNative (width := width) k f n) =
      WordToStackRegFormat.copyRetAux (α := BitVec width) k f n := by
  induction n with
  | zero => simp [copyRetAuxNative, WordToStackRegFormat.copyRetAux, toGeneric, Prog.map]
  | succ n ih =>
    simpa [copyRetAuxNative, WordToStackRegFormat.copyRetAux, listSeq,
      toGeneric, Prog.map] using
      congrArg (fun q : ProgM (BitVec width) =>
        StackLang.Prog.seq (.stackLoad k n) (.seq (.stackStore k (n + f)) q)) ih

/-- Flapjack-only universal wrapper transport for arbitrary continuations and
return-value lists. No wellformedness, bounds, result or target-evaluation premise. -/
theorem toGeneric_copyRetNative {width : Nat} [NeZero width] {β γ : Type}
    (perf isHandle : Bool) (kf : Nat × Nat × γ) (vs : List β) (kont : HolProg width) :
    toGeneric (copyRetNative perf isHandle kf vs kont) =
      WordToStackRegFormat.copyRet perf isHandle kf vs (toGeneric kont) := by
  simp only [copyRetNative, WordToStackRegFormat.copyRet]
  split
  · rfl
  · have mapSeq (p q : HolProg width) :
        toGeneric (StackLang.Prog.seq p q) =
          StackLang.Prog.seq (toGeneric p) (toGeneric q) := by
        simp [toGeneric, Prog.map]
    rw [mapSeq, toGeneric_copyRetAuxNative, toGeneric_seqStackFreeNative]

end Flapjack.Compiler.Backend.WordToStack.Native
