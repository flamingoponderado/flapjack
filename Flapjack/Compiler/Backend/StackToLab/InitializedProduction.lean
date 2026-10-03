import Flapjack.Compiler.Backend.StackToLab.Production
import Flapjack.Compiler.Backend.StackRemove.Compile

/-! Whole-list production boundary required by stack_to_labScript.sml:152–159.
This is Flapjack codec infrastructure, without its own HOL declaration. The
raw-call and allocation passes must already have run, as in the existing
executed caller. Unlike sectionwise removal this boundary retains the complete
reviewed initializer prefix. The actual artifact caller is tracked separately;
this module alone does not establish production replacement or simulation.
-/
namespace Flapjack.Compiler.Backend.StackToLab.InitializedProduction
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Preserve every source section and its order through the complete input codec. -/
def nativeInputs? {width : Nat} [NeZero width]
    (programs : List (Nat × StackProg Nat)) : Option (List (Nat × HolProg width)) :=
  ExecutedCodec.mapCodec? (fun entry =>
    (Production.toNative? entry.2).map (fun body => (entry.1, body))) programs

/-- Complete native post-allocation composition used after production input
normalization. No independent initializer or section lowering is substituted. -/
def compileNative? {width : Nat} [NeZero width] (jump : Bool)
    (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maximumHeap pointer start : Nat) (names : Spt Nat)
    (programs : List (Nat × HolProg width)) : Option (List (LabSection (BitVec width))) :=
  ExecutedCodec.mapCodec? ExecutedInput.sectionToExecuted?
    (Flapjack.Compiler.Backend.StackNames.compileHOL names
      (Flapjack.Compiler.Backend.StackRemove.compileHOL
        jump bounds generateGc maximumHeap pointer start programs))

/-- Original post-allocation composition with all initializer/configuration
arguments retained. Codec failures are explicit, including initializer outputs. -/
def compile? {width : Nat} [NeZero width] (jump : Bool)
    (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maximumHeap pointer start : Nat) (names : Spt Nat)
    (programs : List (Nat × StackProg Nat)) : Option (List (LabSection (BitVec width))) := do
  let native ← nativeInputs? programs
  compileNative? jump bounds generateGc maximumHeap pointer start names native

/-- Successful native whole-list output decodes to every literal original
section, including the initializer prefix. This is Flapjack codec infrastructure:
there is no standalone HOL theorem, and no evaluator simulation is claimed. -/
theorem compileNative_recover {width : Nat} [NeZero width] (jump : Bool)
    (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maximumHeap pointer start : Nat) (names : Spt Nat)
    (native : List (Nat × HolProg width)) (outputs : List (LabSection (BitVec width)))
    (accepted : compileNative? jump bounds generateGc maximumHeap pointer start names native = some outputs) :
    ExecutedCodec.mapCodec? ExecutedCodec.sectionFromExecuted? outputs = some
      ((Flapjack.Compiler.Backend.StackNames.compileHOL names
        (Flapjack.Compiler.Backend.StackRemove.compileHOL
          jump bounds generateGc maximumHeap pointer start native)).map progToSectionHOL) := by
  have lowered : ExecutedCodec.mapCodec? ExecutedInput.sectionToExecuted?
      (Flapjack.Compiler.Backend.StackNames.compileHOL names
        (Flapjack.Compiler.Backend.StackRemove.compileHOL jump bounds generateGc
          maximumHeap pointer start native)) = some outputs := accepted
  clear accepted
  generalize hrenamed : Flapjack.Compiler.Backend.StackNames.compileHOL names
    (Flapjack.Compiler.Backend.StackRemove.compileHOL jump bounds generateGc
      maximumHeap pointer start native) = renamed at lowered ⊢
  clear hrenamed
  induction renamed generalizing outputs with
  | nil =>
    simp [ExecutedCodec.mapCodec?] at lowered
    subst outputs
    rfl
  | cons first rest ih =>
    cases headAccepted : ExecutedInput.sectionToExecuted? first with
    | none => simp [ExecutedCodec.mapCodec?, headAccepted] at lowered
    | some head =>
      cases tailAccepted : ExecutedCodec.mapCodec? ExecutedInput.sectionToExecuted? rest with
      | none => simp [ExecutedCodec.mapCodec?, headAccepted, tailAccepted] at lowered
      | some tail =>
        simp [ExecutedCodec.mapCodec?, headAccepted, tailAccepted] at lowered
        subst outputs
        simp [ExecutedCodec.mapCodec?, ExecutedInput.section_recover _ _ headAccepted,
          ih _ tailAccepted]

/-- Recover the literal native sections of every accepted whole-list lowering.
The premise is codec success, not a target evaluation; this is not pass correctness. -/
theorem compile_recover {width : Nat} [NeZero width] (jump : Bool)
    (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maximumHeap pointer start : Nat) (names : Spt Nat)
    (programs : List (Nat × StackProg Nat)) (outputs : List (LabSection (BitVec width)))
    (accepted : compile? jump bounds generateGc maximumHeap pointer start names programs = some outputs) :
    ∃ native, nativeInputs? programs = some native ∧
      ExecutedCodec.mapCodec? ExecutedCodec.sectionFromExecuted? outputs = some
        ((Flapjack.Compiler.Backend.StackNames.compileHOL names
          (Flapjack.Compiler.Backend.StackRemove.compileHOL
            jump bounds generateGc maximumHeap pointer start native)).map progToSectionHOL) := by
  cases converted : nativeInputs? (width := width) programs with
  | none => simp [compile?, converted] at accepted
  | some native =>
    have lowered : compileNative? jump bounds generateGc maximumHeap pointer start names native = some outputs := by
      simpa [compile?, converted] using accepted
    exact ⟨native, rfl, compileNative_recover jump bounds generateGc maximumHeap pointer start names native outputs lowered⟩

end Flapjack.Compiler.Backend.StackToLab.InitializedProduction
