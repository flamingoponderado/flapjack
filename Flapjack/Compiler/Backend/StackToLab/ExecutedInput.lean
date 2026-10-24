import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec

/-!
Flapjack-specific native section boundary, with no HOL declaration.
The original flatten fallback returns no lines for operations which previous
passes must remove. The structural input codec alone does not establish that
removal. This boundary rejects every residual non-Skip operation, including
inside either optional call body, before using the reviewed native section
wrapper. It preserves the original local seed and label choices, without
adding global fresh-label maxima or explicit entry aliases. Native instruction
payloads may still be rejected by the separate executed-output codec.
This guard is not a proof that production StackRemove produces its domain.
-/
namespace Flapjack.Compiler.Backend.StackToLab.ExecutedInput
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab
open Flapjack.Compiler.Backend.LabSem

/-- Precisely the nonrecursive source flatten cases, with Skip as its deliberate
empty program. Compounds and residual earlier-pass operations are not leaves. -/
def leafSupported {width : Nat} [NeZero width] : HolProg width → Bool
  | .skip | .inst _ | .tick | .halt _ | .raise _ | .ret _
  | .break _ | .continue _ | .rawCall _ | .jumpLower _ _ _
  | .ffi _ _ _ _ _ _ | .locValue _ _ _ | .install _ _ _ _ _
  | .shMemOp _ _ _ | .codeBufferWrite _ _ => true
  | _ => false

/-- Complete structural check, including unused handler bodies on tail calls.
This conservative check keeps the supported input domain explicit. -/
def supported {width : Nat} [NeZero width] (program : HolProg width) : Bool :=
  match program with
  | .seq p q | .ite _ _ _ p q => supported p && supported q
  | .loop p => supported p
  | .call ret _ handler =>
    (match ret with | none => true | some (p, _, _, _) => supported p) &&
    (match handler with | none => true | some (q, _, _) => supported q)
  | _ => leafSupported program
termination_by sizeOf program
decreasing_by all_goals decreasing_trivial

/-- Independent finite-tree grammar for the boundary's post-removal domain. -/
inductive PostRemoval {width : Nat} [NeZero width] : HolProg width → Prop where
  | leaf (p : HolProg width) : leafSupported p = true → PostRemoval p
  | seq {p q} : PostRemoval p → PostRemoval q → PostRemoval (.seq p q)
  | ite {op r right p q} : PostRemoval p → PostRemoval q → PostRemoval (.ite op r right p q)
  | loop {p} : PostRemoval p → PostRemoval (.loop p)
  | callNoneNone (target) : PostRemoval (.call none target none)
  | callNoneSome {q e h} (target) : PostRemoval q → PostRemoval (.call none target (some (q, e, h)))
  | callSomeNone {p r s l} (target) : PostRemoval p → PostRemoval (.call (some (p, r, s, l)) target none)
  | callSomeSome {p r s l q e h} (target) : PostRemoval p → PostRemoval q →
      PostRemoval (.call (some (p, r, s, l)) target (some (q, e, h)))

/-- Sound structural check; no output, evaluation or pass-success premise. -/
theorem supported_postRemoval {width : Nat} [NeZero width]
    (p : HolProg width) (accepted : supported p = true) : PostRemoval p := by
  fun_induction supported p with
  | _ =>
      grind only [PostRemoval.leaf, PostRemoval.seq, PostRemoval.ite, PostRemoval.loop,
        PostRemoval.callNoneNone, PostRemoval.callNoneSome,
        PostRemoval.callSomeNone, PostRemoval.callSomeSome]


/-- All post-removal grammar trees pass the check, at arbitrary positive width. -/
theorem postRemoval_supported {width : Nat} [NeZero width]
    {p : HolProg width} (domain : PostRemoval p) : supported p = true := by
  induction domain with
  | leaf p hp =>
    cases p <;> simp_all [leafSupported, supported]
  | seq _ _ ihp ihq => simp only [supported, ihp, ihq, Bool.and_self]
  | ite _ _ ihp ihq => simp only [supported, ihp, ihq, Bool.and_self]
  | loop _ ih => simp only [supported, ih]
  | callNoneNone target => simp only [supported, Bool.and_self]
  | callNoneSome target _ ih => simp only [supported, ih, Bool.and_self]
  | callSomeNone target _ ih => simp only [supported, ih, Bool.and_self]
  | callSomeSome target _ _ ihp ihq => simp only [supported, ihp, ihq, Bool.and_self]

/-- Literal complete native section lowering, with explicit boundary rejection. -/
def sectionToExecuted? {width : Nat} [NeZero width] (input : Nat × HolProg width) :
    Option (Flapjack.LabSection (BitVec width)) :=
  if supported input.2 then ExecutedCodec.sectionToExecuted? (progToSectionHOL input)
  else none

/-- Every successful section is exactly the reviewed original output when decoded;
this is codec recovery, not a source/target evaluator equivalence theorem. -/
theorem section_recover {width : Nat} [NeZero width]
    (input : Nat × HolProg width) (output : Flapjack.LabSection (BitVec width))
    (accepted : sectionToExecuted? input = some output) :
    ExecutedCodec.sectionFromExecuted? output = some (progToSectionHOL input) := by
  unfold sectionToExecuted? at accepted
  split at accepted
  · exact ExecutedCodec.section_recover _ _ accepted
  · contradiction

/-- Accepted output guarantees the entire native input lies in the checked grammar. -/
theorem section_postRemoval {width : Nat} [NeZero width]
    (input : Nat × HolProg width) (output : Flapjack.LabSection (BitVec width))
    (accepted : sectionToExecuted? input = some output) : PostRemoval input.2 := by
  unfold sectionToExecuted? at accepted
  split at accepted
  · exact supported_postRemoval _ ‹supported input.2 = true›
  · contradiction

end Flapjack.Compiler.Backend.StackToLab.ExecutedInput
