module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Call
public import Flapjack.Compiler.Backend.BviToData.Proofs.Install

@[expose] public section

/-! Entry-call consequences of the BVI-to-data simulation. The evaluator and
state carriers remain pending correspondence review. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Compiling a program part preserves its function name. -/
@[simp, hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "FST_compile_part"]
theorem fst_compilePart (part : Nat × Nat × Bvi.Exp) :
    (compilePart part).1 = part.1 := by
  rfl

/-- An initial direct call never returns the BVI internal return marker. -/
theorem entryCall_notReturn {C F : Type} (start : Nat) (source next : BviSem.BviState C F)
    (res : BviSem.BviResult)
    (run : BviSem.evaluate [.call 0 (some start) [] none] [] source = (res, next)) : ¬ isReturn res := by
  intro ⟨values, eq⟩
  subst res
  simp only [BviSem.evaluate, BviSem.fixClock, Nat.min_self] at run
  cases code : BvlSem.findCode (some start) [] source.code with
  | none => simp [code] at run
  | some pair =>
    obtain ⟨args, body⟩ := pair
    by_cases zero : source.clock = 0
    · simp [code, zero] at run
    · generalize called : BviSem.evaluate [body] args (BviSem.decClock 1 source) = result
      obtain ⟨r, state⟩ := result
      cases r with
      | val xs => simp [code, zero, called] at run
      | err error =>
        cases error with
        | abort reason => simp [code, zero, called] at run
        | raise raised => cases raised <;> simp [code, zero, called] at run

/-- Initial BVI and data states satisfy the simulation relation when the data
code and compiler oracle are obtained by compiling the BVI program lists. -/
theorem initialState_related {C F : Type} (ffi : HolFfiState F)
    (program : List (Nat × Nat × Bvi.Exp)) (oracle : BviSem.CompileOracle C)
    (compiler : DataSem.Compiler C) (stamps : Bool) (limits : DataSem.Limits)
    (sizes : Spt Nat) (clock : Nat) :
    stateRel
      (BviSem.initialState ffi (sptFromAList program) oracle
        (fun cfg code => compiler cfg (compileProg code)) clock)
      (DataSem.initialState ffi (sptFromAList (compileProg program))
        (fun n => let (cfg, code) := oracle n; (cfg, compileProg code))
        compiler stamps limits sizes clock) := by
  simp [stateRel, BviSem.initialState, DataSem.initialState, codeRel_compileProg,
    HolFiniteMapExact.empty, sptMap]

end Flapjack.Compiler.Backend.BviToData
