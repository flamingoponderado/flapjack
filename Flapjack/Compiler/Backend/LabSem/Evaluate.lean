import Flapjack.Compiler.Backend.LabSem.Inst
import Flapjack.Compiler.Backend.LabSem.SharedMemory
import Flapjack.Compiler.Backend.LabSem.Navigation
import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
import Flapjack.Compiler.Backend.Semantics.TargetSem.Machine
import Flapjack.Misc.ShiftSeq

/-! Full native LabSem evaluator, following labSemScript490–617. Recursion
decreases the actual source clock. Instruction failure returns the original
state, whereas a timeout returns the state reached by prior successful steps.
Install uses HOL equality of arbitrary compiler configurations, decided
classically only at that comparison. FP execution inherits the reviewed
real-number translation through asmInst (docs/SOUNDNESS.md item 8).
-/

namespace Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm

@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "evaluate_def"
  (words_as_type_indexed_bitvec)]
noncomputable def evaluate {width : Nat} [NeZero width] {C F : Type}
    (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    MachineResult × Flapjack.Compiler.Backend.LabSem.State width C F :=
  if state.clock = 0 then (.timeOut, state)
  else match asmFetch state with
    | some (.asm (.asmi (.inst instruction)) _ _) =>
        let next := asmInst instruction state
        if next.failed then (.error, state)
        else evaluate (incPc (decClock next))
    | some (.asm (.asmi (.jumpReg register)) _ _) =>
        match state.regs register with
        | .loc sectionId labelId =>
            match locToPc sectionId labelId state.code with
            | none => (.error, state)
            | some pc => evaluate (updPc pc (decClock state))
        | .word _ => (.error, state)
    | some (.asm (.cbw r1 r2) _ _) =>
        match state.regs r1, state.regs r2 with
        | .word address, .word value =>
            match wordSemBufferWrite state.codeBuffer address (value.setWidth 8) with
            | none => (.error, state)
            | some buffer => evaluate (incPc (decClock { state with codeBuffer := buffer }))
        | _, _ => (.error, state)
    | some (.asm (.shareMem operator register address) _ _) =>
        match hshare : shareMemOp operator register address state with
        | none => (.error, state)
        | some (.final outcome, next) => (.halt (.ffiOutcome outcome), next)
        | some (.ret ffi bytes, next) =>
            have _hnextClock : next.clock = state.clock - 1 :=
              shareMemOp_ret_clock operator register address state next ffi bytes hshare
            evaluate { next with
              ioRegs := holShiftSeq 1 next.ioRegs
              ioFpRegs := holShiftSeq 1 next.ioFpRegs }
    | some (.labAsm .halt _ _ _) =>
        match state.regs state.ptrReg with
        | .word value =>
            if value = 0 then (.halt .success, state)
            else (.halt .resourceLimitHit, state)
        | .loc _ _ => (.error, state)
    | some (.labAsm (.locValue register label) _ _ _) =>
        if getPcValue label state = none then (.error, state)
        else evaluate (incPc (decClock (updReg register (labToLoc label) state)))
    | some (.labAsm (.jump label) _ _ _) =>
        match getPcValue label state with
        | none => (.error, state)
        | some pc => evaluate (updPc pc (decClock state))
    | some (.labAsm (.jumpCmp comparison register operand label) _ _ _) =>
        match wordSemWordCmp comparison (state.regs register) (regImm operand state) with
        | none => (.error, state)
        | some false => evaluate (incPc (decClock state))
        | some true =>
            match getPcValue label state with
            | none => (.error, state)
            | some pc => evaluate (updPc pc (decClock state))
    | some (.labAsm (.call label) _ _ _) =>
        match getPcValue label state with
        | none => (.error, state)
        | some pc =>
            match getRetLoc state with
            | none => (.error, state)
            | some location =>
                evaluate (updPc pc (decClock (updReg state.linkReg location state)))
    | some (.labAsm .install _ _ _) =>
        match state.regs state.ptrReg, state.regs state.lenReg, state.regs state.linkReg with
        | .word start, .word finish, .loc sectionId labelId =>
            match wordSemBufferFlush state.codeBuffer start finish,
                locToPc sectionId labelId state.code with
            | some (bytes, buffer), some pc =>
                let (configuration, program) := state.compileOracle 0
                let oracle := holShiftSeq 1 state.compileOracle
                match state.compile configuration program, program with
                | some (compiledBytes, nextConfiguration), ⟨installedSection, _⟩ :: _ =>
                    let valid : Prop := bytes = compiledBytes ∧ (oracle 0).1 = nextConfiguration
                    letI : Decidable valid := Classical.propDecidable _
                    if valid then
                      evaluate { state with
                        pc := pc
                        codeBuffer := buffer
                        code := state.code ++ program
                        ccRegs := holShiftSeq 1 state.ccRegs
                        ccFpRegs := holShiftSeq 1 state.ccFpRegs
                        regs := fun r => if r = state.ptrReg then .loc installedSection 0
                          else getRegValue (state.ccRegs 0 r) (state.regs r) WordLocW.word
                        fpRegs := fun r => state.ccFpRegs 0 r
                        compileOracle := oracle
                        clock := state.clock - 1 }
                    else (.error, state)
                | _, _ => (.error, state)
            | _, _ => (.error, state)
        | _, _, _ => (.error, state)
    | some (.labAsm (.callFFI function) _ _ _) =>
        match state.regs state.lenReg, state.regs state.ptrReg,
            state.regs state.len2Reg, state.regs state.ptr2Reg, state.regs state.linkReg with
        | .word length, .word start, .word length2, .word start2, .loc sectionId labelId =>
            match readBytearrayWordHOL start length.toNat
                    (memLoadByteAuxExact state.memory state.memDomain state.be),
                readBytearrayWordHOL start2 length2.toNat
                    (memLoadByteAuxExact state.memory state.memDomain state.be),
                locToPc sectionId labelId state.code with
            | some configuration, some bytes, some pc =>
                match callFFIHOL state.ffi (.extCall function) configuration bytes with
                | .final outcome => (.halt (.ffiOutcome outcome), state)
                | .ret ffi returned =>
                    evaluate { state with
                      memory := writeBytearrayExact start2 returned state.memory state.memDomain state.be
                      ffi := ffi
                      ioRegs := holShiftSeq 1 state.ioRegs
                      ioFpRegs := holShiftSeq 1 state.ioFpRegs
                      regs := fun r => getRegValue (state.ioRegs 0 (.extCall function) r)
                        (state.regs r) WordLocW.word
                      fpRegs := fun r => state.ioFpRegs 0 r
                      pc := pc
                      clock := state.clock - 1 }
            | _, _, _ => (.error, state)
        | _, _, _, _, _ => (.error, state)
    | _ => (.error, state)
termination_by state.clock
decreasing_by all_goals (try simp_all [incPc, decClock, updPc, updReg, asmInstConsts]) <;> omega

end Flapjack.Compiler.Backend.LabSem
