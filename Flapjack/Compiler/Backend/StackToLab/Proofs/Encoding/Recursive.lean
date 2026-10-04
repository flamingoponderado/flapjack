import Flapjack.Compiler.Backend.StackToLab.Native
import Flapjack.Compiler.Backend.LabProps.Native
import Flapjack.Compiler.Backend.StackProps.ProgramValidity
namespace Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack Flapjack.Compiler.Backend.StackToLab
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm
/-!
Recursive structural constructor pieces of the local `flatten_line_ok_pre` in
`stack_to_labProofScript.sml:3629-3661`. Each case keeps zero-offset validity,
source assembly validity, the actual flatten tuple equation and the full EVERY
conclusion. The additional premises are the whole quantified original-statement
structural motive for the actual subprograms. They are stronger than the
particular recursive-call hypotheses produced by HOL flatten_ind; these pieces
do not claim literal HOL induction-rule arguments. The complete theorem in
Full.lean discharges these motives internally and has no public IH. Counters and continuation
stacks are threaded exactly as in the original definition. If covers all six
branches; returned Call covers both target forms and both handler alternatives.
The original line precheck accepts LabAsm lines without extra jump conditions.
Full.lean assembles the complete flatten and compile_all statements; its
coordinator acceptance is tracked separately. Full compiler correctness and
the executed production replacement remain open work.
-/
/-- Flapjack-specific simplifier extraction of the first conjunct of the
already tagged misc append_thm; no separate HOL declaration is asserted. -/
private theorem appendList_eq {α : Type} (left right : AppList α) :
    appListAppend (.append left right) = appListAppend left ++ appListAppend right :=
  (appListAppend_thm left right []).1

/-- Recursive constructor piece under whole-statement structural motives for its subprograms; not a literal flatten_ind case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem flattenLineOkPreSeq {width : Nat} [NeZero width]
    (tail : Bool) (first second : HolProg width) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config (.seq first second))
    (result : flattenHOL tail (.seq first second) sectionId next conts breaks =
      (lines, done, nextAfter))
    (ihFirst : ∀ (t : Bool) (n m : Nat) (cs bs : List Nat)
      (ls : AppList (LabLineHOL width)) (a : Bool) (b : Nat),
      asmByteOffsetOkExact config 0 = true → stackAsmOkExact config first →
      flattenHOL t first n m cs bs = (ls,a,b) →
      ∀ line ∈ appListAppend ls, lineOkPreHOL config line)
    (ihSecond : ∀ (t : Bool) (n m : Nat) (cs bs : List Nat)
      (ls : AppList (LabLineHOL width)) (a : Bool) (b : Nat),
      asmByteOffsetOkExact config 0 = true → stackAsmOkExact config second →
      flattenHOL t second n m cs bs = (ls,a,b) →
      ∀ line ∈ appListAppend ls, lineOkPreHOL config line)
    : ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  cases firstResult : flattenHOL false first sectionId next conts breaks with
  | mk xs restFirst =>
    cases restFirst with
    | mk nr1 nx1 =>
      cases secondResult : flattenHOL false second sectionId nx1 conts breaks with
      | mk ys restSecond =>
        cases restSecond with
        | mk nr2 nx2 =>
          have hx := ihFirst false sectionId next conts breaks xs nr1 nx1 zero valid.1 firstResult
          have hy := ihSecond false sectionId nx1 conts breaks ys nr2 nx2 zero valid.2 secondResult
          cases tail <;> simp [flattenHOL, firstResult, secondResult] at result <;>
            rcases result with ⟨hLines, _, _⟩ <;> subst lines <;>
            simp only [appendList_eq]
          all_goals
            simp only [appListAppend, appendAux, List.mem_append,
              List.mem_cons, List.not_mem_nil, or_false]
            intro line member
            rcases member with hFirst | hSecond
            · first
              | exact hx line hFirst
              | rcases hFirst with hXs | hLabel
                · exact hx line hXs
                · subst line
                  trivial
            · exact hy line hSecond
/-- Recursive constructor piece under whole-statement structural motives for its subprograms; not a literal flatten_ind case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem flattenLineOkPreLoop {width : Nat} [NeZero width]
    (tail : Bool) (body : HolProg width) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config (.loop body))
    (result : flattenHOL tail (.loop body) sectionId next conts breaks =
      (lines, done, nextAfter))
    (ihBody : ∀ (t : Bool) (n m : Nat) (cs bs : List Nat)
      (ls : AppList (LabLineHOL width)) (a : Bool) (b : Nat),
      asmByteOffsetOkExact config 0 = true → stackAsmOkExact config body →
      flattenHOL t body n m cs bs = (ls,a,b) →
      ∀ line ∈ appListAppend ls, lineOkPreHOL config line) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  cases bodyResult : flattenHOL false body sectionId (next + 2)
      (next :: conts) ((next + 1) :: breaks) with
  | mk xs rest =>
    cases rest with
    | mk nr after =>
      have hx := ihBody false sectionId (next + 2) (next :: conts)
        ((next + 1) :: breaks) xs nr after zero valid bodyResult
      simp [flattenHOL, bodyResult] at result
      rcases result with ⟨hLines, _, _⟩
      subst lines
      simp only [appendList_eq]
      simp only [appListAppend, appendAux, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false]
      intro line member
      rcases member with (hContinue | hBody) | hJump | hBreak
      · subst line
        trivial
      · exact hx line hBody
      · subst line
        trivial
      · subst line
        trivial

/-- Recursive constructor piece under whole-statement structural motives for its subprograms; not a literal flatten_ind case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem flattenLineOkPreIf {width : Nat} [NeZero width]
    (tail : Bool) (condition : HolCmp) (register : Nat) (right : HolRegImm width)
    (first second : HolProg width) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config (.ite condition register right first second))
    (result : flattenHOL tail (.ite condition register right first second)
      sectionId next conts breaks = (lines, done, nextAfter))
    (ihFirst : ∀ (t : Bool) (n m : Nat) (cs bs : List Nat)
      (ls : AppList (LabLineHOL width)) (a : Bool) (b : Nat),
      asmByteOffsetOkExact config 0 = true → stackAsmOkExact config first →
      flattenHOL t first n m cs bs = (ls,a,b) →
      ∀ line ∈ appListAppend ls, lineOkPreHOL config line)
    (ihSecond : ∀ (t : Bool) (n m : Nat) (cs bs : List Nat)
      (ls : AppList (LabLineHOL width)) (a : Bool) (b : Nat),
      asmByteOffsetOkExact config 0 = true → stackAsmOkExact config second →
      flattenHOL t second n m cs bs = (ls,a,b) →
      ∀ line ∈ appListAppend ls, lineOkPreHOL config line)
    : ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  cases firstResult : flattenHOL false first sectionId next conts breaks with
  | mk xs restFirst =>
    cases restFirst with
    | mk nr1 nx1 =>
      cases secondResult : flattenHOL false second sectionId nx1 conts breaks with
      | mk ys restSecond =>
        cases restSecond with
        | mk nr2 nx2 =>
          have hx := ihFirst false sectionId next conts breaks xs nr1 nx1 zero valid.1 firstResult
          have hy := ihSecond false sectionId nx1 conts breaks ys nr2 nx2 zero valid.2 secondResult
          simp only [flattenHOL, firstResult, secondResult] at result
          repeat' split at result
          all_goals
            simp only [Prod.mk.injEq] at result
            rcases result with ⟨hLines, _, _⟩
            subst lines
            try simp only [appendList_eq]
            simp only [appListAppend, appendAux, List.mem_append,
              List.mem_cons, List.not_mem_nil, or_false]
            simp only [appListAppend] at hx hy
            grind only [lineOkPreHOL]

/-- Recursive constructor piece under whole-statement structural motives for its subprograms; not a literal flatten_ind case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem flattenLineOkPreReturnedCallNone {width : Nat} [NeZero width]
    (tail : Bool) (body : HolProg width) (link returnSection returnLabel : Nat)
    (target : Sum Nat Nat) (sectionId next : Nat) (conts breaks : List Nat)
    (lines : AppList (LabLineHOL width)) (done : Bool) (nextAfter : Nat)
    (config : AsmConfigExact width) (zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config
      (.call (some (body,link,returnSection,returnLabel)) target none))
    (result : flattenHOL tail
      (.call (some (body,link,returnSection,returnLabel)) target none)
      sectionId next conts breaks = (lines,done,nextAfter))
    (ihBody : ∀ (t : Bool) (n m : Nat) (cs bs : List Nat)
      (ls : AppList (LabLineHOL width)) (a : Bool) (b : Nat),
      asmByteOffsetOkExact config 0 = true → stackAsmOkExact config body →
      flattenHOL t body n m cs bs = (ls,a,b) →
      ∀ line ∈ appListAppend ls, lineOkPreHOL config line) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  have hJump : lineOkPreHOL config (compileJumpHOL target) := by
    cases target with
    | inl destination => trivial
    | inr register =>
      simpa [compileJumpHOL, lineOkPreHOL, LabToTarget.cbwToAsmHOL,
        asmOkExact, asmRegOkExact] using valid.1
  cases bodyResult : flattenHOL false body sectionId next conts breaks with
  | mk xs rest =>
    cases rest with
    | mk nr after =>
      have hx := ihBody false sectionId next conts breaks xs nr after zero valid.2.1 bodyResult
      simp [flattenHOL, bodyResult] at result
      rcases result with ⟨hLines, _, _⟩
      subst lines
      simp only [appendList_eq]
      simp only [appListAppend, appendAux, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false]
      simp only [appListAppend] at hx
      grind only [lineOkPreHOL]

/-- Recursive constructor piece under whole-statement structural motives for its subprograms; not a literal flatten_ind case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem flattenLineOkPreReturnedCallSome {width : Nat} [NeZero width]
    (tail : Bool) (body : HolProg width) (link returnSection returnLabel : Nat)
    (target : Sum Nat Nat) (handlerBody : HolProg width)
    (handlerSection handlerLabel : Nat) (sectionId next : Nat) (conts breaks : List Nat)
    (lines : AppList (LabLineHOL width)) (done : Bool) (nextAfter : Nat)
    (config : AsmConfigExact width) (zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config
      (.call (some (body,link,returnSection,returnLabel)) target (some (handlerBody,handlerSection,handlerLabel))))
    (result : flattenHOL tail
      (.call (some (body,link,returnSection,returnLabel)) target (some (handlerBody,handlerSection,handlerLabel)))
      sectionId next conts breaks = (lines,done,nextAfter))
    (ihBody : ∀ (t : Bool) (n m : Nat) (cs bs : List Nat)
      (ls : AppList (LabLineHOL width)) (a : Bool) (b : Nat),
      asmByteOffsetOkExact config 0 = true → stackAsmOkExact config body →
      flattenHOL t body n m cs bs = (ls,a,b) →
      ∀ line ∈ appListAppend ls, lineOkPreHOL config line)
    (ihHandler : ∀ (t : Bool) (n m : Nat) (cs bs : List Nat)
      (ls : AppList (LabLineHOL width)) (a : Bool) (b : Nat),
      asmByteOffsetOkExact config 0 = true → stackAsmOkExact config handlerBody →
      flattenHOL t handlerBody n m cs bs = (ls,a,b) →
      ∀ line ∈ appListAppend ls, lineOkPreHOL config line) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line := by
  have hJump : lineOkPreHOL config (compileJumpHOL target) := by
    cases target with
    | inl destination => trivial
    | inr register =>
      simpa [compileJumpHOL, lineOkPreHOL, LabToTarget.cbwToAsmHOL,
        asmOkExact, asmRegOkExact] using valid.1
  cases bodyResult : flattenHOL false body sectionId next conts breaks with
  | mk xs restBody =>
    cases restBody with
    | mk nr1 nx1 =>
      cases handlerResult : flattenHOL false handlerBody sectionId nx1 conts breaks with
      | mk ys restHandler =>
        cases restHandler with
        | mk nr2 nx2 =>
          have hx := ihBody false sectionId next conts breaks xs nr1 nx1 zero valid.2.1 bodyResult
          have hy := ihHandler false sectionId nx1 conts breaks ys nr2 nx2 zero valid.2.2 handlerResult
          simp [flattenHOL, bodyResult, handlerResult] at result
          rcases result with ⟨hLines, _, _⟩
          subst lines
          simp only [appendList_eq]
          simp only [appListAppend, appendAux, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false]
          simp only [appListAppend] at hx hy
          grind only [lineOkPreHOL]

end Flapjack.Compiler.Backend.StackToLab.Proofs
