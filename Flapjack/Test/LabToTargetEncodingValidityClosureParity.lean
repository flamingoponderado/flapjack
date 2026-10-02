import Flapjack.Compiler.Backend.LabToTarget.EncodingValidityClosure
namespace Flapjack.Test.LabToTargetEncodingValidityClosureParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (pos : Nat) (left right : List (Section
      (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
        (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    allEncOk c labs ffis pos left ∧
    allEncOk c labs ffis (pos + (progToBytes left).length) right →
    allEncOk c labs ffis pos (left ++ right) := allEncOk_append c labs ffis pos left right
example {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (pos : Nat) (code : List (Section
      (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
        (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (extended : Spt (Spt Nat)) :
    (∀ sid lid value,labLookup sid lid labs = some value →
      labLookup sid lid extended = some value) ∧ allEncOk c labs ffis pos code →
    allEncOk c extended ffis pos code := allEncOk_extendLabels c labs ffis pos code extended
private def cfg {width : Nat} [NeZero width] (alignment : Nat) (bytes : List (BitVec 8)) : AsmConfigExact width :=
  { isa := .riscv, encode := fun _ => bytes, bigEndian := false, codeAlignment := alignment,
    linkReg := some 7, avoidRegs := [], regCount := 8, fpRegCount := 4,
    twoRegArith := false, validImm := fun _ _ => true,
    addrOffset := (128,127), hwOffset := (128,127), byteOffset := (128,127),
    jumpOffset := (128,127), cjumpOffset := (128,127), locOffset := (128,127) }
private def old : Spt (Spt Nat) := sptFromAList [(1,sptFromAList [(7,20)])]
private def extra := sptInsert 99 (sptFromAList [(8,24)]) old
private def jumpCode : List (Section (LabLineHOL 8)) :=
  [⟨1,[.labAsm (.jump (.lab 1 7)) 99 [0,0] 2,.label 1 7 0]⟩]
private def asmCode : List (Section (LabLineHOL 8)) :=
  [⟨2,[.asm (.asmi (.inst .skip)) [0,0] 2,.label 2 8 0]⟩]
example : allEncOk (cfg (width := 8) 1 [0,0]) old [] 18 jumpCode ∧
    allEncOk (cfg (width := 8) 1 [0,0]) old [] 20 asmCode ∧
    allEncOk (cfg (width := 8) 1 [0,0]) old [] 18 (jumpCode ++ asmCode) := by cbv
example : allEncOk (cfg (width := 8) 1 [0,0]) extra [] 18 jumpCode := by cbv
example : ¬allEncOk (cfg (width := 8) 1 [0,0]) .ln [] 18 jumpCode := by cbv
example : ¬allEncOk (cfg (width := 8) 1 [0,0]) old [] 19 asmCode := by cbv
example : allEncOk (cfg (width := 8) 1 [0,0]) old [] 18 [⟨1,[.label 2 7 0]⟩] := by cbv
example : labLookup 99 8 old = none ∧ labLookup 99 8 extra = some 24 ∧
    labLookup 1 7 old = some 20 ∧ labLookup 1 7 extra = some 20 := by decide +kernel
/-- Actual arbitrary fresh-outer-map consumer: discharge the complete original
lookup-extension guard and obtain validity without assuming target validity. -/
example (fresh : Nat) (payload : Spt Nat) (hne : fresh ≠ 1)
    (h : allEncOk (cfg (width := 8) 1 [0,0]) old [] 18 jumpCode) :
    allEncOk (cfg (width := 8) 1 [0,0]) (sptInsert fresh payload old) [] 18 jumpCode := by
  apply allEncOk_extendLabels _ old [] 18 jumpCode _
  refine ⟨?_,h⟩
  intro sid lid value hv
  by_cases hs : sid = 1
  · subst sid
    simpa only [labLookup,sptLookup_sptInsert_ne _ _ _ _ (Ne.symm hne)] using hv
  · simp [old,labLookup,sptLookup_sptFromAList,sptAListLookup,hs] at hv
example (hleft : allEncOk (cfg (width := 8) 1 [0,0]) old [] 18 jumpCode)
    (hright : allEncOk (cfg (width := 8) 1 [0,0]) old [] 20 asmCode) :
    allEncOk (cfg (width := 8) 1 [0,0]) old [] 18 (jumpCode ++ asmCode) := by
  apply allEncOk_append
  have hlen : (progToBytes jumpCode).length = 2 := by cbv
  refine ⟨hleft,?_⟩
  simpa only [hlen,Nat.reduceAdd] using hright
end Flapjack.Test.LabToTargetEncodingValidityClosureParity
