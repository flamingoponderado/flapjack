import Flapjack.Compiler.Backend.LabToTarget.PositionExtension
import Flapjack.Compiler.Backend.LabToTarget.ShmemInfo
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Full original proof-local line extraction. The code's position dimension
and the independently supplied fetched line's dimension remain distinct.
This is the original proof-side definition, not a production replacement for
get_shmem_info. Unsupported/non-shared-memory constructors produce no entry. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def lineToInfo {codeWidth : Nat} {fetchedWidth : Nat} [NeZero codeWidth] [NeZero fetchedWidth]
    (secs : List (Section (Line (AsmOrCbw (HolAsm codeWidth) HolMemop (HolAddr codeWidth)) (AsmWithLab HolCmp (HolRegImm codeWidth) MlString) (BitVec codeWidth)))) (p : Nat) (x : Nat × Option (Line (AsmOrCbw (HolAsm fetchedWidth) HolMemop (HolAddr fetchedWidth)) (AsmWithLab HolCmp (HolRegImm fetchedWidth) MlString) (BitVec fetchedWidth))) :
    List (HolFfiName × ShmemInfoNum) :=
  match x.2 with
  | some (.asm (.shareMem m r (.addr base offset)) bytes _) =>
    let (name,nb) := getMemopInfo m
    [(.sharedMem name, { entryPc := posVal x.1 p secs, nbytes := nb, addrReg := base, addrOff := offset.toNat, reg := r, exitPc := posVal x.1 p secs + bytes.length })]
  | _ => []

/-- Flapjack position-congruence infrastructure for the original constructor
clauses, with no separately named HOL declaration. -/
private theorem lineToInfo_posCongr {codeWidth : Nat} {fetchedWidth : Nat}
    [NeZero codeWidth] [NeZero fetchedWidth]
    (secs1 secs2 : LabProgHOL codeWidth) (p1 p2 i1 i2 : Nat)
    (fetched : Option (LabLineHOL fetchedWidth)) :
    posVal i1 p1 secs1 = posVal i2 p2 secs2 →
    lineToInfo secs1 p1 (i1,fetched) = lineToInfo secs2 p2 (i2,fetched) := by
  intro h
  simp only [lineToInfo,h]

/-- Full original conjunction. All FOUR source word dimensions are independent:
first code, first fetched line, second code and second fetched line. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem lineToInfo_next {firstCode : Nat} {firstFetched : Nat} {secondCode : Nat} {secondFetched : Nat}
    [NeZero firstCode] [NeZero firstFetched] [NeZero secondCode] [NeZero secondFetched]
    (k1 : Nat) (a : AsmWithLab HolCmp (HolRegImm firstCode) MlString)
    (b : BitVec firstCode) (bytes1 : List (BitVec 8)) (len1 : Nat)
    (xs1 : List (Line (AsmOrCbw (HolAsm firstCode) HolMemop (HolAddr firstCode)) (AsmWithLab HolCmp (HolRegImm firstCode) MlString) (BitVec firstCode))) (rest1 : List (Section (Line (AsmOrCbw (HolAsm firstCode) HolMemop (HolAddr firstCode)) (AsmWithLab HolCmp (HolRegImm firstCode) MlString) (BitVec firstCode)))) (p1 i1 : Nat) (l1 : Option (Line (AsmOrCbw (HolAsm firstFetched) HolMemop (HolAddr firstFetched)) (AsmWithLab HolCmp (HolRegImm firstFetched) MlString) (BitVec firstFetched)))
    (k2 : Nat) (c2 : AsmOrCbw (HolAsm secondCode) HolMemop (HolAddr secondCode))
    (bytes2 : List (BitVec 8)) (len2 : Nat) (xs2 : List (Line (AsmOrCbw (HolAsm secondCode) HolMemop (HolAddr secondCode)) (AsmWithLab HolCmp (HolRegImm secondCode) MlString) (BitVec secondCode)))
    (rest2 : List (Section (Line (AsmOrCbw (HolAsm secondCode) HolMemop (HolAddr secondCode)) (AsmWithLab HolCmp (HolRegImm secondCode) MlString) (BitVec secondCode)))) (p2 i2 : Nat) (l2 : Option (Line (AsmOrCbw (HolAsm secondFetched) HolMemop (HolAddr secondFetched)) (AsmWithLab HolCmp (HolRegImm secondFetched) MlString) (BitVec secondFetched))) :
    lineToInfo (⟨k1,.labAsm a b bytes1 len1::xs1⟩::rest1) p1 (i1+1,l1) =
      lineToInfo (⟨k1,xs1⟩::rest1) (p1+bytes1.length) (i1,l1) ∧
    lineToInfo (⟨k2,.asm c2 bytes2 len2::xs2⟩::rest2) p2 (i2+1,l2) =
      lineToInfo (⟨k2,xs2⟩::rest2) (p2+bytes2.length) (i2,l2) := by
  constructor <;> apply lineToInfo_posCongr <;>
    simp [posVal,isLabelHOL,lineLength]

/-- Full original empty-section equation, retaining independent code/fetch words. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem lineToInfo_hdEmpty {codeWidth : Nat} {fetchedWidth : Nat}
    [NeZero codeWidth] [NeZero fetchedWidth] (k : Nat) (rest : List (Section (Line (AsmOrCbw (HolAsm codeWidth) HolMemop (HolAddr codeWidth)) (AsmWithLab HolCmp (HolRegImm codeWidth) MlString) (BitVec codeWidth))))
    (p : Nat) (t : Nat × Option (Line (AsmOrCbw (HolAsm fetchedWidth) HolMemop (HolAddr fetchedWidth)) (AsmWithLab HolCmp (HolRegImm fetchedWidth) MlString) (BitVec fetchedWidth))) :
    lineToInfo (⟨k,[]⟩::rest) p t = lineToInfo rest p t := by
  rcases t with ⟨i,fetched⟩
  apply lineToInfo_posCongr
  simp only [posVal]

/-- Full original zero-label equation; the source's literal zero annotation
is retained instead of a generic label-length or validity assumption. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem lineToInfo_hdLabel {codeWidth : Nat} {fetchedWidth : Nat}
    [NeZero codeWidth] [NeZero fetchedWidth] (k a b : Nat)
    (xs : List (LabLineHOL codeWidth)) (rest : List (Section (Line (AsmOrCbw (HolAsm codeWidth) HolMemop (HolAddr codeWidth)) (AsmWithLab HolCmp (HolRegImm codeWidth) MlString) (BitVec codeWidth)))) (p : Nat)
    (t : Nat × Option (Line (AsmOrCbw (HolAsm fetchedWidth) HolMemop (HolAddr fetchedWidth)) (AsmWithLab HolCmp (HolRegImm fetchedWidth) MlString) (BitVec fetchedWidth))) :
    lineToInfo (⟨k,.label a b 0::xs⟩::rest) p t =
      lineToInfo (⟨k,xs⟩::rest) p t := by
  rcases t with ⟨i,fetched⟩
  apply lineToInfo_posCongr
  simp [posVal,isLabelHOL,lineLength]

/-- Full original fetch enumeration successor, including all n entries even
past the end of code. The sole source guard excludes a leading Label. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem genlist_asmFetchAux_next {width : Nat} [NeZero width]
    (x : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) (k : Nat) (xs : List (LabLineHOL width)) (rest : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (n : Nat) :
    isLabelHOL x = false →
    (List.range (n+1)).map (fun i => (i,asmFetchAux i (⟨k,x::xs⟩::rest))) =
      (0,some x)::(List.range n).map
        (fun i => (i+1,asmFetchAux i (⟨k,xs⟩::rest))) := by
  intro h
  rw [List.range_succ_eq_map,List.map_cons,List.map_map]
  simp only [asmFetchAux,h,Bool.false_eq_true,↓reduceIte,Nat.add_one_sub_one,
    Nat.succ_ne_zero,Nat.succ_eq_add_one,Function.comp_def]
end Flapjack.Compiler.Backend.LabToTarget
