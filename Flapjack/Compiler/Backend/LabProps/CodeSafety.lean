import Flapjack.Compiler.Backend.LabSem.Navigation

namespace Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm

/-- Literal fetched-Install exclusion. All position and constructor payload quantifiers are retained. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "no_install_def"
  (words_as_type_indexed_bitvec)]
def noInstall {width : Nat} [NeZero width] (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)))) : Prop :=
  ∀ (p : Nat) (w : BitVec width) (bytes : List (BitVec 8)) (l : Nat),
    asmFetchAux p code ≠ some (.labAsm .install w bytes l)

/-- Literal fetched-ShareMem exclusion. All position and constructor payload quantifiers are retained. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "no_share_mem_inst_def"
  (words_as_type_indexed_bitvec)]
def noShareMemInst {width : Nat} [NeZero width] (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)))) : Prop :=
  ∀ (p : Nat) (op : HolMemop) (re : Nat) (a : HolAddr width)
      (inst : List (BitVec 8)) (len : Nat),
    asmFetchAux p code ≠ some (.asm (.shareMem op re a) inst len)

end Flapjack.Compiler.Backend.LabProps
