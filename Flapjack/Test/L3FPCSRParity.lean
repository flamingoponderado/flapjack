import Flapjack.RiscV.L3.Defs.CSRDispatch
namespace Flapjack.Test.L3FPCSRParity
open Flapjack.RiscV.L3
-- Independent bit-position expectations from literal source867-892.
example : (let r := «rec'FPCSR» 0; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 0) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 0⟩ : FPCSR) = 0 := by decide
example : (let r := «rec'FPCSR» 4294967295; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (true, 7, true, true, true, true, 16777215) := by decide
example : «reg'FPCSR» (⟨true, 7, true, true, true, true, 16777215⟩ : FPCSR) = 4294967295 := by decide
example : (let r := «rec'FPCSR» 2863311530; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (true, 5, false, false, false, true, 11184810) := by decide
example : «reg'FPCSR» (⟨true, 5, false, false, false, true, 11184810⟩ : FPCSR) = 2863311530 := by decide
example : (let r := «rec'FPCSR» 1431655765; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 2, true, true, true, false, 5592405) := by decide
example : «reg'FPCSR» (⟨false, 2, true, true, true, false, 5592405⟩ : FPCSR) = 1431655765 := by decide
example : (let r := «rec'FPCSR» 19088743; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 3, false, true, true, true, 74565) := by decide
example : «reg'FPCSR» (⟨false, 3, false, true, true, true, 74565⟩ : FPCSR) = 19088743 := by decide
example : (let r := «rec'FPCSR» 4275878552; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (true, 4, true, false, false, false, 16702650) := by decide
example : «reg'FPCSR» (⟨true, 4, true, false, false, false, 16702650⟩ : FPCSR) = 4275878552 := by decide
example : (let r := «rec'FPCSR» 1; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, true, false, false, 0) := by decide
example : «reg'FPCSR» (⟨false, 0, false, true, false, false, 0⟩ : FPCSR) = 1 := by decide
example : (let r := «rec'FPCSR» 2; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, true, 0) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, true, 0⟩ : FPCSR) = 2 := by decide
example : (let r := «rec'FPCSR» 4; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, true, false, 0) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, true, false, 0⟩ : FPCSR) = 4 := by decide
example : (let r := «rec'FPCSR» 8; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (true, 0, false, false, false, false, 0) := by decide
example : «reg'FPCSR» (⟨true, 0, false, false, false, false, 0⟩ : FPCSR) = 8 := by decide
example : (let r := «rec'FPCSR» 16; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, true, false, false, false, 0) := by decide
example : «reg'FPCSR» (⟨false, 0, true, false, false, false, 0⟩ : FPCSR) = 16 := by decide
example : (let r := «rec'FPCSR» 32; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 1, false, false, false, false, 0) := by decide
example : «reg'FPCSR» (⟨false, 1, false, false, false, false, 0⟩ : FPCSR) = 32 := by decide
example : (let r := «rec'FPCSR» 64; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 2, false, false, false, false, 0) := by decide
example : «reg'FPCSR» (⟨false, 2, false, false, false, false, 0⟩ : FPCSR) = 64 := by decide
example : (let r := «rec'FPCSR» 128; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 4, false, false, false, false, 0) := by decide
example : «reg'FPCSR» (⟨false, 4, false, false, false, false, 0⟩ : FPCSR) = 128 := by decide
example : (let r := «rec'FPCSR» 256; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 1) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 1⟩ : FPCSR) = 256 := by decide
example : (let r := «rec'FPCSR» 512; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 2) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 2⟩ : FPCSR) = 512 := by decide
example : (let r := «rec'FPCSR» 1024; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 4) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 4⟩ : FPCSR) = 1024 := by decide
example : (let r := «rec'FPCSR» 2048; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 8) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 8⟩ : FPCSR) = 2048 := by decide
example : (let r := «rec'FPCSR» 4096; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 16) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 16⟩ : FPCSR) = 4096 := by decide
example : (let r := «rec'FPCSR» 8192; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 32) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 32⟩ : FPCSR) = 8192 := by decide
example : (let r := «rec'FPCSR» 16384; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 64) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 64⟩ : FPCSR) = 16384 := by decide
example : (let r := «rec'FPCSR» 32768; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 128) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 128⟩ : FPCSR) = 32768 := by decide
example : (let r := «rec'FPCSR» 65536; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 256) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 256⟩ : FPCSR) = 65536 := by decide
example : (let r := «rec'FPCSR» 131072; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 512) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 512⟩ : FPCSR) = 131072 := by decide
example : (let r := «rec'FPCSR» 262144; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 1024) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 1024⟩ : FPCSR) = 262144 := by decide
example : (let r := «rec'FPCSR» 524288; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 2048) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 2048⟩ : FPCSR) = 524288 := by decide
example : (let r := «rec'FPCSR» 1048576; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 4096) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 4096⟩ : FPCSR) = 1048576 := by decide
example : (let r := «rec'FPCSR» 2097152; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 8192) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 8192⟩ : FPCSR) = 2097152 := by decide
example : (let r := «rec'FPCSR» 4194304; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 16384) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 16384⟩ : FPCSR) = 4194304 := by decide
example : (let r := «rec'FPCSR» 8388608; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 32768) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 32768⟩ : FPCSR) = 8388608 := by decide
example : (let r := «rec'FPCSR» 16777216; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 65536) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 65536⟩ : FPCSR) = 16777216 := by decide
example : (let r := «rec'FPCSR» 33554432; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 131072) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 131072⟩ : FPCSR) = 33554432 := by decide
example : (let r := «rec'FPCSR» 67108864; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 262144) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 262144⟩ : FPCSR) = 67108864 := by decide
example : (let r := «rec'FPCSR» 134217728; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 524288) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 524288⟩ : FPCSR) = 134217728 := by decide
example : (let r := «rec'FPCSR» 268435456; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 1048576) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 1048576⟩ : FPCSR) = 268435456 := by decide
example : (let r := «rec'FPCSR» 536870912; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 2097152) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 2097152⟩ : FPCSR) = 536870912 := by decide
example : (let r := «rec'FPCSR» 1073741824; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 4194304) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 4194304⟩ : FPCSR) = 1073741824 := by decide
example : (let r := «rec'FPCSR» 2147483648; (r.DZ, r.FRM, r.NV, r.NX, r.OF, r.UF, r.«fpcsr'rst»)) = (false, 0, false, false, false, false, 8388608) := by decide
example : «reg'FPCSR» (⟨false, 0, false, false, false, false, 8388608⟩ : FPCSR) = 2147483648 := by decide
example (old : FPCSR) (x : BitVec 32) : «write'reg'FPCSR» (old,x) = «rec'FPCSR» x := rfl
example (old : BitVec 32) (r : FPCSR) : «write'rec'FPCSR» (old,r) = «reg'FPCSR» r := rfl
end Flapjack.Test.L3FPCSRParity
