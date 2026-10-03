import Flapjack.RiscV.L3.Defs.DecodeImmediates

namespace Flapjack.Test.L3DecodeImmediatesParity
open Flapjack.RiscV.L3
/-! Flapjack-specific numeric fixtures, independently splitting a numeric encoded
word into its original fields and asserting the original assembly value. These
finite regressions are not a complete decode or cross-language proof. -/

-- decode_imm_asImm12_0
example : asImm12 (0,0,0,0) = (0 : BitVec 12) := by decide

-- decode_imm_asImm12_1
example : asImm12 (0,0,0,1) = (1 : BitVec 12) := by decide

-- decode_imm_asImm12_2
example : asImm12 (0,0,0,2) = (2 : BitVec 12) := by decide

-- decode_imm_asImm12_3
example : asImm12 (0,0,0,4) = (4 : BitVec 12) := by decide

-- decode_imm_asImm12_4
example : asImm12 (0,0,0,8) = (8 : BitVec 12) := by decide

-- decode_imm_asImm12_5
example : asImm12 (0,0,1,0) = (16 : BitVec 12) := by decide

-- decode_imm_asImm12_6
example : asImm12 (0,0,2,0) = (32 : BitVec 12) := by decide

-- decode_imm_asImm12_7
example : asImm12 (0,0,4,0) = (64 : BitVec 12) := by decide

-- decode_imm_asImm12_8
example : asImm12 (0,0,8,0) = (128 : BitVec 12) := by decide

-- decode_imm_asImm12_9
example : asImm12 (0,0,16,0) = (256 : BitVec 12) := by decide

-- decode_imm_asImm12_10
example : asImm12 (0,0,32,0) = (512 : BitVec 12) := by decide

-- decode_imm_asImm12_11
example : asImm12 (0,1,0,0) = (1024 : BitVec 12) := by decide

-- decode_imm_asImm12_12
example : asImm12 (0,1,21,5) = (1365 : BitVec 12) := by decide

-- decode_imm_asImm12_13
example : asImm12 (0,1,63,15) = (2047 : BitVec 12) := by decide

-- decode_imm_asImm12_14
example : asImm12 (1,0,0,0) = (2048 : BitVec 12) := by decide

-- decode_imm_asImm12_15
example : asImm12 (1,0,0,1) = (2049 : BitVec 12) := by decide

-- decode_imm_asImm12_16
example : asImm12 (1,0,42,10) = (2730 : BitVec 12) := by decide

-- decode_imm_asImm12_17
example : asImm12 (1,0,63,15) = (3071 : BitVec 12) := by decide

-- decode_imm_asImm12_18
example : asImm12 (1,1,31,15) = (3583 : BitVec 12) := by decide

-- decode_imm_asImm12_19
example : asImm12 (1,1,47,15) = (3839 : BitVec 12) := by decide

-- decode_imm_asImm12_20
example : asImm12 (1,1,55,15) = (3967 : BitVec 12) := by decide

-- decode_imm_asImm12_21
example : asImm12 (1,1,59,15) = (4031 : BitVec 12) := by decide

-- decode_imm_asImm12_22
example : asImm12 (1,1,61,15) = (4063 : BitVec 12) := by decide

-- decode_imm_asImm12_23
example : asImm12 (1,1,62,15) = (4079 : BitVec 12) := by decide

-- decode_imm_asImm12_24
example : asImm12 (1,1,63,7) = (4087 : BitVec 12) := by decide

-- decode_imm_asImm12_25
example : asImm12 (1,1,63,11) = (4091 : BitVec 12) := by decide

-- decode_imm_asImm12_26
example : asImm12 (1,1,63,13) = (4093 : BitVec 12) := by decide

-- decode_imm_asImm12_27
example : asImm12 (1,1,63,14) = (4094 : BitVec 12) := by decide

-- decode_imm_asImm12_28
example : asImm12 (1,1,63,15) = (4095 : BitVec 12) := by decide

-- decode_imm_asImm20_0
example : asImm20 (0,0,0,0) = (0 : BitVec 20) := by decide

-- decode_imm_asImm20_1
example : asImm20 (0,0,0,1) = (1 : BitVec 20) := by decide

-- decode_imm_asImm20_2
example : asImm20 (0,0,0,2) = (2 : BitVec 20) := by decide

-- decode_imm_asImm20_3
example : asImm20 (0,0,0,4) = (4 : BitVec 20) := by decide

-- decode_imm_asImm20_4
example : asImm20 (0,0,0,8) = (8 : BitVec 20) := by decide

-- decode_imm_asImm20_5
example : asImm20 (0,0,0,16) = (16 : BitVec 20) := by decide

-- decode_imm_asImm20_6
example : asImm20 (0,0,0,32) = (32 : BitVec 20) := by decide

-- decode_imm_asImm20_7
example : asImm20 (0,0,0,64) = (64 : BitVec 20) := by decide

-- decode_imm_asImm20_8
example : asImm20 (0,0,0,128) = (128 : BitVec 20) := by decide

-- decode_imm_asImm20_9
example : asImm20 (0,0,0,256) = (256 : BitVec 20) := by decide

-- decode_imm_asImm20_10
example : asImm20 (0,0,0,512) = (512 : BitVec 20) := by decide

-- decode_imm_asImm20_11
example : asImm20 (0,0,1,0) = (1024 : BitVec 20) := by decide

-- decode_imm_asImm20_12
example : asImm20 (0,1,0,0) = (2048 : BitVec 20) := by decide

-- decode_imm_asImm20_13
example : asImm20 (0,2,0,0) = (4096 : BitVec 20) := by decide

-- decode_imm_asImm20_14
example : asImm20 (0,4,0,0) = (8192 : BitVec 20) := by decide

-- decode_imm_asImm20_15
example : asImm20 (0,8,0,0) = (16384 : BitVec 20) := by decide

-- decode_imm_asImm20_16
example : asImm20 (0,16,0,0) = (32768 : BitVec 20) := by decide

-- decode_imm_asImm20_17
example : asImm20 (0,32,0,0) = (65536 : BitVec 20) := by decide

-- decode_imm_asImm20_18
example : asImm20 (0,64,0,0) = (131072 : BitVec 20) := by decide

-- decode_imm_asImm20_19
example : asImm20 (0,128,0,0) = (262144 : BitVec 20) := by decide

-- decode_imm_asImm20_20
example : asImm20 (0,170,1,341) = (349525 : BitVec 20) := by decide

-- decode_imm_asImm20_21
example : asImm20 (0,255,1,1023) = (524287 : BitVec 20) := by decide

-- decode_imm_asImm20_22
example : asImm20 (1,0,0,0) = (524288 : BitVec 20) := by decide

-- decode_imm_asImm20_23
example : asImm20 (1,0,0,1) = (524289 : BitVec 20) := by decide

-- decode_imm_asImm20_24
example : asImm20 (1,85,0,682) = (699050 : BitVec 20) := by decide

-- decode_imm_asImm20_25
example : asImm20 (1,127,1,1023) = (786431 : BitVec 20) := by decide

-- decode_imm_asImm20_26
example : asImm20 (1,191,1,1023) = (917503 : BitVec 20) := by decide

-- decode_imm_asImm20_27
example : asImm20 (1,223,1,1023) = (983039 : BitVec 20) := by decide

-- decode_imm_asImm20_28
example : asImm20 (1,239,1,1023) = (1015807 : BitVec 20) := by decide

-- decode_imm_asImm20_29
example : asImm20 (1,247,1,1023) = (1032191 : BitVec 20) := by decide

-- decode_imm_asImm20_30
example : asImm20 (1,251,1,1023) = (1040383 : BitVec 20) := by decide

-- decode_imm_asImm20_31
example : asImm20 (1,253,1,1023) = (1044479 : BitVec 20) := by decide

-- decode_imm_asImm20_32
example : asImm20 (1,254,1,1023) = (1046527 : BitVec 20) := by decide

-- decode_imm_asImm20_33
example : asImm20 (1,255,0,1023) = (1047551 : BitVec 20) := by decide

-- decode_imm_asImm20_34
example : asImm20 (1,255,1,511) = (1048063 : BitVec 20) := by decide

-- decode_imm_asImm20_35
example : asImm20 (1,255,1,767) = (1048319 : BitVec 20) := by decide

-- decode_imm_asImm20_36
example : asImm20 (1,255,1,895) = (1048447 : BitVec 20) := by decide

-- decode_imm_asImm20_37
example : asImm20 (1,255,1,959) = (1048511 : BitVec 20) := by decide

-- decode_imm_asImm20_38
example : asImm20 (1,255,1,991) = (1048543 : BitVec 20) := by decide

-- decode_imm_asImm20_39
example : asImm20 (1,255,1,1007) = (1048559 : BitVec 20) := by decide

-- decode_imm_asImm20_40
example : asImm20 (1,255,1,1015) = (1048567 : BitVec 20) := by decide

-- decode_imm_asImm20_41
example : asImm20 (1,255,1,1019) = (1048571 : BitVec 20) := by decide

-- decode_imm_asImm20_42
example : asImm20 (1,255,1,1021) = (1048573 : BitVec 20) := by decide

-- decode_imm_asImm20_43
example : asImm20 (1,255,1,1022) = (1048574 : BitVec 20) := by decide

-- decode_imm_asImm20_44
example : asImm20 (1,255,1,1023) = (1048575 : BitVec 20) := by decide

-- decode_imm_asSImm12_0
example : asSImm12 (0,0) = (0 : BitVec 12) := by decide

-- decode_imm_asSImm12_1
example : asSImm12 (0,1) = (1 : BitVec 12) := by decide

-- decode_imm_asSImm12_2
example : asSImm12 (0,2) = (2 : BitVec 12) := by decide

-- decode_imm_asSImm12_3
example : asSImm12 (0,4) = (4 : BitVec 12) := by decide

-- decode_imm_asSImm12_4
example : asSImm12 (0,8) = (8 : BitVec 12) := by decide

-- decode_imm_asSImm12_5
example : asSImm12 (0,16) = (16 : BitVec 12) := by decide

-- decode_imm_asSImm12_6
example : asSImm12 (1,0) = (32 : BitVec 12) := by decide

-- decode_imm_asSImm12_7
example : asSImm12 (2,0) = (64 : BitVec 12) := by decide

-- decode_imm_asSImm12_8
example : asSImm12 (4,0) = (128 : BitVec 12) := by decide

-- decode_imm_asSImm12_9
example : asSImm12 (8,0) = (256 : BitVec 12) := by decide

-- decode_imm_asSImm12_10
example : asSImm12 (16,0) = (512 : BitVec 12) := by decide

-- decode_imm_asSImm12_11
example : asSImm12 (32,0) = (1024 : BitVec 12) := by decide

-- decode_imm_asSImm12_12
example : asSImm12 (42,21) = (1365 : BitVec 12) := by decide

-- decode_imm_asSImm12_13
example : asSImm12 (63,31) = (2047 : BitVec 12) := by decide

-- decode_imm_asSImm12_14
example : asSImm12 (64,0) = (2048 : BitVec 12) := by decide

-- decode_imm_asSImm12_15
example : asSImm12 (64,1) = (2049 : BitVec 12) := by decide

-- decode_imm_asSImm12_16
example : asSImm12 (85,10) = (2730 : BitVec 12) := by decide

-- decode_imm_asSImm12_17
example : asSImm12 (95,31) = (3071 : BitVec 12) := by decide

-- decode_imm_asSImm12_18
example : asSImm12 (111,31) = (3583 : BitVec 12) := by decide

-- decode_imm_asSImm12_19
example : asSImm12 (119,31) = (3839 : BitVec 12) := by decide

-- decode_imm_asSImm12_20
example : asSImm12 (123,31) = (3967 : BitVec 12) := by decide

-- decode_imm_asSImm12_21
example : asSImm12 (125,31) = (4031 : BitVec 12) := by decide

-- decode_imm_asSImm12_22
example : asSImm12 (126,31) = (4063 : BitVec 12) := by decide

-- decode_imm_asSImm12_23
example : asSImm12 (127,15) = (4079 : BitVec 12) := by decide

-- decode_imm_asSImm12_24
example : asSImm12 (127,23) = (4087 : BitVec 12) := by decide

-- decode_imm_asSImm12_25
example : asSImm12 (127,27) = (4091 : BitVec 12) := by decide

-- decode_imm_asSImm12_26
example : asSImm12 (127,29) = (4093 : BitVec 12) := by decide

-- decode_imm_asSImm12_27
example : asSImm12 (127,30) = (4094 : BitVec 12) := by decide

-- decode_imm_asSImm12_28
example : asSImm12 (127,31) = (4095 : BitVec 12) := by decide

end Flapjack.Test.L3DecodeImmediatesParity
