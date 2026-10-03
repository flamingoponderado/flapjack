import Flapjack.RiscV.L3.Defs.MachineCSRCodec
namespace Flapjack.Test.L3MachineCSRCodecParity
open Flapjack.RiscV.L3
private def observation_mcpuid (x : BitVec 64) :=
  let r := «rec'mcpuid» x
  ( «reg'mcpuid» r, ([r.ArchBase.toNat,(if r.I then 1 else 0),(if r.M then 1 else 0),(if r.S then 1 else 0),(if r.U then 1 else 0),r.«mcpuid'rst».toNat] : List Nat))
-- Original mcpuid_0; independent field extraction/packing calculation.
example : observation_mcpuid 0 = (0,[0,0,0,0,0,0]) := by decide
-- Original mcpuid_1; independent field extraction/packing calculation.
example : observation_mcpuid 18446744073709551615 = (18446744073709551615,[3,1,1,1,1,288230376151711743]) := by decide
-- Original mcpuid_2; independent field extraction/packing calculation.
example : observation_mcpuid 12297829382473034410 = (12297829382473034410,[2,0,0,0,0,192202695620515157]) := by decide
-- Original mcpuid_3; independent field extraction/packing calculation.
example : observation_mcpuid 6148914691236517205 = (6148914691236517205,[1,1,1,1,1,96027680531196586]) := by decide
-- Original mcpuid_4; independent field extraction/packing calculation.
example : observation_mcpuid 81985529216486895 = (81985529216486895,[0,1,0,0,0,270068682177854541]) := by decide
-- Original mcpuid_5; independent field extraction/packing calculation.
example : observation_mcpuid 18364758544493064720 = (18364758544493064720,[3,0,1,1,1,18161693973857202]) := by decide
-- Original mcpuid_6; independent field extraction/packing calculation.
example : observation_mcpuid 1 = (1,[0,0,0,0,0,1125899906842624]) := by decide
-- Original mcpuid_7; independent field extraction/packing calculation.
example : observation_mcpuid 2 = (2,[0,0,0,0,0,2251799813685248]) := by decide
-- Original mcpuid_8; independent field extraction/packing calculation.
example : observation_mcpuid 4 = (4,[0,0,0,0,0,4503599627370496]) := by decide
-- Original mcpuid_9; independent field extraction/packing calculation.
example : observation_mcpuid 8 = (8,[0,0,0,0,0,9007199254740992]) := by decide
-- Original mcpuid_10; independent field extraction/packing calculation.
example : observation_mcpuid 16 = (16,[0,0,0,0,0,18014398509481984]) := by decide
-- Original mcpuid_11; independent field extraction/packing calculation.
example : observation_mcpuid 32 = (32,[0,0,0,0,0,36028797018963968]) := by decide
-- Original mcpuid_12; independent field extraction/packing calculation.
example : observation_mcpuid 64 = (64,[0,0,0,0,0,72057594037927936]) := by decide
-- Original mcpuid_13; independent field extraction/packing calculation.
example : observation_mcpuid 128 = (128,[0,0,0,0,0,144115188075855872]) := by decide
-- Original mcpuid_14; independent field extraction/packing calculation.
example : observation_mcpuid 256 = (256,[0,1,0,0,0,0]) := by decide
-- Original mcpuid_15; independent field extraction/packing calculation.
example : observation_mcpuid 512 = (512,[0,0,0,0,0,140737488355328]) := by decide
-- Original mcpuid_16; independent field extraction/packing calculation.
example : observation_mcpuid 1024 = (1024,[0,0,0,0,0,281474976710656]) := by decide
-- Original mcpuid_17; independent field extraction/packing calculation.
example : observation_mcpuid 2048 = (2048,[0,0,0,0,0,562949953421312]) := by decide
-- Original mcpuid_18; independent field extraction/packing calculation.
example : observation_mcpuid 4096 = (4096,[0,0,1,0,0,0]) := by decide
-- Original mcpuid_19; independent field extraction/packing calculation.
example : observation_mcpuid 8192 = (8192,[0,0,0,0,0,4398046511104]) := by decide
-- Original mcpuid_20; independent field extraction/packing calculation.
example : observation_mcpuid 16384 = (16384,[0,0,0,0,0,8796093022208]) := by decide
-- Original mcpuid_21; independent field extraction/packing calculation.
example : observation_mcpuid 32768 = (32768,[0,0,0,0,0,17592186044416]) := by decide
-- Original mcpuid_22; independent field extraction/packing calculation.
example : observation_mcpuid 65536 = (65536,[0,0,0,0,0,35184372088832]) := by decide
-- Original mcpuid_23; independent field extraction/packing calculation.
example : observation_mcpuid 131072 = (131072,[0,0,0,0,0,70368744177664]) := by decide
-- Original mcpuid_24; independent field extraction/packing calculation.
example : observation_mcpuid 262144 = (262144,[0,0,0,1,0,0]) := by decide
-- Original mcpuid_25; independent field extraction/packing calculation.
example : observation_mcpuid 524288 = (524288,[0,0,0,0,0,2199023255552]) := by decide
-- Original mcpuid_26; independent field extraction/packing calculation.
example : observation_mcpuid 1048576 = (1048576,[0,0,0,0,1,0]) := by decide
-- Original mcpuid_27; independent field extraction/packing calculation.
example : observation_mcpuid 2097152 = (2097152,[0,0,0,0,0,1]) := by decide
-- Original mcpuid_28; independent field extraction/packing calculation.
example : observation_mcpuid 4194304 = (4194304,[0,0,0,0,0,2]) := by decide
-- Original mcpuid_29; independent field extraction/packing calculation.
example : observation_mcpuid 8388608 = (8388608,[0,0,0,0,0,4]) := by decide
-- Original mcpuid_30; independent field extraction/packing calculation.
example : observation_mcpuid 16777216 = (16777216,[0,0,0,0,0,8]) := by decide
-- Original mcpuid_31; independent field extraction/packing calculation.
example : observation_mcpuid 33554432 = (33554432,[0,0,0,0,0,16]) := by decide
-- Original mcpuid_32; independent field extraction/packing calculation.
example : observation_mcpuid 67108864 = (67108864,[0,0,0,0,0,32]) := by decide
-- Original mcpuid_33; independent field extraction/packing calculation.
example : observation_mcpuid 134217728 = (134217728,[0,0,0,0,0,64]) := by decide
-- Original mcpuid_34; independent field extraction/packing calculation.
example : observation_mcpuid 268435456 = (268435456,[0,0,0,0,0,128]) := by decide
-- Original mcpuid_35; independent field extraction/packing calculation.
example : observation_mcpuid 536870912 = (536870912,[0,0,0,0,0,256]) := by decide
-- Original mcpuid_36; independent field extraction/packing calculation.
example : observation_mcpuid 1073741824 = (1073741824,[0,0,0,0,0,512]) := by decide
-- Original mcpuid_37; independent field extraction/packing calculation.
example : observation_mcpuid 2147483648 = (2147483648,[0,0,0,0,0,1024]) := by decide
-- Original mcpuid_38; independent field extraction/packing calculation.
example : observation_mcpuid 4294967296 = (4294967296,[0,0,0,0,0,2048]) := by decide
-- Original mcpuid_39; independent field extraction/packing calculation.
example : observation_mcpuid 8589934592 = (8589934592,[0,0,0,0,0,4096]) := by decide
-- Original mcpuid_40; independent field extraction/packing calculation.
example : observation_mcpuid 17179869184 = (17179869184,[0,0,0,0,0,8192]) := by decide
-- Original mcpuid_41; independent field extraction/packing calculation.
example : observation_mcpuid 34359738368 = (34359738368,[0,0,0,0,0,16384]) := by decide
-- Original mcpuid_42; independent field extraction/packing calculation.
example : observation_mcpuid 68719476736 = (68719476736,[0,0,0,0,0,32768]) := by decide
-- Original mcpuid_43; independent field extraction/packing calculation.
example : observation_mcpuid 137438953472 = (137438953472,[0,0,0,0,0,65536]) := by decide
-- Original mcpuid_44; independent field extraction/packing calculation.
example : observation_mcpuid 274877906944 = (274877906944,[0,0,0,0,0,131072]) := by decide
-- Original mcpuid_45; independent field extraction/packing calculation.
example : observation_mcpuid 549755813888 = (549755813888,[0,0,0,0,0,262144]) := by decide
-- Original mcpuid_46; independent field extraction/packing calculation.
example : observation_mcpuid 1099511627776 = (1099511627776,[0,0,0,0,0,524288]) := by decide
-- Original mcpuid_47; independent field extraction/packing calculation.
example : observation_mcpuid 2199023255552 = (2199023255552,[0,0,0,0,0,1048576]) := by decide
-- Original mcpuid_48; independent field extraction/packing calculation.
example : observation_mcpuid 4398046511104 = (4398046511104,[0,0,0,0,0,2097152]) := by decide
-- Original mcpuid_49; independent field extraction/packing calculation.
example : observation_mcpuid 8796093022208 = (8796093022208,[0,0,0,0,0,4194304]) := by decide
-- Original mcpuid_50; independent field extraction/packing calculation.
example : observation_mcpuid 17592186044416 = (17592186044416,[0,0,0,0,0,8388608]) := by decide
-- Original mcpuid_51; independent field extraction/packing calculation.
example : observation_mcpuid 35184372088832 = (35184372088832,[0,0,0,0,0,16777216]) := by decide
-- Original mcpuid_52; independent field extraction/packing calculation.
example : observation_mcpuid 70368744177664 = (70368744177664,[0,0,0,0,0,33554432]) := by decide
-- Original mcpuid_53; independent field extraction/packing calculation.
example : observation_mcpuid 140737488355328 = (140737488355328,[0,0,0,0,0,67108864]) := by decide
-- Original mcpuid_54; independent field extraction/packing calculation.
example : observation_mcpuid 281474976710656 = (281474976710656,[0,0,0,0,0,134217728]) := by decide
-- Original mcpuid_55; independent field extraction/packing calculation.
example : observation_mcpuid 562949953421312 = (562949953421312,[0,0,0,0,0,268435456]) := by decide
-- Original mcpuid_56; independent field extraction/packing calculation.
example : observation_mcpuid 1125899906842624 = (1125899906842624,[0,0,0,0,0,536870912]) := by decide
-- Original mcpuid_57; independent field extraction/packing calculation.
example : observation_mcpuid 2251799813685248 = (2251799813685248,[0,0,0,0,0,1073741824]) := by decide
-- Original mcpuid_58; independent field extraction/packing calculation.
example : observation_mcpuid 4503599627370496 = (4503599627370496,[0,0,0,0,0,2147483648]) := by decide
-- Original mcpuid_59; independent field extraction/packing calculation.
example : observation_mcpuid 9007199254740992 = (9007199254740992,[0,0,0,0,0,4294967296]) := by decide
-- Original mcpuid_60; independent field extraction/packing calculation.
example : observation_mcpuid 18014398509481984 = (18014398509481984,[0,0,0,0,0,8589934592]) := by decide
-- Original mcpuid_61; independent field extraction/packing calculation.
example : observation_mcpuid 36028797018963968 = (36028797018963968,[0,0,0,0,0,17179869184]) := by decide
-- Original mcpuid_62; independent field extraction/packing calculation.
example : observation_mcpuid 72057594037927936 = (72057594037927936,[0,0,0,0,0,34359738368]) := by decide
-- Original mcpuid_63; independent field extraction/packing calculation.
example : observation_mcpuid 144115188075855872 = (144115188075855872,[0,0,0,0,0,68719476736]) := by decide
-- Original mcpuid_64; independent field extraction/packing calculation.
example : observation_mcpuid 288230376151711744 = (288230376151711744,[0,0,0,0,0,137438953472]) := by decide
-- Original mcpuid_65; independent field extraction/packing calculation.
example : observation_mcpuid 576460752303423488 = (576460752303423488,[0,0,0,0,0,274877906944]) := by decide
-- Original mcpuid_66; independent field extraction/packing calculation.
example : observation_mcpuid 1152921504606846976 = (1152921504606846976,[0,0,0,0,0,549755813888]) := by decide
-- Original mcpuid_67; independent field extraction/packing calculation.
example : observation_mcpuid 2305843009213693952 = (2305843009213693952,[0,0,0,0,0,1099511627776]) := by decide
-- Original mcpuid_68; independent field extraction/packing calculation.
example : observation_mcpuid 4611686018427387904 = (4611686018427387904,[1,0,0,0,0,0]) := by decide
-- Original mcpuid_69; independent field extraction/packing calculation.
example : observation_mcpuid 9223372036854775808 = (9223372036854775808,[2,0,0,0,0,0]) := by decide
private def observation_mimpid (x : BitVec 64) :=
  let r := «rec'mimpid» x
  ( «reg'mimpid» r, ([r.RVImpl.toNat,r.RVSource.toNat] : List Nat))
-- Original mimpid_0; independent field extraction/packing calculation.
example : observation_mimpid 0 = (0,[0,0]) := by decide
-- Original mimpid_1; independent field extraction/packing calculation.
example : observation_mimpid 18446744073709551615 = (18446744073709551615,[281474976710655,65535]) := by decide
-- Original mimpid_2; independent field extraction/packing calculation.
example : observation_mimpid 12297829382473034410 = (12297829382473034410,[187649984473770,43690]) := by decide
-- Original mimpid_3; independent field extraction/packing calculation.
example : observation_mimpid 6148914691236517205 = (6148914691236517205,[93824992236885,21845]) := by decide
-- Original mimpid_4; independent field extraction/packing calculation.
example : observation_mimpid 81985529216486895 = (81985529216486895,[1250999896491,52719]) := by decide
-- Original mimpid_5; independent field extraction/packing calculation.
example : observation_mimpid 18364758544493064720 = (18364758544493064720,[280223976814164,12816]) := by decide
-- Original mimpid_6; independent field extraction/packing calculation.
example : observation_mimpid 1 = (1,[0,1]) := by decide
-- Original mimpid_7; independent field extraction/packing calculation.
example : observation_mimpid 2 = (2,[0,2]) := by decide
-- Original mimpid_8; independent field extraction/packing calculation.
example : observation_mimpid 4 = (4,[0,4]) := by decide
-- Original mimpid_9; independent field extraction/packing calculation.
example : observation_mimpid 8 = (8,[0,8]) := by decide
-- Original mimpid_10; independent field extraction/packing calculation.
example : observation_mimpid 16 = (16,[0,16]) := by decide
-- Original mimpid_11; independent field extraction/packing calculation.
example : observation_mimpid 32 = (32,[0,32]) := by decide
-- Original mimpid_12; independent field extraction/packing calculation.
example : observation_mimpid 64 = (64,[0,64]) := by decide
-- Original mimpid_13; independent field extraction/packing calculation.
example : observation_mimpid 128 = (128,[0,128]) := by decide
-- Original mimpid_14; independent field extraction/packing calculation.
example : observation_mimpid 256 = (256,[0,256]) := by decide
-- Original mimpid_15; independent field extraction/packing calculation.
example : observation_mimpid 512 = (512,[0,512]) := by decide
-- Original mimpid_16; independent field extraction/packing calculation.
example : observation_mimpid 1024 = (1024,[0,1024]) := by decide
-- Original mimpid_17; independent field extraction/packing calculation.
example : observation_mimpid 2048 = (2048,[0,2048]) := by decide
-- Original mimpid_18; independent field extraction/packing calculation.
example : observation_mimpid 4096 = (4096,[0,4096]) := by decide
-- Original mimpid_19; independent field extraction/packing calculation.
example : observation_mimpid 8192 = (8192,[0,8192]) := by decide
-- Original mimpid_20; independent field extraction/packing calculation.
example : observation_mimpid 16384 = (16384,[0,16384]) := by decide
-- Original mimpid_21; independent field extraction/packing calculation.
example : observation_mimpid 32768 = (32768,[0,32768]) := by decide
-- Original mimpid_22; independent field extraction/packing calculation.
example : observation_mimpid 65536 = (65536,[1,0]) := by decide
-- Original mimpid_23; independent field extraction/packing calculation.
example : observation_mimpid 131072 = (131072,[2,0]) := by decide
-- Original mimpid_24; independent field extraction/packing calculation.
example : observation_mimpid 262144 = (262144,[4,0]) := by decide
-- Original mimpid_25; independent field extraction/packing calculation.
example : observation_mimpid 524288 = (524288,[8,0]) := by decide
-- Original mimpid_26; independent field extraction/packing calculation.
example : observation_mimpid 1048576 = (1048576,[16,0]) := by decide
-- Original mimpid_27; independent field extraction/packing calculation.
example : observation_mimpid 2097152 = (2097152,[32,0]) := by decide
-- Original mimpid_28; independent field extraction/packing calculation.
example : observation_mimpid 4194304 = (4194304,[64,0]) := by decide
-- Original mimpid_29; independent field extraction/packing calculation.
example : observation_mimpid 8388608 = (8388608,[128,0]) := by decide
-- Original mimpid_30; independent field extraction/packing calculation.
example : observation_mimpid 16777216 = (16777216,[256,0]) := by decide
-- Original mimpid_31; independent field extraction/packing calculation.
example : observation_mimpid 33554432 = (33554432,[512,0]) := by decide
-- Original mimpid_32; independent field extraction/packing calculation.
example : observation_mimpid 67108864 = (67108864,[1024,0]) := by decide
-- Original mimpid_33; independent field extraction/packing calculation.
example : observation_mimpid 134217728 = (134217728,[2048,0]) := by decide
-- Original mimpid_34; independent field extraction/packing calculation.
example : observation_mimpid 268435456 = (268435456,[4096,0]) := by decide
-- Original mimpid_35; independent field extraction/packing calculation.
example : observation_mimpid 536870912 = (536870912,[8192,0]) := by decide
-- Original mimpid_36; independent field extraction/packing calculation.
example : observation_mimpid 1073741824 = (1073741824,[16384,0]) := by decide
-- Original mimpid_37; independent field extraction/packing calculation.
example : observation_mimpid 2147483648 = (2147483648,[32768,0]) := by decide
-- Original mimpid_38; independent field extraction/packing calculation.
example : observation_mimpid 4294967296 = (4294967296,[65536,0]) := by decide
-- Original mimpid_39; independent field extraction/packing calculation.
example : observation_mimpid 8589934592 = (8589934592,[131072,0]) := by decide
-- Original mimpid_40; independent field extraction/packing calculation.
example : observation_mimpid 17179869184 = (17179869184,[262144,0]) := by decide
-- Original mimpid_41; independent field extraction/packing calculation.
example : observation_mimpid 34359738368 = (34359738368,[524288,0]) := by decide
-- Original mimpid_42; independent field extraction/packing calculation.
example : observation_mimpid 68719476736 = (68719476736,[1048576,0]) := by decide
-- Original mimpid_43; independent field extraction/packing calculation.
example : observation_mimpid 137438953472 = (137438953472,[2097152,0]) := by decide
-- Original mimpid_44; independent field extraction/packing calculation.
example : observation_mimpid 274877906944 = (274877906944,[4194304,0]) := by decide
-- Original mimpid_45; independent field extraction/packing calculation.
example : observation_mimpid 549755813888 = (549755813888,[8388608,0]) := by decide
-- Original mimpid_46; independent field extraction/packing calculation.
example : observation_mimpid 1099511627776 = (1099511627776,[16777216,0]) := by decide
-- Original mimpid_47; independent field extraction/packing calculation.
example : observation_mimpid 2199023255552 = (2199023255552,[33554432,0]) := by decide
-- Original mimpid_48; independent field extraction/packing calculation.
example : observation_mimpid 4398046511104 = (4398046511104,[67108864,0]) := by decide
-- Original mimpid_49; independent field extraction/packing calculation.
example : observation_mimpid 8796093022208 = (8796093022208,[134217728,0]) := by decide
-- Original mimpid_50; independent field extraction/packing calculation.
example : observation_mimpid 17592186044416 = (17592186044416,[268435456,0]) := by decide
-- Original mimpid_51; independent field extraction/packing calculation.
example : observation_mimpid 35184372088832 = (35184372088832,[536870912,0]) := by decide
-- Original mimpid_52; independent field extraction/packing calculation.
example : observation_mimpid 70368744177664 = (70368744177664,[1073741824,0]) := by decide
-- Original mimpid_53; independent field extraction/packing calculation.
example : observation_mimpid 140737488355328 = (140737488355328,[2147483648,0]) := by decide
-- Original mimpid_54; independent field extraction/packing calculation.
example : observation_mimpid 281474976710656 = (281474976710656,[4294967296,0]) := by decide
-- Original mimpid_55; independent field extraction/packing calculation.
example : observation_mimpid 562949953421312 = (562949953421312,[8589934592,0]) := by decide
-- Original mimpid_56; independent field extraction/packing calculation.
example : observation_mimpid 1125899906842624 = (1125899906842624,[17179869184,0]) := by decide
-- Original mimpid_57; independent field extraction/packing calculation.
example : observation_mimpid 2251799813685248 = (2251799813685248,[34359738368,0]) := by decide
-- Original mimpid_58; independent field extraction/packing calculation.
example : observation_mimpid 4503599627370496 = (4503599627370496,[68719476736,0]) := by decide
-- Original mimpid_59; independent field extraction/packing calculation.
example : observation_mimpid 9007199254740992 = (9007199254740992,[137438953472,0]) := by decide
-- Original mimpid_60; independent field extraction/packing calculation.
example : observation_mimpid 18014398509481984 = (18014398509481984,[274877906944,0]) := by decide
-- Original mimpid_61; independent field extraction/packing calculation.
example : observation_mimpid 36028797018963968 = (36028797018963968,[549755813888,0]) := by decide
-- Original mimpid_62; independent field extraction/packing calculation.
example : observation_mimpid 72057594037927936 = (72057594037927936,[1099511627776,0]) := by decide
-- Original mimpid_63; independent field extraction/packing calculation.
example : observation_mimpid 144115188075855872 = (144115188075855872,[2199023255552,0]) := by decide
-- Original mimpid_64; independent field extraction/packing calculation.
example : observation_mimpid 288230376151711744 = (288230376151711744,[4398046511104,0]) := by decide
-- Original mimpid_65; independent field extraction/packing calculation.
example : observation_mimpid 576460752303423488 = (576460752303423488,[8796093022208,0]) := by decide
-- Original mimpid_66; independent field extraction/packing calculation.
example : observation_mimpid 1152921504606846976 = (1152921504606846976,[17592186044416,0]) := by decide
-- Original mimpid_67; independent field extraction/packing calculation.
example : observation_mimpid 2305843009213693952 = (2305843009213693952,[35184372088832,0]) := by decide
-- Original mimpid_68; independent field extraction/packing calculation.
example : observation_mimpid 4611686018427387904 = (4611686018427387904,[70368744177664,0]) := by decide
-- Original mimpid_69; independent field extraction/packing calculation.
example : observation_mimpid 9223372036854775808 = (9223372036854775808,[140737488355328,0]) := by decide
private def observation_mstatus (x : BitVec 64) :=
  let r := «rec'mstatus» x
  ( «reg'mstatus» r, ([r.MFS.toNat,(if r.MIE then 1 else 0),(if r.MIE1 then 1 else 0),(if r.MIE2 then 1 else 0),(if r.MIE3 then 1 else 0),(if r.MMPRV then 1 else 0),r.MPRV.toNat,r.MPRV1.toNat,r.MPRV2.toNat,r.MPRV3.toNat,(if r.MSD then 1 else 0),r.MXS.toNat,r.VM.toNat,r.«mstatus'rst».toNat] : List Nat))
-- Original mstatus_0; independent field extraction/packing calculation.
example : observation_mstatus 0 = (0,[0,0,0,0,0,0,0,0,0,0,0,0,0,0]) := by decide
-- Original mstatus_1; independent field extraction/packing calculation.
example : observation_mstatus 18446744073709551615 = (18446744073709551615,[3,1,1,1,1,1,3,3,3,3,1,3,31,2199023255551]) := by decide
-- Original mstatus_2; independent field extraction/packing calculation.
example : observation_mstatus 12297829382473034410 = (12297829382473034410,[2,0,1,0,1,0,1,2,1,2,1,2,21,733007751850]) := by decide
-- Original mstatus_3; independent field extraction/packing calculation.
example : observation_mstatus 6148914691236517205 = (6148914691236517205,[1,1,0,1,0,1,2,1,2,1,0,1,10,1466015503701]) := by decide
-- Original mstatus_4; independent field extraction/packing calculation.
example : observation_mstatus 81985529216486895 = (81985529216486895,[0,1,1,1,0,1,3,2,3,3,0,3,21,19546873382]) := by decide
-- Original mstatus_5; independent field extraction/packing calculation.
example : observation_mstatus 18364758544493064720 = (18364758544493064720,[3,0,0,0,1,0,0,1,0,0,1,0,10,2179476382169]) := by decide
-- Original mstatus_6; independent field extraction/packing calculation.
example : observation_mstatus 1 = (1,[0,1,0,0,0,0,0,0,0,0,0,0,0,0]) := by decide
-- Original mstatus_7; independent field extraction/packing calculation.
example : observation_mstatus 2 = (2,[0,0,0,0,0,0,1,0,0,0,0,0,0,0]) := by decide
-- Original mstatus_8; independent field extraction/packing calculation.
example : observation_mstatus 4 = (4,[0,0,0,0,0,0,2,0,0,0,0,0,0,0]) := by decide
-- Original mstatus_9; independent field extraction/packing calculation.
example : observation_mstatus 8 = (8,[0,0,1,0,0,0,0,0,0,0,0,0,0,0]) := by decide
-- Original mstatus_10; independent field extraction/packing calculation.
example : observation_mstatus 16 = (16,[0,0,0,0,0,0,0,1,0,0,0,0,0,0]) := by decide
-- Original mstatus_11; independent field extraction/packing calculation.
example : observation_mstatus 32 = (32,[0,0,0,0,0,0,0,2,0,0,0,0,0,0]) := by decide
-- Original mstatus_12; independent field extraction/packing calculation.
example : observation_mstatus 64 = (64,[0,0,0,1,0,0,0,0,0,0,0,0,0,0]) := by decide
-- Original mstatus_13; independent field extraction/packing calculation.
example : observation_mstatus 128 = (128,[0,0,0,0,0,0,0,0,1,0,0,0,0,0]) := by decide
-- Original mstatus_14; independent field extraction/packing calculation.
example : observation_mstatus 256 = (256,[0,0,0,0,0,0,0,0,2,0,0,0,0,0]) := by decide
-- Original mstatus_15; independent field extraction/packing calculation.
example : observation_mstatus 512 = (512,[0,0,0,0,1,0,0,0,0,0,0,0,0,0]) := by decide
-- Original mstatus_16; independent field extraction/packing calculation.
example : observation_mstatus 1024 = (1024,[0,0,0,0,0,0,0,0,0,1,0,0,0,0]) := by decide
-- Original mstatus_17; independent field extraction/packing calculation.
example : observation_mstatus 2048 = (2048,[0,0,0,0,0,0,0,0,0,2,0,0,0,0]) := by decide
-- Original mstatus_18; independent field extraction/packing calculation.
example : observation_mstatus 4096 = (4096,[1,0,0,0,0,0,0,0,0,0,0,0,0,0]) := by decide
-- Original mstatus_19; independent field extraction/packing calculation.
example : observation_mstatus 8192 = (8192,[2,0,0,0,0,0,0,0,0,0,0,0,0,0]) := by decide
-- Original mstatus_20; independent field extraction/packing calculation.
example : observation_mstatus 16384 = (16384,[0,0,0,0,0,0,0,0,0,0,0,1,0,0]) := by decide
-- Original mstatus_21; independent field extraction/packing calculation.
example : observation_mstatus 32768 = (32768,[0,0,0,0,0,0,0,0,0,0,0,2,0,0]) := by decide
-- Original mstatus_22; independent field extraction/packing calculation.
example : observation_mstatus 65536 = (65536,[0,0,0,0,0,1,0,0,0,0,0,0,0,0]) := by decide
-- Original mstatus_23; independent field extraction/packing calculation.
example : observation_mstatus 131072 = (131072,[0,0,0,0,0,0,0,0,0,0,0,0,1,0]) := by decide
-- Original mstatus_24; independent field extraction/packing calculation.
example : observation_mstatus 262144 = (262144,[0,0,0,0,0,0,0,0,0,0,0,0,2,0]) := by decide
-- Original mstatus_25; independent field extraction/packing calculation.
example : observation_mstatus 524288 = (524288,[0,0,0,0,0,0,0,0,0,0,0,0,4,0]) := by decide
-- Original mstatus_26; independent field extraction/packing calculation.
example : observation_mstatus 1048576 = (1048576,[0,0,0,0,0,0,0,0,0,0,0,0,8,0]) := by decide
-- Original mstatus_27; independent field extraction/packing calculation.
example : observation_mstatus 2097152 = (2097152,[0,0,0,0,0,0,0,0,0,0,0,0,16,0]) := by decide
-- Original mstatus_28; independent field extraction/packing calculation.
example : observation_mstatus 4194304 = (4194304,[0,0,0,0,0,0,0,0,0,0,0,0,0,1]) := by decide
-- Original mstatus_29; independent field extraction/packing calculation.
example : observation_mstatus 8388608 = (8388608,[0,0,0,0,0,0,0,0,0,0,0,0,0,2]) := by decide
-- Original mstatus_30; independent field extraction/packing calculation.
example : observation_mstatus 16777216 = (16777216,[0,0,0,0,0,0,0,0,0,0,0,0,0,4]) := by decide
-- Original mstatus_31; independent field extraction/packing calculation.
example : observation_mstatus 33554432 = (33554432,[0,0,0,0,0,0,0,0,0,0,0,0,0,8]) := by decide
-- Original mstatus_32; independent field extraction/packing calculation.
example : observation_mstatus 67108864 = (67108864,[0,0,0,0,0,0,0,0,0,0,0,0,0,16]) := by decide
-- Original mstatus_33; independent field extraction/packing calculation.
example : observation_mstatus 134217728 = (134217728,[0,0,0,0,0,0,0,0,0,0,0,0,0,32]) := by decide
-- Original mstatus_34; independent field extraction/packing calculation.
example : observation_mstatus 268435456 = (268435456,[0,0,0,0,0,0,0,0,0,0,0,0,0,64]) := by decide
-- Original mstatus_35; independent field extraction/packing calculation.
example : observation_mstatus 536870912 = (536870912,[0,0,0,0,0,0,0,0,0,0,0,0,0,128]) := by decide
-- Original mstatus_36; independent field extraction/packing calculation.
example : observation_mstatus 1073741824 = (1073741824,[0,0,0,0,0,0,0,0,0,0,0,0,0,256]) := by decide
-- Original mstatus_37; independent field extraction/packing calculation.
example : observation_mstatus 2147483648 = (2147483648,[0,0,0,0,0,0,0,0,0,0,0,0,0,512]) := by decide
-- Original mstatus_38; independent field extraction/packing calculation.
example : observation_mstatus 4294967296 = (4294967296,[0,0,0,0,0,0,0,0,0,0,0,0,0,1024]) := by decide
-- Original mstatus_39; independent field extraction/packing calculation.
example : observation_mstatus 8589934592 = (8589934592,[0,0,0,0,0,0,0,0,0,0,0,0,0,2048]) := by decide
-- Original mstatus_40; independent field extraction/packing calculation.
example : observation_mstatus 17179869184 = (17179869184,[0,0,0,0,0,0,0,0,0,0,0,0,0,4096]) := by decide
-- Original mstatus_41; independent field extraction/packing calculation.
example : observation_mstatus 34359738368 = (34359738368,[0,0,0,0,0,0,0,0,0,0,0,0,0,8192]) := by decide
-- Original mstatus_42; independent field extraction/packing calculation.
example : observation_mstatus 68719476736 = (68719476736,[0,0,0,0,0,0,0,0,0,0,0,0,0,16384]) := by decide
-- Original mstatus_43; independent field extraction/packing calculation.
example : observation_mstatus 137438953472 = (137438953472,[0,0,0,0,0,0,0,0,0,0,0,0,0,32768]) := by decide
-- Original mstatus_44; independent field extraction/packing calculation.
example : observation_mstatus 274877906944 = (274877906944,[0,0,0,0,0,0,0,0,0,0,0,0,0,65536]) := by decide
-- Original mstatus_45; independent field extraction/packing calculation.
example : observation_mstatus 549755813888 = (549755813888,[0,0,0,0,0,0,0,0,0,0,0,0,0,131072]) := by decide
-- Original mstatus_46; independent field extraction/packing calculation.
example : observation_mstatus 1099511627776 = (1099511627776,[0,0,0,0,0,0,0,0,0,0,0,0,0,262144]) := by decide
-- Original mstatus_47; independent field extraction/packing calculation.
example : observation_mstatus 2199023255552 = (2199023255552,[0,0,0,0,0,0,0,0,0,0,0,0,0,524288]) := by decide
-- Original mstatus_48; independent field extraction/packing calculation.
example : observation_mstatus 4398046511104 = (4398046511104,[0,0,0,0,0,0,0,0,0,0,0,0,0,1048576]) := by decide
-- Original mstatus_49; independent field extraction/packing calculation.
example : observation_mstatus 8796093022208 = (8796093022208,[0,0,0,0,0,0,0,0,0,0,0,0,0,2097152]) := by decide
-- Original mstatus_50; independent field extraction/packing calculation.
example : observation_mstatus 17592186044416 = (17592186044416,[0,0,0,0,0,0,0,0,0,0,0,0,0,4194304]) := by decide
-- Original mstatus_51; independent field extraction/packing calculation.
example : observation_mstatus 35184372088832 = (35184372088832,[0,0,0,0,0,0,0,0,0,0,0,0,0,8388608]) := by decide
-- Original mstatus_52; independent field extraction/packing calculation.
example : observation_mstatus 70368744177664 = (70368744177664,[0,0,0,0,0,0,0,0,0,0,0,0,0,16777216]) := by decide
-- Original mstatus_53; independent field extraction/packing calculation.
example : observation_mstatus 140737488355328 = (140737488355328,[0,0,0,0,0,0,0,0,0,0,0,0,0,33554432]) := by decide
-- Original mstatus_54; independent field extraction/packing calculation.
example : observation_mstatus 281474976710656 = (281474976710656,[0,0,0,0,0,0,0,0,0,0,0,0,0,67108864]) := by decide
-- Original mstatus_55; independent field extraction/packing calculation.
example : observation_mstatus 562949953421312 = (562949953421312,[0,0,0,0,0,0,0,0,0,0,0,0,0,134217728]) := by decide
-- Original mstatus_56; independent field extraction/packing calculation.
example : observation_mstatus 1125899906842624 = (1125899906842624,[0,0,0,0,0,0,0,0,0,0,0,0,0,268435456]) := by decide
-- Original mstatus_57; independent field extraction/packing calculation.
example : observation_mstatus 2251799813685248 = (2251799813685248,[0,0,0,0,0,0,0,0,0,0,0,0,0,536870912]) := by decide
-- Original mstatus_58; independent field extraction/packing calculation.
example : observation_mstatus 4503599627370496 = (4503599627370496,[0,0,0,0,0,0,0,0,0,0,0,0,0,1073741824]) := by decide
-- Original mstatus_59; independent field extraction/packing calculation.
example : observation_mstatus 9007199254740992 = (9007199254740992,[0,0,0,0,0,0,0,0,0,0,0,0,0,2147483648]) := by decide
-- Original mstatus_60; independent field extraction/packing calculation.
example : observation_mstatus 18014398509481984 = (18014398509481984,[0,0,0,0,0,0,0,0,0,0,0,0,0,4294967296]) := by decide
-- Original mstatus_61; independent field extraction/packing calculation.
example : observation_mstatus 36028797018963968 = (36028797018963968,[0,0,0,0,0,0,0,0,0,0,0,0,0,8589934592]) := by decide
-- Original mstatus_62; independent field extraction/packing calculation.
example : observation_mstatus 72057594037927936 = (72057594037927936,[0,0,0,0,0,0,0,0,0,0,0,0,0,17179869184]) := by decide
-- Original mstatus_63; independent field extraction/packing calculation.
example : observation_mstatus 144115188075855872 = (144115188075855872,[0,0,0,0,0,0,0,0,0,0,0,0,0,34359738368]) := by decide
-- Original mstatus_64; independent field extraction/packing calculation.
example : observation_mstatus 288230376151711744 = (288230376151711744,[0,0,0,0,0,0,0,0,0,0,0,0,0,68719476736]) := by decide
-- Original mstatus_65; independent field extraction/packing calculation.
example : observation_mstatus 576460752303423488 = (576460752303423488,[0,0,0,0,0,0,0,0,0,0,0,0,0,137438953472]) := by decide
-- Original mstatus_66; independent field extraction/packing calculation.
example : observation_mstatus 1152921504606846976 = (1152921504606846976,[0,0,0,0,0,0,0,0,0,0,0,0,0,274877906944]) := by decide
-- Original mstatus_67; independent field extraction/packing calculation.
example : observation_mstatus 2305843009213693952 = (2305843009213693952,[0,0,0,0,0,0,0,0,0,0,0,0,0,549755813888]) := by decide
-- Original mstatus_68; independent field extraction/packing calculation.
example : observation_mstatus 4611686018427387904 = (4611686018427387904,[0,0,0,0,0,0,0,0,0,0,0,0,0,1099511627776]) := by decide
-- Original mstatus_69; independent field extraction/packing calculation.
example : observation_mstatus 9223372036854775808 = (9223372036854775808,[0,0,0,0,0,0,0,0,0,0,1,0,0,0]) := by decide
private def observation_mtdeleg (x : BitVec 64) :=
  let r := «rec'mtdeleg» x
  ( «reg'mtdeleg» r, ([r.Exc_deleg.toNat,r.Intr_deleg.toNat] : List Nat))
-- Original mtdeleg_0; independent field extraction/packing calculation.
example : observation_mtdeleg 0 = (0,[0,0]) := by decide
-- Original mtdeleg_1; independent field extraction/packing calculation.
example : observation_mtdeleg 18446744073709551615 = (18446744073709551615,[65535,281474976710655]) := by decide
-- Original mtdeleg_2; independent field extraction/packing calculation.
example : observation_mtdeleg 12297829382473034410 = (12297829382473034410,[43690,187649984473770]) := by decide
-- Original mtdeleg_3; independent field extraction/packing calculation.
example : observation_mtdeleg 6148914691236517205 = (6148914691236517205,[21845,93824992236885]) := by decide
-- Original mtdeleg_4; independent field extraction/packing calculation.
example : observation_mtdeleg 81985529216486895 = (81985529216486895,[52719,1250999896491]) := by decide
-- Original mtdeleg_5; independent field extraction/packing calculation.
example : observation_mtdeleg 18364758544493064720 = (18364758544493064720,[12816,280223976814164]) := by decide
-- Original mtdeleg_6; independent field extraction/packing calculation.
example : observation_mtdeleg 1 = (1,[1,0]) := by decide
-- Original mtdeleg_7; independent field extraction/packing calculation.
example : observation_mtdeleg 2 = (2,[2,0]) := by decide
-- Original mtdeleg_8; independent field extraction/packing calculation.
example : observation_mtdeleg 4 = (4,[4,0]) := by decide
-- Original mtdeleg_9; independent field extraction/packing calculation.
example : observation_mtdeleg 8 = (8,[8,0]) := by decide
-- Original mtdeleg_10; independent field extraction/packing calculation.
example : observation_mtdeleg 16 = (16,[16,0]) := by decide
-- Original mtdeleg_11; independent field extraction/packing calculation.
example : observation_mtdeleg 32 = (32,[32,0]) := by decide
-- Original mtdeleg_12; independent field extraction/packing calculation.
example : observation_mtdeleg 64 = (64,[64,0]) := by decide
-- Original mtdeleg_13; independent field extraction/packing calculation.
example : observation_mtdeleg 128 = (128,[128,0]) := by decide
-- Original mtdeleg_14; independent field extraction/packing calculation.
example : observation_mtdeleg 256 = (256,[256,0]) := by decide
-- Original mtdeleg_15; independent field extraction/packing calculation.
example : observation_mtdeleg 512 = (512,[512,0]) := by decide
-- Original mtdeleg_16; independent field extraction/packing calculation.
example : observation_mtdeleg 1024 = (1024,[1024,0]) := by decide
-- Original mtdeleg_17; independent field extraction/packing calculation.
example : observation_mtdeleg 2048 = (2048,[2048,0]) := by decide
-- Original mtdeleg_18; independent field extraction/packing calculation.
example : observation_mtdeleg 4096 = (4096,[4096,0]) := by decide
-- Original mtdeleg_19; independent field extraction/packing calculation.
example : observation_mtdeleg 8192 = (8192,[8192,0]) := by decide
-- Original mtdeleg_20; independent field extraction/packing calculation.
example : observation_mtdeleg 16384 = (16384,[16384,0]) := by decide
-- Original mtdeleg_21; independent field extraction/packing calculation.
example : observation_mtdeleg 32768 = (32768,[32768,0]) := by decide
-- Original mtdeleg_22; independent field extraction/packing calculation.
example : observation_mtdeleg 65536 = (65536,[0,1]) := by decide
-- Original mtdeleg_23; independent field extraction/packing calculation.
example : observation_mtdeleg 131072 = (131072,[0,2]) := by decide
-- Original mtdeleg_24; independent field extraction/packing calculation.
example : observation_mtdeleg 262144 = (262144,[0,4]) := by decide
-- Original mtdeleg_25; independent field extraction/packing calculation.
example : observation_mtdeleg 524288 = (524288,[0,8]) := by decide
-- Original mtdeleg_26; independent field extraction/packing calculation.
example : observation_mtdeleg 1048576 = (1048576,[0,16]) := by decide
-- Original mtdeleg_27; independent field extraction/packing calculation.
example : observation_mtdeleg 2097152 = (2097152,[0,32]) := by decide
-- Original mtdeleg_28; independent field extraction/packing calculation.
example : observation_mtdeleg 4194304 = (4194304,[0,64]) := by decide
-- Original mtdeleg_29; independent field extraction/packing calculation.
example : observation_mtdeleg 8388608 = (8388608,[0,128]) := by decide
-- Original mtdeleg_30; independent field extraction/packing calculation.
example : observation_mtdeleg 16777216 = (16777216,[0,256]) := by decide
-- Original mtdeleg_31; independent field extraction/packing calculation.
example : observation_mtdeleg 33554432 = (33554432,[0,512]) := by decide
-- Original mtdeleg_32; independent field extraction/packing calculation.
example : observation_mtdeleg 67108864 = (67108864,[0,1024]) := by decide
-- Original mtdeleg_33; independent field extraction/packing calculation.
example : observation_mtdeleg 134217728 = (134217728,[0,2048]) := by decide
-- Original mtdeleg_34; independent field extraction/packing calculation.
example : observation_mtdeleg 268435456 = (268435456,[0,4096]) := by decide
-- Original mtdeleg_35; independent field extraction/packing calculation.
example : observation_mtdeleg 536870912 = (536870912,[0,8192]) := by decide
-- Original mtdeleg_36; independent field extraction/packing calculation.
example : observation_mtdeleg 1073741824 = (1073741824,[0,16384]) := by decide
-- Original mtdeleg_37; independent field extraction/packing calculation.
example : observation_mtdeleg 2147483648 = (2147483648,[0,32768]) := by decide
-- Original mtdeleg_38; independent field extraction/packing calculation.
example : observation_mtdeleg 4294967296 = (4294967296,[0,65536]) := by decide
-- Original mtdeleg_39; independent field extraction/packing calculation.
example : observation_mtdeleg 8589934592 = (8589934592,[0,131072]) := by decide
-- Original mtdeleg_40; independent field extraction/packing calculation.
example : observation_mtdeleg 17179869184 = (17179869184,[0,262144]) := by decide
-- Original mtdeleg_41; independent field extraction/packing calculation.
example : observation_mtdeleg 34359738368 = (34359738368,[0,524288]) := by decide
-- Original mtdeleg_42; independent field extraction/packing calculation.
example : observation_mtdeleg 68719476736 = (68719476736,[0,1048576]) := by decide
-- Original mtdeleg_43; independent field extraction/packing calculation.
example : observation_mtdeleg 137438953472 = (137438953472,[0,2097152]) := by decide
-- Original mtdeleg_44; independent field extraction/packing calculation.
example : observation_mtdeleg 274877906944 = (274877906944,[0,4194304]) := by decide
-- Original mtdeleg_45; independent field extraction/packing calculation.
example : observation_mtdeleg 549755813888 = (549755813888,[0,8388608]) := by decide
-- Original mtdeleg_46; independent field extraction/packing calculation.
example : observation_mtdeleg 1099511627776 = (1099511627776,[0,16777216]) := by decide
-- Original mtdeleg_47; independent field extraction/packing calculation.
example : observation_mtdeleg 2199023255552 = (2199023255552,[0,33554432]) := by decide
-- Original mtdeleg_48; independent field extraction/packing calculation.
example : observation_mtdeleg 4398046511104 = (4398046511104,[0,67108864]) := by decide
-- Original mtdeleg_49; independent field extraction/packing calculation.
example : observation_mtdeleg 8796093022208 = (8796093022208,[0,134217728]) := by decide
-- Original mtdeleg_50; independent field extraction/packing calculation.
example : observation_mtdeleg 17592186044416 = (17592186044416,[0,268435456]) := by decide
-- Original mtdeleg_51; independent field extraction/packing calculation.
example : observation_mtdeleg 35184372088832 = (35184372088832,[0,536870912]) := by decide
-- Original mtdeleg_52; independent field extraction/packing calculation.
example : observation_mtdeleg 70368744177664 = (70368744177664,[0,1073741824]) := by decide
-- Original mtdeleg_53; independent field extraction/packing calculation.
example : observation_mtdeleg 140737488355328 = (140737488355328,[0,2147483648]) := by decide
-- Original mtdeleg_54; independent field extraction/packing calculation.
example : observation_mtdeleg 281474976710656 = (281474976710656,[0,4294967296]) := by decide
-- Original mtdeleg_55; independent field extraction/packing calculation.
example : observation_mtdeleg 562949953421312 = (562949953421312,[0,8589934592]) := by decide
-- Original mtdeleg_56; independent field extraction/packing calculation.
example : observation_mtdeleg 1125899906842624 = (1125899906842624,[0,17179869184]) := by decide
-- Original mtdeleg_57; independent field extraction/packing calculation.
example : observation_mtdeleg 2251799813685248 = (2251799813685248,[0,34359738368]) := by decide
-- Original mtdeleg_58; independent field extraction/packing calculation.
example : observation_mtdeleg 4503599627370496 = (4503599627370496,[0,68719476736]) := by decide
-- Original mtdeleg_59; independent field extraction/packing calculation.
example : observation_mtdeleg 9007199254740992 = (9007199254740992,[0,137438953472]) := by decide
-- Original mtdeleg_60; independent field extraction/packing calculation.
example : observation_mtdeleg 18014398509481984 = (18014398509481984,[0,274877906944]) := by decide
-- Original mtdeleg_61; independent field extraction/packing calculation.
example : observation_mtdeleg 36028797018963968 = (36028797018963968,[0,549755813888]) := by decide
-- Original mtdeleg_62; independent field extraction/packing calculation.
example : observation_mtdeleg 72057594037927936 = (72057594037927936,[0,1099511627776]) := by decide
-- Original mtdeleg_63; independent field extraction/packing calculation.
example : observation_mtdeleg 144115188075855872 = (144115188075855872,[0,2199023255552]) := by decide
-- Original mtdeleg_64; independent field extraction/packing calculation.
example : observation_mtdeleg 288230376151711744 = (288230376151711744,[0,4398046511104]) := by decide
-- Original mtdeleg_65; independent field extraction/packing calculation.
example : observation_mtdeleg 576460752303423488 = (576460752303423488,[0,8796093022208]) := by decide
-- Original mtdeleg_66; independent field extraction/packing calculation.
example : observation_mtdeleg 1152921504606846976 = (1152921504606846976,[0,17592186044416]) := by decide
-- Original mtdeleg_67; independent field extraction/packing calculation.
example : observation_mtdeleg 2305843009213693952 = (2305843009213693952,[0,35184372088832]) := by decide
-- Original mtdeleg_68; independent field extraction/packing calculation.
example : observation_mtdeleg 4611686018427387904 = (4611686018427387904,[0,70368744177664]) := by decide
-- Original mtdeleg_69; independent field extraction/packing calculation.
example : observation_mtdeleg 9223372036854775808 = (9223372036854775808,[0,140737488355328]) := by decide
private def observation_mip (x : BitVec 64) :=
  let r := «rec'mip» x
  ( «reg'mip» r, ([(if r.HSIP then 1 else 0),(if r.HTIP then 1 else 0),(if r.MSIP then 1 else 0),(if r.MTIP then 1 else 0),(if r.SSIP then 1 else 0),(if r.STIP then 1 else 0),r.«mip'rst».toNat] : List Nat))
-- Original mip_0; independent field extraction/packing calculation.
example : observation_mip 0 = (0,[0,0,0,0,0,0,0]) := by decide
-- Original mip_1; independent field extraction/packing calculation.
example : observation_mip 18446744073709551615 = (18446744073709551615,[1,1,1,1,1,1,288230376151711743]) := by decide
-- Original mip_2; independent field extraction/packing calculation.
example : observation_mip 12297829382473034410 = (12297829382473034410,[0,0,1,1,1,1,48038396025285290]) := by decide
-- Original mip_3; independent field extraction/packing calculation.
example : observation_mip 6148914691236517205 = (6148914691236517205,[1,1,0,0,0,0,240191980126426453]) := by decide
-- Original mip_4; independent field extraction/packing calculation.
example : observation_mip 81985529216486895 = (81985529216486895,[1,1,1,1,1,1,144435444049357773]) := by decide
-- Original mip_5; independent field extraction/packing calculation.
example : observation_mip 18364758544493064720 = (18364758544493064720,[0,0,0,0,0,0,143794932102353970]) := by decide
-- Original mip_6; independent field extraction/packing calculation.
example : observation_mip 1 = (1,[0,0,0,0,0,0,144115188075855872]) := by decide
-- Original mip_7; independent field extraction/packing calculation.
example : observation_mip 2 = (2,[0,0,0,0,1,0,0]) := by decide
-- Original mip_8; independent field extraction/packing calculation.
example : observation_mip 4 = (4,[1,0,0,0,0,0,0]) := by decide
-- Original mip_9; independent field extraction/packing calculation.
example : observation_mip 8 = (8,[0,0,1,0,0,0,0]) := by decide
-- Original mip_10; independent field extraction/packing calculation.
example : observation_mip 16 = (16,[0,0,0,0,0,0,72057594037927936]) := by decide
-- Original mip_11; independent field extraction/packing calculation.
example : observation_mip 32 = (32,[0,0,0,0,0,1,0]) := by decide
-- Original mip_12; independent field extraction/packing calculation.
example : observation_mip 64 = (64,[0,1,0,0,0,0,0]) := by decide
-- Original mip_13; independent field extraction/packing calculation.
example : observation_mip 128 = (128,[0,0,0,1,0,0,0]) := by decide
-- Original mip_14; independent field extraction/packing calculation.
example : observation_mip 256 = (256,[0,0,0,0,0,0,1]) := by decide
-- Original mip_15; independent field extraction/packing calculation.
example : observation_mip 512 = (512,[0,0,0,0,0,0,2]) := by decide
-- Original mip_16; independent field extraction/packing calculation.
example : observation_mip 1024 = (1024,[0,0,0,0,0,0,4]) := by decide
-- Original mip_17; independent field extraction/packing calculation.
example : observation_mip 2048 = (2048,[0,0,0,0,0,0,8]) := by decide
-- Original mip_18; independent field extraction/packing calculation.
example : observation_mip 4096 = (4096,[0,0,0,0,0,0,16]) := by decide
-- Original mip_19; independent field extraction/packing calculation.
example : observation_mip 8192 = (8192,[0,0,0,0,0,0,32]) := by decide
-- Original mip_20; independent field extraction/packing calculation.
example : observation_mip 16384 = (16384,[0,0,0,0,0,0,64]) := by decide
-- Original mip_21; independent field extraction/packing calculation.
example : observation_mip 32768 = (32768,[0,0,0,0,0,0,128]) := by decide
-- Original mip_22; independent field extraction/packing calculation.
example : observation_mip 65536 = (65536,[0,0,0,0,0,0,256]) := by decide
-- Original mip_23; independent field extraction/packing calculation.
example : observation_mip 131072 = (131072,[0,0,0,0,0,0,512]) := by decide
-- Original mip_24; independent field extraction/packing calculation.
example : observation_mip 262144 = (262144,[0,0,0,0,0,0,1024]) := by decide
-- Original mip_25; independent field extraction/packing calculation.
example : observation_mip 524288 = (524288,[0,0,0,0,0,0,2048]) := by decide
-- Original mip_26; independent field extraction/packing calculation.
example : observation_mip 1048576 = (1048576,[0,0,0,0,0,0,4096]) := by decide
-- Original mip_27; independent field extraction/packing calculation.
example : observation_mip 2097152 = (2097152,[0,0,0,0,0,0,8192]) := by decide
-- Original mip_28; independent field extraction/packing calculation.
example : observation_mip 4194304 = (4194304,[0,0,0,0,0,0,16384]) := by decide
-- Original mip_29; independent field extraction/packing calculation.
example : observation_mip 8388608 = (8388608,[0,0,0,0,0,0,32768]) := by decide
-- Original mip_30; independent field extraction/packing calculation.
example : observation_mip 16777216 = (16777216,[0,0,0,0,0,0,65536]) := by decide
-- Original mip_31; independent field extraction/packing calculation.
example : observation_mip 33554432 = (33554432,[0,0,0,0,0,0,131072]) := by decide
-- Original mip_32; independent field extraction/packing calculation.
example : observation_mip 67108864 = (67108864,[0,0,0,0,0,0,262144]) := by decide
-- Original mip_33; independent field extraction/packing calculation.
example : observation_mip 134217728 = (134217728,[0,0,0,0,0,0,524288]) := by decide
-- Original mip_34; independent field extraction/packing calculation.
example : observation_mip 268435456 = (268435456,[0,0,0,0,0,0,1048576]) := by decide
-- Original mip_35; independent field extraction/packing calculation.
example : observation_mip 536870912 = (536870912,[0,0,0,0,0,0,2097152]) := by decide
-- Original mip_36; independent field extraction/packing calculation.
example : observation_mip 1073741824 = (1073741824,[0,0,0,0,0,0,4194304]) := by decide
-- Original mip_37; independent field extraction/packing calculation.
example : observation_mip 2147483648 = (2147483648,[0,0,0,0,0,0,8388608]) := by decide
-- Original mip_38; independent field extraction/packing calculation.
example : observation_mip 4294967296 = (4294967296,[0,0,0,0,0,0,16777216]) := by decide
-- Original mip_39; independent field extraction/packing calculation.
example : observation_mip 8589934592 = (8589934592,[0,0,0,0,0,0,33554432]) := by decide
-- Original mip_40; independent field extraction/packing calculation.
example : observation_mip 17179869184 = (17179869184,[0,0,0,0,0,0,67108864]) := by decide
-- Original mip_41; independent field extraction/packing calculation.
example : observation_mip 34359738368 = (34359738368,[0,0,0,0,0,0,134217728]) := by decide
-- Original mip_42; independent field extraction/packing calculation.
example : observation_mip 68719476736 = (68719476736,[0,0,0,0,0,0,268435456]) := by decide
-- Original mip_43; independent field extraction/packing calculation.
example : observation_mip 137438953472 = (137438953472,[0,0,0,0,0,0,536870912]) := by decide
-- Original mip_44; independent field extraction/packing calculation.
example : observation_mip 274877906944 = (274877906944,[0,0,0,0,0,0,1073741824]) := by decide
-- Original mip_45; independent field extraction/packing calculation.
example : observation_mip 549755813888 = (549755813888,[0,0,0,0,0,0,2147483648]) := by decide
-- Original mip_46; independent field extraction/packing calculation.
example : observation_mip 1099511627776 = (1099511627776,[0,0,0,0,0,0,4294967296]) := by decide
-- Original mip_47; independent field extraction/packing calculation.
example : observation_mip 2199023255552 = (2199023255552,[0,0,0,0,0,0,8589934592]) := by decide
-- Original mip_48; independent field extraction/packing calculation.
example : observation_mip 4398046511104 = (4398046511104,[0,0,0,0,0,0,17179869184]) := by decide
-- Original mip_49; independent field extraction/packing calculation.
example : observation_mip 8796093022208 = (8796093022208,[0,0,0,0,0,0,34359738368]) := by decide
-- Original mip_50; independent field extraction/packing calculation.
example : observation_mip 17592186044416 = (17592186044416,[0,0,0,0,0,0,68719476736]) := by decide
-- Original mip_51; independent field extraction/packing calculation.
example : observation_mip 35184372088832 = (35184372088832,[0,0,0,0,0,0,137438953472]) := by decide
-- Original mip_52; independent field extraction/packing calculation.
example : observation_mip 70368744177664 = (70368744177664,[0,0,0,0,0,0,274877906944]) := by decide
-- Original mip_53; independent field extraction/packing calculation.
example : observation_mip 140737488355328 = (140737488355328,[0,0,0,0,0,0,549755813888]) := by decide
-- Original mip_54; independent field extraction/packing calculation.
example : observation_mip 281474976710656 = (281474976710656,[0,0,0,0,0,0,1099511627776]) := by decide
-- Original mip_55; independent field extraction/packing calculation.
example : observation_mip 562949953421312 = (562949953421312,[0,0,0,0,0,0,2199023255552]) := by decide
-- Original mip_56; independent field extraction/packing calculation.
example : observation_mip 1125899906842624 = (1125899906842624,[0,0,0,0,0,0,4398046511104]) := by decide
-- Original mip_57; independent field extraction/packing calculation.
example : observation_mip 2251799813685248 = (2251799813685248,[0,0,0,0,0,0,8796093022208]) := by decide
-- Original mip_58; independent field extraction/packing calculation.
example : observation_mip 4503599627370496 = (4503599627370496,[0,0,0,0,0,0,17592186044416]) := by decide
-- Original mip_59; independent field extraction/packing calculation.
example : observation_mip 9007199254740992 = (9007199254740992,[0,0,0,0,0,0,35184372088832]) := by decide
-- Original mip_60; independent field extraction/packing calculation.
example : observation_mip 18014398509481984 = (18014398509481984,[0,0,0,0,0,0,70368744177664]) := by decide
-- Original mip_61; independent field extraction/packing calculation.
example : observation_mip 36028797018963968 = (36028797018963968,[0,0,0,0,0,0,140737488355328]) := by decide
-- Original mip_62; independent field extraction/packing calculation.
example : observation_mip 72057594037927936 = (72057594037927936,[0,0,0,0,0,0,281474976710656]) := by decide
-- Original mip_63; independent field extraction/packing calculation.
example : observation_mip 144115188075855872 = (144115188075855872,[0,0,0,0,0,0,562949953421312]) := by decide
-- Original mip_64; independent field extraction/packing calculation.
example : observation_mip 288230376151711744 = (288230376151711744,[0,0,0,0,0,0,1125899906842624]) := by decide
-- Original mip_65; independent field extraction/packing calculation.
example : observation_mip 576460752303423488 = (576460752303423488,[0,0,0,0,0,0,2251799813685248]) := by decide
-- Original mip_66; independent field extraction/packing calculation.
example : observation_mip 1152921504606846976 = (1152921504606846976,[0,0,0,0,0,0,4503599627370496]) := by decide
-- Original mip_67; independent field extraction/packing calculation.
example : observation_mip 2305843009213693952 = (2305843009213693952,[0,0,0,0,0,0,9007199254740992]) := by decide
-- Original mip_68; independent field extraction/packing calculation.
example : observation_mip 4611686018427387904 = (4611686018427387904,[0,0,0,0,0,0,18014398509481984]) := by decide
-- Original mip_69; independent field extraction/packing calculation.
example : observation_mip 9223372036854775808 = (9223372036854775808,[0,0,0,0,0,0,36028797018963968]) := by decide
private def observation_mie (x : BitVec 64) :=
  let r := «rec'mie» x
  ( «reg'mie» r, ([(if r.HSIE then 1 else 0),(if r.HTIE then 1 else 0),(if r.MSIE then 1 else 0),(if r.MTIE then 1 else 0),(if r.SSIE then 1 else 0),(if r.STIE then 1 else 0),r.«mie'rst».toNat] : List Nat))
-- Original mie_0; independent field extraction/packing calculation.
example : observation_mie 0 = (0,[0,0,0,0,0,0,0]) := by decide
-- Original mie_1; independent field extraction/packing calculation.
example : observation_mie 18446744073709551615 = (18446744073709551615,[1,1,1,1,1,1,288230376151711743]) := by decide
-- Original mie_2; independent field extraction/packing calculation.
example : observation_mie 12297829382473034410 = (12297829382473034410,[0,0,1,1,1,1,48038396025285290]) := by decide
-- Original mie_3; independent field extraction/packing calculation.
example : observation_mie 6148914691236517205 = (6148914691236517205,[1,1,0,0,0,0,240191980126426453]) := by decide
-- Original mie_4; independent field extraction/packing calculation.
example : observation_mie 81985529216486895 = (81985529216486895,[1,1,1,1,1,1,144435444049357773]) := by decide
-- Original mie_5; independent field extraction/packing calculation.
example : observation_mie 18364758544493064720 = (18364758544493064720,[0,0,0,0,0,0,143794932102353970]) := by decide
-- Original mie_6; independent field extraction/packing calculation.
example : observation_mie 1 = (1,[0,0,0,0,0,0,144115188075855872]) := by decide
-- Original mie_7; independent field extraction/packing calculation.
example : observation_mie 2 = (2,[0,0,0,0,1,0,0]) := by decide
-- Original mie_8; independent field extraction/packing calculation.
example : observation_mie 4 = (4,[1,0,0,0,0,0,0]) := by decide
-- Original mie_9; independent field extraction/packing calculation.
example : observation_mie 8 = (8,[0,0,1,0,0,0,0]) := by decide
-- Original mie_10; independent field extraction/packing calculation.
example : observation_mie 16 = (16,[0,0,0,0,0,0,72057594037927936]) := by decide
-- Original mie_11; independent field extraction/packing calculation.
example : observation_mie 32 = (32,[0,0,0,0,0,1,0]) := by decide
-- Original mie_12; independent field extraction/packing calculation.
example : observation_mie 64 = (64,[0,1,0,0,0,0,0]) := by decide
-- Original mie_13; independent field extraction/packing calculation.
example : observation_mie 128 = (128,[0,0,0,1,0,0,0]) := by decide
-- Original mie_14; independent field extraction/packing calculation.
example : observation_mie 256 = (256,[0,0,0,0,0,0,1]) := by decide
-- Original mie_15; independent field extraction/packing calculation.
example : observation_mie 512 = (512,[0,0,0,0,0,0,2]) := by decide
-- Original mie_16; independent field extraction/packing calculation.
example : observation_mie 1024 = (1024,[0,0,0,0,0,0,4]) := by decide
-- Original mie_17; independent field extraction/packing calculation.
example : observation_mie 2048 = (2048,[0,0,0,0,0,0,8]) := by decide
-- Original mie_18; independent field extraction/packing calculation.
example : observation_mie 4096 = (4096,[0,0,0,0,0,0,16]) := by decide
-- Original mie_19; independent field extraction/packing calculation.
example : observation_mie 8192 = (8192,[0,0,0,0,0,0,32]) := by decide
-- Original mie_20; independent field extraction/packing calculation.
example : observation_mie 16384 = (16384,[0,0,0,0,0,0,64]) := by decide
-- Original mie_21; independent field extraction/packing calculation.
example : observation_mie 32768 = (32768,[0,0,0,0,0,0,128]) := by decide
-- Original mie_22; independent field extraction/packing calculation.
example : observation_mie 65536 = (65536,[0,0,0,0,0,0,256]) := by decide
-- Original mie_23; independent field extraction/packing calculation.
example : observation_mie 131072 = (131072,[0,0,0,0,0,0,512]) := by decide
-- Original mie_24; independent field extraction/packing calculation.
example : observation_mie 262144 = (262144,[0,0,0,0,0,0,1024]) := by decide
-- Original mie_25; independent field extraction/packing calculation.
example : observation_mie 524288 = (524288,[0,0,0,0,0,0,2048]) := by decide
-- Original mie_26; independent field extraction/packing calculation.
example : observation_mie 1048576 = (1048576,[0,0,0,0,0,0,4096]) := by decide
-- Original mie_27; independent field extraction/packing calculation.
example : observation_mie 2097152 = (2097152,[0,0,0,0,0,0,8192]) := by decide
-- Original mie_28; independent field extraction/packing calculation.
example : observation_mie 4194304 = (4194304,[0,0,0,0,0,0,16384]) := by decide
-- Original mie_29; independent field extraction/packing calculation.
example : observation_mie 8388608 = (8388608,[0,0,0,0,0,0,32768]) := by decide
-- Original mie_30; independent field extraction/packing calculation.
example : observation_mie 16777216 = (16777216,[0,0,0,0,0,0,65536]) := by decide
-- Original mie_31; independent field extraction/packing calculation.
example : observation_mie 33554432 = (33554432,[0,0,0,0,0,0,131072]) := by decide
-- Original mie_32; independent field extraction/packing calculation.
example : observation_mie 67108864 = (67108864,[0,0,0,0,0,0,262144]) := by decide
-- Original mie_33; independent field extraction/packing calculation.
example : observation_mie 134217728 = (134217728,[0,0,0,0,0,0,524288]) := by decide
-- Original mie_34; independent field extraction/packing calculation.
example : observation_mie 268435456 = (268435456,[0,0,0,0,0,0,1048576]) := by decide
-- Original mie_35; independent field extraction/packing calculation.
example : observation_mie 536870912 = (536870912,[0,0,0,0,0,0,2097152]) := by decide
-- Original mie_36; independent field extraction/packing calculation.
example : observation_mie 1073741824 = (1073741824,[0,0,0,0,0,0,4194304]) := by decide
-- Original mie_37; independent field extraction/packing calculation.
example : observation_mie 2147483648 = (2147483648,[0,0,0,0,0,0,8388608]) := by decide
-- Original mie_38; independent field extraction/packing calculation.
example : observation_mie 4294967296 = (4294967296,[0,0,0,0,0,0,16777216]) := by decide
-- Original mie_39; independent field extraction/packing calculation.
example : observation_mie 8589934592 = (8589934592,[0,0,0,0,0,0,33554432]) := by decide
-- Original mie_40; independent field extraction/packing calculation.
example : observation_mie 17179869184 = (17179869184,[0,0,0,0,0,0,67108864]) := by decide
-- Original mie_41; independent field extraction/packing calculation.
example : observation_mie 34359738368 = (34359738368,[0,0,0,0,0,0,134217728]) := by decide
-- Original mie_42; independent field extraction/packing calculation.
example : observation_mie 68719476736 = (68719476736,[0,0,0,0,0,0,268435456]) := by decide
-- Original mie_43; independent field extraction/packing calculation.
example : observation_mie 137438953472 = (137438953472,[0,0,0,0,0,0,536870912]) := by decide
-- Original mie_44; independent field extraction/packing calculation.
example : observation_mie 274877906944 = (274877906944,[0,0,0,0,0,0,1073741824]) := by decide
-- Original mie_45; independent field extraction/packing calculation.
example : observation_mie 549755813888 = (549755813888,[0,0,0,0,0,0,2147483648]) := by decide
-- Original mie_46; independent field extraction/packing calculation.
example : observation_mie 1099511627776 = (1099511627776,[0,0,0,0,0,0,4294967296]) := by decide
-- Original mie_47; independent field extraction/packing calculation.
example : observation_mie 2199023255552 = (2199023255552,[0,0,0,0,0,0,8589934592]) := by decide
-- Original mie_48; independent field extraction/packing calculation.
example : observation_mie 4398046511104 = (4398046511104,[0,0,0,0,0,0,17179869184]) := by decide
-- Original mie_49; independent field extraction/packing calculation.
example : observation_mie 8796093022208 = (8796093022208,[0,0,0,0,0,0,34359738368]) := by decide
-- Original mie_50; independent field extraction/packing calculation.
example : observation_mie 17592186044416 = (17592186044416,[0,0,0,0,0,0,68719476736]) := by decide
-- Original mie_51; independent field extraction/packing calculation.
example : observation_mie 35184372088832 = (35184372088832,[0,0,0,0,0,0,137438953472]) := by decide
-- Original mie_52; independent field extraction/packing calculation.
example : observation_mie 70368744177664 = (70368744177664,[0,0,0,0,0,0,274877906944]) := by decide
-- Original mie_53; independent field extraction/packing calculation.
example : observation_mie 140737488355328 = (140737488355328,[0,0,0,0,0,0,549755813888]) := by decide
-- Original mie_54; independent field extraction/packing calculation.
example : observation_mie 281474976710656 = (281474976710656,[0,0,0,0,0,0,1099511627776]) := by decide
-- Original mie_55; independent field extraction/packing calculation.
example : observation_mie 562949953421312 = (562949953421312,[0,0,0,0,0,0,2199023255552]) := by decide
-- Original mie_56; independent field extraction/packing calculation.
example : observation_mie 1125899906842624 = (1125899906842624,[0,0,0,0,0,0,4398046511104]) := by decide
-- Original mie_57; independent field extraction/packing calculation.
example : observation_mie 2251799813685248 = (2251799813685248,[0,0,0,0,0,0,8796093022208]) := by decide
-- Original mie_58; independent field extraction/packing calculation.
example : observation_mie 4503599627370496 = (4503599627370496,[0,0,0,0,0,0,17592186044416]) := by decide
-- Original mie_59; independent field extraction/packing calculation.
example : observation_mie 9007199254740992 = (9007199254740992,[0,0,0,0,0,0,35184372088832]) := by decide
-- Original mie_60; independent field extraction/packing calculation.
example : observation_mie 18014398509481984 = (18014398509481984,[0,0,0,0,0,0,70368744177664]) := by decide
-- Original mie_61; independent field extraction/packing calculation.
example : observation_mie 36028797018963968 = (36028797018963968,[0,0,0,0,0,0,140737488355328]) := by decide
-- Original mie_62; independent field extraction/packing calculation.
example : observation_mie 72057594037927936 = (72057594037927936,[0,0,0,0,0,0,281474976710656]) := by decide
-- Original mie_63; independent field extraction/packing calculation.
example : observation_mie 144115188075855872 = (144115188075855872,[0,0,0,0,0,0,562949953421312]) := by decide
-- Original mie_64; independent field extraction/packing calculation.
example : observation_mie 288230376151711744 = (288230376151711744,[0,0,0,0,0,0,1125899906842624]) := by decide
-- Original mie_65; independent field extraction/packing calculation.
example : observation_mie 576460752303423488 = (576460752303423488,[0,0,0,0,0,0,2251799813685248]) := by decide
-- Original mie_66; independent field extraction/packing calculation.
example : observation_mie 1152921504606846976 = (1152921504606846976,[0,0,0,0,0,0,4503599627370496]) := by decide
-- Original mie_67; independent field extraction/packing calculation.
example : observation_mie 2305843009213693952 = (2305843009213693952,[0,0,0,0,0,0,9007199254740992]) := by decide
-- Original mie_68; independent field extraction/packing calculation.
example : observation_mie 4611686018427387904 = (4611686018427387904,[0,0,0,0,0,0,18014398509481984]) := by decide
-- Original mie_69; independent field extraction/packing calculation.
example : observation_mie 9223372036854775808 = (9223372036854775808,[0,0,0,0,0,0,36028797018963968]) := by decide
private def observation_mcause (x : BitVec 64) :=
  let r := «rec'mcause» x
  ( «reg'mcause» r, ([r.EC.toNat,(if r.Int then 1 else 0),r.«mcause'rst».toNat] : List Nat))
-- Original mcause_0; independent field extraction/packing calculation.
example : observation_mcause 0 = (0,[0,0,0]) := by decide
-- Original mcause_1; independent field extraction/packing calculation.
example : observation_mcause 18446744073709551615 = (18446744073709551615,[15,1,576460752303423487]) := by decide
-- Original mcause_2; independent field extraction/packing calculation.
example : observation_mcause 12297829382473034410 = (12297829382473034410,[10,1,192153584101141162]) := by decide
-- Original mcause_3; independent field extraction/packing calculation.
example : observation_mcause 6148914691236517205 = (6148914691236517205,[5,0,384307168202282325]) := by decide
-- Original mcause_4; independent field extraction/packing calculation.
example : observation_mcause 81985529216486895 = (81985529216486895,[15,0,5124095576030430]) := by decide
-- Original mcause_5; independent field extraction/packing calculation.
example : observation_mcause 18364758544493064720 = (18364758544493064720,[0,1,571336656727393057]) := by decide
-- Original mcause_6; independent field extraction/packing calculation.
example : observation_mcause 1 = (1,[1,0,0]) := by decide
-- Original mcause_7; independent field extraction/packing calculation.
example : observation_mcause 2 = (2,[2,0,0]) := by decide
-- Original mcause_8; independent field extraction/packing calculation.
example : observation_mcause 4 = (4,[4,0,0]) := by decide
-- Original mcause_9; independent field extraction/packing calculation.
example : observation_mcause 8 = (8,[8,0,0]) := by decide
-- Original mcause_10; independent field extraction/packing calculation.
example : observation_mcause 16 = (16,[0,0,1]) := by decide
-- Original mcause_11; independent field extraction/packing calculation.
example : observation_mcause 32 = (32,[0,0,2]) := by decide
-- Original mcause_12; independent field extraction/packing calculation.
example : observation_mcause 64 = (64,[0,0,4]) := by decide
-- Original mcause_13; independent field extraction/packing calculation.
example : observation_mcause 128 = (128,[0,0,8]) := by decide
-- Original mcause_14; independent field extraction/packing calculation.
example : observation_mcause 256 = (256,[0,0,16]) := by decide
-- Original mcause_15; independent field extraction/packing calculation.
example : observation_mcause 512 = (512,[0,0,32]) := by decide
-- Original mcause_16; independent field extraction/packing calculation.
example : observation_mcause 1024 = (1024,[0,0,64]) := by decide
-- Original mcause_17; independent field extraction/packing calculation.
example : observation_mcause 2048 = (2048,[0,0,128]) := by decide
-- Original mcause_18; independent field extraction/packing calculation.
example : observation_mcause 4096 = (4096,[0,0,256]) := by decide
-- Original mcause_19; independent field extraction/packing calculation.
example : observation_mcause 8192 = (8192,[0,0,512]) := by decide
-- Original mcause_20; independent field extraction/packing calculation.
example : observation_mcause 16384 = (16384,[0,0,1024]) := by decide
-- Original mcause_21; independent field extraction/packing calculation.
example : observation_mcause 32768 = (32768,[0,0,2048]) := by decide
-- Original mcause_22; independent field extraction/packing calculation.
example : observation_mcause 65536 = (65536,[0,0,4096]) := by decide
-- Original mcause_23; independent field extraction/packing calculation.
example : observation_mcause 131072 = (131072,[0,0,8192]) := by decide
-- Original mcause_24; independent field extraction/packing calculation.
example : observation_mcause 262144 = (262144,[0,0,16384]) := by decide
-- Original mcause_25; independent field extraction/packing calculation.
example : observation_mcause 524288 = (524288,[0,0,32768]) := by decide
-- Original mcause_26; independent field extraction/packing calculation.
example : observation_mcause 1048576 = (1048576,[0,0,65536]) := by decide
-- Original mcause_27; independent field extraction/packing calculation.
example : observation_mcause 2097152 = (2097152,[0,0,131072]) := by decide
-- Original mcause_28; independent field extraction/packing calculation.
example : observation_mcause 4194304 = (4194304,[0,0,262144]) := by decide
-- Original mcause_29; independent field extraction/packing calculation.
example : observation_mcause 8388608 = (8388608,[0,0,524288]) := by decide
-- Original mcause_30; independent field extraction/packing calculation.
example : observation_mcause 16777216 = (16777216,[0,0,1048576]) := by decide
-- Original mcause_31; independent field extraction/packing calculation.
example : observation_mcause 33554432 = (33554432,[0,0,2097152]) := by decide
-- Original mcause_32; independent field extraction/packing calculation.
example : observation_mcause 67108864 = (67108864,[0,0,4194304]) := by decide
-- Original mcause_33; independent field extraction/packing calculation.
example : observation_mcause 134217728 = (134217728,[0,0,8388608]) := by decide
-- Original mcause_34; independent field extraction/packing calculation.
example : observation_mcause 268435456 = (268435456,[0,0,16777216]) := by decide
-- Original mcause_35; independent field extraction/packing calculation.
example : observation_mcause 536870912 = (536870912,[0,0,33554432]) := by decide
-- Original mcause_36; independent field extraction/packing calculation.
example : observation_mcause 1073741824 = (1073741824,[0,0,67108864]) := by decide
-- Original mcause_37; independent field extraction/packing calculation.
example : observation_mcause 2147483648 = (2147483648,[0,0,134217728]) := by decide
-- Original mcause_38; independent field extraction/packing calculation.
example : observation_mcause 4294967296 = (4294967296,[0,0,268435456]) := by decide
-- Original mcause_39; independent field extraction/packing calculation.
example : observation_mcause 8589934592 = (8589934592,[0,0,536870912]) := by decide
-- Original mcause_40; independent field extraction/packing calculation.
example : observation_mcause 17179869184 = (17179869184,[0,0,1073741824]) := by decide
-- Original mcause_41; independent field extraction/packing calculation.
example : observation_mcause 34359738368 = (34359738368,[0,0,2147483648]) := by decide
-- Original mcause_42; independent field extraction/packing calculation.
example : observation_mcause 68719476736 = (68719476736,[0,0,4294967296]) := by decide
-- Original mcause_43; independent field extraction/packing calculation.
example : observation_mcause 137438953472 = (137438953472,[0,0,8589934592]) := by decide
-- Original mcause_44; independent field extraction/packing calculation.
example : observation_mcause 274877906944 = (274877906944,[0,0,17179869184]) := by decide
-- Original mcause_45; independent field extraction/packing calculation.
example : observation_mcause 549755813888 = (549755813888,[0,0,34359738368]) := by decide
-- Original mcause_46; independent field extraction/packing calculation.
example : observation_mcause 1099511627776 = (1099511627776,[0,0,68719476736]) := by decide
-- Original mcause_47; independent field extraction/packing calculation.
example : observation_mcause 2199023255552 = (2199023255552,[0,0,137438953472]) := by decide
-- Original mcause_48; independent field extraction/packing calculation.
example : observation_mcause 4398046511104 = (4398046511104,[0,0,274877906944]) := by decide
-- Original mcause_49; independent field extraction/packing calculation.
example : observation_mcause 8796093022208 = (8796093022208,[0,0,549755813888]) := by decide
-- Original mcause_50; independent field extraction/packing calculation.
example : observation_mcause 17592186044416 = (17592186044416,[0,0,1099511627776]) := by decide
-- Original mcause_51; independent field extraction/packing calculation.
example : observation_mcause 35184372088832 = (35184372088832,[0,0,2199023255552]) := by decide
-- Original mcause_52; independent field extraction/packing calculation.
example : observation_mcause 70368744177664 = (70368744177664,[0,0,4398046511104]) := by decide
-- Original mcause_53; independent field extraction/packing calculation.
example : observation_mcause 140737488355328 = (140737488355328,[0,0,8796093022208]) := by decide
-- Original mcause_54; independent field extraction/packing calculation.
example : observation_mcause 281474976710656 = (281474976710656,[0,0,17592186044416]) := by decide
-- Original mcause_55; independent field extraction/packing calculation.
example : observation_mcause 562949953421312 = (562949953421312,[0,0,35184372088832]) := by decide
-- Original mcause_56; independent field extraction/packing calculation.
example : observation_mcause 1125899906842624 = (1125899906842624,[0,0,70368744177664]) := by decide
-- Original mcause_57; independent field extraction/packing calculation.
example : observation_mcause 2251799813685248 = (2251799813685248,[0,0,140737488355328]) := by decide
-- Original mcause_58; independent field extraction/packing calculation.
example : observation_mcause 4503599627370496 = (4503599627370496,[0,0,281474976710656]) := by decide
-- Original mcause_59; independent field extraction/packing calculation.
example : observation_mcause 9007199254740992 = (9007199254740992,[0,0,562949953421312]) := by decide
-- Original mcause_60; independent field extraction/packing calculation.
example : observation_mcause 18014398509481984 = (18014398509481984,[0,0,1125899906842624]) := by decide
-- Original mcause_61; independent field extraction/packing calculation.
example : observation_mcause 36028797018963968 = (36028797018963968,[0,0,2251799813685248]) := by decide
-- Original mcause_62; independent field extraction/packing calculation.
example : observation_mcause 72057594037927936 = (72057594037927936,[0,0,4503599627370496]) := by decide
-- Original mcause_63; independent field extraction/packing calculation.
example : observation_mcause 144115188075855872 = (144115188075855872,[0,0,9007199254740992]) := by decide
-- Original mcause_64; independent field extraction/packing calculation.
example : observation_mcause 288230376151711744 = (288230376151711744,[0,0,18014398509481984]) := by decide
-- Original mcause_65; independent field extraction/packing calculation.
example : observation_mcause 576460752303423488 = (576460752303423488,[0,0,36028797018963968]) := by decide
-- Original mcause_66; independent field extraction/packing calculation.
example : observation_mcause 1152921504606846976 = (1152921504606846976,[0,0,72057594037927936]) := by decide
-- Original mcause_67; independent field extraction/packing calculation.
example : observation_mcause 2305843009213693952 = (2305843009213693952,[0,0,144115188075855872]) := by decide
-- Original mcause_68; independent field extraction/packing calculation.
example : observation_mcause 4611686018427387904 = (4611686018427387904,[0,0,288230376151711744]) := by decide
-- Original mcause_69; independent field extraction/packing calculation.
example : observation_mcause 9223372036854775808 = (9223372036854775808,[0,1,0]) := by decide
end Flapjack.Test.L3MachineCSRCodecParity
