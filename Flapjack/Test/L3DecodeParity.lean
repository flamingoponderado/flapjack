import Flapjack.RiscV.L3.Defs.Decode

/-! Integer decoder acceptance rows use the original HOL oracle values.
Inputs that formerly selected FP, atomic, privileged, CSR or compressed
instructions now assert UnknownInstruction as branch-specific rejection tests.
These rejection results deliberately differ from the full HOL model.
-/
set_option maxRecDepth 200000
namespace Flapjack.Test.L3DecodeParity
open Flapjack.RiscV.L3

-- Oracle Decode_path0_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 99) = (instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path0_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294938595) = (instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path0_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863303395) = (instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 10), (BitVec.ofNat 12 3418)))))))) := by decide

-- Oracle Decode_path1_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4195) = (instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path1_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294942691) = (instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path1_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863307491) = (instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 10), (BitVec.ofNat 12 3418)))))))) := by decide

-- Oracle Decode_path2_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 16483) = (instruction.Branch ((Branch.BLT (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path2_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294954979) = (instruction.Branch ((Branch.BLT (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path2_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863319779) = (instruction.Branch ((Branch.BLT (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 10), (BitVec.ofNat 12 3418)))))))) := by decide

-- Oracle Decode_path3_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 20579) = (instruction.Branch ((Branch.BGE (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path3_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294959075) = (instruction.Branch ((Branch.BGE (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path3_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863323875) = (instruction.Branch ((Branch.BGE (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 10), (BitVec.ofNat 12 3418)))))))) := by decide

-- Oracle Decode_path4_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 24675) = (instruction.Branch ((Branch.BLTU (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path4_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294963171) = (instruction.Branch ((Branch.BLTU (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path4_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863327971) = (instruction.Branch ((Branch.BLTU (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 10), (BitVec.ofNat 12 3418)))))))) := by decide

-- Oracle Decode_path5_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 28771) = (instruction.Branch ((Branch.BGEU (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path5_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294967267) = (instruction.Branch ((Branch.BGEU (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path5_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863332067) = (instruction.Branch ((Branch.BGEU (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 10), (BitVec.ofNat 12 3418)))))))) := by decide

-- Oracle Decode_path6_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 103) = (instruction.Branch ((Branch.JALR (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path6_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294938599) = (instruction.Branch ((Branch.JALR (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path6_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863303399) = (instruction.Branch ((Branch.JALR (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 12 2730)))))))) := by decide

-- Oracle Decode_path7_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 111) = (instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 0)))))) := by decide

-- Oracle Decode_path7_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294967279) = (instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 31), (BitVec.ofNat 20 1048575)))))) := by decide

-- Oracle Decode_path7_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863311599) = (instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 21), (BitVec.ofNat 20 872789)))))) := by decide

-- Oracle Decode_path8_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 67) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path8_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4194303939) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path8_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2829757123) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path9_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 71) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path9_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4194303943) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path9_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2829757127) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path10_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 75) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path10_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4194303947) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path10_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2829757131) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path11_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 79) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path11_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4194303951) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path11_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2829757135) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path12_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 83) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path12_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 33554387) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path12_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 11184851) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path13_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 134217811) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path13_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 167772115) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path13_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 145402579) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path14_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 268435539) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path14_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 301989843) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path14_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 279620307) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path15_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 402653267) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path15_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 436207571) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path15_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 413838035) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path16_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1476395091) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path16_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1477443539) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path16_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1477094099) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path17_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 671088723) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path17_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 704614355) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path17_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 682265299) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path18_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 671092819) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path18_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 704618451) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path18_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 682269395) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path19_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2684362835) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path19_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2717888467) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path19_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2695539411) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path20_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2684358739) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path20_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2717884371) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path20_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2695535315) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path21_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2684354643) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path21_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2717880275) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path21_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2695531219) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path22_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 536870995) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path22_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 570396627) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path22_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 548047571) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path23_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 536875091) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path23_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 570400723) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path23_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 548051667) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path24_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 536879187) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path24_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 570404819) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path24_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 548055763) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path25_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3221225555) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path25_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3222274003) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path25_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3221924563) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path26_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3222274131) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path26_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3223322579) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path26_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3222973139) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path27_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3758096467) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path27_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3759116243) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path27_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3758787283) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path28_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3758100563) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path28_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3759120339) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path28_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3758791379) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path29_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3489661011) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path29_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3490709459) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path29_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3490360019) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path30_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3490709587) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path30_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3491758035) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path30_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3491408595) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path31_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4026531923) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path31_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4027551699) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path31_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4027222739) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path32_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 33554499) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path32_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4227858371) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path32_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2863311555) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path33_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 33554503) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path33_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4227858375) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path33_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2863311559) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path34_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 33554507) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path34_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4227858379) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path34_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2863311563) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path35_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 33554511) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path35_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4227858383) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path35_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2863311567) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path36_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 33554515) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path36_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 67108819) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path36_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 44739283) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path37_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 167772243) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path37_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 201326547) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path37_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 178957011) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path38_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 301989971) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path38_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 335544275) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path38_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 313174739) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path39_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 436207699) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path39_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 469762003) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path39_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 447392467) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path40_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1509949523) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path40_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1510997971) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path40_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1510648531) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path41_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 704643155) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path41_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 738168787) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path41_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 715819731) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path42_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 704647251) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path42_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 738172883) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path42_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 715823827) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path43_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2717917267) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path43_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2751442899) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path43_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2729093843) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path44_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2717913171) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path44_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2751438803) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path44_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2729089747) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path45_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2717909075) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path45_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2751434707) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path45_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2729085651) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path46_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 570425427) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path46_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 603951059) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path46_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 581602003) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path47_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 570429523) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path47_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 603955155) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path47_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 581606099) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path48_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 570433619) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path48_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 603959251) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path48_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 581610195) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path49_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3254779987) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path49_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3255828435) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path49_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3255478995) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path50_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3255828563) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path50_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3256877011) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path50_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3256527571) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path51_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3791654995) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path51_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3792674771) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path51_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3792345811) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path52_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3523215443) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path52_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3524263891) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path52_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3523914451) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path53_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3524264019) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path53_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3525312467) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path53_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3524963027) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path54_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3223322707) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path54_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3224371155) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path54_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3224021715) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path55_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3224371283) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path55_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3225419731) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path55_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3225070291) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path56_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3491758163) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path56_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3492806611) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path56_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3492457171) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path57_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3492806739) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path57_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3493855187) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path57_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3493505747) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path58_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3256877139) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path58_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3257925587) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path58_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3257576147) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path59_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3257925715) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path59_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3258974163) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path59_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3258624723) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path60_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3525312595) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path60_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3526361043) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path60_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3526011603) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path61_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3526361171) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path61_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3527409619) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path61_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3527060179) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path62_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3791650899) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path62_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3792670675) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path62_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3792341715) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path63_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4060086355) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path63_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4061106131) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path63_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4060777171) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path64_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1074790483) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path64_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1075838931) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path64_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1075489491) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path65_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1107296339) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path65_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1108344787) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path65_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1107995347) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path66_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4211) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path66_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4294942707) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path66_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2863307507) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path67_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 8307) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path67_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4294946803) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path67_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2863311603) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path68_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 12403) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path68_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4294950899) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path68_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2863315699) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path69_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 20595) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path69_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4294959091) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path69_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2863323891) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path70_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 24691) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path70_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4294963187) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path70_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2863327987) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path71_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 28787) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path71_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4294967283) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path71_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2863332083) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path72_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 115) = (instruction.System System.ECALL) := by decide

-- Oracle Decode_path73_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 1048691) = (instruction.System System.EBREAK) := by decide

-- Oracle Decode_path74_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 268435571) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path75_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 810549363) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path76_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 270532723) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path77_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 269484147) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path77_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 270499955) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path77_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 270172275) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path78_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 67137603) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path78_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294967263) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path78_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2930440907) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path79_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 64) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path79_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294967293) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path79_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863311592) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path80_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 55) = (instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 0), (BitVec.ofNat 20 0)))))) := by decide

-- Oracle Decode_path80_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294967223) = (instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 31), (BitVec.ofNat 20 1048575)))))) := by decide

-- Oracle Decode_path80_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863311543) = (instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 21), (BitVec.ofNat 20 699050)))))) := by decide

-- Oracle Decode_path81_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 23) = (instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 0), (BitVec.ofNat 20 0)))))) := by decide

-- Oracle Decode_path81_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294967191) = (instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 31), (BitVec.ofNat 20 1048575)))))) := by decide

-- Oracle Decode_path81_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863311511) = (instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 21), (BitVec.ofNat 20 699050)))))) := by decide

-- Oracle Decode_path82_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 19) = (instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path82_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294938515) = (instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path82_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863303315) = (instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 12 2730)))))))) := by decide

-- Oracle Decode_path83_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4115) = (instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 6 0)))))))) := by decide

-- Oracle Decode_path83_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 67084179) = (instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 6 63)))))))) := by decide

-- Oracle Decode_path83_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 44735123) = (instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 6 42)))))))) := by decide

-- Oracle Decode_path84_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 8211) = (instruction.ArithI ((ArithI.SLTI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path84_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294946707) = (instruction.ArithI ((ArithI.SLTI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path84_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863311507) = (instruction.ArithI ((ArithI.SLTI (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 12 2730)))))))) := by decide

-- Oracle Decode_path85_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 12307) = (instruction.ArithI ((ArithI.SLTIU (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path85_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294950803) = (instruction.ArithI ((ArithI.SLTIU (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path85_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863315603) = (instruction.ArithI ((ArithI.SLTIU (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 12 2730)))))))) := by decide

-- Oracle Decode_path86_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 16403) = (instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path86_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294954899) = (instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path86_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863319699) = (instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 12 2730)))))))) := by decide

-- Oracle Decode_path87_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 20499) = (instruction.Shift ((Shift.SRLI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 6 0)))))))) := by decide

-- Oracle Decode_path87_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 67100563) = (instruction.Shift ((Shift.SRLI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 6 63)))))))) := by decide

-- Oracle Decode_path87_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 44751507) = (instruction.Shift ((Shift.SRLI (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 6 42)))))))) := by decide

-- Oracle Decode_path88_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 1073762323) = (instruction.Shift ((Shift.SRAI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 6 0)))))))) := by decide

-- Oracle Decode_path88_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 1140842387) = (instruction.Shift ((Shift.SRAI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 6 63)))))))) := by decide

-- Oracle Decode_path88_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 1118493331) = (instruction.Shift ((Shift.SRAI (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 6 42)))))))) := by decide

-- Oracle Decode_path89_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 24595) = (instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path89_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294963091) = (instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path89_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863327891) = (instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 12 2730)))))))) := by decide

-- Oracle Decode_path90_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 28691) = (instruction.ArithI ((ArithI.ANDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path90_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294967187) = (instruction.ArithI ((ArithI.ANDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path90_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863331987) = (instruction.ArithI ((ArithI.ANDI (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 12 2730)))))))) := by decide

-- Oracle Decode_path91_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 51) = (instruction.ArithR ((ArithR.ADD (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path91_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33525683) = (instruction.ArithR ((ArithR.ADD (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path91_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 11176627) = (instruction.ArithR ((ArithR.ADD (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path92_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 1073741875) = (instruction.ArithR ((ArithR.SUB (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path92_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 1107267507) = (instruction.ArithR ((ArithR.SUB (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path92_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 1084918451) = (instruction.ArithR ((ArithR.SUB (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path93_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4147) = (instruction.Shift ((Shift.SLL (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path93_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33529779) = (instruction.Shift ((Shift.SLL (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path93_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 11180723) = (instruction.Shift ((Shift.SLL (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path94_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 8243) = (instruction.ArithR ((ArithR.SLT (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path94_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33533875) = (instruction.ArithR ((ArithR.SLT (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path94_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 11184819) = (instruction.ArithR ((ArithR.SLT (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path95_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 12339) = (instruction.ArithR ((ArithR.SLTU (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path95_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33537971) = (instruction.ArithR ((ArithR.SLTU (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path95_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 11188915) = (instruction.ArithR ((ArithR.SLTU (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path96_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 16435) = (instruction.ArithR ((ArithR.XOR (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path96_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33542067) = (instruction.ArithR ((ArithR.XOR (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path96_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 11193011) = (instruction.ArithR ((ArithR.XOR (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path97_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 20531) = (instruction.Shift ((Shift.SRL (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path97_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33546163) = (instruction.Shift ((Shift.SRL (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path97_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 11197107) = (instruction.Shift ((Shift.SRL (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path98_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 1073762355) = (instruction.Shift ((Shift.SRA (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path98_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 1107287987) = (instruction.Shift ((Shift.SRA (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path98_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 1084938931) = (instruction.Shift ((Shift.SRA (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path99_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 24627) = (instruction.ArithR ((ArithR.OR (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path99_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33550259) = (instruction.ArithR ((ArithR.OR (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path99_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 11201203) = (instruction.ArithR ((ArithR.OR (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path100_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 28723) = (instruction.ArithR ((ArithR.AND (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path100_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33554355) = (instruction.ArithR ((ArithR.AND (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path100_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 11205299) = (instruction.ArithR ((ArithR.AND (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path101_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 27) = (instruction.ArithI ((ArithI.ADDIW (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path101_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294938523) = (instruction.ArithI ((ArithI.ADDIW (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path101_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863303323) = (instruction.ArithI ((ArithI.ADDIW (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 12 2730)))))))) := by decide

-- Oracle Decode_path102_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4123) = (instruction.Shift ((Shift.SLLIW (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path102_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33529755) = (instruction.Shift ((Shift.SLLIW (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path102_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 11180699) = (instruction.Shift ((Shift.SLLIW (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path103_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 20507) = (instruction.Shift ((Shift.SRLIW (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path103_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33546139) = (instruction.Shift ((Shift.SRLIW (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path103_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 11197083) = (instruction.Shift ((Shift.SRLIW (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path104_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 1073762331) = (instruction.Shift ((Shift.SRAIW (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path104_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 1107287963) = (instruction.Shift ((Shift.SRAIW (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path104_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 1084938907) = (instruction.Shift ((Shift.SRAIW (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path105_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 59) = (instruction.ArithR ((ArithR.ADDW (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path105_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33525691) = (instruction.ArithR ((ArithR.ADDW (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path105_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 11176635) = (instruction.ArithR ((ArithR.ADDW (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path106_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 1073741883) = (instruction.ArithR ((ArithR.SUBW (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path106_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 1107267515) = (instruction.ArithR ((ArithR.SUBW (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path106_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 1084918459) = (instruction.ArithR ((ArithR.SUBW (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path107_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4155) = (instruction.Shift ((Shift.SLLW (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path107_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33529787) = (instruction.Shift ((Shift.SLLW (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path107_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 11180731) = (instruction.Shift ((Shift.SLLW (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path108_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 20539) = (instruction.Shift ((Shift.SRLW (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path108_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33546171) = (instruction.Shift ((Shift.SRLW (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path108_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 11197115) = (instruction.Shift ((Shift.SRLW (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path109_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 1073762363) = (instruction.Shift ((Shift.SRAW (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path109_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 1107287995) = (instruction.Shift ((Shift.SRAW (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path109_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 1084938939) = (instruction.Shift ((Shift.SRAW (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path110_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33554483) = (instruction.MulDiv ((MulDiv.MUL (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path110_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 67080115) = (instruction.MulDiv ((MulDiv.MUL (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path110_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 44731059) = (instruction.MulDiv ((MulDiv.MUL (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path111_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33558579) = (instruction.MulDiv ((MulDiv.MULH (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path111_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 67084211) = (instruction.MulDiv ((MulDiv.MULH (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path111_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 44735155) = (instruction.MulDiv ((MulDiv.MULH (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path112_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33562675) = (instruction.MulDiv ((MulDiv.MULHSU (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path112_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 67088307) = (instruction.MulDiv ((MulDiv.MULHSU (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path112_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 44739251) = (instruction.MulDiv ((MulDiv.MULHSU (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path113_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33566771) = (instruction.MulDiv ((MulDiv.MULHU (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path113_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 67092403) = (instruction.MulDiv ((MulDiv.MULHU (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path113_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 44743347) = (instruction.MulDiv ((MulDiv.MULHU (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path114_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33570867) = (instruction.MulDiv ((MulDiv.DIV (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path114_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 67096499) = (instruction.MulDiv ((MulDiv.DIV (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path114_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 44747443) = (instruction.MulDiv ((MulDiv.DIV (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path115_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33574963) = (instruction.MulDiv ((MulDiv.DIVU (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path115_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 67100595) = (instruction.MulDiv ((MulDiv.DIVU (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path115_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 44751539) = (instruction.MulDiv ((MulDiv.DIVU (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path116_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33579059) = (instruction.MulDiv ((MulDiv.REM (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path116_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 67104691) = (instruction.MulDiv ((MulDiv.REM (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path116_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 44755635) = (instruction.MulDiv ((MulDiv.REM (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path117_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33583155) = (instruction.MulDiv ((MulDiv.REMU (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path117_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 67108787) = (instruction.MulDiv ((MulDiv.REMU (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path117_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 44759731) = (instruction.MulDiv ((MulDiv.REMU (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path118_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33554491) = (instruction.MulDiv ((MulDiv.MULW (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path118_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 67080123) = (instruction.MulDiv ((MulDiv.MULW (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path118_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 44731067) = (instruction.MulDiv ((MulDiv.MULW (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path119_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33570875) = (instruction.MulDiv ((MulDiv.DIVW (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path119_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 67096507) = (instruction.MulDiv ((MulDiv.DIVW (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path119_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 44747451) = (instruction.MulDiv ((MulDiv.DIVW (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path120_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33574971) = (instruction.MulDiv ((MulDiv.DIVUW (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path120_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 67100603) = (instruction.MulDiv ((MulDiv.DIVUW (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path120_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 44751547) = (instruction.MulDiv ((MulDiv.DIVUW (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path121_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33579067) = (instruction.MulDiv ((MulDiv.REMW (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path121_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 67104699) = (instruction.MulDiv ((MulDiv.REMW (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path121_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 44755643) = (instruction.MulDiv ((MulDiv.REMW (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path122_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 33583163) = (instruction.MulDiv ((MulDiv.REMUW (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 0)))))))) := by decide

-- Oracle Decode_path122_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 67108795) = (instruction.MulDiv ((MulDiv.REMUW (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 31)))))))) := by decide

-- Oracle Decode_path122_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 44759739) = (instruction.MulDiv ((MulDiv.REMUW (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 5 10)))))))) := by decide

-- Oracle Decode_path123_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 3) = (instruction.Load ((Load.LB (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path123_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294938499) = (instruction.Load ((Load.LB (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path123_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863303299) = (instruction.Load ((Load.LB (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 12 2730)))))))) := by decide

-- Oracle Decode_path124_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4099) = (instruction.Load ((Load.LH (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path124_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294942595) = (instruction.Load ((Load.LH (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path124_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863307395) = (instruction.Load ((Load.LH (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 12 2730)))))))) := by decide

-- Oracle Decode_path125_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 8195) = (instruction.Load ((Load.LW (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path125_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294946691) = (instruction.Load ((Load.LW (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path125_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863311491) = (instruction.Load ((Load.LW (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 12 2730)))))))) := by decide

-- Oracle Decode_path126_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 12291) = (instruction.Load ((Load.LD (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path126_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294950787) = (instruction.Load ((Load.LD (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path126_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863315587) = (instruction.Load ((Load.LD (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 12 2730)))))))) := by decide

-- Oracle Decode_path127_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 16387) = (instruction.Load ((Load.LBU (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path127_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294954883) = (instruction.Load ((Load.LBU (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path127_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863319683) = (instruction.Load ((Load.LBU (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 12 2730)))))))) := by decide

-- Oracle Decode_path128_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 20483) = (instruction.Load ((Load.LHU (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path128_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294958979) = (instruction.Load ((Load.LHU (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path128_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863323779) = (instruction.Load ((Load.LHU (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 12 2730)))))))) := by decide

-- Oracle Decode_path129_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 24579) = (instruction.Load ((Load.LWU (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path129_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294963075) = (instruction.Load ((Load.LWU (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path129_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863327875) = (instruction.Load ((Load.LWU (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (BitVec.ofNat 12 2730)))))))) := by decide

-- Oracle Decode_path130_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 35) = (instruction.Store ((Store.SB (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path130_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294938531) = (instruction.Store ((Store.SB (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path130_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863303331) = (instruction.Store ((Store.SB (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 10), (BitVec.ofNat 12 2741)))))))) := by decide

-- Oracle Decode_path131_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4131) = (instruction.Store ((Store.SH (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path131_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294942627) = (instruction.Store ((Store.SH (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path131_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863307427) = (instruction.Store ((Store.SH (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 10), (BitVec.ofNat 12 2741)))))))) := by decide

-- Oracle Decode_path132_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 8227) = (instruction.Store ((Store.SW (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path132_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294946723) = (instruction.Store ((Store.SW (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path132_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863311523) = (instruction.Store ((Store.SW (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 10), (BitVec.ofNat 12 2741)))))))) := by decide

-- Oracle Decode_path133_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 12323) = (instruction.Store ((Store.SD (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0)))))))) := by decide

-- Oracle Decode_path133_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294950819) = (instruction.Store ((Store.SD (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095)))))))) := by decide

-- Oracle Decode_path133_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863315619) = (instruction.Store ((Store.SD (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 10), (BitVec.ofNat 12 2741)))))))) := by decide

-- Oracle Decode_path134_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 15) = (instruction.FENCE (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (((BitVec.ofNat 4 0), (BitVec.ofNat 4 0)))))))) := by decide

-- Oracle Decode_path134_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294938511) = (instruction.FENCE (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (((BitVec.ofNat 4 15), (BitVec.ofNat 4 15)))))))) := by decide

-- Oracle Decode_path134_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863303311) = (instruction.FENCE (((BitVec.ofNat 5 21), (((BitVec.ofNat 5 21), (((BitVec.ofNat 4 10), (BitVec.ofNat 4 10)))))))) := by decide

-- Oracle Decode_path135_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4111) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path135_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4294942607) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path135_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2863307407) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path136_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 8199) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path136_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4294946695) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path136_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2863311495) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path137_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 12295) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path137_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4294950791) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path137_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2863315591) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path138_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 8231) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path138_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4294946727) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path138_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2863311527) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path139_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 12327) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path139_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 4294950823) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path139_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2863315623) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path140_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 268443695) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path140_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 370126767) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path140_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 302688943) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path141_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 268447791) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path141_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 370130863) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path141_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 302693039) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path142_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 402661423) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path142_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 536850351) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path142_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 447392431) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path143_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 402665519) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path143_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 536854447) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path143_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 447396527) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path144_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 134225967) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path144_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 268414895) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path144_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 178956975) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path145_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 8239) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path145_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 134197167) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path145_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 44739247) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path146_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 536879151) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path146_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 671068079) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path146_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 581610159) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path147_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1610620975) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path147_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1744809903) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path147_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1655351983) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path148_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1073750063) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path148_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1207938991) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path148_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1118481071) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path149_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2147491887) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path149_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2281680815) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path149_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2192222895) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path150_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2684362799) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path150_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2818551727) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path150_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2729093807) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path151_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3221233711) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path151_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3355422639) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path151_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3265964719) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path152_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3758104623) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path152_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3892293551) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path152_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3802835631) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path153_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 134230063) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path153_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 268418991) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path153_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 178961071) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path154_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 12335) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path154_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 134201263) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path154_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 44743343) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path155_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 536883247) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path155_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 671072175) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path155_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 581614255) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path156_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1610625071) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path156_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1744813999) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path156_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1655356079) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path157_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1073754159) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path157_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1207943087) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path157_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 1118485167) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path158_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2147495983) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path158_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2281684911) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path158_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2192226991) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path159_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2684366895) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path159_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2818555823) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path159_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 2729097903) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path160_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3221237807) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path160_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3355426735) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path160_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3265968815) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path161_sample0: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3758108719) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path161_sample1: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3892297647) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path161_sample2: riscv-mi rejects the original removed instruction.
example : Decode (BitVec.ofNat 32 3802839727) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path162_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 28675) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path162_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294967183) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path162_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863331979) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path163_sample0: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 0) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path163_sample1: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 4294967229) = instruction.UnknownInstruction := by decide

-- Oracle Decode_path163_sample2: original complete instruction including all payloads.
example : Decode (BitVec.ofNat 32 2863311528) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path0_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 32769) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path0_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 37885) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path0_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 33449) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path1_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 33793) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path1_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 38909) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path1_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 34473) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path2_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 34817) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path2_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 39933) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path2_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 35497) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path3_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 35841) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path3_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 36765) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path3_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 36489) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path4_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 35873) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path4_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 36797) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path4_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 36521) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path5_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 35905) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path5_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 36829) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path5_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 36553) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path6_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 35937) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path6_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 36861) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path6_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 36585) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path7_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 39937) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path7_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 40861) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path7_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 40585) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path8_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 39969) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path8_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 40893) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path8_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 40617) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path9_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 40961) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path9_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 49149) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path9_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 43689) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path10_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 49153) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path10_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 57341) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path10_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 51881) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path11_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 57345) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path11_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 65533) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path11_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 60073) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path12_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 40001) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path12_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 40957) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path12_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 40681) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path13_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 32771) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path13_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 65535) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path13_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 43691) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path14_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 49152) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path14_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 57340) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path14_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 51880) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path15_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 57344) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path15_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 65532) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path15_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 60072) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path16_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 49154) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path16_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 57342) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path16_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 51882) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path17_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 57346) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path17_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 65534) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path17_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 60074) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path19_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 40960) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path19_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 49148) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path19_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 43688) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path20_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 32770) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path21_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 34818) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path21_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 36738) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path21_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 35458) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path22_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 34882) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path22_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 36862) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path22_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 35562) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path23_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 36866) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path24_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 38914) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path24_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 40834) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path24_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 39554) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path25_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 38978) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path25_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 40958) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path25_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 39658) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path26_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 40962) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path26_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 49150) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path26_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 43690) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path27_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 36864) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path27_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 40956) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path27_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 39592) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path28_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 8193) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path28_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 16381) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path28_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 10921) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path29_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 24833) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path30_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 28929) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path30_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 29053) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path30_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 28969) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path31_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 26625) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path31_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 28545) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path31_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 27265) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path32_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 30721) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path32_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 32765) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path32_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 31401) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path34_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 8195) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path34_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 32767) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path34_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 10923) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path35_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 8192) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path35_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 16380) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path35_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 10920) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path36_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 24576) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path36_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 32764) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path36_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 27304) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path37_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 8194) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path37_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 16382) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path37_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 10922) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path38_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 24578) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path38_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 28798) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path38_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 24618) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path39_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 26626) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path39_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 32766) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path39_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 27306) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path41_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 16384) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path41_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 24572) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path41_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 19112) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path42_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 16385) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path42_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 24573) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path42_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 19113) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path43_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 16386) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path43_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 20606) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path43_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 16426) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path44_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 18434) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path44_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 24574) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path44_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 19114) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path45_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 16387) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path45_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 24575) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path45_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 19115) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path46_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 0) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path46_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 28) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path46_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 8) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path47_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 4096) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path47_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 8188) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path47_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 6824) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path48_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 1) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path49_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 4097) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path49_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 8189) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path49_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 6825) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path50_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 2) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path50_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 8190) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path50_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 2730) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path51_sample0: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 4099) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path51_sample1: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 8191) = instruction.UnknownInstruction := by decide

-- Oracle DecodeRVC_path51_sample2: riscv-mi rejects the original removed instruction.
example : DecodeRVC (BitVec.ofNat 16 6827) = instruction.UnknownInstruction := by decide

end Flapjack.Test.L3DecodeParity
