import Flapjack.RiscV.L3.Defs.Encode

/-! Original HOL numeric Encode observations over every constructor, including
zero/max/nonuniform/sign-bit payloads. Finite fixtures are not universal equivalence. -/
namespace Flapjack.Test.L3EncodeParity
open Flapjack.RiscV.L3

-- Oracle Encode_LR_D_0
-- Oracle Encode_LR_D_1
-- Oracle Encode_LR_D_2
-- Oracle Encode_LR_D_3
-- Oracle Encode_LR_W_0
-- Oracle Encode_LR_W_1
-- Oracle Encode_LR_W_2
-- Oracle Encode_LR_W_3
-- Oracle Encode_SC_D_0
-- Oracle Encode_SC_D_1
-- Oracle Encode_SC_D_2
-- Oracle Encode_SC_D_3
-- Oracle Encode_SC_W_0
-- Oracle Encode_SC_W_1
-- Oracle Encode_SC_W_2
-- Oracle Encode_SC_W_3
-- Oracle Encode_ADDI_0
example : Encode (.ArithI (.ADDI ((0#5, (0#5, 0#12))))) = 19#32 := by decide
-- Oracle Encode_ADDI_1
example : Encode (.ArithI (.ADDI ((31#5, (31#5, 4095#12))))) = 4294938515#32 := by decide
-- Oracle Encode_ADDI_2
example : Encode (.ArithI (.ADDI ((19#5, (28#5, 860#12))))) = 902695315#32 := by decide
-- Oracle Encode_ADDI_3
example : Encode (.ArithI (.ADDI ((9#5, (12#5, 2079#12))))) = 2180383891#32 := by decide
-- Oracle Encode_ADDIW_0
example : Encode (.ArithI (.ADDIW ((0#5, (0#5, 0#12))))) = 27#32 := by decide
-- Oracle Encode_ADDIW_1
example : Encode (.ArithI (.ADDIW ((31#5, (31#5, 4095#12))))) = 4294938523#32 := by decide
-- Oracle Encode_ADDIW_2
example : Encode (.ArithI (.ADDIW ((6#5, (15#5, 879#12))))) = 922190619#32 := by decide
-- Oracle Encode_ADDIW_3
example : Encode (.ArithI (.ADDIW ((10#5, (13#5, 2080#12))))) = 2181465371#32 := by decide
-- Oracle Encode_ANDI_0
example : Encode (.ArithI (.ANDI ((0#5, (0#5, 0#12))))) = 28691#32 := by decide
-- Oracle Encode_ANDI_1
example : Encode (.ArithI (.ANDI ((31#5, (31#5, 4095#12))))) = 4294967187#32 := by decide
-- Oracle Encode_ANDI_2
example : Encode (.ArithI (.ANDI ((25#5, (2#5, 898#12))))) = 941718675#32 := by decide
-- Oracle Encode_ANDI_3
example : Encode (.ArithI (.ANDI ((11#5, (14#5, 2081#12))))) = 2182575507#32 := by decide
-- Oracle Encode_AUIPC_0
example : Encode (.ArithI (.AUIPC ((0#5, 0#20)))) = 23#32 := by decide
-- Oracle Encode_AUIPC_1
example : Encode (.ArithI (.AUIPC ((31#5, 1048575#20)))) = 4294967191#32 := by decide
-- Oracle Encode_AUIPC_2
example : Encode (.ArithI (.AUIPC ((12#5, 980#20)))) = 4015639#32 := by decide
-- Oracle Encode_AUIPC_3
example : Encode (.ArithI (.AUIPC ((12#5, 524319#20)))) = 2147612183#32 := by decide
-- Oracle Encode_LUI_0
example : Encode (.ArithI (.LUI ((0#5, 0#20)))) = 55#32 := by decide
-- Oracle Encode_LUI_1
example : Encode (.ArithI (.LUI ((31#5, 1048575#20)))) = 4294967223#32 := by decide
-- Oracle Encode_LUI_2
example : Encode (.ArithI (.LUI ((31#5, 999#20)))) = 4095927#32 := by decide
-- Oracle Encode_LUI_3
example : Encode (.ArithI (.LUI ((13#5, 524320#20)))) = 2147616439#32 := by decide
-- Oracle Encode_ORI_0
example : Encode (.ArithI (.ORI ((0#5, (0#5, 0#12))))) = 24595#32 := by decide
-- Oracle Encode_ORI_1
example : Encode (.ArithI (.ORI ((31#5, (31#5, 4095#12))))) = 4294963091#32 := by decide
-- Oracle Encode_ORI_2
example : Encode (.ArithI (.ORI ((18#5, (27#5, 955#12))))) = 1002301715#32 := by decide
-- Oracle Encode_ORI_3
example : Encode (.ArithI (.ORI ((14#5, (17#5, 2084#12))))) = 2185815827#32 := by decide
-- Oracle Encode_SLTI_0
example : Encode (.ArithI (.SLTI ((0#5, (0#5, 0#12))))) = 8211#32 := by decide
-- Oracle Encode_SLTI_1
example : Encode (.ArithI (.SLTI ((31#5, (31#5, 4095#12))))) = 4294946707#32 := by decide
-- Oracle Encode_SLTI_2
example : Encode (.ArithI (.SLTI ((5#5, (14#5, 974#12))))) = 1021780627#32 := by decide
-- Oracle Encode_SLTI_3
example : Encode (.ArithI (.SLTI ((15#5, (18#5, 2085#12))))) = 2186880915#32 := by decide
-- Oracle Encode_SLTIU_0
example : Encode (.ArithI (.SLTIU ((0#5, (0#5, 0#12))))) = 12307#32 := by decide
-- Oracle Encode_SLTIU_1
example : Encode (.ArithI (.SLTIU ((31#5, (31#5, 4095#12))))) = 4294950803#32 := by decide
-- Oracle Encode_SLTIU_2
example : Encode (.ArithI (.SLTIU ((24#5, (1#5, 993#12))))) = 1041284115#32 := by decide
-- Oracle Encode_SLTIU_3
example : Encode (.ArithI (.SLTIU ((16#5, (19#5, 2086#12))))) = 2187966483#32 := by decide
-- Oracle Encode_XORI_0
example : Encode (.ArithI (.XORI ((0#5, (0#5, 0#12))))) = 16403#32 := by decide
-- Oracle Encode_XORI_1
example : Encode (.ArithI (.XORI ((31#5, (31#5, 4095#12))))) = 4294954899#32 := by decide
-- Oracle Encode_XORI_2
example : Encode (.ArithI (.XORI ((11#5, (20#5, 1012#12))))) = 1061832083#32 := by decide
-- Oracle Encode_XORI_3
example : Encode (.ArithI (.XORI ((17#5, (20#5, 2087#12))))) = 2189052051#32 := by decide
-- Oracle Encode_ADD_0
example : Encode (.ArithR (.ADD ((0#5, (0#5, 0#5))))) = 51#32 := by decide
-- Oracle Encode_ADD_1
example : Encode (.ArithR (.ADD ((31#5, (31#5, 31#5))))) = 33525683#32 := by decide
-- Oracle Encode_ADD_2
example : Encode (.ArithR (.ADD ((30#5, (7#5, 16#5))))) = 17010483#32 := by decide
-- Oracle Encode_ADD_3
example : Encode (.ArithR (.ADD ((18#5, (21#5, 24#5))))) = 25856307#32 := by decide
-- Oracle Encode_ADDW_0
example : Encode (.ArithR (.ADDW ((0#5, (0#5, 0#5))))) = 59#32 := by decide
-- Oracle Encode_ADDW_1
example : Encode (.ArithR (.ADDW ((31#5, (31#5, 31#5))))) = 33525691#32 := by decide
-- Oracle Encode_ADDW_2
example : Encode (.ArithR (.ADDW ((17#5, (26#5, 3#5))))) = 3999931#32 := by decide
-- Oracle Encode_ADDW_3
example : Encode (.ArithR (.ADDW ((19#5, (22#5, 25#5))))) = 26937787#32 := by decide
-- Oracle Encode_AND_0
example : Encode (.ArithR (.AND ((0#5, (0#5, 0#5))))) = 28723#32 := by decide
-- Oracle Encode_AND_1
example : Encode (.ArithR (.AND ((31#5, (31#5, 31#5))))) = 33554355#32 := by decide
-- Oracle Encode_AND_2
example : Encode (.ArithR (.AND ((4#5, (13#5, 22#5))))) = 23523891#32 := by decide
-- Oracle Encode_AND_3
example : Encode (.ArithR (.AND ((20#5, (23#5, 26#5))))) = 28047923#32 := by decide
-- Oracle Encode_OR_0
example : Encode (.ArithR (.OR ((0#5, (0#5, 0#5))))) = 24627#32 := by decide
-- Oracle Encode_OR_1
example : Encode (.ArithR (.OR ((31#5, (31#5, 31#5))))) = 33550259#32 := by decide
-- Oracle Encode_OR_2
example : Encode (.ArithR (.OR ((23#5, (0#5, 9#5))))) = 9464755#32 := by decide
-- Oracle Encode_OR_3
example : Encode (.ArithR (.OR ((21#5, (24#5, 27#5))))) = 29125299#32 := by decide
-- Oracle Encode_SLT_0
example : Encode (.ArithR (.SLT ((0#5, (0#5, 0#5))))) = 8243#32 := by decide
-- Oracle Encode_SLT_1
example : Encode (.ArithR (.SLT ((31#5, (31#5, 31#5))))) = 33533875#32 := by decide
-- Oracle Encode_SLT_2
example : Encode (.ArithR (.SLT ((10#5, (19#5, 28#5))))) = 29992243#32 := by decide
-- Oracle Encode_SLT_3
example : Encode (.ArithR (.SLT ((22#5, (25#5, 28#5))))) = 30190387#32 := by decide
-- Oracle Encode_SLTU_0
example : Encode (.ArithR (.SLTU ((0#5, (0#5, 0#5))))) = 12339#32 := by decide
-- Oracle Encode_SLTU_1
example : Encode (.ArithR (.SLTU ((31#5, (31#5, 31#5))))) = 33537971#32 := by decide
-- Oracle Encode_SLTU_2
example : Encode (.ArithR (.SLTU ((29#5, (6#5, 15#5))))) = 15941299#32 := by decide
-- Oracle Encode_SLTU_3
example : Encode (.ArithR (.SLTU ((23#5, (26#5, 29#5))))) = 31275955#32 := by decide
-- Oracle Encode_SUB_0
example : Encode (.ArithR (.SUB ((0#5, (0#5, 0#5))))) = 1073741875#32 := by decide
-- Oracle Encode_SUB_1
example : Encode (.ArithR (.SUB ((31#5, (31#5, 31#5))))) = 1107267507#32 := by decide
-- Oracle Encode_SUB_2
example : Encode (.ArithR (.SUB ((16#5, (25#5, 2#5))))) = 1076660275#32 := by decide
-- Oracle Encode_SUB_3
example : Encode (.ArithR (.SUB ((24#5, (27#5, 30#5))))) = 1106086963#32 := by decide
-- Oracle Encode_SUBW_0
example : Encode (.ArithR (.SUBW ((0#5, (0#5, 0#5))))) = 1073741883#32 := by decide
-- Oracle Encode_SUBW_1
example : Encode (.ArithR (.SUBW ((31#5, (31#5, 31#5))))) = 1107267515#32 := by decide
-- Oracle Encode_SUBW_2
example : Encode (.ArithR (.SUBW ((3#5, (12#5, 21#5))))) = 1096155579#32 := by decide
-- Oracle Encode_SUBW_3
example : Encode (.ArithR (.SUBW ((25#5, (28#5, 31#5))))) = 1107168443#32 := by decide
-- Oracle Encode_XOR_0
example : Encode (.ArithR (.XOR ((0#5, (0#5, 0#5))))) = 16435#32 := by decide
-- Oracle Encode_XOR_1
example : Encode (.ArithR (.XOR ((31#5, (31#5, 31#5))))) = 33542067#32 := by decide
-- Oracle Encode_XOR_2
example : Encode (.ArithR (.XOR ((22#5, (31#5, 8#5))))) = 9423667#32 := by decide
-- Oracle Encode_XOR_3
example : Encode (.ArithR (.XOR ((26#5, (29#5, 0#5))))) = 970035#32 := by decide
-- Oracle Encode_BEQ_0
example : Encode (.Branch (.BEQ ((0#5, (0#5, 0#12))))) = 99#32 := by decide
-- Oracle Encode_BEQ_1
example : Encode (.Branch (.BEQ ((31#5, (31#5, 4095#12))))) = 4294938595#32 := by decide
-- Oracle Encode_BEQ_2
example : Encode (.Branch (.BEQ ((9#5, (18#5, 1202#12))))) = 388268771#32 := by decide
-- Oracle Encode_BEQ_3
example : Encode (.Branch (.BEQ ((27#5, (30#5, 2097#12))))) = 2280489315#32 := by decide
-- Oracle Encode_BGE_0
example : Encode (.Branch (.BGE ((0#5, (0#5, 0#12))))) = 20579#32 := by decide
-- Oracle Encode_BGE_1
example : Encode (.Branch (.BGE ((31#5, (31#5, 4095#12))))) = 4294959075#32 := by decide
-- Oracle Encode_BGE_2
example : Encode (.Branch (.BGE ((28#5, (5#5, 1221#12))))) = 408835555#32 := by decide
-- Oracle Encode_BGE_3
example : Encode (.Branch (.BGE ((28#5, (31#5, 2098#12))))) = 2281591395#32 := by decide
-- Oracle Encode_BGEU_0
example : Encode (.Branch (.BGEU ((0#5, (0#5, 0#12))))) = 28771#32 := by decide
-- Oracle Encode_BGEU_1
example : Encode (.Branch (.BGEU ((31#5, (31#5, 4095#12))))) = 4294967267#32 := by decide
-- Oracle Encode_BGEU_2
example : Encode (.Branch (.BGEU ((15#5, (24#5, 1240#12))))) = 461895907#32 := by decide
-- Oracle Encode_BGEU_3
example : Encode (.Branch (.BGEU ((29#5, (0#5, 2099#12))))) = 2249126755#32 := by decide
-- Oracle Encode_BLT_0
example : Encode (.Branch (.BLT ((0#5, (0#5, 0#12))))) = 16483#32 := by decide
-- Oracle Encode_BLT_1
example : Encode (.Branch (.BLT ((31#5, (31#5, 4095#12))))) = 4294954979#32 := by decide
-- Oracle Encode_BLT_2
example : Encode (.Branch (.BLT ((2#5, (11#5, 1259#12))))) = 481381347#32 := by decide
-- Oracle Encode_BLT_3
example : Encode (.Branch (.BLT ((30#5, (1#5, 2100#12))))) = 2250196067#32 := by decide
-- Oracle Encode_BLTU_0
example : Encode (.Branch (.BLTU ((0#5, (0#5, 0#12))))) = 24675#32 := by decide
-- Oracle Encode_BLTU_1
example : Encode (.Branch (.BLTU ((31#5, (31#5, 4095#12))))) = 4294963171#32 := by decide
-- Oracle Encode_BLTU_2
example : Encode (.Branch (.BLTU ((21#5, (30#5, 1278#12))))) = 535490275#32 := by decide
-- Oracle Encode_BLTU_3
example : Encode (.Branch (.BLTU ((31#5, (2#5, 2101#12))))) = 2251285859#32 := by decide
-- Oracle Encode_BNE_0
example : Encode (.Branch (.BNE ((0#5, (0#5, 0#12))))) = 4195#32 := by decide
-- Oracle Encode_BNE_1
example : Encode (.Branch (.BNE ((31#5, (31#5, 4095#12))))) = 4294942691#32 := by decide
-- Oracle Encode_BNE_2
example : Encode (.Branch (.BNE ((8#5, (17#5, 1297#12))))) = 588517859#32 := by decide
-- Oracle Encode_BNE_3
example : Encode (.Branch (.BNE ((0#5, (3#5, 2102#12))))) = 2251298403#32 := by decide
-- Oracle Encode_JAL_0
example : Encode (.Branch (.JAL ((0#5, 0#20)))) = 111#32 := by decide
-- Oracle Encode_JAL_1
example : Encode (.Branch (.JAL ((31#5, 1048575#20)))) = 4294967279#32 := by decide
-- Oracle Encode_JAL_2
example : Encode (.Branch (.JAL ((27#5, 1379#20)))) = 745541103#32 := by decide
-- Oracle Encode_JAL_3
example : Encode (.Branch (.JAL ((1#5, 524340#20)))) = 2256535791#32 := by decide
-- Oracle Encode_JALR_0
example : Encode (.Branch (.JALR ((0#5, (0#5, 0#12))))) = 103#32 := by decide
-- Oracle Encode_JALR_1
example : Encode (.Branch (.JALR ((31#5, (31#5, 4095#12))))) = 4294938599#32 := by decide
-- Oracle Encode_JALR_2
example : Encode (.Branch (.JALR ((14#5, (23#5, 1335#12))))) = 1400604519#32 := by decide
-- Oracle Encode_JALR_3
example : Encode (.Branch (.JALR ((2#5, (5#5, 2104#12))))) = 2206368103#32 := by decide
-- Oracle Encode_FENCE_0
example : Encode (.FENCE ((0#5, (0#5, (0#4, 0#4))))) = 15#32 := by decide
-- Oracle Encode_FENCE_1
example : Encode (.FENCE ((31#5, (31#5, (15#4, 15#4))))) = 268406671#32 := by decide
-- Oracle Encode_FENCE_2
example : Encode (.FENCE ((15#5, (24#5, (0#4, 9#4))))) = 10225551#32 := by decide
-- Oracle Encode_FENCE_3
example : Encode (.FENCE ((29#5, (0#5, (11#4, 14#4))))) = 199233167#32 := by decide
-- Oracle Encode_FETCH_FAULT_0
example : Encode (.Internal (.FETCH_FAULT (0#64))) = 0#32 := by decide
-- Oracle Encode_FETCH_FAULT_1
example : Encode (.Internal (.FETCH_FAULT (18446744073709551615#64))) = 0#32 := by decide
-- Oracle Encode_FETCH_FAULT_2
example : Encode (.Internal (.FETCH_FAULT (3308#64))) = 0#32 := by decide
-- Oracle Encode_FETCH_FAULT_3
example : Encode (.Internal (.FETCH_FAULT (9223372036854775923#64))) = 0#32 := by decide
-- Oracle Encode_FETCH_MISALIGNED_0
example : Encode (.Internal (.FETCH_MISALIGNED (0#64))) = 0#32 := by decide
-- Oracle Encode_FETCH_MISALIGNED_1
example : Encode (.Internal (.FETCH_MISALIGNED (18446744073709551615#64))) = 0#32 := by decide
-- Oracle Encode_FETCH_MISALIGNED_2
example : Encode (.Internal (.FETCH_MISALIGNED (3327#64))) = 0#32 := by decide
-- Oracle Encode_FETCH_MISALIGNED_3
example : Encode (.Internal (.FETCH_MISALIGNED (9223372036854775924#64))) = 0#32 := by decide
-- Oracle Encode_LB_0
example : Encode (.Load (.LB ((0#5, (0#5, 0#12))))) = 3#32 := by decide
-- Oracle Encode_LB_1
example : Encode (.Load (.LB ((31#5, (31#5, 4095#12))))) = 4294938499#32 := by decide
-- Oracle Encode_LB_2
example : Encode (.Load (.LB ((7#5, (16#5, 2608#12))))) = 2735211395#32 := by decide
-- Oracle Encode_LB_3
example : Encode (.Load (.LB ((5#5, (8#5, 2171#12))))) = 2276721283#32 := by decide
-- Oracle Encode_LBU_0
example : Encode (.Load (.LBU ((0#5, (0#5, 0#12))))) = 16387#32 := by decide
-- Oracle Encode_LBU_1
example : Encode (.Load (.LBU ((31#5, (31#5, 4095#12))))) = 4294954883#32 := by decide
-- Oracle Encode_LBU_2
example : Encode (.Load (.LBU ((26#5, (3#5, 2627#12))))) = 2754727171#32 := by decide
-- Oracle Encode_LBU_3
example : Encode (.Load (.LBU ((6#5, (9#5, 2172#12))))) = 2277819139#32 := by decide
-- Oracle Encode_LD_0
example : Encode (.Load (.LD ((0#5, (0#5, 0#12))))) = 12291#32 := by decide
-- Oracle Encode_LD_1
example : Encode (.Load (.LD ((31#5, (31#5, 4095#12))))) = 4294950787#32 := by decide
-- Oracle Encode_LD_2
example : Encode (.Load (.LD ((13#5, (22#5, 2646#12))))) = 2775266947#32 := by decide
-- Oracle Encode_LD_3
example : Encode (.Load (.LD ((7#5, (10#5, 2173#12))))) = 2278896515#32 := by decide
-- Oracle Encode_LH_0
example : Encode (.Load (.LH ((0#5, (0#5, 0#12))))) = 4099#32 := by decide
-- Oracle Encode_LH_1
example : Encode (.Load (.LH ((31#5, (31#5, 4095#12))))) = 4294942595#32 := by decide
-- Oracle Encode_LH_2
example : Encode (.Load (.LH ((0#5, (9#5, 2665#12))))) = 2794754051#32 := by decide
-- Oracle Encode_LH_3
example : Encode (.Load (.LH ((8#5, (11#5, 2174#12))))) = 2279969795#32 := by decide
-- Oracle Encode_LHU_0
example : Encode (.Load (.LHU ((0#5, (0#5, 0#12))))) = 20483#32 := by decide
-- Oracle Encode_LHU_1
example : Encode (.Load (.LHU ((31#5, (31#5, 4095#12))))) = 4294958979#32 := by decide
-- Oracle Encode_LHU_2
example : Encode (.Load (.LHU ((19#5, (28#5, 2684#12))))) = 2815318403#32 := by decide
-- Oracle Encode_LHU_3
example : Encode (.Load (.LHU ((9#5, (12#5, 2175#12))))) = 2281067651#32 := by decide
-- Oracle Encode_LW_0
example : Encode (.Load (.LW ((0#5, (0#5, 0#12))))) = 8195#32 := by decide
-- Oracle Encode_LW_1
example : Encode (.Load (.LW ((31#5, (31#5, 4095#12))))) = 4294946691#32 := by decide
-- Oracle Encode_LW_2
example : Encode (.Load (.LW ((6#5, (15#5, 2703#12))))) = 2834801411#32 := by decide
-- Oracle Encode_LW_3
example : Encode (.Load (.LW ((10#5, (13#5, 2176#12))))) = 2282136835#32 := by decide
-- Oracle Encode_LWU_0
example : Encode (.Load (.LWU ((0#5, (0#5, 0#12))))) = 24579#32 := by decide
-- Oracle Encode_LWU_1
example : Encode (.Load (.LWU ((31#5, (31#5, 4095#12))))) = 4294963075#32 := by decide
-- Oracle Encode_LWU_2
example : Encode (.Load (.LWU ((25#5, (2#5, 2722#12))))) = 2854317187#32 := by decide
-- Oracle Encode_LWU_3
example : Encode (.Load (.LWU ((11#5, (14#5, 2177#12))))) = 2283234691#32 := by decide
-- Oracle Encode_DIV_0
example : Encode (.MulDiv (.DIV ((0#5, (0#5, 0#5))))) = 33570867#32 := by decide
-- Oracle Encode_DIV_1
example : Encode (.MulDiv (.DIV ((31#5, (31#5, 31#5))))) = 67096499#32 := by decide
-- Oracle Encode_DIV_2
example : Encode (.MulDiv (.DIV ((12#5, (21#5, 30#5))))) = 65717811#32 := by decide
-- Oracle Encode_DIV_3
example : Encode (.MulDiv (.DIV ((12#5, (15#5, 18#5))))) = 52938291#32 := by decide
-- Oracle Encode_DIVU_0
example : Encode (.MulDiv (.DIVU ((0#5, (0#5, 0#5))))) = 33574963#32 := by decide
-- Oracle Encode_DIVU_1
example : Encode (.MulDiv (.DIVU ((31#5, (31#5, 31#5))))) = 67100595#32 := by decide
-- Oracle Encode_DIVU_2
example : Encode (.MulDiv (.DIVU ((31#5, (8#5, 17#5))))) = 51666867#32 := by decide
-- Oracle Encode_DIVU_3
example : Encode (.MulDiv (.DIVU ((13#5, (16#5, 19#5))))) = 54023859#32 := by decide
-- Oracle Encode_DIVUW_0
example : Encode (.MulDiv (.DIVUW ((0#5, (0#5, 0#5))))) = 33574971#32 := by decide
-- Oracle Encode_DIVUW_1
example : Encode (.MulDiv (.DIVUW ((31#5, (31#5, 31#5))))) = 67100603#32 := by decide
-- Oracle Encode_DIVUW_2
example : Encode (.MulDiv (.DIVUW ((18#5, (27#5, 4#5))))) = 38656315#32 := by decide
-- Oracle Encode_DIVUW_3
example : Encode (.MulDiv (.DIVUW ((14#5, (17#5, 20#5))))) = 55105339#32 := by decide
-- Oracle Encode_DIVW_0
example : Encode (.MulDiv (.DIVW ((0#5, (0#5, 0#5))))) = 33570875#32 := by decide
-- Oracle Encode_DIVW_1
example : Encode (.MulDiv (.DIVW ((31#5, (31#5, 31#5))))) = 67096507#32 := by decide
-- Oracle Encode_DIVW_2
example : Encode (.MulDiv (.DIVW ((5#5, (14#5, 23#5))))) = 58147515#32 := by decide
-- Oracle Encode_DIVW_3
example : Encode (.MulDiv (.DIVW ((15#5, (18#5, 21#5))))) = 56182715#32 := by decide
-- Oracle Encode_MUL_0
example : Encode (.MulDiv (.MUL ((0#5, (0#5, 0#5))))) = 33554483#32 := by decide
-- Oracle Encode_MUL_1
example : Encode (.MulDiv (.MUL ((31#5, (31#5, 31#5))))) = 67080115#32 := by decide
-- Oracle Encode_MUL_2
example : Encode (.MulDiv (.MUL ((24#5, (1#5, 10#5))))) = 44076083#32 := by decide
-- Oracle Encode_MUL_3
example : Encode (.MulDiv (.MUL ((16#5, (19#5, 22#5))))) = 57247795#32 := by decide
-- Oracle Encode_MULH_0
example : Encode (.MulDiv (.MULH ((0#5, (0#5, 0#5))))) = 33558579#32 := by decide
-- Oracle Encode_MULH_1
example : Encode (.MulDiv (.MULH ((31#5, (31#5, 31#5))))) = 67084211#32 := by decide
-- Oracle Encode_MULH_2
example : Encode (.MulDiv (.MULH ((11#5, (20#5, 29#5))))) = 64624051#32 := by decide
-- Oracle Encode_MULH_3
example : Encode (.MulDiv (.MULH ((17#5, (20#5, 23#5))))) = 58333363#32 := by decide
-- Oracle Encode_MULHSU_0
example : Encode (.MulDiv (.MULHSU ((0#5, (0#5, 0#5))))) = 33562675#32 := by decide
-- Oracle Encode_MULHSU_1
example : Encode (.MulDiv (.MULHSU ((31#5, (31#5, 31#5))))) = 67088307#32 := by decide
-- Oracle Encode_MULHSU_2
example : Encode (.MulDiv (.MULHSU ((30#5, (7#5, 16#5))))) = 50573107#32 := by decide
-- Oracle Encode_MULHSU_3
example : Encode (.MulDiv (.MULHSU ((18#5, (21#5, 24#5))))) = 59418931#32 := by decide
-- Oracle Encode_MULHU_0
example : Encode (.MulDiv (.MULHU ((0#5, (0#5, 0#5))))) = 33566771#32 := by decide
-- Oracle Encode_MULHU_1
example : Encode (.MulDiv (.MULHU ((31#5, (31#5, 31#5))))) = 67092403#32 := by decide
-- Oracle Encode_MULHU_2
example : Encode (.MulDiv (.MULHU ((17#5, (26#5, 3#5))))) = 37566643#32 := by decide
-- Oracle Encode_MULHU_3
example : Encode (.MulDiv (.MULHU ((19#5, (22#5, 25#5))))) = 60504499#32 := by decide
-- Oracle Encode_MULW_0
example : Encode (.MulDiv (.MULW ((0#5, (0#5, 0#5))))) = 33554491#32 := by decide
-- Oracle Encode_MULW_1
example : Encode (.MulDiv (.MULW ((31#5, (31#5, 31#5))))) = 67080123#32 := by decide
-- Oracle Encode_MULW_2
example : Encode (.MulDiv (.MULW ((4#5, (13#5, 22#5))))) = 57049659#32 := by decide
-- Oracle Encode_MULW_3
example : Encode (.MulDiv (.MULW ((20#5, (23#5, 26#5))))) = 61573691#32 := by decide
-- Oracle Encode_REM_0
example : Encode (.MulDiv (.REM ((0#5, (0#5, 0#5))))) = 33579059#32 := by decide
-- Oracle Encode_REM_1
example : Encode (.MulDiv (.REM ((31#5, (31#5, 31#5))))) = 67104691#32 := by decide
-- Oracle Encode_REM_2
example : Encode (.MulDiv (.REM ((23#5, (0#5, 9#5))))) = 43019187#32 := by decide
-- Oracle Encode_REM_3
example : Encode (.MulDiv (.REM ((21#5, (24#5, 27#5))))) = 62679731#32 := by decide
-- Oracle Encode_REMU_0
example : Encode (.MulDiv (.REMU ((0#5, (0#5, 0#5))))) = 33583155#32 := by decide
-- Oracle Encode_REMU_1
example : Encode (.MulDiv (.REMU ((31#5, (31#5, 31#5))))) = 67108787#32 := by decide
-- Oracle Encode_REMU_2
example : Encode (.MulDiv (.REMU ((10#5, (19#5, 28#5))))) = 63567155#32 := by decide
-- Oracle Encode_REMU_3
example : Encode (.MulDiv (.REMU ((22#5, (25#5, 28#5))))) = 63765299#32 := by decide
-- Oracle Encode_REMUW_0
example : Encode (.MulDiv (.REMUW ((0#5, (0#5, 0#5))))) = 33583163#32 := by decide
-- Oracle Encode_REMUW_1
example : Encode (.MulDiv (.REMUW ((31#5, (31#5, 31#5))))) = 67108795#32 := by decide
-- Oracle Encode_REMUW_2
example : Encode (.MulDiv (.REMUW ((29#5, (6#5, 15#5))))) = 49512123#32 := by decide
-- Oracle Encode_REMUW_3
example : Encode (.MulDiv (.REMUW ((23#5, (26#5, 29#5))))) = 64846779#32 := by decide
-- Oracle Encode_REMW_0
example : Encode (.MulDiv (.REMW ((0#5, (0#5, 0#5))))) = 33579067#32 := by decide
-- Oracle Encode_REMW_1
example : Encode (.MulDiv (.REMW ((31#5, (31#5, 31#5))))) = 67104699#32 := by decide
-- Oracle Encode_REMW_2
example : Encode (.MulDiv (.REMW ((16#5, (25#5, 2#5))))) = 36497467#32 := by decide
-- Oracle Encode_REMW_3
example : Encode (.MulDiv (.REMW ((24#5, (27#5, 30#5))))) = 65924155#32 := by decide
-- Oracle Encode_SLL_0
example : Encode (.Shift (.SLL ((0#5, (0#5, 0#5))))) = 4147#32 := by decide
-- Oracle Encode_SLL_1
example : Encode (.Shift (.SLL ((31#5, (31#5, 31#5))))) = 33529779#32 := by decide
-- Oracle Encode_SLL_2
example : Encode (.Shift (.SLL ((3#5, (12#5, 21#5))))) = 22417843#32 := by decide
-- Oracle Encode_SLL_3
example : Encode (.Shift (.SLL ((25#5, (28#5, 31#5))))) = 33430707#32 := by decide
-- Oracle Encode_SLLI_0
example : Encode (.Shift (.SLLI ((0#5, (0#5, 0#6))))) = 4115#32 := by decide
-- Oracle Encode_SLLI_1
example : Encode (.Shift (.SLLI ((31#5, (31#5, 63#6))))) = 67084179#32 := by decide
-- Oracle Encode_SLLI_2
example : Encode (.Shift (.SLLI ((22#5, (31#5, 25#6))))) = 27237139#32 := by decide
-- Oracle Encode_SLLI_3
example : Encode (.Shift (.SLLI ((26#5, (29#5, 48#6))))) = 51289363#32 := by decide
-- Oracle Encode_SLLIW_0
example : Encode (.Shift (.SLLIW ((0#5, (0#5, 0#5))))) = 4123#32 := by decide
-- Oracle Encode_SLLIW_1
example : Encode (.Shift (.SLLIW ((31#5, (31#5, 31#5))))) = 33529755#32 := by decide
-- Oracle Encode_SLLIW_2
example : Encode (.Shift (.SLLIW ((9#5, (18#5, 27#5))))) = 28906651#32 := by decide
-- Oracle Encode_SLLIW_3
example : Encode (.Shift (.SLLIW ((27#5, (30#5, 1#5))))) = 2039195#32 := by decide
-- Oracle Encode_SLLW_0
example : Encode (.Shift (.SLLW ((0#5, (0#5, 0#5))))) = 4155#32 := by decide
-- Oracle Encode_SLLW_1
example : Encode (.Shift (.SLLW ((31#5, (31#5, 31#5))))) = 33529787#32 := by decide
-- Oracle Encode_SLLW_2
example : Encode (.Shift (.SLLW ((28#5, (5#5, 14#5))))) = 14851643#32 := by decide
-- Oracle Encode_SLLW_3
example : Encode (.Shift (.SLLW ((28#5, (31#5, 2#5))))) = 3120699#32 := by decide
-- Oracle Encode_SRA_0
example : Encode (.Shift (.SRA ((0#5, (0#5, 0#5))))) = 1073762355#32 := by decide
-- Oracle Encode_SRA_1
example : Encode (.Shift (.SRA ((31#5, (31#5, 31#5))))) = 1107287987#32 := by decide
-- Oracle Encode_SRA_2
example : Encode (.Shift (.SRA ((15#5, (24#5, 1#5))))) = 1075599283#32 := by decide
-- Oracle Encode_SRA_3
example : Encode (.Shift (.SRA ((29#5, (0#5, 3#5))))) = 1076911795#32 := by decide
-- Oracle Encode_SRAI_0
example : Encode (.Shift (.SRAI ((0#5, (0#5, 0#6))))) = 1073762323#32 := by decide
-- Oracle Encode_SRAI_1
example : Encode (.Shift (.SRAI ((31#5, (31#5, 63#6))))) = 1140842387#32 := by decide
-- Oracle Encode_SRAI_2
example : Encode (.Shift (.SRAI ((2#5, (11#5, 37#6))))) = 1112920339#32 := by decide
-- Oracle Encode_SRAI_3
example : Encode (.Shift (.SRAI ((30#5, (1#5, 52#6))))) = 1128324883#32 := by decide
-- Oracle Encode_SRAIW_0
example : Encode (.Shift (.SRAIW ((0#5, (0#5, 0#5))))) = 1073762331#32 := by decide
-- Oracle Encode_SRAIW_1
example : Encode (.Shift (.SRAIW ((31#5, (31#5, 31#5))))) = 1107287963#32 := by decide
-- Oracle Encode_SRAIW_2
example : Encode (.Shift (.SRAIW ((21#5, (30#5, 7#5))))) = 1082088091#32 := by decide
-- Oracle Encode_SRAIW_3
example : Encode (.Shift (.SRAIW ((31#5, (2#5, 5#5))))) = 1079074715#32 := by decide
-- Oracle Encode_SRAW_0
example : Encode (.Shift (.SRAW ((0#5, (0#5, 0#5))))) = 1073762363#32 := by decide
-- Oracle Encode_SRAW_1
example : Encode (.Shift (.SRAW ((31#5, (31#5, 31#5))))) = 1107287995#32 := by decide
-- Oracle Encode_SRAW_2
example : Encode (.Shift (.SRAW ((8#5, (17#5, 26#5))))) = 1101583419#32 := by decide
-- Oracle Encode_SRAW_3
example : Encode (.Shift (.SRAW ((0#5, (3#5, 6#5))))) = 1080152123#32 := by decide
-- Oracle Encode_SRL_0
example : Encode (.Shift (.SRL ((0#5, (0#5, 0#5))))) = 20531#32 := by decide
-- Oracle Encode_SRL_1
example : Encode (.Shift (.SRL ((31#5, (31#5, 31#5))))) = 33546163#32 := by decide
-- Oracle Encode_SRL_2
example : Encode (.Shift (.SRL ((27#5, (4#5, 13#5))))) = 13786547#32 := by decide
-- Oracle Encode_SRL_3
example : Encode (.Shift (.SRL ((1#5, (4#5, 7#5))))) = 7491763#32 := by decide
-- Oracle Encode_SRLI_0
example : Encode (.Shift (.SRLI ((0#5, (0#5, 0#6))))) = 20499#32 := by decide
-- Oracle Encode_SRLI_1
example : Encode (.Shift (.SRLI ((31#5, (31#5, 63#6))))) = 67100563#32 := by decide
-- Oracle Encode_SRLI_2
example : Encode (.Shift (.SRLI ((14#5, (23#5, 49#6))))) = 52156179#32 := by decide
-- Oracle Encode_SRLI_3
example : Encode (.Shift (.SRLI ((2#5, (5#5, 56#6))))) = 58904851#32 := by decide
-- Oracle Encode_SRLIW_0
example : Encode (.Shift (.SRLIW ((0#5, (0#5, 0#5))))) = 20507#32 := by decide
-- Oracle Encode_SRLIW_1
example : Encode (.Shift (.SRLIW ((31#5, (31#5, 31#5))))) = 33546139#32 := by decide
-- Oracle Encode_SRLIW_2
example : Encode (.Shift (.SRLIW ((1#5, (10#5, 19#5))))) = 20271259#32 := by decide
-- Oracle Encode_SRLIW_3
example : Encode (.Shift (.SRLIW ((3#5, (6#5, 9#5))))) = 9654683#32 := by decide
-- Oracle Encode_SRLW_0
example : Encode (.Shift (.SRLW ((0#5, (0#5, 0#5))))) = 20539#32 := by decide
-- Oracle Encode_SRLW_1
example : Encode (.Shift (.SRLW ((31#5, (31#5, 31#5))))) = 33546171#32 := by decide
-- Oracle Encode_SRLW_2
example : Encode (.Shift (.SRLW ((20#5, (29#5, 6#5))))) = 7264827#32 := by decide
-- Oracle Encode_SRLW_3
example : Encode (.Shift (.SRLW ((4#5, (7#5, 10#5))))) = 10736187#32 := by decide
-- Oracle Encode_SB_0
example : Encode (.Store (.SB ((0#5, (0#5, 0#12))))) = 35#32 := by decide
-- Oracle Encode_SB_1
example : Encode (.Store (.SB ((31#5, (31#5, 4095#12))))) = 4294938531#32 := by decide
-- Oracle Encode_SB_2
example : Encode (.Store (.SB ((7#5, (16#5, 3216#12))))) = 3372451875#32 := by decide
-- Oracle Encode_SB_3
example : Encode (.Store (.SB ((5#5, (8#5, 2203#12))))) = 2290257315#32 := by decide
-- Oracle Encode_SD_0
example : Encode (.Store (.SD ((0#5, (0#5, 0#12))))) = 12323#32 := by decide
-- Oracle Encode_SD_1
example : Encode (.Store (.SD ((31#5, (31#5, 4095#12))))) = 4294950819#32 := by decide
-- Oracle Encode_SD_2
example : Encode (.Store (.SD ((26#5, (3#5, 3235#12))))) = 3393008035#32 := by decide
-- Oracle Encode_SD_3
example : Encode (.Store (.SD ((6#5, (9#5, 2204#12))))) = 2291351075#32 := by decide
-- Oracle Encode_SH_0
example : Encode (.Store (.SH ((0#5, (0#5, 0#12))))) = 4131#32 := by decide
-- Oracle Encode_SH_1
example : Encode (.Store (.SH ((31#5, (31#5, 4095#12))))) = 4294942627#32 := by decide
-- Oracle Encode_SH_2
example : Encode (.Store (.SH ((13#5, (22#5, 3254#12))))) = 3412499235#32 := by decide
-- Oracle Encode_SH_3
example : Encode (.Store (.SH ((7#5, (10#5, 2205#12))))) = 2292424355#32 := by decide
-- Oracle Encode_SW_0
example : Encode (.Store (.SW ((0#5, (0#5, 0#12))))) = 8227#32 := by decide
-- Oracle Encode_SW_1
example : Encode (.Store (.SW ((31#5, (31#5, 4095#12))))) = 4294946723#32 := by decide
-- Oracle Encode_SW_2
example : Encode (.Store (.SW ((0#5, (9#5, 3273#12))))) = 3431998627#32 := by decide
-- Oracle Encode_SW_3
example : Encode (.Store (.SW ((8#5, (11#5, 2206#12))))) = 2293509923#32 := by decide
-- Oracle Encode_EBREAK_0
example : Encode (.System (.EBREAK)) = 1048691#32 := by decide
-- Oracle Encode_ECALL_0
example : Encode (.System (.ECALL)) = 115#32 := by decide
-- Oracle Encode_UnknownInstruction_0
example : Encode (.UnknownInstruction) = 0#32 := by decide

end Flapjack.Test.L3EncodeParity
