import Flapjack.RiscV.L3.Defs.Encode

/-! Original HOL numeric Encode observations over every constructor, including
zero/max/nonuniform/sign-bit payloads. Finite fixtures are not universal equivalence. -/
namespace Flapjack.Test.L3EncodeParity
open Flapjack.RiscV.L3

-- Oracle Encode_AMOADD_D_0
example : Encode (.AMO (.AMOADD_D ((0#1, (0#1, (0#5, (0#5, 0#5))))))) = 12335#32 := by decide
-- Oracle Encode_AMOADD_D_1
example : Encode (.AMO (.AMOADD_D ((1#1, (1#1, (31#5, (31#5, 31#5))))))) = 134201263#32 := by decide
-- Oracle Encode_AMOADD_D_2
example : Encode (.AMO (.AMOADD_D ((1#1, (0#1, (3#5, (12#5, 21#5))))))) = 89534895#32 := by decide
-- Oracle Encode_AMOADD_D_3
example : Encode (.AMO (.AMOADD_D ((0#1, (1#1, (25#5, (28#5, 31#5))))))) = 66993327#32 := by decide
-- Oracle Encode_AMOADD_W_0
example : Encode (.AMO (.AMOADD_W ((0#1, (0#1, (0#5, (0#5, 0#5))))))) = 8239#32 := by decide
-- Oracle Encode_AMOADD_W_1
example : Encode (.AMO (.AMOADD_W ((1#1, (1#1, (31#5, (31#5, 31#5))))))) = 134197167#32 := by decide
-- Oracle Encode_AMOADD_W_2
example : Encode (.AMO (.AMOADD_W ((0#1, (1#1, (22#5, (31#5, 8#5))))))) = 42969903#32 := by decide
-- Oracle Encode_AMOADD_W_3
example : Encode (.AMO (.AMOADD_W ((1#1, (0#1, (26#5, (29#5, 0#5))))))) = 68070703#32 := by decide
-- Oracle Encode_AMOAND_D_0
example : Encode (.AMO (.AMOAND_D ((0#1, (0#1, (0#5, (0#5, 0#5))))))) = 1610625071#32 := by decide
-- Oracle Encode_AMOAND_D_1
example : Encode (.AMO (.AMOAND_D ((1#1, (1#1, (31#5, (31#5, 31#5))))))) = 1744813999#32 := by decide
-- Oracle Encode_AMOAND_D_2
example : Encode (.AMO (.AMOAND_D ((1#1, (0#1, (9#5, (18#5, 27#5))))))) = 1706636463#32 := by decide
-- Oracle Encode_AMOAND_D_3
example : Encode (.AMO (.AMOAND_D ((0#1, (1#1, (27#5, (30#5, 1#5))))))) = 1646214575#32 := by decide
-- Oracle Encode_AMOAND_W_0
example : Encode (.AMO (.AMOAND_W ((0#1, (0#1, (0#5, (0#5, 0#5))))))) = 1610620975#32 := by decide
-- Oracle Encode_AMOAND_W_1
example : Encode (.AMO (.AMOAND_W ((1#1, (1#1, (31#5, (31#5, 31#5))))))) = 1744809903#32 := by decide
-- Oracle Encode_AMOAND_W_2
example : Encode (.AMO (.AMOAND_W ((0#1, (1#1, (28#5, (5#5, 14#5))))))) = 1659022895#32 := by decide
-- Oracle Encode_AMOAND_W_3
example : Encode (.AMO (.AMOAND_W ((1#1, (0#1, (28#5, (31#5, 2#5))))))) = 1680846383#32 := by decide
-- Oracle Encode_AMOMAXU_D_0
example : Encode (.AMO (.AMOMAXU_D ((0#1, (0#1, (0#5, (0#5, 0#5))))))) = 3758108719#32 := by decide
-- Oracle Encode_AMOMAXU_D_1
example : Encode (.AMO (.AMOMAXU_D ((1#1, (1#1, (31#5, (31#5, 31#5))))))) = 3892297647#32 := by decide
-- Oracle Encode_AMOMAXU_D_2
example : Encode (.AMO (.AMOMAXU_D ((1#1, (0#1, (15#5, (24#5, 1#5))))))) = 3827054511#32 := by decide
-- Oracle Encode_AMOMAXU_D_3
example : Encode (.AMO (.AMOMAXU_D ((0#1, (1#1, (29#5, (0#5, 3#5))))))) = 3794812591#32 := by decide
-- Oracle Encode_AMOMAXU_W_0
example : Encode (.AMO (.AMOMAXU_W ((0#1, (0#1, (0#5, (0#5, 0#5))))))) = 3758104623#32 := by decide
-- Oracle Encode_AMOMAXU_W_1
example : Encode (.AMO (.AMOMAXU_W ((1#1, (1#1, (31#5, (31#5, 31#5))))))) = 3892293551#32 := by decide
-- Oracle Encode_AMOMAXU_W_2
example : Encode (.AMO (.AMOMAXU_W ((0#1, (1#1, (2#5, (11#5, 20#5))))))) = 3812991279#32 := by decide
-- Oracle Encode_AMOMAXU_W_3
example : Encode (.AMO (.AMOMAXU_W ((1#1, (0#1, (30#5, (1#5, 4#5))))))) = 3829444399#32 := by decide
-- Oracle Encode_AMOMAX_D_0
example : Encode (.AMO (.AMOMAX_D ((0#1, (0#1, (0#5, (0#5, 0#5))))))) = 2684366895#32 := by decide
-- Oracle Encode_AMOMAX_D_1
example : Encode (.AMO (.AMOMAX_D ((1#1, (1#1, (31#5, (31#5, 31#5))))))) = 2818555823#32 := by decide
-- Oracle Encode_AMOMAX_D_2
example : Encode (.AMO (.AMOMAX_D ((1#1, (0#1, (21#5, (30#5, 7#5))))))) = 2759801519#32 := by decide
-- Oracle Encode_AMOMAX_D_3
example : Encode (.AMO (.AMOMAX_D ((0#1, (1#1, (31#5, (2#5, 5#5))))))) = 2723233711#32 := by decide
-- Oracle Encode_AMOMAX_W_0
example : Encode (.AMO (.AMOMAX_W ((0#1, (0#1, (0#5, (0#5, 0#5))))))) = 2684362799#32 := by decide
-- Oracle Encode_AMOMAX_W_1
example : Encode (.AMO (.AMOMAX_W ((1#1, (1#1, (31#5, (31#5, 31#5))))))) = 2818551727#32 := by decide
-- Oracle Encode_AMOMAX_W_2
example : Encode (.AMO (.AMOMAX_W ((0#1, (1#1, (8#5, (17#5, 26#5))))))) = 2745738287#32 := by decide
-- Oracle Encode_AMOMAX_W_3
example : Encode (.AMO (.AMOMAX_W ((1#1, (0#1, (0#5, (3#5, 6#5))))))) = 2757861423#32 := by decide
-- Oracle Encode_AMOMINU_D_0
example : Encode (.AMO (.AMOMINU_D ((0#1, (0#1, (0#5, (0#5, 0#5))))))) = 3221237807#32 := by decide
-- Oracle Encode_AMOMINU_D_1
example : Encode (.AMO (.AMOMINU_D ((1#1, (1#1, (31#5, (31#5, 31#5))))))) = 3355426735#32 := by decide
-- Oracle Encode_AMOMINU_D_2
example : Encode (.AMO (.AMOMINU_D ((1#1, (0#1, (27#5, (4#5, 13#5))))))) = 3302112687#32 := by decide
-- Oracle Encode_AMOMINU_D_3
example : Encode (.AMO (.AMOMINU_D ((0#1, (1#1, (1#5, (4#5, 7#5))))))) = 3262263471#32 := by decide
-- Oracle Encode_AMOMINU_W_0
example : Encode (.AMO (.AMOMINU_W ((0#1, (0#1, (0#5, (0#5, 0#5))))))) = 3221233711#32 := by decide
-- Oracle Encode_AMOMINU_W_1
example : Encode (.AMO (.AMOMINU_W ((1#1, (1#1, (31#5, (31#5, 31#5))))))) = 3355422639#32 := by decide
-- Oracle Encode_AMOMINU_W_2
example : Encode (.AMO (.AMOMINU_W ((0#1, (1#1, (14#5, (23#5, 0#5))))))) = 3255543599#32 := by decide
-- Oracle Encode_AMOMINU_W_3
example : Encode (.AMO (.AMOMINU_W ((1#1, (0#1, (2#5, (5#5, 8#5))))))) = 3296895279#32 := by decide
-- Oracle Encode_AMOMIN_D_0
example : Encode (.AMO (.AMOMIN_D ((0#1, (0#1, (0#5, (0#5, 0#5))))))) = 2147495983#32 := by decide
-- Oracle Encode_AMOMIN_D_1
example : Encode (.AMO (.AMOMIN_D ((1#1, (1#1, (31#5, (31#5, 31#5))))))) = 2281684911#32 := by decide
-- Oracle Encode_AMOMIN_D_2
example : Encode (.AMO (.AMOMIN_D ((1#1, (0#1, (1#5, (10#5, 19#5))))))) = 2234855599#32 := by decide
-- Oracle Encode_AMOMIN_D_3
example : Encode (.AMO (.AMOMIN_D ((0#1, (1#1, (3#5, (6#5, 9#5))))))) = 2190684591#32 := by decide
-- Oracle Encode_AMOMIN_W_0
example : Encode (.AMO (.AMOMIN_W ((0#1, (0#1, (0#5, (0#5, 0#5))))))) = 2147491887#32 := by decide
-- Oracle Encode_AMOMIN_W_1
example : Encode (.AMO (.AMOMIN_W ((1#1, (1#1, (31#5, (31#5, 31#5))))))) = 2281680815#32 := by decide
-- Oracle Encode_AMOMIN_W_2
example : Encode (.AMO (.AMOMIN_W ((0#1, (1#1, (20#5, (29#5, 6#5))))))) = 2188290607#32 := by decide
-- Oracle Encode_AMOMIN_W_3
example : Encode (.AMO (.AMOMIN_W ((1#1, (0#1, (4#5, (7#5, 10#5))))))) = 2225316399#32 := by decide
-- Oracle Encode_AMOOR_D_0
example : Encode (.AMO (.AMOOR_D ((0#1, (0#1, (0#5, (0#5, 0#5))))))) = 1073754159#32 := by decide
-- Oracle Encode_AMOOR_D_1
example : Encode (.AMO (.AMOOR_D ((1#1, (1#1, (31#5, (31#5, 31#5))))))) = 1207943087#32 := by decide
-- Oracle Encode_AMOOR_D_2
example : Encode (.AMO (.AMOOR_D ((1#1, (0#1, (7#5, (16#5, 25#5))))))) = 1167602607#32 := by decide
-- Oracle Encode_AMOOR_D_3
example : Encode (.AMO (.AMOOR_D ((0#1, (1#1, (5#5, (8#5, 11#5))))))) = 1119105711#32 := by decide
-- Oracle Encode_AMOOR_W_0
example : Encode (.AMO (.AMOOR_W ((0#1, (0#1, (0#5, (0#5, 0#5))))))) = 1073750063#32 := by decide
-- Oracle Encode_AMOOR_W_1
example : Encode (.AMO (.AMOOR_W ((1#1, (1#1, (31#5, (31#5, 31#5))))))) = 1207938991#32 := by decide
-- Oracle Encode_AMOOR_W_2
example : Encode (.AMO (.AMOOR_W ((0#1, (1#1, (26#5, (3#5, 12#5))))))) = 1119989039#32 := by decide
-- Oracle Encode_AMOOR_W_3
example : Encode (.AMO (.AMOOR_W ((1#1, (0#1, (6#5, (9#5, 12#5))))))) = 1153737519#32 := by decide
-- Oracle Encode_AMOSWAP_D_0
example : Encode (.AMO (.AMOSWAP_D ((0#1, (0#1, (0#5, (0#5, 0#5))))))) = 134230063#32 := by decide
-- Oracle Encode_AMOSWAP_D_1
example : Encode (.AMO (.AMOSWAP_D ((1#1, (1#1, (31#5, (31#5, 31#5))))))) = 268418991#32 := by decide
-- Oracle Encode_AMOSWAP_D_2
example : Encode (.AMO (.AMOSWAP_D ((1#1, (0#1, (13#5, (22#5, 31#5))))))) = 234567343#32 := by decide
-- Oracle Encode_AMOSWAP_D_3
example : Encode (.AMO (.AMOSWAP_D ((0#1, (1#1, (7#5, (10#5, 13#5))))))) = 181744559#32 := by decide
-- Oracle Encode_AMOSWAP_W_0
example : Encode (.AMO (.AMOSWAP_W ((0#1, (0#1, (0#5, (0#5, 0#5))))))) = 134225967#32 := by decide
-- Oracle Encode_AMOSWAP_W_1
example : Encode (.AMO (.AMOSWAP_W ((1#1, (1#1, (31#5, (31#5, 31#5))))))) = 268414895#32 := by decide
-- Oracle Encode_AMOSWAP_W_2
example : Encode (.AMO (.AMOSWAP_W ((0#1, (1#1, (0#5, (9#5, 18#5))))))) = 186949679#32 := by decide
-- Oracle Encode_AMOSWAP_W_3
example : Encode (.AMO (.AMOSWAP_W ((1#1, (0#1, (8#5, (11#5, 14#5))))))) = 216376367#32 := by decide
-- Oracle Encode_AMOXOR_D_0
example : Encode (.AMO (.AMOXOR_D ((0#1, (0#1, (0#5, (0#5, 0#5))))))) = 536883247#32 := by decide
-- Oracle Encode_AMOXOR_D_1
example : Encode (.AMO (.AMOXOR_D ((1#1, (1#1, (31#5, (31#5, 31#5))))))) = 671072175#32 := by decide
-- Oracle Encode_AMOXOR_D_2
example : Encode (.AMO (.AMOXOR_D ((1#1, (0#1, (19#5, (28#5, 5#5))))))) = 610154927#32 := by decide
-- Oracle Encode_AMOXOR_D_3
example : Encode (.AMO (.AMOXOR_D ((0#1, (1#1, (9#5, (12#5, 15#5))))))) = 586560687#32 := by decide
-- Oracle Encode_AMOXOR_W_0
example : Encode (.AMO (.AMOXOR_W ((0#1, (0#1, (0#5, (0#5, 0#5))))))) = 536879151#32 := by decide
-- Oracle Encode_AMOXOR_W_1
example : Encode (.AMO (.AMOXOR_W ((1#1, (1#1, (31#5, (31#5, 31#5))))))) = 671068079#32 := by decide
-- Oracle Encode_AMOXOR_W_2
example : Encode (.AMO (.AMOXOR_W ((0#1, (1#1, (6#5, (15#5, 24#5))))))) = 596091695#32 := by decide
-- Oracle Encode_AMOXOR_W_3
example : Encode (.AMO (.AMOXOR_W ((1#1, (0#1, (10#5, (13#5, 16#5))))))) = 621192495#32 := by decide
-- Oracle Encode_LR_D_0
example : Encode (.AMO (.LR_D ((0#1, (0#1, (0#5, 0#5)))))) = 268447791#32 := by decide
-- Oracle Encode_LR_D_1
example : Encode (.AMO (.LR_D ((1#1, (1#1, (31#5, 31#5)))))) = 370130863#32 := by decide
-- Oracle Encode_LR_D_2
example : Encode (.AMO (.LR_D ((1#1, (0#1, (25#5, 2#5)))))) = 335625391#32 := by decide
-- Oracle Encode_LR_D_3
example : Encode (.AMO (.LR_D ((0#1, (1#1, (11#5, 14#5)))))) = 302462383#32 := by decide
-- Oracle Encode_LR_W_0
example : Encode (.AMO (.LR_W ((0#1, (0#1, (0#5, 0#5)))))) = 268443695#32 := by decide
-- Oracle Encode_LR_W_1
example : Encode (.AMO (.LR_W ((1#1, (1#1, (31#5, 31#5)))))) = 370126767#32 := by decide
-- Oracle Encode_LR_W_2
example : Encode (.AMO (.LR_W ((0#1, (1#1, (12#5, 21#5)))))) = 302687791#32 := by decide
-- Oracle Encode_LR_W_3
example : Encode (.AMO (.LR_W ((1#1, (0#1, (12#5, 15#5)))))) = 336045615#32 := by decide
-- Oracle Encode_SC_D_0
example : Encode (.AMO (.SC_D ((0#1, (0#1, (0#5, (0#5, 0#5))))))) = 268447791#32 := by decide
-- Oracle Encode_SC_D_1
example : Encode (.AMO (.SC_D ((1#1, (1#1, (31#5, (31#5, 31#5))))))) = 402636719#32 := by decide
-- Oracle Encode_SC_D_2
example : Encode (.AMO (.SC_D ((1#1, (0#1, (31#5, (8#5, 17#5))))))) = 353648559#32 := by decide
-- Oracle Encode_SC_D_3
example : Encode (.AMO (.SC_D ((0#1, (1#1, (13#5, (16#5, 19#5))))))) = 322451119#32 := by decide
-- Oracle Encode_SC_W_0
example : Encode (.AMO (.SC_W ((0#1, (0#1, (0#5, (0#5, 0#5))))))) = 402661423#32 := by decide
-- Oracle Encode_SC_W_1
example : Encode (.AMO (.SC_W ((1#1, (1#1, (31#5, (31#5, 31#5))))))) = 536850351#32 := by decide
-- Oracle Encode_SC_W_2
example : Encode (.AMO (.SC_W ((0#1, (1#1, (18#5, (27#5, 4#5))))))) = 441297199#32 := by decide
-- Oracle Encode_SC_W_3
example : Encode (.AMO (.SC_W ((1#1, (0#1, (14#5, (17#5, 20#5))))))) = 491300655#32 := by decide
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
-- Oracle Encode_FADD_D_0
example : Encode (.FArith (.FADD_D ((0#5, (0#5, (0#5, 0#3)))))) = 33554515#32 := by decide
-- Oracle Encode_FADD_D_1
example : Encode (.FArith (.FADD_D ((31#5, (31#5, (31#5, 7#3)))))) = 67108819#32 := by decide
-- Oracle Encode_FADD_D_2
example : Encode (.FArith (.FADD_D ((1#5, (10#5, (19#5, 2#3)))))) = 53813459#32 := by decide
-- Oracle Encode_FADD_D_3
example : Encode (.FArith (.FADD_D ((3#5, (6#5, (9#5, 0#3)))))) = 43188691#32 := by decide
-- Oracle Encode_FADD_S_0
example : Encode (.FArith (.FADD_S ((0#5, (0#5, (0#5, 0#3)))))) = 83#32 := by decide
-- Oracle Encode_FADD_S_1
example : Encode (.FArith (.FADD_S ((31#5, (31#5, (31#5, 7#3)))))) = 33554387#32 := by decide
-- Oracle Encode_FADD_S_2
example : Encode (.FArith (.FADD_S ((20#5, (29#5, (6#5, 5#3)))))) = 7264851#32 := by decide
-- Oracle Encode_FADD_S_3
example : Encode (.FArith (.FADD_S ((4#5, (7#5, (10#5, 1#3)))))) = 10719827#32 := by decide
-- Oracle Encode_FDIV_D_0
example : Encode (.FArith (.FDIV_D ((0#5, (0#5, (0#5, 0#3)))))) = 436207699#32 := by decide
-- Oracle Encode_FDIV_D_1
example : Encode (.FArith (.FDIV_D ((31#5, (31#5, (31#5, 7#3)))))) = 469762003#32 := by decide
-- Oracle Encode_FDIV_D_2
example : Encode (.FArith (.FDIV_D ((7#5, (16#5, (25#5, 0#3)))))) = 462947283#32 := by decide
-- Oracle Encode_FDIV_D_3
example : Encode (.FArith (.FDIV_D ((5#5, (8#5, (11#5, 2#3)))))) = 448013011#32 := by decide
-- Oracle Encode_FDIV_S_0
example : Encode (.FArith (.FDIV_S ((0#5, (0#5, (0#5, 0#3)))))) = 402653267#32 := by decide
-- Oracle Encode_FDIV_S_1
example : Encode (.FArith (.FDIV_S ((31#5, (31#5, (31#5, 7#3)))))) = 436207571#32 := by decide
-- Oracle Encode_FDIV_S_2
example : Encode (.FArith (.FDIV_S ((26#5, (3#5, (12#5, 3#3)))))) = 415350099#32 := by decide
-- Oracle Encode_FDIV_S_3
example : Encode (.FArith (.FDIV_S ((6#5, (9#5, (12#5, 3#3)))))) = 415544147#32 := by decide
-- Oracle Encode_FEQ_D_0
example : Encode (.FArith (.FEQ_D ((0#5, (0#5, 0#5))))) = 2717917267#32 := by decide
-- Oracle Encode_FEQ_D_1
example : Encode (.FArith (.FEQ_D ((31#5, (31#5, 31#5))))) = 2751442899#32 := by decide
-- Oracle Encode_FEQ_D_2
example : Encode (.FArith (.FEQ_D ((13#5, (22#5, 31#5))))) = 2751145683#32 := by decide
-- Oracle Encode_FEQ_D_3
example : Encode (.FArith (.FEQ_D ((7#5, (10#5, 13#5))))) = 2731877331#32 := by decide
-- Oracle Encode_FEQ_S_0
example : Encode (.FArith (.FEQ_S ((0#5, (0#5, 0#5))))) = 2684362835#32 := by decide
-- Oracle Encode_FEQ_S_1
example : Encode (.FArith (.FEQ_S ((31#5, (31#5, 31#5))))) = 2717888467#32 := by decide
-- Oracle Encode_FEQ_S_2
example : Encode (.FArith (.FEQ_S ((0#5, (9#5, 18#5))))) = 2703532115#32 := by decide
-- Oracle Encode_FEQ_S_3
example : Encode (.FArith (.FEQ_S ((8#5, (11#5, 14#5))))) = 2699404371#32 := by decide
-- Oracle Encode_FLE_D_0
example : Encode (.FArith (.FLE_D ((0#5, (0#5, 0#5))))) = 2717909075#32 := by decide
-- Oracle Encode_FLE_D_1
example : Encode (.FArith (.FLE_D ((31#5, (31#5, 31#5))))) = 2751434707#32 := by decide
-- Oracle Encode_FLE_D_2
example : Encode (.FArith (.FLE_D ((19#5, (28#5, 5#5))))) = 2724071891#32 := by decide
-- Oracle Encode_FLE_D_3
example : Encode (.FArith (.FLE_D ((9#5, (12#5, 15#5))))) = 2734032083#32 := by decide
-- Oracle Encode_FLE_S_0
example : Encode (.FArith (.FLE_S ((0#5, (0#5, 0#5))))) = 2684354643#32 := by decide
-- Oracle Encode_FLE_S_1
example : Encode (.FArith (.FLE_S ((31#5, (31#5, 31#5))))) = 2717880275#32 := by decide
-- Oracle Encode_FLE_S_2
example : Encode (.FArith (.FLE_S ((6#5, (15#5, 24#5))))) = 2710012755#32 := by decide
-- Oracle Encode_FLE_S_3
example : Encode (.FArith (.FLE_S ((10#5, (13#5, 16#5))))) = 2701559123#32 := by decide
-- Oracle Encode_FLT_D_0
example : Encode (.FArith (.FLT_D ((0#5, (0#5, 0#5))))) = 2717913171#32 := by decide
-- Oracle Encode_FLT_D_1
example : Encode (.FArith (.FLT_D ((31#5, (31#5, 31#5))))) = 2751438803#32 := by decide
-- Oracle Encode_FLT_D_2
example : Encode (.FArith (.FLT_D ((25#5, (2#5, 11#5))))) = 2729516243#32 := by decide
-- Oracle Encode_FLT_D_3
example : Encode (.FArith (.FLT_D ((11#5, (14#5, 17#5))))) = 2736199123#32 := by decide
-- Oracle Encode_FLT_S_0
example : Encode (.FArith (.FLT_S ((0#5, (0#5, 0#5))))) = 2684358739#32 := by decide
-- Oracle Encode_FLT_S_1
example : Encode (.FArith (.FLT_S ((31#5, (31#5, 31#5))))) = 2717884371#32 := by decide
-- Oracle Encode_FLT_S_2
example : Encode (.FArith (.FLT_S ((12#5, (21#5, 30#5))))) = 2716505683#32 := by decide
-- Oracle Encode_FLT_S_3
example : Encode (.FArith (.FLT_S ((12#5, (15#5, 18#5))))) = 2703726163#32 := by decide
-- Oracle Encode_FMADD_D_0
example : Encode (.FArith (.FMADD_D ((0#5, (0#5, (0#5, (0#5, 0#3))))))) = 33554499#32 := by decide
-- Oracle Encode_FMADD_D_1
example : Encode (.FArith (.FMADD_D ((31#5, (31#5, (31#5, (31#5, 7#3))))))) = 4227858371#32 := by decide
-- Oracle Encode_FMADD_D_2
example : Encode (.FArith (.FMADD_D ((31#5, (8#5, (17#5, (26#5, 1#3))))))) = 3541311427#32 := by decide
-- Oracle Encode_FMADD_D_3
example : Encode (.FArith (.FMADD_D ((13#5, (16#5, (19#5, (22#5, 5#3))))))) = 3006813891#32 := by decide
-- Oracle Encode_FMADD_S_0
example : Encode (.FArith (.FMADD_S ((0#5, (0#5, (0#5, (0#5, 0#3))))))) = 67#32 := by decide
-- Oracle Encode_FMADD_S_1
example : Encode (.FArith (.FMADD_S ((31#5, (31#5, (31#5, (31#5, 7#3))))))) = 4194303939#32 := by decide
-- Oracle Encode_FMADD_S_2
example : Encode (.FArith (.FMADD_S ((18#5, (27#5, (4#5, (13#5, 4#3))))))) = 1749928259#32 := by decide
-- Oracle Encode_FMADD_S_3
example : Encode (.FArith (.FMADD_S ((14#5, (17#5, (20#5, (23#5, 6#3))))))) = 3108562755#32 := by decide
-- Oracle Encode_FMAX_D_0
example : Encode (.FArith (.FMAX_D ((0#5, (0#5, 0#5))))) = 704647251#32 := by decide
-- Oracle Encode_FMAX_D_1
example : Encode (.FArith (.FMAX_D ((31#5, (31#5, 31#5))))) = 738172883#32 := by decide
-- Oracle Encode_FMAX_D_2
example : Encode (.FArith (.FMAX_D ((5#5, (14#5, 23#5))))) = 729223891#32 := by decide
-- Oracle Encode_FMAX_D_3
example : Encode (.FArith (.FMAX_D ((15#5, (18#5, 21#5))))) = 727259091#32 := by decide
-- Oracle Encode_FMAX_S_0
example : Encode (.FArith (.FMAX_S ((0#5, (0#5, 0#5))))) = 671092819#32 := by decide
-- Oracle Encode_FMAX_S_1
example : Encode (.FArith (.FMAX_S ((31#5, (31#5, 31#5))))) = 704618451#32 := by decide
-- Oracle Encode_FMAX_S_2
example : Encode (.FArith (.FMAX_S ((24#5, (1#5, 10#5))))) = 681614419#32 := by decide
-- Oracle Encode_FMAX_S_3
example : Encode (.FArith (.FMAX_S ((16#5, (19#5, 22#5))))) = 694786131#32 := by decide
-- Oracle Encode_FMIN_D_0
example : Encode (.FArith (.FMIN_D ((0#5, (0#5, 0#5))))) = 704643155#32 := by decide
-- Oracle Encode_FMIN_D_1
example : Encode (.FArith (.FMIN_D ((31#5, (31#5, 31#5))))) = 738168787#32 := by decide
-- Oracle Encode_FMIN_D_2
example : Encode (.FArith (.FMIN_D ((11#5, (20#5, 29#5))))) = 735708627#32 := by decide
-- Oracle Encode_FMIN_D_3
example : Encode (.FArith (.FMIN_D ((17#5, (20#5, 23#5))))) = 729417939#32 := by decide
-- Oracle Encode_FMIN_S_0
example : Encode (.FArith (.FMIN_S ((0#5, (0#5, 0#5))))) = 671088723#32 := by decide
-- Oracle Encode_FMIN_S_1
example : Encode (.FArith (.FMIN_S ((31#5, (31#5, 31#5))))) = 704614355#32 := by decide
-- Oracle Encode_FMIN_S_2
example : Encode (.FArith (.FMIN_S ((30#5, (7#5, 16#5))))) = 688099155#32 := by decide
-- Oracle Encode_FMIN_S_3
example : Encode (.FArith (.FMIN_S ((18#5, (21#5, 24#5))))) = 696944979#32 := by decide
-- Oracle Encode_FMSUB_D_0
example : Encode (.FArith (.FMSUB_D ((0#5, (0#5, (0#5, (0#5, 0#3))))))) = 33554503#32 := by decide
-- Oracle Encode_FMSUB_D_1
example : Encode (.FArith (.FMSUB_D ((31#5, (31#5, (31#5, (31#5, 7#3))))))) = 4227858375#32 := by decide
-- Oracle Encode_FMSUB_D_2
example : Encode (.FArith (.FMSUB_D ((17#5, (26#5, (3#5, (12#5, 3#3))))))) = 1648179399#32 := by decide
-- Oracle Encode_FMSUB_D_3
example : Encode (.FArith (.FMSUB_D ((19#5, (22#5, (25#5, (28#5, 3#3))))))) = 3818600903#32 := by decide
-- Oracle Encode_FMSUB_S_0
example : Encode (.FArith (.FMSUB_S ((0#5, (0#5, (0#5, (0#5, 0#3))))))) = 71#32 := by decide
-- Oracle Encode_FMSUB_S_1
example : Encode (.FArith (.FMSUB_S ((31#5, (31#5, (31#5, (31#5, 7#3))))))) = 4194303943#32 := by decide
-- Oracle Encode_FMSUB_S_2
example : Encode (.FArith (.FMSUB_S ((4#5, (13#5, (22#5, (31#5, 6#3))))))) = 4184269383#32 := by decide
-- Oracle Encode_FMSUB_S_3
example : Encode (.FArith (.FMSUB_S ((20#5, (23#5, (26#5, (29#5, 4#3))))))) = 3920349767#32 := by decide
-- Oracle Encode_FMUL_D_0
example : Encode (.FArith (.FMUL_D ((0#5, (0#5, (0#5, 0#3)))))) = 301989971#32 := by decide
-- Oracle Encode_FMUL_D_1
example : Encode (.FArith (.FMUL_D ((31#5, (31#5, (31#5, 7#3)))))) = 335544275#32 := by decide
-- Oracle Encode_FMUL_D_2
example : Encode (.FArith (.FMUL_D ((23#5, (0#5, (9#5, 0#3)))))) = 311430099#32 := by decide
-- Oracle Encode_FMUL_D_3
example : Encode (.FArith (.FMUL_D ((21#5, (24#5, (27#5, 2#3)))))) = 331098835#32 := by decide
-- Oracle Encode_FMUL_S_0
example : Encode (.FArith (.FMUL_S ((0#5, (0#5, (0#5, 0#3)))))) = 268435539#32 := by decide
-- Oracle Encode_FMUL_S_1
example : Encode (.FArith (.FMUL_S ((31#5, (31#5, (31#5, 7#3)))))) = 301989843#32 := by decide
-- Oracle Encode_FMUL_S_2
example : Encode (.FArith (.FMUL_S ((10#5, (19#5, (28#5, 3#3)))))) = 298431827#32 := by decide
-- Oracle Encode_FMUL_S_3
example : Encode (.FArith (.FMUL_S ((22#5, (25#5, (28#5, 3#3)))))) = 298629971#32 := by decide
-- Oracle Encode_FNMADD_D_0
example : Encode (.FArith (.FNMADD_D ((0#5, (0#5, (0#5, (0#5, 0#3))))))) = 33554511#32 := by decide
-- Oracle Encode_FNMADD_D_1
example : Encode (.FArith (.FNMADD_D ((31#5, (31#5, (31#5, (31#5, 7#3))))))) = 4227858383#32 := by decide
-- Oracle Encode_FNMADD_D_2
example : Encode (.FArith (.FNMADD_D ((29#5, (6#5, (15#5, (24#5, 7#3))))))) = 3270737615#32 := by decide
-- Oracle Encode_FNMADD_D_3
example : Encode (.FArith (.FNMADD_D ((23#5, (26#5, (29#5, (0#5, 7#3))))))) = 64846799#32 := by decide
-- Oracle Encode_FNMADD_S_0
example : Encode (.FArith (.FNMADD_S ((0#5, (0#5, (0#5, (0#5, 0#3))))))) = 79#32 := by decide
-- Oracle Encode_FNMADD_S_1
example : Encode (.FArith (.FNMADD_S ((31#5, (31#5, (31#5, (31#5, 7#3))))))) = 4194303951#32 := by decide
-- Oracle Encode_FNMADD_S_2
example : Encode (.FArith (.FNMADD_S ((16#5, (25#5, (2#5, (11#5, 2#3))))))) = 1479321679#32 := by decide
-- Oracle Encode_FNMADD_S_3
example : Encode (.FArith (.FNMADD_S ((24#5, (27#5, (30#5, (1#5, 0#3))))))) = 166562895#32 := by decide
-- Oracle Encode_FNMSUB_D_0
example : Encode (.FArith (.FNMSUB_D ((0#5, (0#5, (0#5, (0#5, 0#3))))))) = 33554507#32 := by decide
-- Oracle Encode_FNMSUB_D_1
example : Encode (.FArith (.FNMSUB_D ((31#5, (31#5, (31#5, (31#5, 7#3))))))) = 4227858379#32 := by decide
-- Oracle Encode_FNMSUB_D_2
example : Encode (.FArith (.FNMSUB_D ((3#5, (12#5, (21#5, (30#5, 5#3))))))) = 4082520523#32 := by decide
-- Oracle Encode_FNMSUB_D_3
example : Encode (.FArith (.FNMSUB_D ((25#5, (28#5, (31#5, (2#5, 1#3))))))) = 335420619#32 := by decide
-- Oracle Encode_FNMSUB_S_0
example : Encode (.FArith (.FNMSUB_S ((0#5, (0#5, (0#5, (0#5, 0#3))))))) = 75#32 := by decide
-- Oracle Encode_FNMSUB_S_1
example : Encode (.FArith (.FNMSUB_S ((31#5, (31#5, (31#5, (31#5, 7#3))))))) = 4194303947#32 := by decide
-- Oracle Encode_FNMSUB_S_2
example : Encode (.FArith (.FNMSUB_S ((22#5, (31#5, (8#5, (17#5, 0#3))))))) = 2291108683#32 := by decide
-- Oracle Encode_FNMSUB_S_3
example : Encode (.FArith (.FNMSUB_S ((26#5, (29#5, (0#5, (3#5, 2#3))))))) = 403615051#32 := by decide
-- Oracle Encode_FSQRT_D_0
example : Encode (.FArith (.FSQRT_D ((0#5, (0#5, 0#3))))) = 1509949523#32 := by decide
-- Oracle Encode_FSQRT_D_1
example : Encode (.FArith (.FSQRT_D ((31#5, (31#5, 7#3))))) = 1510997971#32 := by decide
-- Oracle Encode_FSQRT_D_2
example : Encode (.FArith (.FSQRT_D ((9#5, (18#5, 1#3))))) = 1510544595#32 := by decide
-- Oracle Encode_FSQRT_D_3
example : Encode (.FArith (.FSQRT_D ((27#5, (30#5, 5#3))))) = 1510956499#32 := by decide
-- Oracle Encode_FSQRT_S_0
example : Encode (.FArith (.FSQRT_S ((0#5, (0#5, 0#3))))) = 1476395091#32 := by decide
-- Oracle Encode_FSQRT_S_1
example : Encode (.FArith (.FSQRT_S ((31#5, (31#5, 7#3))))) = 1477443539#32 := by decide
-- Oracle Encode_FSQRT_S_2
example : Encode (.FArith (.FSQRT_S ((28#5, (5#5, 4#3))))) = 1476578899#32 := by decide
-- Oracle Encode_FSQRT_S_3
example : Encode (.FArith (.FSQRT_S ((28#5, (31#5, 6#3))))) = 1477439059#32 := by decide
-- Oracle Encode_FSUB_D_0
example : Encode (.FArith (.FSUB_D ((0#5, (0#5, (0#5, 0#3)))))) = 167772243#32 := by decide
-- Oracle Encode_FSUB_D_1
example : Encode (.FArith (.FSUB_D ((31#5, (31#5, (31#5, 7#3)))))) = 201326547#32 := by decide
-- Oracle Encode_FSUB_D_2
example : Encode (.FArith (.FSUB_D ((15#5, (24#5, (1#5, 0#3)))))) = 169609171#32 := by decide
-- Oracle Encode_FSUB_D_3
example : Encode (.FArith (.FSUB_D ((29#5, (0#5, (3#5, 2#3)))))) = 170929875#32 := by decide
-- Oracle Encode_FSUB_S_0
example : Encode (.FArith (.FSUB_S ((0#5, (0#5, (0#5, 0#3)))))) = 134217811#32 := by decide
-- Oracle Encode_FSUB_S_1
example : Encode (.FArith (.FSUB_S ((31#5, (31#5, (31#5, 7#3)))))) = 167772115#32 := by decide
-- Oracle Encode_FSUB_S_2
example : Encode (.FArith (.FSUB_S ((2#5, (11#5, (20#5, 3#3)))))) = 155562323#32 := by decide
-- Oracle Encode_FSUB_S_3
example : Encode (.FArith (.FSUB_S ((30#5, (1#5, (4#5, 3#3)))))) = 138461011#32 := by decide
-- Oracle Encode_FCLASS_D_0
example : Encode (.FConv (.FCLASS_D ((0#5, 0#5)))) = 3791654995#32 := by decide
-- Oracle Encode_FCLASS_D_1
example : Encode (.FConv (.FCLASS_D ((31#5, 31#5)))) = 3792674771#32 := by decide
-- Oracle Encode_FCLASS_D_2
example : Encode (.FConv (.FCLASS_D ((21#5, 30#5)))) = 3792640723#32 := by decide
-- Oracle Encode_FCLASS_D_3
example : Encode (.FConv (.FCLASS_D ((31#5, 2#5)))) = 3791724499#32 := by decide
-- Oracle Encode_FCLASS_S_0
example : Encode (.FConv (.FCLASS_S ((0#5, 0#5)))) = 3758100563#32 := by decide
-- Oracle Encode_FCLASS_S_1
example : Encode (.FConv (.FCLASS_S ((31#5, 31#5)))) = 3759120339#32 := by decide
-- Oracle Encode_FCLASS_S_2
example : Encode (.FConv (.FCLASS_S ((8#5, 17#5)))) = 3758658643#32 := by decide
-- Oracle Encode_FCLASS_S_3
example : Encode (.FConv (.FCLASS_S ((0#5, 3#5)))) = 3758198867#32 := by decide
-- Oracle Encode_FCVT_D_L_0
example : Encode (.FConv (.FCVT_D_L ((0#5, (0#5, 0#3))))) = 3525312595#32 := by decide
-- Oracle Encode_FCVT_D_L_1
example : Encode (.FConv (.FCVT_D_L ((31#5, (31#5, 7#3))))) = 3526361043#32 := by decide
-- Oracle Encode_FCVT_D_L_2
example : Encode (.FConv (.FCVT_D_L ((27#5, (4#5, 3#3))))) = 3525459411#32 := by decide
-- Oracle Encode_FCVT_D_L_3
example : Encode (.FConv (.FCVT_D_L ((1#5, (4#5, 3#3))))) = 3525456083#32 := by decide
-- Oracle Encode_FCVT_D_LU_0
example : Encode (.FConv (.FCVT_D_LU ((0#5, (0#5, 0#3))))) = 3526361171#32 := by decide
-- Oracle Encode_FCVT_D_LU_1
example : Encode (.FConv (.FCVT_D_LU ((31#5, (31#5, 7#3))))) = 3527409619#32 := by decide
-- Oracle Encode_FCVT_D_LU_2
example : Encode (.FConv (.FCVT_D_LU ((14#5, (23#5, 6#3))))) = 3527141203#32 := by decide
-- Oracle Encode_FCVT_D_LU_3
example : Encode (.FConv (.FCVT_D_LU ((2#5, (5#5, 4#3))))) = 3526541651#32 := by decide
-- Oracle Encode_FCVT_D_S_0
example : Encode (.FConv (.FCVT_D_S ((0#5, (0#5, 0#3))))) = 1107296339#32 := by decide
-- Oracle Encode_FCVT_D_S_1
example : Encode (.FConv (.FCVT_D_S ((31#5, (31#5, 7#3))))) = 1108344787#32 := by decide
-- Oracle Encode_FCVT_D_S_2
example : Encode (.FConv (.FCVT_D_S ((1#5, (10#5, 1#3))))) = 1107628243#32 := by decide
-- Oracle Encode_FCVT_D_S_3
example : Encode (.FConv (.FCVT_D_S ((3#5, (6#5, 5#3))))) = 1107513811#32 := by decide
-- Oracle Encode_FCVT_D_W_0
example : Encode (.FConv (.FCVT_D_W ((0#5, (0#5, 0#3))))) = 3523215443#32 := by decide
-- Oracle Encode_FCVT_D_W_1
example : Encode (.FConv (.FCVT_D_W ((31#5, (31#5, 7#3))))) = 3524263891#32 := by decide
-- Oracle Encode_FCVT_D_W_2
example : Encode (.FConv (.FCVT_D_W ((20#5, (29#5, 4#3))))) = 3524184659#32 := by decide
-- Oracle Encode_FCVT_D_W_3
example : Encode (.FConv (.FCVT_D_W ((4#5, (7#5, 6#3))))) = 3523469907#32 := by decide
-- Oracle Encode_FCVT_D_WU_0
example : Encode (.FConv (.FCVT_D_WU ((0#5, (0#5, 0#3))))) = 3524264019#32 := by decide
-- Oracle Encode_FCVT_D_WU_1
example : Encode (.FConv (.FCVT_D_WU ((31#5, (31#5, 7#3))))) = 3525312467#32 := by decide
-- Oracle Encode_FCVT_D_WU_2
example : Encode (.FConv (.FCVT_D_WU ((7#5, (16#5, 7#3))))) = 3524817875#32 := by decide
-- Oracle Encode_FCVT_D_WU_3
example : Encode (.FConv (.FCVT_D_WU ((5#5, (8#5, 7#3))))) = 3524555475#32 := by decide
-- Oracle Encode_FCVT_LU_D_0
example : Encode (.FConv (.FCVT_LU_D ((0#5, (0#5, 0#3))))) = 3257925715#32 := by decide
-- Oracle Encode_FCVT_LU_D_1
example : Encode (.FConv (.FCVT_LU_D ((31#5, (31#5, 7#3))))) = 3258974163#32 := by decide
-- Oracle Encode_FCVT_LU_D_2
example : Encode (.FConv (.FCVT_LU_D ((26#5, (3#5, 2#3))))) = 3258035539#32 := by decide
-- Oracle Encode_FCVT_LU_D_3
example : Encode (.FConv (.FCVT_LU_D ((6#5, (9#5, 0#3))))) = 3258221395#32 := by decide
-- Oracle Encode_FCVT_LU_S_0
example : Encode (.FConv (.FCVT_LU_S ((0#5, (0#5, 0#3))))) = 3224371283#32 := by decide
-- Oracle Encode_FCVT_LU_S_1
example : Encode (.FConv (.FCVT_LU_S ((31#5, (31#5, 7#3))))) = 3225419731#32 := by decide
-- Oracle Encode_FCVT_LU_S_2
example : Encode (.FConv (.FCVT_LU_S ((13#5, (22#5, 5#3))))) = 3225114323#32 := by decide
-- Oracle Encode_FCVT_LU_S_3
example : Encode (.FConv (.FCVT_LU_S ((7#5, (10#5, 1#3))))) = 3224703955#32 := by decide
-- Oracle Encode_FCVT_L_D_0
example : Encode (.FConv (.FCVT_L_D ((0#5, (0#5, 0#3))))) = 3256877139#32 := by decide
-- Oracle Encode_FCVT_L_D_1
example : Encode (.FConv (.FCVT_L_D ((31#5, (31#5, 7#3))))) = 3257925587#32 := by decide
-- Oracle Encode_FCVT_L_D_2
example : Encode (.FConv (.FCVT_L_D ((0#5, (9#5, 0#3))))) = 3257172051#32 := by decide
-- Oracle Encode_FCVT_L_D_3
example : Encode (.FConv (.FCVT_L_D ((8#5, (11#5, 2#3))))) = 3257246803#32 := by decide
-- Oracle Encode_FCVT_L_S_0
example : Encode (.FConv (.FCVT_L_S ((0#5, (0#5, 0#3))))) = 3223322707#32 := by decide
-- Oracle Encode_FCVT_L_S_1
example : Encode (.FConv (.FCVT_L_S ((31#5, (31#5, 7#3))))) = 3224371155#32 := by decide
-- Oracle Encode_FCVT_L_S_2
example : Encode (.FConv (.FCVT_L_S ((19#5, (28#5, 3#3))))) = 3224254931#32 := by decide
-- Oracle Encode_FCVT_L_S_3
example : Encode (.FConv (.FCVT_L_S ((9#5, (12#5, 3#3))))) = 3223729363#32 := by decide
-- Oracle Encode_FCVT_S_D_0
example : Encode (.FConv (.FCVT_S_D ((0#5, (0#5, 0#3))))) = 1074790483#32 := by decide
-- Oracle Encode_FCVT_S_D_1
example : Encode (.FConv (.FCVT_S_D ((31#5, (31#5, 7#3))))) = 1075838931#32 := by decide
-- Oracle Encode_FCVT_S_D_2
example : Encode (.FConv (.FCVT_S_D ((6#5, (15#5, 6#3))))) = 1075307347#32 := by decide
-- Oracle Encode_FCVT_S_D_3
example : Encode (.FConv (.FCVT_S_D ((10#5, (13#5, 4#3))))) = 1075234131#32 := by decide
-- Oracle Encode_FCVT_S_L_0
example : Encode (.FConv (.FCVT_S_L ((0#5, (0#5, 0#3))))) = 3491758163#32 := by decide
-- Oracle Encode_FCVT_S_L_1
example : Encode (.FConv (.FCVT_S_L ((31#5, (31#5, 7#3))))) = 3492806611#32 := by decide
-- Oracle Encode_FCVT_S_L_2
example : Encode (.FConv (.FCVT_S_L ((25#5, (2#5, 1#3))))) = 3491830995#32 := by decide
-- Oracle Encode_FCVT_S_L_3
example : Encode (.FConv (.FCVT_S_L ((11#5, (14#5, 5#3))))) = 3492238803#32 := by decide
-- Oracle Encode_FCVT_S_LU_0
example : Encode (.FConv (.FCVT_S_LU ((0#5, (0#5, 0#3))))) = 3492806739#32 := by decide
-- Oracle Encode_FCVT_S_LU_1
example : Encode (.FConv (.FCVT_S_LU ((31#5, (31#5, 7#3))))) = 3493855187#32 := by decide
-- Oracle Encode_FCVT_S_LU_2
example : Encode (.FConv (.FCVT_S_LU ((12#5, (21#5, 4#3))))) = 3493512787#32 := by decide
-- Oracle Encode_FCVT_S_LU_3
example : Encode (.FConv (.FCVT_S_LU ((12#5, (15#5, 6#3))))) = 3493324371#32 := by decide
-- Oracle Encode_FCVT_S_W_0
example : Encode (.FConv (.FCVT_S_W ((0#5, (0#5, 0#3))))) = 3489661011#32 := by decide
-- Oracle Encode_FCVT_S_W_1
example : Encode (.FConv (.FCVT_S_W ((31#5, (31#5, 7#3))))) = 3490709459#32 := by decide
-- Oracle Encode_FCVT_S_W_2
example : Encode (.FConv (.FCVT_S_W ((31#5, (8#5, 7#3))))) = 3489955795#32 := by decide
-- Oracle Encode_FCVT_S_W_3
example : Encode (.FConv (.FCVT_S_W ((13#5, (16#5, 7#3))))) = 3490215635#32 := by decide
-- Oracle Encode_FCVT_S_WU_0
example : Encode (.FConv (.FCVT_S_WU ((0#5, (0#5, 0#3))))) = 3490709587#32 := by decide
-- Oracle Encode_FCVT_S_WU_1
example : Encode (.FConv (.FCVT_S_WU ((31#5, (31#5, 7#3))))) = 3491758035#32 := by decide
-- Oracle Encode_FCVT_S_WU_2
example : Encode (.FConv (.FCVT_S_WU ((18#5, (27#5, 2#3))))) = 3491604819#32 := by decide
-- Oracle Encode_FCVT_S_WU_3
example : Encode (.FConv (.FCVT_S_WU ((14#5, (17#5, 0#3))))) = 3491268435#32 := by decide
-- Oracle Encode_FCVT_WU_D_0
example : Encode (.FConv (.FCVT_WU_D ((0#5, (0#5, 0#3))))) = 3255828563#32 := by decide
-- Oracle Encode_FCVT_WU_D_1
example : Encode (.FConv (.FCVT_WU_D ((31#5, (31#5, 7#3))))) = 3256877011#32 := by decide
-- Oracle Encode_FCVT_WU_D_2
example : Encode (.FConv (.FCVT_WU_D ((5#5, (14#5, 5#3))))) = 3256308435#32 := by decide
-- Oracle Encode_FCVT_WU_D_3
example : Encode (.FConv (.FCVT_WU_D ((15#5, (18#5, 1#3))))) = 3256424403#32 := by decide
-- Oracle Encode_FCVT_WU_S_0
example : Encode (.FConv (.FCVT_WU_S ((0#5, (0#5, 0#3))))) = 3222274131#32 := by decide
-- Oracle Encode_FCVT_WU_S_1
example : Encode (.FConv (.FCVT_WU_S ((31#5, (31#5, 7#3))))) = 3223322579#32 := by decide
-- Oracle Encode_FCVT_WU_S_2
example : Encode (.FConv (.FCVT_WU_S ((24#5, (1#5, 0#3))))) = 3222309971#32 := by decide
-- Oracle Encode_FCVT_WU_S_3
example : Encode (.FConv (.FCVT_WU_S ((16#5, (19#5, 2#3))))) = 3222906963#32 := by decide
-- Oracle Encode_FCVT_W_D_0
example : Encode (.FConv (.FCVT_W_D ((0#5, (0#5, 0#3))))) = 3254779987#32 := by decide
-- Oracle Encode_FCVT_W_D_1
example : Encode (.FConv (.FCVT_W_D ((31#5, (31#5, 7#3))))) = 3255828435#32 := by decide
-- Oracle Encode_FCVT_W_D_2
example : Encode (.FConv (.FCVT_W_D ((11#5, (20#5, 3#3))))) = 3255449043#32 := by decide
-- Oracle Encode_FCVT_W_D_3
example : Encode (.FConv (.FCVT_W_D ((17#5, (20#5, 3#3))))) = 3255449811#32 := by decide
-- Oracle Encode_FCVT_W_S_0
example : Encode (.FConv (.FCVT_W_S ((0#5, (0#5, 0#3))))) = 3221225555#32 := by decide
-- Oracle Encode_FCVT_W_S_1
example : Encode (.FConv (.FCVT_W_S ((31#5, (31#5, 7#3))))) = 3222274003#32 := by decide
-- Oracle Encode_FCVT_W_S_2
example : Encode (.FConv (.FCVT_W_S ((30#5, (7#5, 6#3))))) = 3221483347#32 := by decide
-- Oracle Encode_FCVT_W_S_3
example : Encode (.FConv (.FCVT_W_S ((18#5, (21#5, 4#3))))) = 3221932371#32 := by decide
-- Oracle Encode_FMV_D_X_0
example : Encode (.FConv (.FMV_D_X ((0#5, 0#5)))) = 4060086355#32 := by decide
-- Oracle Encode_FMV_D_X_1
example : Encode (.FConv (.FMV_D_X ((31#5, 31#5)))) = 4061106131#32 := by decide
-- Oracle Encode_FMV_D_X_2
example : Encode (.FConv (.FMV_D_X ((17#5, 26#5)))) = 4060940499#32 := by decide
-- Oracle Encode_FMV_D_X_3
example : Encode (.FConv (.FMV_D_X ((19#5, 22#5)))) = 4060809683#32 := by decide
-- Oracle Encode_FMV_S_X_0
example : Encode (.FConv (.FMV_S_X ((0#5, 0#5)))) = 4026531923#32 := by decide
-- Oracle Encode_FMV_S_X_1
example : Encode (.FConv (.FMV_S_X ((31#5, 31#5)))) = 4027551699#32 := by decide
-- Oracle Encode_FMV_S_X_2
example : Encode (.FConv (.FMV_S_X ((4#5, 13#5)))) = 4026958419#32 := by decide
-- Oracle Encode_FMV_S_X_3
example : Encode (.FConv (.FMV_S_X ((20#5, 23#5)))) = 4027288147#32 := by decide
-- Oracle Encode_FMV_X_D_0
example : Encode (.FConv (.FMV_X_D ((0#5, 0#5)))) = 3791650899#32 := by decide
-- Oracle Encode_FMV_X_D_1
example : Encode (.FConv (.FMV_X_D ((31#5, 31#5)))) = 3792670675#32 := by decide
-- Oracle Encode_FMV_X_D_2
example : Encode (.FConv (.FMV_X_D ((23#5, 0#5)))) = 3791653843#32 := by decide
-- Oracle Encode_FMV_X_D_3
example : Encode (.FConv (.FMV_X_D ((21#5, 24#5)))) = 3792440019#32 := by decide
-- Oracle Encode_FMV_X_S_0
example : Encode (.FConv (.FMV_X_S ((0#5, 0#5)))) = 3758096467#32 := by decide
-- Oracle Encode_FMV_X_S_1
example : Encode (.FConv (.FMV_X_S ((31#5, 31#5)))) = 3759116243#32 := by decide
-- Oracle Encode_FMV_X_S_2
example : Encode (.FConv (.FMV_X_S ((10#5, 19#5)))) = 3758720339#32 := by decide
-- Oracle Encode_FMV_X_S_3
example : Encode (.FConv (.FMV_X_S ((22#5, 25#5)))) = 3758918483#32 := by decide
-- Oracle Encode_FSGNJN_D_0
example : Encode (.FConv (.FSGNJN_D ((0#5, (0#5, 0#5))))) = 570429523#32 := by decide
-- Oracle Encode_FSGNJN_D_1
example : Encode (.FConv (.FSGNJN_D ((31#5, (31#5, 31#5))))) = 603955155#32 := by decide
-- Oracle Encode_FSGNJN_D_2
example : Encode (.FConv (.FSGNJN_D ((29#5, (6#5, 15#5))))) = 586358483#32 := by decide
-- Oracle Encode_FSGNJN_D_3
example : Encode (.FConv (.FSGNJN_D ((23#5, (26#5, 29#5))))) = 601693139#32 := by decide
-- Oracle Encode_FSGNJN_S_0
example : Encode (.FConv (.FSGNJN_S ((0#5, (0#5, 0#5))))) = 536875091#32 := by decide
-- Oracle Encode_FSGNJN_S_1
example : Encode (.FConv (.FSGNJN_S ((31#5, (31#5, 31#5))))) = 570400723#32 := by decide
-- Oracle Encode_FSGNJN_S_2
example : Encode (.FConv (.FSGNJN_S ((16#5, (25#5, 2#5))))) = 539793491#32 := by decide
-- Oracle Encode_FSGNJN_S_3
example : Encode (.FConv (.FSGNJN_S ((24#5, (27#5, 30#5))))) = 569220179#32 := by decide
-- Oracle Encode_FSGNJX_D_0
example : Encode (.FConv (.FSGNJX_D ((0#5, (0#5, 0#5))))) = 570433619#32 := by decide
-- Oracle Encode_FSGNJX_D_1
example : Encode (.FConv (.FSGNJX_D ((31#5, (31#5, 31#5))))) = 603959251#32 := by decide
-- Oracle Encode_FSGNJX_D_2
example : Encode (.FConv (.FSGNJX_D ((3#5, (12#5, 21#5))))) = 592847315#32 := by decide
-- Oracle Encode_FSGNJX_D_3
example : Encode (.FConv (.FSGNJX_D ((25#5, (28#5, 31#5))))) = 603860179#32 := by decide
-- Oracle Encode_FSGNJX_S_0
example : Encode (.FConv (.FSGNJX_S ((0#5, (0#5, 0#5))))) = 536879187#32 := by decide
-- Oracle Encode_FSGNJX_S_1
example : Encode (.FConv (.FSGNJX_S ((31#5, (31#5, 31#5))))) = 570404819#32 := by decide
-- Oracle Encode_FSGNJX_S_2
example : Encode (.FConv (.FSGNJX_S ((22#5, (31#5, 8#5))))) = 546286419#32 := by decide
-- Oracle Encode_FSGNJX_S_3
example : Encode (.FConv (.FSGNJX_S ((26#5, (29#5, 0#5))))) = 537832787#32 := by decide
-- Oracle Encode_FSGNJ_D_0
example : Encode (.FConv (.FSGNJ_D ((0#5, (0#5, 0#5))))) = 570425427#32 := by decide
-- Oracle Encode_FSGNJ_D_1
example : Encode (.FConv (.FSGNJ_D ((31#5, (31#5, 31#5))))) = 603951059#32 := by decide
-- Oracle Encode_FSGNJ_D_2
example : Encode (.FConv (.FSGNJ_D ((9#5, (18#5, 27#5))))) = 599327955#32 := by decide
-- Oracle Encode_FSGNJ_D_3
example : Encode (.FConv (.FSGNJ_D ((27#5, (30#5, 1#5))))) = 572460499#32 := by decide
-- Oracle Encode_FSGNJ_S_0
example : Encode (.FConv (.FSGNJ_S ((0#5, (0#5, 0#5))))) = 536870995#32 := by decide
-- Oracle Encode_FSGNJ_S_1
example : Encode (.FConv (.FSGNJ_S ((31#5, (31#5, 31#5))))) = 570396627#32 := by decide
-- Oracle Encode_FSGNJ_S_2
example : Encode (.FConv (.FSGNJ_S ((28#5, (5#5, 14#5))))) = 551718483#32 := by decide
-- Oracle Encode_FSGNJ_S_3
example : Encode (.FConv (.FSGNJ_S ((28#5, (31#5, 2#5))))) = 539987539#32 := by decide
-- Oracle Encode_FENCE_0
example : Encode (.FENCE ((0#5, (0#5, (0#4, 0#4))))) = 15#32 := by decide
-- Oracle Encode_FENCE_1
example : Encode (.FENCE ((31#5, (31#5, (15#4, 15#4))))) = 268406671#32 := by decide
-- Oracle Encode_FENCE_2
example : Encode (.FENCE ((15#5, (24#5, (0#4, 9#4))))) = 10225551#32 := by decide
-- Oracle Encode_FENCE_3
example : Encode (.FENCE ((29#5, (0#5, (11#4, 14#4))))) = 199233167#32 := by decide
-- Oracle Encode_FENCE_I_0
example : Encode (.FENCE_I ((0#5, (0#5, 0#12)))) = 4111#32 := by decide
-- Oracle Encode_FENCE_I_1
example : Encode (.FENCE_I ((31#5, (31#5, 4095#12)))) = 4294942607#32 := by decide
-- Oracle Encode_FENCE_I_2
example : Encode (.FENCE_I ((2#5, (11#5, 2475#12)))) = 2595590415#32 := by decide
-- Oracle Encode_FENCE_I_3
example : Encode (.FENCE_I ((30#5, (1#5, 2164#12)))) = 2269159183#32 := by decide
-- Oracle Encode_FLD_0
example : Encode (.FPLoad (.FLD ((0#5, (0#5, 0#12))))) = 12295#32 := by decide
-- Oracle Encode_FLD_1
example : Encode (.FPLoad (.FLD ((31#5, (31#5, 4095#12))))) = 4294950791#32 := by decide
-- Oracle Encode_FLD_2
example : Encode (.FPLoad (.FLD ((21#5, (30#5, 2494#12))))) = 2616146567#32 := by decide
-- Oracle Encode_FLD_3
example : Encode (.FPLoad (.FLD ((31#5, (2#5, 2165#12))))) = 2270248839#32 := by decide
-- Oracle Encode_FLW_0
example : Encode (.FPLoad (.FLW ((0#5, (0#5, 0#12))))) = 8199#32 := by decide
-- Oracle Encode_FLW_1
example : Encode (.FPLoad (.FLW ((31#5, (31#5, 4095#12))))) = 4294946695#32 := by decide
-- Oracle Encode_FLW_2
example : Encode (.FPLoad (.FLW ((8#5, (17#5, 2513#12))))) = 2635637767#32 := by decide
-- Oracle Encode_FLW_3
example : Encode (.FPLoad (.FLW ((0#5, (3#5, 2166#12))))) = 2271322119#32 := by decide
-- Oracle Encode_FSD_0
example : Encode (.FPStore (.FSD ((0#5, (0#5, 0#12))))) = 12327#32 := by decide
-- Oracle Encode_FSD_1
example : Encode (.FPStore (.FSD ((31#5, (31#5, 4095#12))))) = 4294950823#32 := by decide
-- Oracle Encode_FSD_2
example : Encode (.FPStore (.FSD ((27#5, (4#5, 2532#12))))) = 2655892007#32 := by decide
-- Oracle Encode_FSD_3
example : Encode (.FPStore (.FSD ((1#5, (4#5, 2167#12))))) = 2252389287#32 := by decide
-- Oracle Encode_FSW_0
example : Encode (.FPStore (.FSW ((0#5, (0#5, 0#12))))) = 8231#32 := by decide
-- Oracle Encode_FSW_1
example : Encode (.FPStore (.FSW ((31#5, (31#5, 4095#12))))) = 4294946727#32 := by decide
-- Oracle Encode_FSW_2
example : Encode (.FPStore (.FSW ((14#5, (23#5, 2551#12))))) = 2675387303#32 := by decide
-- Oracle Encode_FSW_3
example : Encode (.FPStore (.FSW ((2#5, (5#5, 2168#12))))) = 2253466663#32 := by decide
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
-- Oracle Encode_CSRRC_0
example : Encode (.System (.CSRRC ((0#5, (0#5, 0#12))))) = 12403#32 := by decide
-- Oracle Encode_CSRRC_1
example : Encode (.System (.CSRRC ((31#5, (31#5, 4095#12))))) = 4294950899#32 := by decide
-- Oracle Encode_CSRRC_2
example : Encode (.System (.CSRRC ((19#5, (28#5, 3292#12))))) = 3452844531#32 := by decide
-- Oracle Encode_CSRRC_3
example : Encode (.System (.CSRRC ((9#5, (12#5, 2207#12))))) = 2314614003#32 := by decide
-- Oracle Encode_CSRRCI_0
example : Encode (.System (.CSRRCI ((0#5, (0#5, 0#12))))) = 28787#32 := by decide
-- Oracle Encode_CSRRCI_1
example : Encode (.System (.CSRRCI ((31#5, (31#5, 4095#12))))) = 4294967283#32 := by decide
-- Oracle Encode_CSRRCI_2
example : Encode (.System (.CSRRCI ((6#5, (15#5, 3311#12))))) = 3472356211#32 := by decide
-- Oracle Encode_CSRRCI_3
example : Encode (.System (.CSRRCI ((10#5, (13#5, 2208#12))))) = 2315711859#32 := by decide
-- Oracle Encode_CSRRS_0
example : Encode (.System (.CSRRS ((0#5, (0#5, 0#12))))) = 8307#32 := by decide
-- Oracle Encode_CSRRS_1
example : Encode (.System (.CSRRS ((31#5, (31#5, 4095#12))))) = 4294946803#32 := by decide
-- Oracle Encode_CSRRS_2
example : Encode (.System (.CSRRS ((25#5, (2#5, 3330#12))))) = 3491835123#32 := by decide
-- Oracle Encode_CSRRS_3
example : Encode (.System (.CSRRS ((11#5, (14#5, 2209#12))))) = 2316772851#32 := by decide
-- Oracle Encode_CSRRSI_0
example : Encode (.System (.CSRRSI ((0#5, (0#5, 0#12))))) = 24691#32 := by decide
-- Oracle Encode_CSRRSI_1
example : Encode (.System (.CSRRSI ((31#5, (31#5, 4095#12))))) = 4294963187#32 := by decide
-- Oracle Encode_CSRRSI_2
example : Encode (.System (.CSRRSI ((12#5, (21#5, 3349#12))))) = 3512395379#32 := by decide
-- Oracle Encode_CSRRSI_3
example : Encode (.System (.CSRRSI ((12#5, (15#5, 2210#12))))) = 2317870707#32 := by decide
-- Oracle Encode_CSRRW_0
example : Encode (.System (.CSRRW ((0#5, (0#5, 0#12))))) = 4211#32 := by decide
-- Oracle Encode_CSRRW_1
example : Encode (.System (.CSRRW ((31#5, (31#5, 4095#12))))) = 4294942707#32 := by decide
-- Oracle Encode_CSRRW_2
example : Encode (.System (.CSRRW ((31#5, (8#5, 3368#12))))) = 3531874291#32 := by decide
-- Oracle Encode_CSRRW_3
example : Encode (.System (.CSRRW ((13#5, (16#5, 2211#12))))) = 2318931699#32 := by decide
-- Oracle Encode_CSRRWI_0
example : Encode (.System (.CSRRWI ((0#5, (0#5, 0#12))))) = 20595#32 := by decide
-- Oracle Encode_CSRRWI_1
example : Encode (.System (.CSRRWI ((31#5, (31#5, 4095#12))))) = 4294959091#32 := by decide
-- Oracle Encode_CSRRWI_2
example : Encode (.System (.CSRRWI ((18#5, (27#5, 3387#12))))) = 3552434547#32 := by decide
-- Oracle Encode_CSRRWI_3
example : Encode (.System (.CSRRWI ((14#5, (17#5, 2212#12))))) = 2320029555#32 := by decide
-- Oracle Encode_EBREAK_0
example : Encode (.System (.EBREAK)) = 1048691#32 := by decide
-- Oracle Encode_ECALL_0
example : Encode (.System (.ECALL)) = 115#32 := by decide
-- Oracle Encode_ERET_0
example : Encode (.System (.ERET)) = 268435571#32 := by decide
-- Oracle Encode_MRTS_0
example : Encode (.System (.MRTS)) = 810549363#32 := by decide
-- Oracle Encode_SFENCE_VM_0
example : Encode (.System (.SFENCE_VM (0#5))) = 269484147#32 := by decide
-- Oracle Encode_SFENCE_VM_1
example : Encode (.System (.SFENCE_VM (31#5))) = 270499955#32 := by decide
-- Oracle Encode_SFENCE_VM_2
example : Encode (.System (.SFENCE_VM (17#5))) = 270041203#32 := by decide
-- Oracle Encode_SFENCE_VM_3
example : Encode (.System (.SFENCE_VM (19#5))) = 270106739#32 := by decide
-- Oracle Encode_WFI_0
example : Encode (.System (.WFI)) = 270532723#32 := by decide
-- Oracle Encode_UnknownInstruction_0
example : Encode (.UnknownInstruction) = 0#32 := by decide

end Flapjack.Test.L3EncodeParity
