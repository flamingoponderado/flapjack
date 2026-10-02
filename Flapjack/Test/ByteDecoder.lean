import Flapjack.Byte.WordOfBytes
set_option maxRecDepth 32768
namespace Flapjack.Test.ByteDecoder
open Flapjack.HolByte
-- byte_set_0
example : setByte (width := 1) 0 0 1 false = 0 := by decide

-- byte_set_1
example : setByte (width := 1) 0 255 1 false = 1 := by decide

-- byte_set_2
example : setByte (width := 1) 0 165 1 false = 1 := by decide

-- byte_set_3
example : setByte (width := 1) 1 0 1 false = 1 := by decide

-- byte_set_4
example : setByte (width := 1) 1 255 1 false = 1 := by decide

-- byte_set_5
example : setByte (width := 1) 1 165 1 false = 1 := by decide

-- byte_set_6
example : setByte (width := 1) 1 0 1 false = 1 := by decide

-- byte_set_7
example : setByte (width := 1) 1 255 1 false = 1 := by decide

-- byte_set_8
example : setByte (width := 1) 1 165 1 false = 1 := by decide

-- byte_set_9
example : setByte (width := 1) 0 0 1 true = 0 := by decide

-- byte_set_10
example : setByte (width := 1) 0 255 1 true = 1 := by decide

-- byte_set_11
example : setByte (width := 1) 0 165 1 true = 1 := by decide

-- byte_set_12
example : setByte (width := 1) 1 0 1 true = 0 := by decide

-- byte_set_13
example : setByte (width := 1) 1 255 1 true = 1 := by decide

-- byte_set_14
example : setByte (width := 1) 1 165 1 true = 1 := by decide

-- byte_set_15
example : setByte (width := 1) 1 0 1 true = 0 := by decide

-- byte_set_16
example : setByte (width := 1) 1 255 1 true = 1 := by decide

-- byte_set_17
example : setByte (width := 1) 1 165 1 true = 1 := by decide

-- byte_set_18
example : setByte (width := 7) 0 0 17 false = 0 := by decide

-- byte_set_19
example : setByte (width := 7) 0 255 17 false = 127 := by decide

-- byte_set_20
example : setByte (width := 7) 0 165 17 false = 37 := by decide

-- byte_set_21
example : setByte (width := 7) 1 0 17 false = 17 := by decide

-- byte_set_22
example : setByte (width := 7) 1 255 17 false = 17 := by decide

-- byte_set_23
example : setByte (width := 7) 1 165 17 false = 17 := by decide

-- byte_set_24
example : setByte (width := 7) 127 0 17 false = 17 := by decide

-- byte_set_25
example : setByte (width := 7) 127 255 17 false = 17 := by decide

-- byte_set_26
example : setByte (width := 7) 127 165 17 false = 17 := by decide

-- byte_set_27
example : setByte (width := 7) 0 0 17 true = 0 := by decide

-- byte_set_28
example : setByte (width := 7) 0 255 17 true = 127 := by decide

-- byte_set_29
example : setByte (width := 7) 0 165 17 true = 37 := by decide

-- byte_set_30
example : setByte (width := 7) 1 0 17 true = 0 := by decide

-- byte_set_31
example : setByte (width := 7) 1 255 17 true = 127 := by decide

-- byte_set_32
example : setByte (width := 7) 1 165 17 true = 37 := by decide

-- byte_set_33
example : setByte (width := 7) 127 0 17 true = 0 := by decide

-- byte_set_34
example : setByte (width := 7) 127 255 17 true = 127 := by decide

-- byte_set_35
example : setByte (width := 7) 127 165 17 true = 37 := by decide

-- byte_set_36
example : setByte (width := 8) 0 0 17 false = 0 := by decide

-- byte_set_37
example : setByte (width := 8) 0 255 17 false = 255 := by decide

-- byte_set_38
example : setByte (width := 8) 0 165 17 false = 165 := by decide

-- byte_set_39
example : setByte (width := 8) 1 0 17 false = 0 := by decide

-- byte_set_40
example : setByte (width := 8) 1 255 17 false = 255 := by decide

-- byte_set_41
example : setByte (width := 8) 1 165 17 false = 165 := by decide

-- byte_set_42
example : setByte (width := 8) 255 0 17 false = 0 := by decide

-- byte_set_43
example : setByte (width := 8) 255 255 17 false = 255 := by decide

-- byte_set_44
example : setByte (width := 8) 255 165 17 false = 165 := by decide

-- byte_set_45
example : setByte (width := 8) 0 0 17 true = 0 := by decide

-- byte_set_46
example : setByte (width := 8) 0 255 17 true = 255 := by decide

-- byte_set_47
example : setByte (width := 8) 0 165 17 true = 165 := by decide

-- byte_set_48
example : setByte (width := 8) 1 0 17 true = 0 := by decide

-- byte_set_49
example : setByte (width := 8) 1 255 17 true = 255 := by decide

-- byte_set_50
example : setByte (width := 8) 1 165 17 true = 165 := by decide

-- byte_set_51
example : setByte (width := 8) 255 0 17 true = 0 := by decide

-- byte_set_52
example : setByte (width := 8) 255 255 17 true = 255 := by decide

-- byte_set_53
example : setByte (width := 8) 255 165 17 true = 165 := by decide

-- byte_set_54
example : setByte (width := 16) 0 0 12817 false = 12800 := by decide

-- byte_set_55
example : setByte (width := 16) 0 255 12817 false = 13055 := by decide

-- byte_set_56
example : setByte (width := 16) 0 165 12817 false = 12965 := by decide

-- byte_set_57
example : setByte (width := 16) 1 0 12817 false = 17 := by decide

-- byte_set_58
example : setByte (width := 16) 1 255 12817 false = 65297 := by decide

-- byte_set_59
example : setByte (width := 16) 1 165 12817 false = 42257 := by decide

-- byte_set_60
example : setByte (width := 16) 65535 0 12817 false = 17 := by decide

-- byte_set_61
example : setByte (width := 16) 65535 255 12817 false = 65297 := by decide

-- byte_set_62
example : setByte (width := 16) 65535 165 12817 false = 42257 := by decide

-- byte_set_63
example : setByte (width := 16) 0 0 12817 true = 17 := by decide

-- byte_set_64
example : setByte (width := 16) 0 255 12817 true = 65297 := by decide

-- byte_set_65
example : setByte (width := 16) 0 165 12817 true = 42257 := by decide

-- byte_set_66
example : setByte (width := 16) 1 0 12817 true = 12800 := by decide

-- byte_set_67
example : setByte (width := 16) 1 255 12817 true = 13055 := by decide

-- byte_set_68
example : setByte (width := 16) 1 165 12817 true = 12965 := by decide

-- byte_set_69
example : setByte (width := 16) 65535 0 12817 true = 12800 := by decide

-- byte_set_70
example : setByte (width := 16) 65535 255 12817 true = 13055 := by decide

-- byte_set_71
example : setByte (width := 16) 65535 165 12817 true = 12965 := by decide

-- byte_set_72
example : setByte (width := 64) 0 0 18364758544493064721 false = 18364758544493064704 := by decide

-- byte_set_73
example : setByte (width := 64) 0 255 18364758544493064721 false = 18364758544493064959 := by decide

-- byte_set_74
example : setByte (width := 64) 0 165 18364758544493064721 false = 18364758544493064869 := by decide

-- byte_set_75
example : setByte (width := 64) 1 0 18364758544493064721 false = 18364758544493051921 := by decide

-- byte_set_76
example : setByte (width := 64) 1 255 18364758544493064721 false = 18364758544493117201 := by decide

-- byte_set_77
example : setByte (width := 64) 1 165 18364758544493064721 false = 18364758544493094161 := by decide

-- byte_set_78
example : setByte (width := 64) 18446744073709551615 0 18364758544493064721 false = 62129658859368977 := by decide

-- byte_set_79
example : setByte (width := 64) 18446744073709551615 255 18364758544493064721 false = 18436816138530992657 := by decide

-- byte_set_80
example : setByte (width := 64) 18446744073709551615 165 18364758544493064721 false = 11951632675117478417 := by decide

-- byte_set_81
example : setByte (width := 64) 0 0 18364758544493064721 true = 62129658859368977 := by decide

-- byte_set_82
example : setByte (width := 64) 0 255 18364758544493064721 true = 18436816138530992657 := by decide

-- byte_set_83
example : setByte (width := 64) 0 165 18364758544493064721 true = 11951632675117478417 := by decide

-- byte_set_84
example : setByte (width := 64) 1 0 18364758544493064721 true = 18302834049616720401 := by decide

-- byte_set_85
example : setByte (width := 64) 1 255 18364758544493064721 true = 18374610168677937681 := by decide

-- byte_set_86
example : setByte (width := 64) 1 165 18364758544493064721 true = 18349277420773978641 := by decide

-- byte_set_87
example : setByte (width := 64) 18446744073709551615 0 18364758544493064721 true = 18364758544493064704 := by decide

-- byte_set_88
example : setByte (width := 64) 18446744073709551615 255 18364758544493064721 true = 18364758544493064959 := by decide

-- byte_set_89
example : setByte (width := 64) 18446744073709551615 165 18364758544493064721 true = 18364758544493064869 := by decide

-- byte_set_90
example : setByte (width := 80) 0 0 18364758544493064721 false = 18364758544493064704 := by decide

-- byte_set_91
example : setByte (width := 80) 0 255 18364758544493064721 false = 18364758544493064959 := by decide

-- byte_set_92
example : setByte (width := 80) 0 165 18364758544493064721 false = 18364758544493064869 := by decide

-- byte_set_93
example : setByte (width := 80) 1 0 18364758544493064721 false = 18364758544493051921 := by decide

-- byte_set_94
example : setByte (width := 80) 1 255 18364758544493064721 false = 18364758544493117201 := by decide

-- byte_set_95
example : setByte (width := 80) 1 165 18364758544493064721 false = 18364758544493094161 := by decide

-- byte_set_96
example : setByte (width := 80) 1208925819614629174706175 0 18364758544493064721 false = 18364554035330298385 := by decide

-- byte_set_97
example : setByte (width := 80) 1208925819614629174706175 255 18364758544493064721 false = 18364834410795381265 := by decide

-- byte_set_98
example : setByte (width := 80) 1208925819614629174706175 165 18364758544493064721 false = 18364735454748881425 := by decide

-- byte_set_99
example : setByte (width := 80) 0 0 18364758544493064721 true = 18364758544493064721 := by decide

-- byte_set_100
example : setByte (width := 80) 0 255 18364758544493064721 true = 1204221817890304022557201 := by decide

-- byte_set_101
example : setByte (width := 80) 0 165 18364758544493064721 true = 779208834432035953324561 := by decide

-- byte_set_102
example : setByte (width := 80) 1 0 18364758544493064721 true = 18364758544493064721 := by decide

-- byte_set_103
example : setByte (width := 80) 1 255 18364758544493064721 true = 4722284497340428726801 := by decide

-- byte_set_104
example : setByte (width := 80) 1 165 18364758544493064721 true = 3062077530706569081361 := by decide

-- byte_set_105
example : setByte (width := 80) 1208925819614629174706175 0 18364758544493064721 true = 18364757891658035729 := by decide

-- byte_set_106
example : setByte (width := 80) 1208925819614629174706175 255 18364758544493064721 true = 18364758986874696209 := by decide

-- byte_set_107
example : setByte (width := 80) 1208925819614629174706175 165 18364758544493064721 true = 18364758600327639569 := by decide

-- byte_decode_0
example : wordOfBytes (width := 1) false 0 [] = 0 := by decide

-- byte_decode_1
example : wordOfBytes (width := 1) false 0 [165] = 1 := by decide

-- byte_decode_2
example : wordOfBytes (width := 1) false 0 [1, 2, 3, 4, 5] = 1 := by decide

-- byte_decode_3
example : wordOfBytes (width := 1) false 0 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 1 := by decide

-- byte_decode_4
example : wordOfBytes (width := 1) false 1 [] = 0 := by decide

-- byte_decode_5
example : wordOfBytes (width := 1) false 1 [165] = 0 := by decide

-- byte_decode_6
example : wordOfBytes (width := 1) false 1 [1, 2, 3, 4, 5] = 0 := by decide

-- byte_decode_7
example : wordOfBytes (width := 1) false 1 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 0 := by decide

-- byte_decode_8
example : wordOfBytes (width := 1) false 1 [] = 0 := by decide

-- byte_decode_9
example : wordOfBytes (width := 1) false 1 [165] = 0 := by decide

-- byte_decode_10
example : wordOfBytes (width := 1) false 1 [1, 2, 3, 4, 5] = 0 := by decide

-- byte_decode_11
example : wordOfBytes (width := 1) false 1 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 0 := by decide

-- byte_decode_12
example : wordOfBytes (width := 1) true 0 [] = 0 := by decide

-- byte_decode_13
example : wordOfBytes (width := 1) true 0 [165] = 1 := by decide

-- byte_decode_14
example : wordOfBytes (width := 1) true 0 [1, 2, 3, 4, 5] = 1 := by decide

-- byte_decode_15
example : wordOfBytes (width := 1) true 0 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 1 := by decide

-- byte_decode_16
example : wordOfBytes (width := 1) true 1 [] = 0 := by decide

-- byte_decode_17
example : wordOfBytes (width := 1) true 1 [165] = 1 := by decide

-- byte_decode_18
example : wordOfBytes (width := 1) true 1 [1, 2, 3, 4, 5] = 1 := by decide

-- byte_decode_19
example : wordOfBytes (width := 1) true 1 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 1 := by decide

-- byte_decode_20
example : wordOfBytes (width := 1) true 1 [] = 0 := by decide

-- byte_decode_21
example : wordOfBytes (width := 1) true 1 [165] = 1 := by decide

-- byte_decode_22
example : wordOfBytes (width := 1) true 1 [1, 2, 3, 4, 5] = 1 := by decide

-- byte_decode_23
example : wordOfBytes (width := 1) true 1 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 1 := by decide

-- byte_decode_24
example : wordOfBytes (width := 7) false 0 [] = 0 := by decide

-- byte_decode_25
example : wordOfBytes (width := 7) false 0 [165] = 37 := by decide

-- byte_decode_26
example : wordOfBytes (width := 7) false 0 [1, 2, 3, 4, 5] = 1 := by decide

-- byte_decode_27
example : wordOfBytes (width := 7) false 0 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 127 := by decide

-- byte_decode_28
example : wordOfBytes (width := 7) false 1 [] = 0 := by decide

-- byte_decode_29
example : wordOfBytes (width := 7) false 1 [165] = 0 := by decide

-- byte_decode_30
example : wordOfBytes (width := 7) false 1 [1, 2, 3, 4, 5] = 0 := by decide

-- byte_decode_31
example : wordOfBytes (width := 7) false 1 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 0 := by decide

-- byte_decode_32
example : wordOfBytes (width := 7) false 127 [] = 0 := by decide

-- byte_decode_33
example : wordOfBytes (width := 7) false 127 [165] = 0 := by decide

-- byte_decode_34
example : wordOfBytes (width := 7) false 127 [1, 2, 3, 4, 5] = 2 := by decide

-- byte_decode_35
example : wordOfBytes (width := 7) false 127 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 0 := by decide

-- byte_decode_36
example : wordOfBytes (width := 7) true 0 [] = 0 := by decide

-- byte_decode_37
example : wordOfBytes (width := 7) true 0 [165] = 37 := by decide

-- byte_decode_38
example : wordOfBytes (width := 7) true 0 [1, 2, 3, 4, 5] = 1 := by decide

-- byte_decode_39
example : wordOfBytes (width := 7) true 0 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 127 := by decide

-- byte_decode_40
example : wordOfBytes (width := 7) true 1 [] = 0 := by decide

-- byte_decode_41
example : wordOfBytes (width := 7) true 1 [165] = 37 := by decide

-- byte_decode_42
example : wordOfBytes (width := 7) true 1 [1, 2, 3, 4, 5] = 1 := by decide

-- byte_decode_43
example : wordOfBytes (width := 7) true 1 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 127 := by decide

-- byte_decode_44
example : wordOfBytes (width := 7) true 127 [] = 0 := by decide

-- byte_decode_45
example : wordOfBytes (width := 7) true 127 [165] = 37 := by decide

-- byte_decode_46
example : wordOfBytes (width := 7) true 127 [1, 2, 3, 4, 5] = 1 := by decide

-- byte_decode_47
example : wordOfBytes (width := 7) true 127 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 127 := by decide

-- byte_decode_48
example : wordOfBytes (width := 8) false 0 [] = 0 := by decide

-- byte_decode_49
example : wordOfBytes (width := 8) false 0 [165] = 165 := by decide

-- byte_decode_50
example : wordOfBytes (width := 8) false 0 [1, 2, 3, 4, 5] = 1 := by decide

-- byte_decode_51
example : wordOfBytes (width := 8) false 0 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 255 := by decide

-- byte_decode_52
example : wordOfBytes (width := 8) false 1 [] = 0 := by decide

-- byte_decode_53
example : wordOfBytes (width := 8) false 1 [165] = 165 := by decide

-- byte_decode_54
example : wordOfBytes (width := 8) false 1 [1, 2, 3, 4, 5] = 1 := by decide

-- byte_decode_55
example : wordOfBytes (width := 8) false 1 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 255 := by decide

-- byte_decode_56
example : wordOfBytes (width := 8) false 255 [] = 0 := by decide

-- byte_decode_57
example : wordOfBytes (width := 8) false 255 [165] = 165 := by decide

-- byte_decode_58
example : wordOfBytes (width := 8) false 255 [1, 2, 3, 4, 5] = 1 := by decide

-- byte_decode_59
example : wordOfBytes (width := 8) false 255 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 255 := by decide

-- byte_decode_60
example : wordOfBytes (width := 8) true 0 [] = 0 := by decide

-- byte_decode_61
example : wordOfBytes (width := 8) true 0 [165] = 165 := by decide

-- byte_decode_62
example : wordOfBytes (width := 8) true 0 [1, 2, 3, 4, 5] = 1 := by decide

-- byte_decode_63
example : wordOfBytes (width := 8) true 0 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 255 := by decide

-- byte_decode_64
example : wordOfBytes (width := 8) true 1 [] = 0 := by decide

-- byte_decode_65
example : wordOfBytes (width := 8) true 1 [165] = 165 := by decide

-- byte_decode_66
example : wordOfBytes (width := 8) true 1 [1, 2, 3, 4, 5] = 1 := by decide

-- byte_decode_67
example : wordOfBytes (width := 8) true 1 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 255 := by decide

-- byte_decode_68
example : wordOfBytes (width := 8) true 255 [] = 0 := by decide

-- byte_decode_69
example : wordOfBytes (width := 8) true 255 [165] = 165 := by decide

-- byte_decode_70
example : wordOfBytes (width := 8) true 255 [1, 2, 3, 4, 5] = 1 := by decide

-- byte_decode_71
example : wordOfBytes (width := 8) true 255 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 255 := by decide

-- byte_decode_72
example : wordOfBytes (width := 16) false 0 [] = 0 := by decide

-- byte_decode_73
example : wordOfBytes (width := 16) false 0 [165] = 165 := by decide

-- byte_decode_74
example : wordOfBytes (width := 16) false 0 [1, 2, 3, 4, 5] = 513 := by decide

-- byte_decode_75
example : wordOfBytes (width := 16) false 0 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 255 := by decide

-- byte_decode_76
example : wordOfBytes (width := 16) false 1 [] = 0 := by decide

-- byte_decode_77
example : wordOfBytes (width := 16) false 1 [165] = 42240 := by decide

-- byte_decode_78
example : wordOfBytes (width := 16) false 1 [1, 2, 3, 4, 5] = 258 := by decide

-- byte_decode_79
example : wordOfBytes (width := 16) false 1 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 65280 := by decide

-- byte_decode_80
example : wordOfBytes (width := 16) false 65535 [] = 0 := by decide

-- byte_decode_81
example : wordOfBytes (width := 16) false 65535 [165] = 42240 := by decide

-- byte_decode_82
example : wordOfBytes (width := 16) false 65535 [1, 2, 3, 4, 5] = 258 := by decide

-- byte_decode_83
example : wordOfBytes (width := 16) false 65535 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 65280 := by decide

-- byte_decode_84
example : wordOfBytes (width := 16) true 0 [] = 0 := by decide

-- byte_decode_85
example : wordOfBytes (width := 16) true 0 [165] = 42240 := by decide

-- byte_decode_86
example : wordOfBytes (width := 16) true 0 [1, 2, 3, 4, 5] = 258 := by decide

-- byte_decode_87
example : wordOfBytes (width := 16) true 0 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 65280 := by decide

-- byte_decode_88
example : wordOfBytes (width := 16) true 1 [] = 0 := by decide

-- byte_decode_89
example : wordOfBytes (width := 16) true 1 [165] = 165 := by decide

-- byte_decode_90
example : wordOfBytes (width := 16) true 1 [1, 2, 3, 4, 5] = 513 := by decide

-- byte_decode_91
example : wordOfBytes (width := 16) true 1 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 255 := by decide

-- byte_decode_92
example : wordOfBytes (width := 16) true 65535 [] = 0 := by decide

-- byte_decode_93
example : wordOfBytes (width := 16) true 65535 [165] = 165 := by decide

-- byte_decode_94
example : wordOfBytes (width := 16) true 65535 [1, 2, 3, 4, 5] = 513 := by decide

-- byte_decode_95
example : wordOfBytes (width := 16) true 65535 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 255 := by decide

-- byte_decode_96
example : wordOfBytes (width := 64) false 0 [] = 0 := by decide

-- byte_decode_97
example : wordOfBytes (width := 64) false 0 [165] = 165 := by decide

-- byte_decode_98
example : wordOfBytes (width := 64) false 0 [1, 2, 3, 4, 5] = 21542142465 := by decide

-- byte_decode_99
example : wordOfBytes (width := 64) false 0 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 6144092013055705343 := by decide

-- byte_decode_100
example : wordOfBytes (width := 64) false 1 [] = 0 := by decide

-- byte_decode_101
example : wordOfBytes (width := 64) false 1 [165] = 42240 := by decide

-- byte_decode_102
example : wordOfBytes (width := 64) false 1 [1, 2, 3, 4, 5] = 5514788471040 := by decide

-- byte_decode_103
example : wordOfBytes (width := 64) false 1 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 4914309076948680533 := by decide

-- byte_decode_104
example : wordOfBytes (width := 64) false 18446744073709551615 [] = 0 := by decide

-- byte_decode_105
example : wordOfBytes (width := 64) false 18446744073709551615 [165] = 11889503016258109440 := by decide

-- byte_decode_106
example : wordOfBytes (width := 64) false 18446744073709551615 [1, 2, 3, 4, 5] = 72057594122076930 := by decide

-- byte_decode_107
example : wordOfBytes (width := 64) false 18446744073709551615 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 18398686839097622528 := by decide

-- byte_decode_108
example : wordOfBytes (width := 64) true 0 [] = 0 := by decide

-- byte_decode_109
example : wordOfBytes (width := 64) true 0 [165] = 11889503016258109440 := by decide

-- byte_decode_110
example : wordOfBytes (width := 64) true 0 [1, 2, 3, 4, 5] = 72623859789987840 := by decide

-- byte_decode_111
example : wordOfBytes (width := 64) true 0 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 18374827290748208213 := by decide

-- byte_decode_112
example : wordOfBytes (width := 64) true 1 [] = 0 := by decide

-- byte_decode_113
example : wordOfBytes (width := 64) true 1 [165] = 46443371157258240 := by decide

-- byte_decode_114
example : wordOfBytes (width := 64) true 1 [1, 2, 3, 4, 5] = 283686952304640 := by decide

-- byte_decode_115
example : wordOfBytes (width := 64) true 1 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 6196672162328359748 := by decide

-- byte_decode_116
example : wordOfBytes (width := 64) true 18446744073709551615 [] = 0 := by decide

-- byte_decode_117
example : wordOfBytes (width := 64) true 18446744073709551615 [165] = 165 := by decide

-- byte_decode_118
example : wordOfBytes (width := 64) true 18446744073709551615 [1, 2, 3, 4, 5] = 144964032527335425 := by decide

-- byte_decode_119
example : wordOfBytes (width := 64) true 18446744073709551615 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 36047635605640703 := by decide

-- byte_decode_120
example : wordOfBytes (width := 80) false 0 [] = 0 := by decide

-- byte_decode_121
example : wordOfBytes (width := 80) false 0 [165] = 165 := by decide

-- byte_decode_122
example : wordOfBytes (width := 80) false 0 [1, 2, 3, 4, 5] = 21542142465 := by decide

-- byte_decode_123
example : wordOfBytes (width := 80) false 0 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 563849323449019210399999 := by decide

-- byte_decode_124
example : wordOfBytes (width := 80) false 1 [] = 0 := by decide

-- byte_decode_125
example : wordOfBytes (width := 80) false 1 [165] = 42240 := by decide

-- byte_decode_126
example : wordOfBytes (width := 80) false 1 [1, 2, 3, 4, 5] = 5514788471040 := by decide

-- byte_decode_127
example : wordOfBytes (width := 80) false 1 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 483254268808046072364919 := by decide

-- byte_decode_128
example : wordOfBytes (width := 80) false 1208925819614629174706175 [] = 0 := by decide

-- byte_decode_129
example : wordOfBytes (width := 80) false 1208925819614629174706175 [165] = 181419418583040 := by decide

-- byte_decode_130
example : wordOfBytes (width := 80) false 1208925819614629174706175 [1, 2, 3, 4, 5] = 1099595776770 := by decide

-- byte_decode_131
example : wordOfBytes (width := 80) false 1208925819614629174706175 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 644444378295603154747392 := by decide

-- byte_decode_132
example : wordOfBytes (width := 80) true 0 [] = 0 := by decide

-- byte_decode_133
example : wordOfBytes (width := 80) true 0 [165] = 779190469673491460259840 := by decide

-- byte_decode_134
example : wordOfBytes (width := 80) true 0 [1, 2, 3, 4, 5] = 4759477275196643082240 := by decide

-- byte_decode_135
example : wordOfBytes (width := 80) true 0 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 1204212681326474573473399 := by decide

-- byte_decode_136
example : wordOfBytes (width := 80) true 1 [] = 0 := by decide

-- byte_decode_137
example : wordOfBytes (width := 80) true 1 [165] = 3043712772162076016640 := by decide

-- byte_decode_138
example : wordOfBytes (width := 80) true 1 [1, 2, 3, 4, 5] = 18591708106236887040 := by decide

-- byte_decode_139
example : wordOfBytes (width := 80) true 1 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 566665567247919321732454 := by decide

-- byte_decode_140
example : wordOfBytes (width := 80) true 1208925819614629174706175 [] = 0 := by decide

-- byte_decode_141
example : wordOfBytes (width := 80) true 1208925819614629174706175 [165] = 708669603840 := by decide

-- byte_decode_142
example : wordOfBytes (width := 80) true 1208925819614629174706175 [1, 2, 3, 4, 5] = 9500362835715749314560 := by decide

-- byte_decode_143
example : wordOfBytes (width := 80) true 1208925819614629174706175 [255, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136] = 2362417847854417999752 := by decide

end Flapjack.Test.ByteDecoder
