import Flapjack.Byte.WordSliceAlt
set_option maxRecDepth 2048
namespace Flapjack.Test.ByteWordSliceAlt
open Flapjack.HolByte
-- slice_alt_1_0
example : wordSliceAlt (width := 1) 0 0 18364758544493064725 = 0 := by decide

-- slice_alt_1_1
example : wordSliceAlt (width := 1) 1 0 18364758544493064725 = 1 := by decide

-- slice_alt_1_2
example : wordSliceAlt (width := 1) 1 1 18364758544493064725 = 0 := by decide

-- slice_alt_1_3
example : wordSliceAlt (width := 1) 8 0 18364758544493064725 = 1 := by decide

-- slice_alt_1_4
example : wordSliceAlt (width := 1) 16 8 18364758544493064725 = 0 := by decide

-- slice_alt_1_5
example : wordSliceAlt (width := 1) 1 1 18364758544493064725 = 0 := by decide

-- slice_alt_1_6
example : wordSliceAlt (width := 1) 0 1 18364758544493064725 = 0 := by decide

-- slice_alt_1_7
example : wordSliceAlt (width := 1) 2 0 18364758544493064725 = 1 := by decide

-- slice_alt_1_8
example : wordSliceAlt (width := 1) 2 0 18364758544493064725 = 1 := by decide

-- slice_alt_1_9
example : wordSliceAlt (width := 1) 8 4 18364758544493064725 = 0 := by decide

-- slice_alt_1_10
example : wordSliceAlt (width := 1) 1208925819614629174706183 1208925819614629174706185 18364758544493064725 = 0 := by decide

-- slice_alt_7_0
example : wordSliceAlt (width := 7) 0 0 18364758544493064977 = 0 := by decide

-- slice_alt_7_1
example : wordSliceAlt (width := 7) 7 0 18364758544493064977 = 17 := by decide

-- slice_alt_7_2
example : wordSliceAlt (width := 7) 7 1 18364758544493064977 = 16 := by decide

-- slice_alt_7_3
example : wordSliceAlt (width := 7) 8 0 18364758544493064977 = 17 := by decide

-- slice_alt_7_4
example : wordSliceAlt (width := 7) 16 8 18364758544493064977 = 0 := by decide

-- slice_alt_7_5
example : wordSliceAlt (width := 7) 7 7 18364758544493064977 = 0 := by decide

-- slice_alt_7_6
example : wordSliceAlt (width := 7) 0 7 18364758544493064977 = 0 := by decide

-- slice_alt_7_7
example : wordSliceAlt (width := 7) 14 0 18364758544493064977 = 17 := by decide

-- slice_alt_7_8
example : wordSliceAlt (width := 7) 14 6 18364758544493064977 = 0 := by decide

-- slice_alt_7_9
example : wordSliceAlt (width := 7) 14 10 18364758544493064977 = 0 := by decide

-- slice_alt_7_10
example : wordSliceAlt (width := 7) 1208925819614629174706183 1208925819614629174706185 18364758544493064977 = 0 := by decide

-- slice_alt_8_0
example : wordSliceAlt (width := 8) 0 0 18364758544493065233 = 0 := by decide

-- slice_alt_8_1
example : wordSliceAlt (width := 8) 8 0 18364758544493065233 = 17 := by decide

-- slice_alt_8_2
example : wordSliceAlt (width := 8) 8 1 18364758544493065233 = 16 := by decide

-- slice_alt_8_3
example : wordSliceAlt (width := 8) 8 0 18364758544493065233 = 17 := by decide

-- slice_alt_8_4
example : wordSliceAlt (width := 8) 16 8 18364758544493065233 = 0 := by decide

-- slice_alt_8_5
example : wordSliceAlt (width := 8) 8 8 18364758544493065233 = 0 := by decide

-- slice_alt_8_6
example : wordSliceAlt (width := 8) 0 8 18364758544493065233 = 0 := by decide

-- slice_alt_8_7
example : wordSliceAlt (width := 8) 16 0 18364758544493065233 = 17 := by decide

-- slice_alt_8_8
example : wordSliceAlt (width := 8) 16 7 18364758544493065233 = 0 := by decide

-- slice_alt_8_9
example : wordSliceAlt (width := 8) 15 11 18364758544493065233 = 0 := by decide

-- slice_alt_8_10
example : wordSliceAlt (width := 8) 1208925819614629174706183 1208925819614629174706185 18364758544493065233 = 0 := by decide

-- slice_alt_16_0
example : wordSliceAlt (width := 16) 0 0 18364758544493195793 = 0 := by decide

-- slice_alt_16_1
example : wordSliceAlt (width := 16) 16 0 18364758544493195793 = 12817 := by decide

-- slice_alt_16_2
example : wordSliceAlt (width := 16) 16 1 18364758544493195793 = 12816 := by decide

-- slice_alt_16_3
example : wordSliceAlt (width := 16) 8 0 18364758544493195793 = 17 := by decide

-- slice_alt_16_4
example : wordSliceAlt (width := 16) 16 8 18364758544493195793 = 12800 := by decide

-- slice_alt_16_5
example : wordSliceAlt (width := 16) 16 16 18364758544493195793 = 0 := by decide

-- slice_alt_16_6
example : wordSliceAlt (width := 16) 0 16 18364758544493195793 = 0 := by decide

-- slice_alt_16_7
example : wordSliceAlt (width := 16) 32 0 18364758544493195793 = 12817 := by decide

-- slice_alt_16_8
example : wordSliceAlt (width := 16) 32 15 18364758544493195793 = 0 := by decide

-- slice_alt_16_9
example : wordSliceAlt (width := 16) 23 19 18364758544493195793 = 0 := by decide

-- slice_alt_16_10
example : wordSliceAlt (width := 16) 1208925819614629174706183 1208925819614629174706185 18364758544493195793 = 0 := by decide

-- slice_alt_64_0
example : wordSliceAlt (width := 64) 0 0 55258246691912167953 = 0 := by decide

-- slice_alt_64_1
example : wordSliceAlt (width := 64) 64 0 55258246691912167953 = 18364758544493064721 := by decide

-- slice_alt_64_2
example : wordSliceAlt (width := 64) 64 1 55258246691912167953 = 18364758544493064720 := by decide

-- slice_alt_64_3
example : wordSliceAlt (width := 64) 8 0 55258246691912167953 = 17 := by decide

-- slice_alt_64_4
example : wordSliceAlt (width := 64) 16 8 55258246691912167953 = 12800 := by decide

-- slice_alt_64_5
example : wordSliceAlt (width := 64) 64 64 55258246691912167953 = 0 := by decide

-- slice_alt_64_6
example : wordSliceAlt (width := 64) 0 64 55258246691912167953 = 0 := by decide

-- slice_alt_64_7
example : wordSliceAlt (width := 64) 128 0 55258246691912167953 = 18364758544493064721 := by decide

-- slice_alt_64_8
example : wordSliceAlt (width := 64) 128 63 55258246691912167953 = 9223372036854775808 := by decide

-- slice_alt_64_9
example : wordSliceAlt (width := 64) 71 67 55258246691912167953 = 0 := by decide

-- slice_alt_64_10
example : wordSliceAlt (width := 64) 1208925819614629174706183 1208925819614629174706185 55258246691912167953 = 0 := by decide

-- slice_alt_80_0
example : wordSliceAlt (width := 80) 0 0 2417870003987802842477073 = 0 := by decide

-- slice_alt_80_1
example : wordSliceAlt (width := 80) 80 0 2417870003987802842477073 = 18364758544493064721 := by decide

-- slice_alt_80_2
example : wordSliceAlt (width := 80) 80 1 2417870003987802842477073 = 18364758544493064720 := by decide

-- slice_alt_80_3
example : wordSliceAlt (width := 80) 8 0 2417870003987802842477073 = 17 := by decide

-- slice_alt_80_4
example : wordSliceAlt (width := 80) 16 8 2417870003987802842477073 = 12800 := by decide

-- slice_alt_80_5
example : wordSliceAlt (width := 80) 80 80 2417870003987802842477073 = 0 := by decide

-- slice_alt_80_6
example : wordSliceAlt (width := 80) 0 80 2417870003987802842477073 = 0 := by decide

-- slice_alt_80_7
example : wordSliceAlt (width := 80) 160 0 2417870003987802842477073 = 18364758544493064721 := by decide

-- slice_alt_80_8
example : wordSliceAlt (width := 80) 160 79 2417870003987802842477073 = 0 := by decide

-- slice_alt_80_9
example : wordSliceAlt (width := 80) 87 83 2417870003987802842477073 = 0 := by decide

-- slice_alt_80_10
example : wordSliceAlt (width := 80) 1208925819614629174706183 1208925819614629174706185 2417870003987802842477073 = 0 := by decide

end Flapjack.Test.ByteWordSliceAlt
