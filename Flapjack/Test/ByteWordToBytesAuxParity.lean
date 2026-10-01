import Flapjack.Byte
namespace Flapjack.Test.ByteWordToBytesAuxParity
open Flapjack.HolByte
example : wordToBytesAux 5 (4660 : BitVec 16) false = [52,18,52,18,52] := by decide +kernel
example : wordToBytesAux 5 (4660 : BitVec 16) true = [18,52,18,52,18] := by decide +kernel
example : wordToBytesAux 6 (305419896 : BitVec 32) false = [120,86,52,18,120,86] := by decide +kernel
example : wordToBytesAux 6 (305419896 : BitVec 32) true = [18,52,86,120,18,52] := by decide +kernel
example : wordToBytesAux 3 (165 : BitVec 8) false = [165,165,165] := by decide +kernel
example : wordToBytesAux 5 (1 : BitVec 1) false = [1,0,1,0,1] := by decide +kernel
example : wordToBytesAux 5 (1 : BitVec 1) true = [1,1,1,1,1] := by decide +kernel
example : wordToBytesAux 0 (4660 : BitVec 16) true = [] := by decide +kernel
example : wordToBytes (4660 : BitVec 16) false = [52,18] := by decide +kernel
example : wordToBytes (4660 : BitVec 16) true = [18,52] := by decide +kernel
example : wordToBytes (1 : BitVec 1) false = [] := by decide +kernel
example : byteIndex (1 : BitVec 1) false = 8 := by decide +kernel
example : byteIndex (1 : BitVec 1) true = 0 := by decide +kernel
example : getByte (1 : BitVec 1) (1 : BitVec 1) false = 0 := by decide +kernel

def runChecks : IO Bool := do
  IO.println "PASS original byte word_to_bytes_aux arbitrary counts/endian/subbyte/wrap (14 kernel replays)"
  pure true
end Flapjack.Test.ByteWordToBytesAuxParity
