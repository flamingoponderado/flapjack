import Flapjack.Misc.BytesInMemory.Domain

namespace Flapjack.Test.BytesInMemoryDomainParity
open Flapjack

private def region {width : Nat} (address query : BitVec width) : Prop :=
  query = address ∨ query = address + 1 ∨ query = address + 2

private instance regionDecidable {width : Nat} (address query : BitVec width) :
    Decidable (region address query) := inferInstanceAs (Decidable
      (query = address ∨ query = address + 1 ∨ query = address + 2))

private instance memoryDecidable {width : Nat} [NeZero width]
    (address : BitVec width) (bytes : List (BitVec 8))
    (memory : BitVec width → BitVec 8) (domain : BitVec width → Prop)
    [domainDecide : DecidablePred domain] : Decidable (bytesInMemoryHOL address bytes memory domain) :=
  match bytes with
  | [] => isTrue trivial
  | x :: xs =>
      letI : Decidable (domain address) := domainDecide address
      letI : Decidable (bytesInMemoryHOL (address + 1) xs memory domain) :=
        memoryDecidable (address + 1) xs memory domain
      inferInstanceAs (Decidable (memory address = x ∧ domain address ∧
        bytesInMemoryHOL (address + 1) xs memory domain))

private def observe {width : Nat} [NeZero width] (address : BitVec width) (index : Nat) :
    Bool × Nat × Bool :=
  (decide (bytesInMemoryHOL address [7,7,7] (fun _ => 7) (region address) ∧ index < 3),
    (address + BitVec.ofNat width index).toNat, decide (region address (address + BitVec.ofNat width index)))

-- Expected observations are decoded only from the fresh original HOL capture.
-- domain_w1_k0
example : observe (width := 1) 1 0 = (true,1,true) := by decide
-- domain_w1_k1
example : observe (width := 1) 1 1 = (true,0,true) := by decide
-- domain_w1_k2
example : observe (width := 1) 1 2 = (true,1,true) := by decide
-- domain_w8_k0
example : observe (width := 8) 255 0 = (true,255,true) := by decide
-- domain_w8_k1
example : observe (width := 8) 255 1 = (true,0,true) := by decide
-- domain_w8_k2
example : observe (width := 8) 255 2 = (true,1,true) := by decide
-- domain_w64_k0
example : observe (width := 64) 18446744073709551615 0 = (true,18446744073709551615,true) := by decide
-- domain_w64_k1
example : observe (width := 64) 18446744073709551615 1 = (true,0,true) := by decide
-- domain_w64_k2
example : observe (width := 64) 18446744073709551615 2 = (true,1,true) := by decide
-- domain_w80_k0
example : observe (width := 80) 1208925819614629174706175 0 = (true,1208925819614629174706175,true) := by decide
-- domain_w80_k1
example : observe (width := 80) 1208925819614629174706175 1 = (true,0,true) := by decide
-- domain_w80_k2
example : observe (width := 80) 1208925819614629174706175 2 = (true,1,true) := by decide

example : region (1 : BitVec 1)
    ((1 : BitVec 1) + BitVec.ofNat 1 0) := by
  exact bytesInMemoryInDomain (1 : BitVec 1) [7,7,7] (fun _ => 7)
    (region (1 : BitVec 1)) 0 ⟨by decide, by decide⟩

example : region (1 : BitVec 1)
    ((1 : BitVec 1) + BitVec.ofNat 1 1) := by
  exact bytesInMemoryInDomain (1 : BitVec 1) [7,7,7] (fun _ => 7)
    (region (1 : BitVec 1)) 1 ⟨by decide, by decide⟩

example : region (1 : BitVec 1)
    ((1 : BitVec 1) + BitVec.ofNat 1 2) := by
  exact bytesInMemoryInDomain (1 : BitVec 1) [7,7,7] (fun _ => 7)
    (region (1 : BitVec 1)) 2 ⟨by decide, by decide⟩

example : region (255 : BitVec 8)
    ((255 : BitVec 8) + BitVec.ofNat 8 0) := by
  exact bytesInMemoryInDomain (255 : BitVec 8) [7,7,7] (fun _ => 7)
    (region (255 : BitVec 8)) 0 ⟨by decide, by decide⟩

example : region (255 : BitVec 8)
    ((255 : BitVec 8) + BitVec.ofNat 8 1) := by
  exact bytesInMemoryInDomain (255 : BitVec 8) [7,7,7] (fun _ => 7)
    (region (255 : BitVec 8)) 1 ⟨by decide, by decide⟩

example : region (255 : BitVec 8)
    ((255 : BitVec 8) + BitVec.ofNat 8 2) := by
  exact bytesInMemoryInDomain (255 : BitVec 8) [7,7,7] (fun _ => 7)
    (region (255 : BitVec 8)) 2 ⟨by decide, by decide⟩

example : region (18446744073709551615 : BitVec 64)
    ((18446744073709551615 : BitVec 64) + BitVec.ofNat 64 0) := by
  exact bytesInMemoryInDomain (18446744073709551615 : BitVec 64) [7,7,7] (fun _ => 7)
    (region (18446744073709551615 : BitVec 64)) 0 ⟨by decide, by decide⟩

example : region (18446744073709551615 : BitVec 64)
    ((18446744073709551615 : BitVec 64) + BitVec.ofNat 64 1) := by
  exact bytesInMemoryInDomain (18446744073709551615 : BitVec 64) [7,7,7] (fun _ => 7)
    (region (18446744073709551615 : BitVec 64)) 1 ⟨by decide, by decide⟩

example : region (18446744073709551615 : BitVec 64)
    ((18446744073709551615 : BitVec 64) + BitVec.ofNat 64 2) := by
  exact bytesInMemoryInDomain (18446744073709551615 : BitVec 64) [7,7,7] (fun _ => 7)
    (region (18446744073709551615 : BitVec 64)) 2 ⟨by decide, by decide⟩

example : region (1208925819614629174706175 : BitVec 80)
    ((1208925819614629174706175 : BitVec 80) + BitVec.ofNat 80 0) := by
  exact bytesInMemoryInDomain (1208925819614629174706175 : BitVec 80) [7,7,7] (fun _ => 7)
    (region (1208925819614629174706175 : BitVec 80)) 0 ⟨by decide, by decide⟩

example : region (1208925819614629174706175 : BitVec 80)
    ((1208925819614629174706175 : BitVec 80) + BitVec.ofNat 80 1) := by
  exact bytesInMemoryInDomain (1208925819614629174706175 : BitVec 80) [7,7,7] (fun _ => 7)
    (region (1208925819614629174706175 : BitVec 80)) 1 ⟨by decide, by decide⟩

example : region (1208925819614629174706175 : BitVec 80)
    ((1208925819614629174706175 : BitVec 80) + BitVec.ofNat 80 2) := by
  exact bytesInMemoryInDomain (1208925819614629174706175 : BitVec 80) [7,7,7] (fun _ => 7)
    (region (1208925819614629174706175 : BitVec 80)) 2 ⟨by decide, by decide⟩

-- domain_empty
example : (decide (bytesInMemoryHOL (255 : BitVec 8) [] (fun _ => 7) (fun _ => False)), decide (0 < ([] : List (BitVec 8)).length), decide ((fun _ => False) ((255 : BitVec 8) + BitVec.ofNat 8 0))) = (true,false,false) := by decide

-- domain_hole
example : (decide (bytesInMemoryHOL (255 : BitVec 8) [7,7,7] (fun _ => 7) (fun q => q = 255 ∨ q = 1)), decide (1 < ([7,7,7] : List (BitVec 8)).length), decide ((fun q => q = 255 ∨ q = 1) ((255 : BitVec 8) + BitVec.ofNat 8 1))) = (false,true,false) := by decide

-- domain_wrong_byte
example : (decide (bytesInMemoryHOL (255 : BitVec 8) [7,8,7] (fun _ => 7) (region (255 : BitVec 8))), decide (1 < ([7,8,7] : List (BitVec 8)).length), decide ((region (255 : BitVec 8)) ((255 : BitVec 8) + BitVec.ofNat 8 1))) = (false,true,true) := by decide

-- domain_past_end
example : (decide (bytesInMemoryHOL (255 : BitVec 8) [7,7,7] (fun _ => 7) (region (255 : BitVec 8))), decide (3 < ([7,7,7] : List (BitVec 8)).length), decide ((region (255 : BitVec 8)) ((255 : BitVec 8) + BitVec.ofNat 8 3))) = (true,false,false) := by decide

def runChecks : IO Bool := do
  let ok := (observe (width := 1) 1 0 == (true,1,true)) &&
    (observe (width := 1) 1 1 == (true,0,true)) &&
    (observe (width := 1) 1 2 == (true,1,true)) &&
    (observe (width := 8) 255 0 == (true,255,true)) &&
    (observe (width := 8) 255 1 == (true,0,true)) &&
    (observe (width := 8) 255 2 == (true,1,true)) &&
    (observe (width := 64) 18446744073709551615 0 == (true,18446744073709551615,true)) &&
    (observe (width := 64) 18446744073709551615 1 == (true,0,true)) &&
    (observe (width := 64) 18446744073709551615 2 == (true,1,true)) &&
    (observe (width := 80) 1208925819614629174706175 0 == (true,1208925819614629174706175,true)) &&
    (observe (width := 80) 1208925819614629174706175 1 == (true,0,true)) &&
    (observe (width := 80) 1208925819614629174706175 2 == (true,1,true)) &&
    ((decide (bytesInMemoryHOL (255 : BitVec 8) [] (fun _ => 7) (fun _ => False)), decide (0 < ([] : List (BitVec 8)).length), decide ((fun _ => False) ((255 : BitVec 8) + BitVec.ofNat 8 0))) == (true,false,false)) &&
    ((decide (bytesInMemoryHOL (255 : BitVec 8) [7,7,7] (fun _ => 7) (fun q => q = 255 ∨ q = 1)), decide (1 < ([7,7,7] : List (BitVec 8)).length), decide ((fun q => q = 255 ∨ q = 1) ((255 : BitVec 8) + BitVec.ofNat 8 1))) == (false,true,false)) &&
    ((decide (bytesInMemoryHOL (255 : BitVec 8) [7,8,7] (fun _ => 7) (region (255 : BitVec 8))), decide (1 < ([7,8,7] : List (BitVec 8)).length), decide ((region (255 : BitVec 8)) ((255 : BitVec 8) + BitVec.ofNat 8 1))) == (false,true,true)) &&
    ((decide (bytesInMemoryHOL (255 : BitVec 8) [7,7,7] (fun _ => 7) (region (255 : BitVec 8))), decide (3 < ([7,7,7] : List (BitVec 8)).length), decide ((region (255 : BitVec 8)) ((255 : BitVec 8) + BitVec.ofNat 8 3))) == (true,false,false))
  IO.println (if ok then "PASS original byte-memory domain (16 kernel/runtime observations, 12 full theorem consumers)" else "FAIL byte-memory domain")
  pure ok

end Flapjack.Test.BytesInMemoryDomainParity
