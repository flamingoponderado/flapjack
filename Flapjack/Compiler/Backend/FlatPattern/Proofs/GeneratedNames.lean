import Flapjack.Compiler.Backend.FlatPattern.Names

/-! Round-trip properties for pattern-compiler generated names. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Basis.Pure.MlString

/-- Character-offset summation is the sum of offsets after the dropped prefix. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "sum_string_ords_eq"]
theorem sumStringOrds_eq (index : Nat) (name : MlString) :
    sumStringOrds index name = ((name.explode.drop index).map (fun c => c.toNat - 35)).foldr (· + ·) 0 := rfl

/-- Decode an auxiliary generated name, including the offsets contributed by
its existing suffix. The name carrier and original definitions remain pending
HOL correspondence review. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "dec_enc_aux"]
theorem decEncAux (index : Nat) (suffix : List HolChar) :
    decNameToNum (.implode (encNumToNameAux index suffix)) =
      index + ((suffix.map (fun c => c.toNat - 35)).foldr (· + ·) 0) := by
  induction index using Nat.strongRecOn generalizing suffix with
  | ind index ih =>
    rw [encNumToNameAux]
    split
    · rename_i small
      simp [decNameToNum, sumStringOrds, MlString.explode_implode, BitVec.toNat_ofNat]
      omega
    · rename_i large
      have recursive := ih (index - 90) (by omega) (125 :: suffix)
      rw [recursive]
      simp [List.map, BitVec.toNat_ofNat]
      omega

/-- The generated-name decoder is a left inverse of the encoder. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "dec_enc"]
theorem decEnc (index : Nat) : decNameToNum (encNumToName index) = index := by
  simpa [encNumToName] using decEncAux index []

/-- Generated names are injective. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "enc_num_to_name_inj"]
theorem encNumToName_inj (left right : Nat) : encNumToName left = encNumToName right ↔ left = right := by
  constructor
  · intro equal
    have decoded := congrArg decNameToNum equal
    simpa [decEnc] using decoded
  · intro equal
    cases equal
    rfl

end Flapjack.Compiler.Backend.FlatPattern
