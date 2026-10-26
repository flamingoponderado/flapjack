import Flapjack.Compiler.Backend.FlatPattern.Names
import Flapjack.Compiler.Backend.PatternSemantics
import Flapjack.Misc.Sptree

/-! Decode pattern-compiler decision trees back into flat expressions. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Basis.Pure.MlString FlatLang PatternCommon PatternSemantics
open Flapjack.Compiler.Backend.BackendCommon

/-- Follow a decision-tree position using flat element projections. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "decode_pos_def"]
def decodePos (t : Tra) (v : Exp) : Position → Exp
  | .emptyPos => v
  | .pos i p => decodePos t (.app t (.el i) [v]) p

/-- Decode a decision-tree atomic test. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "decode_test_def"]
def decodeTest (t : Tra) : DTest → Exp → Exp
  | .tagLenEq tag len, v => .app t (.tagLenEq tag len) [v]
  | .litEq lit, v => .app t (.src .equality) [v, .lit t lit]

/-- Simplify guards using precisely the source's constant and double-negation rules. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "simp_guard_def"]
def simpGuard : DGuard → DGuard
  | .conj x y =>
      let v := simpGuard x
      let w := simpGuard y
      if v = .not .true_ ∨ w = .not .true_ then .not .true_
      else if v = .true_ then w
      else if w = .true_ then v
      else .conj v w
  | .disj x y =>
      let v := simpGuard x
      let w := simpGuard y
      if v = .true_ ∨ w = .true_ then .true_
      else if v = .not .true_ then w
      else if w = .not .true_ then v
      else .disj v w
  | .not x =>
      match simpGuard x with
      | .not .true_ => .true_
      | .not w => w
      | v => .not v
  | x => x

/-- Decode a guard into short-circuiting flat expressions. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "decode_guard_def"]
def decodeGuard (t : Tra) (v : Exp) : DGuard → Exp
  | .not g => .app t (.src .equality) [decodeGuard t v g, mkBool t false]
  | .conj a b => smartIf t (decodeGuard t v a) (decodeGuard t v b) (mkBool t false)
  | .disj a b => smartIf t (decodeGuard t v a) (mkBool t true) (decodeGuard t v b)
  | .true_ => mkBool t true
  | .posTest pos test => decodeTest t test (decodePos t v pos)

/-- Decode a decision tree, retaining its default and type-failure branches. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "decode_dtree_def"]
def decodeDtree (t : Tra) (branches : Spt Exp) (v default : Exp) : DTree → Exp
  | .leaf n => (sptLookup n branches).getD default
  | .fail => default
  | .typeFail => .varLocal t (ofString "impossible-case")
  | .if_ guard a b =>
      let g := simpGuard guard
      let a' := decodeDtree t branches v default a
      let b' := decodeDtree t branches v default b
      if g = .true_ then a'
      else if g = .not .true_ then b'
      else smartIf t (decodeGuard t v g) a' b'

end Flapjack.Compiler.Backend.FlatPattern
