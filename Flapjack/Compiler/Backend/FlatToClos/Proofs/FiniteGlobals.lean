module

public import Flapjack.Compiler.Backend.FlatProps.Globals
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Globals
public import Flapjack.Compiler.Backend.FlatToClos.Proofs.CompileGlobals

@[expose] public section

/-! Finiteness of source and target global-write bags. -/
namespace Flapjack.Compiler.Backend.FlatToClos

private theorem finiteSingleton (key : Nat) :
    finiteBag (fun x : Nat => if x = key then 1 else 0) := by
  have eq : (fun x : Nat => if x = key then 1 else 0) = bagInsert key emptyBag := by
    funext x
    simp [bagInsert, emptyBag]
  rw [eq]
  exact finiteBagInsert _ finiteEmptyBag _

private theorem flatOpFinite (op : FlatLang.Op) : finiteBag (FlatProps.opGlobalBag op) := by
  cases op <;> simp [FlatProps.opGlobalBag, finiteEmptyBag, finiteSingleton]

private theorem flatSetFinite (e : FlatLang.Exp) : finiteBag (FlatProps.setGlobals e) := by
  induction e using FlatProps.setGlobals.induct
    (motive2 := fun fns => finiteBag (FlatProps.funGlobals fns))
    (motive3 := fun es => finiteBag (FlatProps.elistGlobals es))
    (motive4 := fun rows => finiteBag (FlatProps.rowGlobals rows)) <;>
    simp_all [FlatProps.setGlobals, FlatProps.elistGlobals, FlatProps.rowGlobals,
      FlatProps.funGlobals, FlatProps.emptyGlobalBag, FlatProps.unionGlobalBag,
      finiteEmptyBag, finiteBagUnion, flatOpFinite]

/-- Both flat expression and expression-list global bags are finite. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "flat_FINITE_BAG_set_globals"]
theorem flatFiniteBagSetGlobals :
    (∀ e, finiteBag (FlatProps.setGlobals e)) ∧
      (∀ es, finiteBag (FlatProps.elistGlobals es)) := by
  constructor
  · exact flatSetFinite
  · intro es
    induction es with
    | nil => simpa [FlatProps.elistGlobals, FlatProps.emptyGlobalBag] using (finiteEmptyBag (α := Nat))
    | cons e es ih =>
      simpa [FlatProps.elistGlobals, FlatProps.unionGlobalBag] using finiteBagUnion _ (flatSetFinite e) _ ih

private theorem closOpFinite (op : ClosLang.Op) : finiteBag (ClosProps.opGlobalBag op) := by
  cases op <;> try simp [ClosProps.opGlobalBag, FlatProps.emptyGlobalBag, finiteEmptyBag]
  case globOp op => cases op <;> simp [finiteEmptyBag, finiteSingleton]

private theorem closSetFinite (e : ClosLang.Exp) : finiteBag (ClosProps.setGlobals e) := by
  induction e using ClosProps.setGlobals.induct
    (motive2 := fun fns => finiteBag (ClosProps.funGlobals fns))
    (motive3 := fun es => finiteBag (ClosProps.elistGlobals es)) <;>
    simp_all [ClosProps.setGlobals, ClosProps.elistGlobals, ClosProps.funGlobals,
      FlatProps.emptyGlobalBag, FlatProps.unionGlobalBag, finiteEmptyBag, finiteBagUnion, closOpFinite]

/-- Both closure expression and expression-list global bags are finite. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "clos_FINITE_BAG_set_globals"]
theorem closFiniteBagSetGlobals :
    (∀ e, finiteBag (ClosProps.setGlobals e)) ∧
      (∀ es, finiteBag (ClosProps.elistGlobals es)) := by
  constructor
  · exact closSetFinite
  · intro es
    induction es with
    | nil => simpa [ClosProps.elistGlobals, FlatProps.emptyGlobalBag] using (finiteEmptyBag (α := Nat))
    | cons e es ih =>
      simpa [ClosProps.elistGlobals, FlatProps.unionGlobalBag] using finiteBagUnion _ (closSetFinite e) _ ih

/-- Shifting a fold of flat global bags distributes over the fold, which is finite.
The original `BAG_IMAGE SUC` equals `shiftGlobalBag` on finite bags; the
`bag_image_suc_finite_typed` HOL replay checks that source-side equation. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "BAG_IMAGE_FOLDR_lemma"]
theorem bagImageFoldrLemma (xs : List FlatLang.Exp) :
    shiftGlobalBag ((xs.map FlatProps.setGlobals).foldr bagUnion emptyBag) =
      (xs.map (fun e => shiftGlobalBag (FlatProps.setGlobals e))).foldr bagUnion emptyBag ∧
    finiteBag ((xs.map FlatProps.setGlobals).foldr bagUnion emptyBag) := by
  induction xs with
  | nil => simp [shiftEmpty, finiteEmptyBag]
  | cons e es ih =>
    simp only [List.map_cons, List.foldr_cons]
    constructor
    · have shiftUnion (a b : FlatProps.GlobalBag) :
          shiftGlobalBag (bagUnion a b) = bagUnion (shiftGlobalBag a) (shiftGlobalBag b) := by
        funext key
        by_cases h : key = 0 <;> simp [shiftGlobalBag, bagUnion, h]
      rw [shiftUnion, ih.1]
    · exact finiteBagUnion _ (flatFiniteBagSetGlobals.1 e) _ ih.2

end Flapjack.Compiler.Backend.FlatToClos
