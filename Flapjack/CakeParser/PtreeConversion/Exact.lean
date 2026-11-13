module

public import Flapjack.CakeParser.PtreeConversion
public import Flapjack.CakeParser.PegActions
public import Flapjack.CakeParser.CfgLocation
public import Flapjack.CakeParser.Grammar
public import Flapjack.Misc.Grammar
public import Flapjack.Misc.List
public import Flapjack.AstHOL.Syntax
public import Flapjack.Basis.Pure.MlString
public import Flapjack.NamespaceHOL

@[expose] public section

/-! Exact generic ports of `cakeml/semantics/cmlPtreeConversionScript.sml`'s
parse-tree conversion helpers, stated over the reviewed generic grammar
carrier `Flapjack.Misc.Grammar.ParseTree` so HOL's polymorphic terminal,
nonterminal and location types are preserved. The executed conversion keeps
its specialized `Flapjack.CakeParser.ParseTree` implementation; the two are
connected by `Flapjack.CakeParser.ParseTree.toGrammarTree` and
`ofGrammarTree`. -/
namespace Flapjack.CakeParser.PtreeConversion.Exact

open Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL

/-- Exact port of HOL `ifM_def` (`cmlPtreeConversionScript.sml:96`): the
    option-monadic conditional, selecting the first branch on `SOME T` and the
    second on every other boolean option. -/
@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "ifM_def"]
def ifMHOL {α : Type} (bM : Option Bool) (tM eM : Option α) : Option α :=
  bM >>= fun b => if b then tM else eM

/-- Exact port of HOL `isSymbolicConstructor`
    (`cmlPtreeConversionScript.sml:533`): the character list spells `"::"`. -/
@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "isSymbolicConstructor_def"]
def isSymbolicConstructorHOL (s : List HolChar) : Option Bool :=
  some (s = [58, 58])

/-- Exact port of HOL `isConstructor` (`cmlPtreeConversionScript.sml:538`):
    symbolic constructors plus a character list whose head is an uppercase
    alphabetic character. -/
@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "isConstructor_def"]
def isConstructorHOL (s : List HolChar) : Option Bool :=
  ifMHOL (isSymbolicConstructorHOL s) (some true)
    (some (match Flapjack.oHD s with
      | none => false
      | some c => isAlphaChar c && isUpperChar c))

/-- Exact port of HOL `tokcheck_def`, generic in the terminal type `α`, the
    nonterminal type `β` and the location type `γ`. HOL's equality on the
    generic terminal type is rendered by `DecidableEq α`, the established
    rendering of HOL equality on a generic key type. -/
@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "tokcheck_def"]
def tokcheckHOL {α β γ : Type} [DecidableEq α]
    (pt : Misc.Grammar.ParseTree α β γ) (tok : α) : Bool :=
  decide ((Misc.Grammar.destLf pt >>= Misc.Grammar.destTokSym) = some tok)

/-- Exact port of HOL `tokcheckl_def`: pointwise `tokcheck` over the tree and
    token lists, false when the lists have different lengths. -/
@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "tokcheckl_def"]
def tokchecklHOL {α β γ : Type} [DecidableEq α] :
    List (Misc.Grammar.ParseTree α β γ) → List α → Bool
  | [], [] => true
  | pt :: prest, tok :: tokrest => tokcheckHOL pt tok && tokchecklHOL prest tokrest
  | _, _ => false

/-- Exact port of HOL `singleSymP_def`: the single-leaf symbol token of a
    one-element tree list, filtered by `P` and returned as `Short`. Generic in
    the identifier's module type `α`, the nonterminal type `β` and the location
    type `γ`, with the terminal type fixed to CakeML's `token`. HOL's
    `assert (P s)` guard is the `if P s` test around `return (Short s)`. -/
@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "singleSymP_def"]
def singleSymPHOL {α β γ : Type} (P : MlString → Bool) :
    List (Misc.Grammar.ParseTree CakeParser.Token β γ) → Option (Ident α MlString)
  | [pt] =>
      (Misc.Grammar.destLf pt >>= Misc.Grammar.destTokSym >>= CakeParser.destSymbolT) >>= fun s =>
        if P s then some (.short s) else none
  | _ => none

/-- The generic grammar tree at HOL's `token` terminal type, as used by the
    parse-tree conversion helpers. -/
abbrev TokenTree (β γ : Type) := Misc.Grammar.ParseTree CakeParser.Token β γ

/-- Exact port of HOL `ptree_UQTyop_def`: the `SymbolT`/`AlphaT` payload of the
    single leaf of an `nUQTyOp` node. Generic in the location type `α`. -/
@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "ptree_UQTyop_def"]
def ptreeUQTyopHOL {loc : Type} : TokenTree Nonterminal loc → Option MlString
  | .leaf _ => none
  | .node (rule, _) args =>
      if rule ≠ .inl .nUQTyOp then none
      else match args with
        | [] => none
        | [pt] =>
            (Misc.Grammar.destLf pt >>= Misc.Grammar.destTokSym) >>= fun tk =>
              CakeParser.destSymbolT tk <|> CakeParser.destAlphaT tk
        | _ :: _ :: _ => none

/-- Exact port of HOL `ptree_TyvarN_def`: the type variable of the single leaf
    of an `nTyvarN` node. Generic in the location type `α`. -/
@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "ptree_TyvarN_def"]
def ptreeTyvarNHOL {loc : Type} : TokenTree Nonterminal loc → Option MlString
  | .leaf _ => none
  | .node (rule, _) args =>
      if rule ≠ .inl .nTyvarN then none
      else match args with
        | [] => none
        | [tyv] => Misc.Grammar.destTyvarPT tyv
        | _ :: _ :: _ => none

/-- Exact port of HOL `ptree_Tyop_def`: the type operator of an `nTyOp` node,
    preferring a qualified `LongidT` name over the single-leaf `UQTyop` form.
    Generic in the location type `α`. -/
@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "ptree_Tyop_def"]
def ptreeTyopHOL {loc : Type} : TokenTree Nonterminal loc → Option (Ident MlString MlString)
  | .leaf _ => none
  | .node (rule, _) args =>
      if rule ≠ .inl .nTyOp then none
      else match args with
        | [] => none
        | [pt] =>
            ((Misc.Grammar.destLf pt >>= Misc.Grammar.destTokSym >>= CakeParser.destLongidT)
              >>= fun (xs, s) => some (longShort xs s)) <|>
              (ptreeUQTyopHOL pt).map (fun nm => .short nm)
        | _ :: _ :: _ => none

/-- Exact port of HOL `ptree_V_def`: the `AlphaT`/`SymbolT` payload of the
    single leaf of an `nV` node. HOL's `OPTION_GUARD (FST nt = mkNT nV)` around
    the case analysis is rendered as the `if rule = ...` test. Generic in the
    location type `α`. -/
@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "ptree_V_def"]
def ptreeVHOL {loc : Type} : TokenTree Nonterminal loc → Option MlString
  | .leaf _ => none
  | .node (rule, _) subs =>
      if rule = .inl .nV then
        match subs with
        | [] => none
        | [pt] =>
            (Misc.Grammar.destLf pt >>= Misc.Grammar.destTokSym) >>= fun t =>
              CakeParser.destAlphaT t <|> CakeParser.destSymbolT t
        | _ :: _ :: _ => none
      else none

/-- Exact port of HOL `ptree_FQV_def`: a short `nV` name or a qualified
    `LongidT` name of the single leaf of an `nFQV` node. Generic in the
    location type `α`. -/
@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "ptree_FQV_def"]
def ptreeFQVHOL {loc : Type} : TokenTree Nonterminal loc → Option (Ident MlString MlString)
  | .leaf _ => none
  | .node (rule, _) args =>
      if rule ≠ .inl .nFQV then none
      else match args with
        | [] => none
        | [pt] =>
            (ptreeVHOL pt).map (fun s => .short s) <|>
              ((Misc.Grammar.destLf pt >>= Misc.Grammar.destTokSym >>= CakeParser.destLongidT)
                >>= fun (xs, s) => some (longShort xs s))
        | _ :: _ :: _ => none

/-- Exact port of HOL `ptree_UQConstructorName_def`: the `AlphaT` payload of the
    single leaf of an `nUQConstructorName` node. Generic in the location type
    `α`. -/
@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "ptree_UQConstructorName_def"]
def ptreeUQConstructorNameHOL {loc : Type} : TokenTree Nonterminal loc → Option MlString
  | .leaf _ => none
  | .node (rule, _) args =>
      if rule ≠ .inl .nUQConstructorName then none
      else match args with
        | [] => none
        | [pt] => (Misc.Grammar.destLf pt >>= Misc.Grammar.destTokSym) >>= CakeParser.destAlphaT
        | _ :: _ :: _ => none

/-- Exact port of HOL `ptree_ConstructorName_def`: a short constructor name from
    `ptree_UQConstructorName` or a qualified `LongidT` name. Generic in the
    location type `α`. -/
@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "ptree_ConstructorName_def"]
def ptreeConstructorNameHOL {loc : Type} :
    TokenTree Nonterminal loc → Option (Ident MlString MlString)
  | .leaf _ => none
  | .node (rule, _) args =>
      if rule ≠ .inl .nConstructorName then none
      else match args with
        | [] => none
        | [pt] =>
            (ptreeUQConstructorNameHOL pt).map (fun s => .short s) <|>
              ((Misc.Grammar.destLf pt >>= Misc.Grammar.destTokSym >>= CakeParser.destLongidT)
                >>= fun (xs, s) => some (longShort xs s))
        | _ :: _ :: _ => none

/-- Exact port of HOL `ptree_OpID_def`: the constructor/variable expression of
    an `nOpID` node. Generic in the location type `α`; the identifier's module
    type is fixed to `mlstring`. -/
@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "ptree_OpID_def"]
def ptreeOpIDHOL {loc : Type} : TokenTree Nonterminal loc → Option AstHOL.Exp
  | .leaf _ => none
  | .node (rule, _) subs =>
      if rule ≠ .inl .nOpID then none
      else match subs with
        | [] => none
        | [.leaf (.tok tk, _)] =>
            (CakeParser.destAlphaT tk >>= fun s =>
              ifMHOL (isConstructorHOL s.explode)
                (some (.con (some (.short s)) []))
                (some (.var (.short s)))) <|>
            (CakeParser.destSymbolT tk >>= fun s =>
              ifMHOL (isSymbolicConstructorHOL s.explode)
                (some (.con (some (.short s)) []))
                (some (.var (.short s)))) <|>
            (CakeParser.destLongidT tk >>= fun (path, s) =>
              ifMHOL (isConstructorHOL s.explode)
                (some (.con (some (longShort path s)) []))
                (some (.var (longShort path s)))) <|>
            (if tk = .starT then
              ifMHOL (isSymbolicConstructorHOL (ofString "*").explode)
                (some (.con (some (.short (ofString "*"))) []))
                (some (.var (.short (ofString "*"))))
             else if tk = .equalsT then some (.var (.short (ofString "=")))
             else none)
        | _ => none

/-- Exact port of HOL `ptree_Eliteral_def`: the literal or `FFI` expression of
    an `nEliteral` node. HOL guards with `LENGTH subs = 1 ∧ FST nt = mkNT
    nEliteral` and then takes `HD subs`; Lean renders the guard as the `if` and
    the `HD` by matching the single-element list, which the guard forces.
    Generic in the location type `α`. -/
@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "ptree_Eliteral_def"]
def ptreeEliteralHOL {loc : Type} : TokenTree Nonterminal loc → Option AstHOL.Exp
  | .leaf _ => none
  | .node (rule, _) subs =>
      if subs.length = 1 ∧ rule = .inl .nEliteral then
        match subs with
        | [pt] =>
            (Misc.Grammar.destLf pt >>= Misc.Grammar.destTokSym) >>= fun t =>
              (CakeParser.destIntT t >>= fun i => some (.lit (.intLit i))) <|>
              (CakeParser.destCharT t >>= fun c => some (.lit (.char c))) <|>
              (CakeParser.destStringT t >>= fun s => some (.lit (.strLit s))) <|>
              (CakeParser.destWordT t >>= fun n =>
                some (.lit (.word64 (BitVec.ofNat 64 n)))) <|>
              (CakeParser.destFFIT t >>= fun s => some (.app (.ffi s) []))
        | _ => none
      else none

/-- Exact port of HOL `ptree_Op_def`: the operator identifier of an
    `nMultOps`/`nAddOps`/`nListOps`/`nRelOps`/`nCompOps` node. Generic in the
    identifier's module type `α` and in the location type `β`. -/
@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "ptree_Op_def"]
def ptreeOpHOL {α β : Type} : TokenTree Nonterminal β → Option (Ident α MlString)
  | .leaf _ => none
  | .node (rule, _) subs =>
      if rule = .inl .nMultOps then
        if tokchecklHOL subs [.starT] then some (.short (ofString "*"))
        else if tokchecklHOL subs [.alphaT (ofString "mod")] then some (.short (ofString "mod"))
        else if tokchecklHOL subs [.alphaT (ofString "div")] then some (.short (ofString "div"))
        else singleSymPHOL (fun s => Grammar.validMultSym s.explode) subs
      else if rule = .inl .nAddOps then
        singleSymPHOL (fun s => Grammar.validAddSym s.explode) subs
      else if rule = .inl .nListOps then
        singleSymPHOL (fun s => Grammar.validListSym s.explode) subs
      else if rule = .inl .nRelOps then
        singleSymPHOL (fun s => Grammar.validRelSym s.explode) subs <|>
          (if tokchecklHOL subs [.equalsT] then some (.short (ofString "=")) else none)
      else if rule = .inl .nCompOps then
        if tokchecklHOL subs [.symbolT (ofString ":=")] then some (.short (ofString ":="))
        else if tokchecklHOL subs [.alphaT (ofString "o")] then some (.short (ofString "o"))
        else none
      else none

/-- Exact port of HOL `ptree_StructName_def`: the `AlphaT` payload of the
    single leaf of an `nStructName` node. Generic in the location type `α`. -/
@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "ptree_StructName_def"]
def ptreeStructNameHOL {loc : Type} : TokenTree Nonterminal loc → Option MlString
  | .leaf _ => none
  | .node (rule, _) args =>
      if rule ≠ .inl .nStructName then none
      else match args with
        | [] => none
        | [pt] => (Misc.Grammar.destLf pt >>= Misc.Grammar.destTokSym) >>= CakeParser.destAlphaT
        | _ :: _ :: _ => none

/-! ## Bridges to the executed specialization

The executed frontend keeps its specialized `CakeParser.ParseTree`
implementation. These theorems connect the exact generic twins above to it
through `ParseTree.toGrammarTree`/`toGrammarTrees`; they are Flapjack
infrastructure and have no HOL original. -/

/-- Merging the locations of converted trees is the executable child-location
calculation. -/
theorem treeListLoc_map_toGrammarTree (trees : List CakeParser.ParseTree) :
    Misc.Grammar.treeListLoc (trees.map ParseTree.toGrammarTree) =
      ParseTree.listLocation trees := by
  simpa [CfgValidation.toGrammarTrees_eq_map] using CfgLocation.grammarTreeListLoc trees

/-- The generic `mkNd_fo` twin is the conversion of the executable `mkNode`. -/
theorem mkNdHOL_toGrammarTree (target : Rule) (children : List CakeParser.ParseTree) :
    PegActions.mkNdHOL target (ParseTree.toGrammarTrees children) =
      ParseTree.toGrammarTree (ParseTree.mkNode target children) := by
  simp [PegActions.mkNdHOL, ParseTree.mkNode, ParseTree.toGrammarTree,
    CfgValidation.toGrammarTrees_eq_map, treeListLoc_map_toGrammarTree]

/-- `mkNd_fo` on three converted children is the conversion of `mkNode` on the
three executable children. -/
theorem mkNdHOL_toGrammarTree3 (target : Rule) (first second third : CakeParser.ParseTree) :
    PegActions.mkNdHOL target
        [ParseTree.toGrammarTree first, ParseTree.toGrammarTree second,
          ParseTree.toGrammarTree third] =
      ParseTree.toGrammarTree (ParseTree.mkNode target [first, second, third]) := by
  simp [PegActions.mkNdHOL, ParseTree.mkNode, ParseTree.toGrammarTree,
    CfgValidation.toGrammarTrees_eq_map, ParseTree.listLocation, Misc.Grammar.treeListLoc,
    Misc.Location.mergeListLocs, Misc.Location.mergeLocs, ParseTree.toGrammarTree_location]

/-- The exact generic `eval_unary` twin agrees with the executable
`evalUnary` under the tree conversion. -/
theorem evalUnaryHOL_toGrammarTrees (action : PegActions.Unary)
    (v : List CakeParser.ParseTree) :
    PegActions.evalUnaryHOL action (ParseTree.toGrammarTrees v) =
      ParseTree.toGrammarTrees (PegActions.evalUnary action v) := by
  cases action with
  | id => simp [PegActions.evalUnaryHOL, PegActions.evalUnary]
  | bindNT nt =>
    simp [PegActions.evalUnaryHOL, PegActions.evalUnary, ParseTree.mkNode,
      ParseTree.toGrammarTree, CfgValidation.toGrammarTrees_eq_map,
      treeListLoc_map_toGrammarTree]

/-- The exact generic `mk_linfix_fo` twin agrees with the executable
`mkLinfix` under the tree conversion. -/
theorem mkLinfixHOL_toGrammarTree (target : Rule) (acc : CakeParser.ParseTree)
    (v : List CakeParser.ParseTree) :
    PegActions.mkLinfixHOL target (ParseTree.toGrammarTree acc) (ParseTree.toGrammarTrees v) =
      ParseTree.toGrammarTree (PegActions.mkLinfix target acc v) := by
  have main : ∀ (n : Nat) (v : List CakeParser.ParseTree), v.length = n → ∀ acc,
      PegActions.mkLinfixHOL target (ParseTree.toGrammarTree acc) (ParseTree.toGrammarTrees v) =
        ParseTree.toGrammarTree (PegActions.mkLinfix target acc v) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro v hv acc
      match v with
      | [] =>
        simp [ParseTree.toGrammarTrees, PegActions.mkLinfixHOL, PegActions.mkLinfix]
      | [_] =>
        simp [ParseTree.toGrammarTrees, PegActions.mkLinfixHOL, PegActions.mkLinfix]
      | x :: y :: ys =>
        have hlen : ys.length < n := by
          simp at hv
          omega
        rw [PegActions.mkLinfixHOL.eq_def, PegActions.mkLinfix.eq_def]
        simp only [ParseTree.toGrammarTrees]
        rw [mkNdHOL_toGrammarTree3]
        exact ih ys.length hlen ys rfl (ParseTree.mkNode target [acc, x, y])
  exact main v.length v rfl acc

/-- Deciding equality of token options is their `BEq` comparison. -/
theorem decide_eq_beq_token (a b : CakeParser.Token) :
    decide (a = b) = (a == b) := rfl

theorem decide_eq_beq_option (a b : Option CakeParser.Token) :
    decide (a = b) = (a == b) := by
  cases a with
  | none => cases b <;> rfl
  | some x => cases b with
    | none => rfl
    | some y => simp [decide_eq_beq_token]

/-- The exact generic `tokcheck` twin agrees with the executable `tokcheck`
under the tree conversion. -/
theorem tokcheckHOL_toGrammarTree (pt : CakeParser.ParseTree) (tok : CakeParser.Token) :
    tokcheckHOL (ParseTree.toGrammarTree pt) tok = PtreeConversion.tokcheck pt tok := by
  cases pt with
  | leaf symbol loc =>
    cases symbol with
    | inl rule =>
      simp [tokcheckHOL, PtreeConversion.tokcheck, ParseTree.toGrammarTree,
        ParseTree.toGrammarSymbol, ParseTree.token, Misc.Grammar.destLf,
        Misc.Grammar.destTokSym]
    | inr token =>
      simp [tokcheckHOL, PtreeConversion.tokcheck, ParseTree.toGrammarTree,
        ParseTree.toGrammarSymbol, ParseTree.token, Misc.Grammar.destLf,
        Misc.Grammar.destTokSym, decide_eq_beq_token]
  | node rule loc children =>
    simp [tokcheckHOL, PtreeConversion.tokcheck, ParseTree.toGrammarTree,
      ParseTree.token, Misc.Grammar.destLf]

end Flapjack.CakeParser.PtreeConversion.Exact
