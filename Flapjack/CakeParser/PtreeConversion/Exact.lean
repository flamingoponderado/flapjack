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
    simp [PegActions.evalUnaryHOL, PegActions.evalUnary, ParseTree.mkNode, ParseTree.toGrammarTree,
      CfgValidation.toGrammarTrees_eq_map, treeListLoc_map_toGrammarTree]

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
        ParseTree.toGrammarSymbol, ParseTree.token, Misc.Grammar.destLf, Misc.Grammar.destTokSym]
    | inr token =>
      simp [tokcheckHOL, PtreeConversion.tokcheck, ParseTree.toGrammarTree,
        ParseTree.toGrammarSymbol, ParseTree.token, Misc.Grammar.destLf, Misc.Grammar.destTokSym,
        decide_eq_beq_token]
  | node rule loc children =>
    simp [tokcheckHOL, PtreeConversion.tokcheck, ParseTree.toGrammarTree, ParseTree.token,
      Misc.Grammar.destLf]

/-! ### Bridges for the `ptree_*` conversions

The executed conversions keep their specialized implementation; these theorems
connect the exact generic twins to them through `ParseTree.toGrammarTree`.
They are Flapjack infrastructure and have no HOL original. -/

/-- Deciding equality of nonterminals is their `BEq` comparison. -/
theorem decide_eq_beq_nonterminal (a b : Nonterminal) :
    decide (a = b) = (a == b) := rfl

/-- The exact generic `ptree_UQTyop` twin agrees with the executable
conversion. -/
theorem ptreeUQTyopHOL_toGrammarTree (pt : CakeParser.ParseTree) :
    ptreeUQTyopHOL (ParseTree.toGrammarTree pt) = PtreeConversion.ptreeUQTyop pt := by
  cases pt with
  | leaf symbol loc =>
    simp [ptreeUQTyopHOL, PtreeConversion.ptreeUQTyop, PtreeConversion.children,
      ParseTree.toGrammarTree, ParseTree.toGrammarSymbol, ParseTree.token]
  | node rule loc children =>
    cases rule with
    | inr k =>
      simp [ptreeUQTyopHOL, PtreeConversion.ptreeUQTyop, PtreeConversion.children,
        ParseTree.toGrammarTree, ParseTree.token]
    | inl n =>
      by_cases hn : n = .nUQTyOp
      · subst hn
        cases children with
        | nil =>
          simp [ptreeUQTyopHOL, PtreeConversion.ptreeUQTyop, PtreeConversion.children,
            ParseTree.toGrammarTree, ParseTree.token, CfgValidation.toGrammarTrees_eq_map]
        | cons c rest =>
          cases rest with
          | nil =>
            cases c with
            | leaf sym l =>
              cases sym with
              | inl r =>
                simp [ptreeUQTyopHOL, PtreeConversion.ptreeUQTyop, PtreeConversion.children,
                  ParseTree.toGrammarTree, ParseTree.toGrammarSymbol, ParseTree.token,
                  Misc.Grammar.destLf, Misc.Grammar.destTokSym, CakeParser.destSymbolT,
                  CakeParser.destAlphaT, CfgValidation.toGrammarTrees_eq_map]
              | inr tok =>
                cases tok <;>
                  simp [ptreeUQTyopHOL, PtreeConversion.ptreeUQTyop, PtreeConversion.children,
                    ParseTree.toGrammarTree, ParseTree.toGrammarSymbol, ParseTree.token,
                    Misc.Grammar.destLf, Misc.Grammar.destTokSym, CakeParser.destSymbolT,
                    CakeParser.destAlphaT, CfgValidation.toGrammarTrees_eq_map]
            | node r l cs =>
              simp [ptreeUQTyopHOL, PtreeConversion.ptreeUQTyop, PtreeConversion.children,
                ParseTree.toGrammarTree, ParseTree.token, Misc.Grammar.destLf,
                CakeParser.destSymbolT, CakeParser.destAlphaT, CfgValidation.toGrammarTrees_eq_map]
          | cons c2 rest2 =>
            simp [ptreeUQTyopHOL, PtreeConversion.ptreeUQTyop, PtreeConversion.children,
              ParseTree.toGrammarTree, ParseTree.token, CfgValidation.toGrammarTrees_eq_map]
      · simp [ptreeUQTyopHOL, PtreeConversion.ptreeUQTyop, PtreeConversion.children,
        ParseTree.toGrammarTree, ParseTree.token, hn]

/-- The exact generic `ptree_TyvarN` twin agrees with the executable
conversion. -/
theorem ptreeTyvarNHOL_toGrammarTree (pt : CakeParser.ParseTree) :
    ptreeTyvarNHOL (ParseTree.toGrammarTree pt) = PtreeConversion.ptreeTyvarN pt := by
  cases pt with
  | leaf symbol loc =>
    simp [ptreeTyvarNHOL, PtreeConversion.ptreeTyvarN, PtreeConversion.children,
      ParseTree.toGrammarTree, ParseTree.toGrammarSymbol, ParseTree.token, PtreeConversion.tyvar]
  | node rule loc children =>
    cases rule with
    | inr k =>
      simp [ptreeTyvarNHOL, PtreeConversion.ptreeTyvarN, PtreeConversion.children,
        ParseTree.toGrammarTree, ParseTree.token, PtreeConversion.tyvar]
    | inl n =>
      by_cases hn : n = .nTyvarN
      · subst hn
        cases children with
        | nil =>
          simp [ptreeTyvarNHOL, PtreeConversion.ptreeTyvarN, PtreeConversion.children,
            ParseTree.toGrammarTree, ParseTree.token, PtreeConversion.tyvar,
            CfgValidation.toGrammarTrees_eq_map]
        | cons c rest =>
          cases rest with
          | nil =>
            cases c with
            | leaf sym l =>
              cases sym with
              | inl r =>
                simp [ptreeTyvarNHOL, PtreeConversion.ptreeTyvarN, PtreeConversion.children,
                  ParseTree.toGrammarTree, ParseTree.toGrammarSymbol, ParseTree.token,
                  PtreeConversion.tyvar, Misc.Grammar.destTyvarPT,
                  CfgValidation.toGrammarTrees_eq_map]
              | inr tok =>
                cases tok <;>
                  simp [ptreeTyvarNHOL, PtreeConversion.ptreeTyvarN, PtreeConversion.children,
                    ParseTree.toGrammarTree, ParseTree.toGrammarSymbol, ParseTree.token,
                    PtreeConversion.tyvar, Misc.Grammar.destTyvarPT,
                    CfgValidation.toGrammarTrees_eq_map]
            | node r l cs =>
              simp [ptreeTyvarNHOL, PtreeConversion.ptreeTyvarN, PtreeConversion.children,
                ParseTree.toGrammarTree, ParseTree.token, PtreeConversion.tyvar,
                Misc.Grammar.destTyvarPT, CfgValidation.toGrammarTrees_eq_map]
          | cons c2 rest2 =>
            simp [ptreeTyvarNHOL, PtreeConversion.ptreeTyvarN, PtreeConversion.children,
              ParseTree.toGrammarTree, ParseTree.token, PtreeConversion.tyvar,
              CfgValidation.toGrammarTrees_eq_map]
      · simp [ptreeTyvarNHOL, PtreeConversion.ptreeTyvarN, PtreeConversion.children,
        ParseTree.toGrammarTree, ParseTree.token, PtreeConversion.tyvar, hn]

/-- The exact generic `ptree_V` twin agrees with the executable conversion. -/
theorem ptreeVHOL_toGrammarTree (pt : CakeParser.ParseTree) :
    ptreeVHOL (ParseTree.toGrammarTree pt) = PtreeConversion.ptreeV pt := by
  cases pt with
  | leaf symbol loc =>
    simp [ptreeVHOL, PtreeConversion.ptreeV, PtreeConversion.children, ParseTree.toGrammarTree,
      ParseTree.toGrammarSymbol, ParseTree.token]
  | node rule loc children =>
    cases rule with
    | inr k =>
      simp [ptreeVHOL, PtreeConversion.ptreeV, PtreeConversion.children, ParseTree.toGrammarTree,
        ParseTree.token]
    | inl n =>
      by_cases hn : n = .nV
      · subst hn
        cases children with
        | nil =>
          simp [ptreeVHOL, PtreeConversion.ptreeV, PtreeConversion.children,
            ParseTree.toGrammarTree, ParseTree.token, CfgValidation.toGrammarTrees_eq_map]
        | cons c rest =>
          cases rest with
          | nil =>
            cases c with
            | leaf sym l =>
              cases sym with
              | inl r =>
                simp [ptreeVHOL, PtreeConversion.ptreeV, PtreeConversion.children,
                  ParseTree.toGrammarTree, ParseTree.toGrammarSymbol, ParseTree.token,
                  Misc.Grammar.destLf, Misc.Grammar.destTokSym, CakeParser.destAlphaT,
                  CakeParser.destSymbolT, CfgValidation.toGrammarTrees_eq_map]
              | inr tok =>
                cases tok <;>
                  simp [ptreeVHOL, PtreeConversion.ptreeV, PtreeConversion.children,
                    ParseTree.toGrammarTree, ParseTree.toGrammarSymbol, ParseTree.token,
                    Misc.Grammar.destLf, Misc.Grammar.destTokSym, CakeParser.destAlphaT,
                    CakeParser.destSymbolT, CfgValidation.toGrammarTrees_eq_map]
            | node r l cs =>
              simp [ptreeVHOL, PtreeConversion.ptreeV, PtreeConversion.children,
                ParseTree.toGrammarTree, ParseTree.token, Misc.Grammar.destLf,
                CakeParser.destAlphaT, CakeParser.destSymbolT, CfgValidation.toGrammarTrees_eq_map]
          | cons c2 rest2 =>
            simp [ptreeVHOL, PtreeConversion.ptreeV, PtreeConversion.children,
              ParseTree.toGrammarTree, ParseTree.token, CfgValidation.toGrammarTrees_eq_map]
      · simp [ptreeVHOL, PtreeConversion.ptreeV, PtreeConversion.children, ParseTree.toGrammarTree,
        ParseTree.token, hn]

/-- The exact generic `ptree_UQConstructorName` twin agrees with the
executable conversion. -/
theorem ptreeUQConstructorNameHOL_toGrammarTree (pt : CakeParser.ParseTree) :
    ptreeUQConstructorNameHOL (ParseTree.toGrammarTree pt) =
      PtreeConversion.ptreeUQConstructorName pt := by
  cases pt with
  | leaf symbol loc =>
    simp [ptreeUQConstructorNameHOL, PtreeConversion.ptreeUQConstructorName,
      PtreeConversion.children, ParseTree.toGrammarTree, ParseTree.toGrammarSymbol, ParseTree.token]
  | node rule loc children =>
    cases rule with
    | inr k =>
      simp [ptreeUQConstructorNameHOL, PtreeConversion.ptreeUQConstructorName,
        PtreeConversion.children, ParseTree.toGrammarTree, ParseTree.token]
    | inl n =>
      by_cases hn : n = .nUQConstructorName
      · subst hn
        cases children with
        | nil =>
          simp [ptreeUQConstructorNameHOL, PtreeConversion.ptreeUQConstructorName,
            PtreeConversion.children, ParseTree.toGrammarTree, ParseTree.token,
            CfgValidation.toGrammarTrees_eq_map]
        | cons c rest =>
          cases rest with
          | nil =>
            cases c with
            | leaf sym l =>
              cases sym with
              | inl r =>
                simp [ptreeUQConstructorNameHOL, PtreeConversion.ptreeUQConstructorName,
                  PtreeConversion.children, ParseTree.toGrammarTree, ParseTree.toGrammarSymbol,
                  ParseTree.token, Misc.Grammar.destLf, Misc.Grammar.destTokSym,
                  CfgValidation.toGrammarTrees_eq_map]
              | inr tok =>
                cases tok <;>
                  simp [ptreeUQConstructorNameHOL, PtreeConversion.ptreeUQConstructorName,
                    PtreeConversion.children, ParseTree.toGrammarTree, ParseTree.toGrammarSymbol,
                    ParseTree.token, Misc.Grammar.destLf, Misc.Grammar.destTokSym,
                    CakeParser.destAlphaT, CfgValidation.toGrammarTrees_eq_map]
            | node r l cs =>
              simp [ptreeUQConstructorNameHOL, PtreeConversion.ptreeUQConstructorName,
                PtreeConversion.children, ParseTree.toGrammarTree, ParseTree.token,
                Misc.Grammar.destLf, CfgValidation.toGrammarTrees_eq_map]
          | cons c2 rest2 =>
            simp [ptreeUQConstructorNameHOL, PtreeConversion.ptreeUQConstructorName,
              PtreeConversion.children, ParseTree.toGrammarTree, ParseTree.token,
              CfgValidation.toGrammarTrees_eq_map]
      · simp [ptreeUQConstructorNameHOL, PtreeConversion.ptreeUQConstructorName,
        PtreeConversion.children, ParseTree.toGrammarTree, ParseTree.token, hn]

/-- The exact generic `ptree_StructName` twin agrees with the executable
conversion. -/
theorem ptreeStructNameHOL_toGrammarTree (pt : CakeParser.ParseTree) :
    ptreeStructNameHOL (ParseTree.toGrammarTree pt) =
      PtreeConversion.ptreeStructName pt := by
  cases pt with
  | leaf symbol loc =>
    simp [ptreeStructNameHOL, PtreeConversion.ptreeStructName, PtreeConversion.children,
      ParseTree.toGrammarTree, ParseTree.toGrammarSymbol, ParseTree.token]
  | node rule loc children =>
    cases rule with
    | inr k =>
      simp [ptreeStructNameHOL, PtreeConversion.ptreeStructName, PtreeConversion.children,
        ParseTree.toGrammarTree, ParseTree.token]
    | inl n =>
      by_cases hn : n = .nStructName
      · subst hn
        cases children with
        | nil =>
          simp [ptreeStructNameHOL, PtreeConversion.ptreeStructName, PtreeConversion.children,
            ParseTree.toGrammarTree, ParseTree.token, CfgValidation.toGrammarTrees_eq_map]
        | cons c rest =>
          cases rest with
          | nil =>
            cases c with
            | leaf sym l =>
              cases sym with
              | inl r =>
                simp [ptreeStructNameHOL, PtreeConversion.ptreeStructName,
                  PtreeConversion.children, ParseTree.toGrammarTree, ParseTree.toGrammarSymbol,
                  ParseTree.token, Misc.Grammar.destLf, Misc.Grammar.destTokSym,
                  CfgValidation.toGrammarTrees_eq_map]
              | inr tok =>
                cases tok <;>
                  simp [ptreeStructNameHOL, PtreeConversion.ptreeStructName,
                    PtreeConversion.children, ParseTree.toGrammarTree, ParseTree.toGrammarSymbol,
                    ParseTree.token, Misc.Grammar.destLf, Misc.Grammar.destTokSym,
                    CakeParser.destAlphaT, CfgValidation.toGrammarTrees_eq_map]
            | node r l cs =>
              simp [ptreeStructNameHOL, PtreeConversion.ptreeStructName, PtreeConversion.children,
                ParseTree.toGrammarTree, ParseTree.token, Misc.Grammar.destLf,
                CfgValidation.toGrammarTrees_eq_map]
          | cons c2 rest2 =>
            simp [ptreeStructNameHOL, PtreeConversion.ptreeStructName, PtreeConversion.children,
              ParseTree.toGrammarTree, ParseTree.token, CfgValidation.toGrammarTrees_eq_map]
      · simp [ptreeStructNameHOL, PtreeConversion.ptreeStructName, PtreeConversion.children,
        ParseTree.toGrammarTree, ParseTree.token, hn]

/-- The exact generic `ptree_Eliteral` twin agrees with the executable
conversion. -/
theorem ptreeEliteralHOL_toGrammarTree (pt : CakeParser.ParseTree) :
    ptreeEliteralHOL (ParseTree.toGrammarTree pt) = PtreeConversion.ptreeEliteral pt := by
  cases pt with
  | leaf symbol loc =>
    simp [ptreeEliteralHOL, PtreeConversion.ptreeEliteral, PtreeConversion.children,
      ParseTree.toGrammarTree, ParseTree.toGrammarSymbol, ParseTree.token]
  | node rule loc children =>
    cases rule with
    | inr k =>
      simp [ptreeEliteralHOL, PtreeConversion.ptreeEliteral, PtreeConversion.children,
        ParseTree.toGrammarTree, ParseTree.token]
    | inl n =>
      by_cases hn : n = .nEliteral
      · subst hn
        cases children with
        | nil =>
          simp [ptreeEliteralHOL, PtreeConversion.ptreeEliteral, PtreeConversion.children,
            ParseTree.toGrammarTree, ParseTree.token, CfgValidation.toGrammarTrees_eq_map]
        | cons c rest =>
          cases rest with
          | nil =>
            cases c with
            | leaf sym l =>
              cases sym with
              | inl r =>
                simp [ptreeEliteralHOL, PtreeConversion.ptreeEliteral, PtreeConversion.children,
                  ParseTree.toGrammarTree, ParseTree.toGrammarSymbol, ParseTree.token,
                  Misc.Grammar.destLf, Misc.Grammar.destTokSym, CakeParser.destIntT,
                  CakeParser.destCharT, CakeParser.destStringT, CakeParser.destWordT,
                  CakeParser.destFFIT, CfgValidation.toGrammarTrees_eq_map]
              | inr tok =>
                cases tok <;>
                  simp [ptreeEliteralHOL, PtreeConversion.ptreeEliteral, PtreeConversion.children,
                    ParseTree.toGrammarTree, ParseTree.toGrammarSymbol, ParseTree.token,
                    Misc.Grammar.destLf, Misc.Grammar.destTokSym, CakeParser.destIntT,
                    CakeParser.destCharT, CakeParser.destStringT, CakeParser.destWordT,
                    CakeParser.destFFIT, CfgValidation.toGrammarTrees_eq_map]
            | node r l cs =>
              simp [ptreeEliteralHOL, PtreeConversion.ptreeEliteral, PtreeConversion.children,
                ParseTree.toGrammarTree, ParseTree.token, Misc.Grammar.destLf, CakeParser.destIntT,
                CakeParser.destCharT, CakeParser.destStringT, CakeParser.destWordT,
                CakeParser.destFFIT, CfgValidation.toGrammarTrees_eq_map]
          | cons c2 rest2 =>
            simp [ptreeEliteralHOL, PtreeConversion.ptreeEliteral, PtreeConversion.children,
              ParseTree.toGrammarTree, ParseTree.token, CfgValidation.toGrammarTrees_eq_map]
      · simp [ptreeEliteralHOL, PtreeConversion.ptreeEliteral, PtreeConversion.children,
        ParseTree.toGrammarTree, ParseTree.token, hn]

/-- The exact generic `ptree_Tyop` twin agrees with the executable
conversion. -/
theorem ptreeTyopHOL_toGrammarTree (pt : CakeParser.ParseTree) :
    ptreeTyopHOL (ParseTree.toGrammarTree pt) = PtreeConversion.ptreeTyop pt := by
  cases pt with
  | leaf symbol loc =>
    simp [ptreeTyopHOL, PtreeConversion.ptreeTyop, PtreeConversion.children,
      ParseTree.toGrammarTree, ParseTree.toGrammarSymbol, ParseTree.token,
      PtreeConversion.ptreeUQTyop]
  | node rule loc children =>
    cases rule with
    | inr k =>
      simp [ptreeTyopHOL, PtreeConversion.ptreeTyop, PtreeConversion.children,
        ParseTree.toGrammarTree, ParseTree.token, PtreeConversion.ptreeUQTyop]
    | inl n =>
      by_cases hn : n = .nTyOp
      · subst hn
        cases children with
        | nil =>
          simp [ptreeTyopHOL, PtreeConversion.ptreeTyop, PtreeConversion.children,
            ParseTree.toGrammarTree, ParseTree.token, PtreeConversion.ptreeUQTyop,
            CfgValidation.toGrammarTrees_eq_map]
        | cons c rest =>
          cases rest with
          | nil =>
            cases c with
            | leaf sym l =>
              cases sym with
              | inl r =>
                simp [ptreeTyopHOL, PtreeConversion.ptreeTyop, PtreeConversion.children,
                  ParseTree.toGrammarTree, ParseTree.toGrammarSymbol, ParseTree.token,
                  Misc.Grammar.destLf, Misc.Grammar.destTokSym, ptreeUQTyopHOL,
                  PtreeConversion.ptreeUQTyop, CfgValidation.toGrammarTrees_eq_map]
              | inr tok =>
                cases tok <;>
                  simp [ptreeTyopHOL, PtreeConversion.ptreeTyop, PtreeConversion.children,
                    ParseTree.toGrammarTree, ParseTree.toGrammarSymbol, ParseTree.token,
                    Misc.Grammar.destLf, Misc.Grammar.destTokSym, CakeParser.destLongidT,
                    ptreeUQTyopHOL, PtreeConversion.ptreeUQTyop,
                    CfgValidation.toGrammarTrees_eq_map]
            | node r l cs =>
              have h : ptreeUQTyopHOL (Misc.Grammar.ParseTree.node (r, l)
                    (cs.map ParseTree.toGrammarTree)) =
                  PtreeConversion.ptreeUQTyop (ParseTree.node r l cs) := by
                simpa only [ParseTree.toGrammarTree,
                  CfgValidation.toGrammarTrees_eq_map] using
                  ptreeUQTyopHOL_toGrammarTree (ParseTree.node r l cs)
              simp [ptreeTyopHOL, PtreeConversion.ptreeTyop, PtreeConversion.children,
                ParseTree.toGrammarTree, ParseTree.token, Misc.Grammar.destLf,
                CfgValidation.toGrammarTrees_eq_map, Option.map, h]
          | cons c2 rest2 =>
            simp [ptreeTyopHOL, PtreeConversion.ptreeTyop, PtreeConversion.children,
              ParseTree.toGrammarTree, ParseTree.token, PtreeConversion.ptreeUQTyop,
              CfgValidation.toGrammarTrees_eq_map]
      · simp [ptreeTyopHOL, PtreeConversion.ptreeTyop, PtreeConversion.children,
        ParseTree.toGrammarTree, ParseTree.token, PtreeConversion.ptreeUQTyop, hn]

/-- The exact generic `ptree_FQV` twin agrees with the executable
conversion. -/
theorem ptreeFQVHOL_toGrammarTree (pt : CakeParser.ParseTree) :
    ptreeFQVHOL (ParseTree.toGrammarTree pt) = PtreeConversion.ptreeFQV pt := by
  cases pt with
  | leaf symbol loc =>
    simp [ptreeFQVHOL, PtreeConversion.ptreeFQV, PtreeConversion.children, ParseTree.toGrammarTree,
      ParseTree.toGrammarSymbol, ParseTree.token, PtreeConversion.ptreeV]
  | node rule loc children =>
    cases rule with
    | inr k =>
      simp [ptreeFQVHOL, PtreeConversion.ptreeFQV, PtreeConversion.children,
        ParseTree.toGrammarTree, ParseTree.token, PtreeConversion.ptreeV]
    | inl n =>
      by_cases hn : n = .nFQV
      · subst hn
        cases children with
        | nil =>
          simp [ptreeFQVHOL, PtreeConversion.ptreeFQV, PtreeConversion.children,
            ParseTree.toGrammarTree, ParseTree.token, PtreeConversion.ptreeV,
            CfgValidation.toGrammarTrees_eq_map]
        | cons c rest =>
          cases rest with
          | nil =>
            cases c with
            | leaf sym l =>
              cases sym with
              | inl r =>
                simp [ptreeFQVHOL, PtreeConversion.ptreeFQV, PtreeConversion.children,
                  ParseTree.toGrammarTree, ParseTree.toGrammarSymbol, ParseTree.token,
                  Misc.Grammar.destLf, Misc.Grammar.destTokSym, ptreeVHOL, PtreeConversion.ptreeV,
                  CfgValidation.toGrammarTrees_eq_map]
              | inr tok =>
                cases tok <;>
                  simp [ptreeFQVHOL, PtreeConversion.ptreeFQV, PtreeConversion.children,
                    ParseTree.toGrammarTree, ParseTree.toGrammarSymbol, ParseTree.token,
                    Misc.Grammar.destLf, Misc.Grammar.destTokSym, CakeParser.destLongidT,
                    ptreeVHOL, PtreeConversion.ptreeV, CfgValidation.toGrammarTrees_eq_map]
            | node r l cs =>
              have h : ptreeVHOL (Misc.Grammar.ParseTree.node (r, l)
                    (cs.map ParseTree.toGrammarTree)) =
                  PtreeConversion.ptreeV (ParseTree.node r l cs) := by
                simpa only [ParseTree.toGrammarTree,
                  CfgValidation.toGrammarTrees_eq_map] using
                  ptreeVHOL_toGrammarTree (ParseTree.node r l cs)
              simp [ptreeFQVHOL, PtreeConversion.ptreeFQV, PtreeConversion.children,
                ParseTree.toGrammarTree, ParseTree.token, Misc.Grammar.destLf,
                CfgValidation.toGrammarTrees_eq_map, Option.map, h]
              cases hpt : PtreeConversion.ptreeV (ParseTree.node r l cs) <;>
                simp
          | cons c2 rest2 =>
            simp [ptreeFQVHOL, PtreeConversion.ptreeFQV, PtreeConversion.children,
              ParseTree.toGrammarTree, ParseTree.token, PtreeConversion.ptreeV,
              CfgValidation.toGrammarTrees_eq_map]
      · simp [ptreeFQVHOL, PtreeConversion.ptreeFQV, PtreeConversion.children,
        ParseTree.toGrammarTree, ParseTree.token, PtreeConversion.ptreeV, hn]

/-- The exact generic `ptree_ConstructorName` twin agrees with the executable
conversion. -/
theorem ptreeConstructorNameHOL_toGrammarTree (pt : CakeParser.ParseTree) :
    ptreeConstructorNameHOL (ParseTree.toGrammarTree pt) =
      PtreeConversion.ptreeConstructorName pt := by
  cases pt with
  | leaf symbol loc =>
    simp [ptreeConstructorNameHOL, PtreeConversion.ptreeConstructorName, PtreeConversion.children,
      ParseTree.toGrammarTree, ParseTree.toGrammarSymbol, ParseTree.token,
      PtreeConversion.ptreeUQConstructorName]
  | node rule loc children =>
    cases rule with
    | inr k =>
      simp [ptreeConstructorNameHOL, PtreeConversion.ptreeConstructorName,
        PtreeConversion.children, ParseTree.toGrammarTree, ParseTree.token,
        PtreeConversion.ptreeUQConstructorName]
    | inl n =>
      by_cases hn : n = .nConstructorName
      · subst hn
        cases children with
        | nil =>
          simp [ptreeConstructorNameHOL, PtreeConversion.ptreeConstructorName,
            PtreeConversion.children, ParseTree.toGrammarTree, ParseTree.token,
            PtreeConversion.ptreeUQConstructorName, CfgValidation.toGrammarTrees_eq_map]
        | cons c rest =>
          cases rest with
          | nil =>
            cases c with
            | leaf sym l =>
              cases sym with
              | inl r =>
                simp [ptreeConstructorNameHOL, PtreeConversion.ptreeConstructorName,
                  PtreeConversion.children, ParseTree.toGrammarTree, ParseTree.toGrammarSymbol,
                  ParseTree.token, Misc.Grammar.destLf, Misc.Grammar.destTokSym,
                  ptreeUQConstructorNameHOL, PtreeConversion.ptreeUQConstructorName,
                  CfgValidation.toGrammarTrees_eq_map]
              | inr tok =>
                cases tok <;>
                  simp [ptreeConstructorNameHOL, PtreeConversion.ptreeConstructorName,
                    PtreeConversion.children, ParseTree.toGrammarTree, ParseTree.toGrammarSymbol,
                    ParseTree.token, Misc.Grammar.destLf, Misc.Grammar.destTokSym,
                    CakeParser.destLongidT, ptreeUQConstructorNameHOL,
                    PtreeConversion.ptreeUQConstructorName, CfgValidation.toGrammarTrees_eq_map]
            | node r l cs =>
              have h : ptreeUQConstructorNameHOL (Misc.Grammar.ParseTree.node (r, l)
                    (cs.map ParseTree.toGrammarTree)) =
                  PtreeConversion.ptreeUQConstructorName (ParseTree.node r l cs) := by
                simpa only [ParseTree.toGrammarTree,
                  CfgValidation.toGrammarTrees_eq_map] using
                  ptreeUQConstructorNameHOL_toGrammarTree (ParseTree.node r l cs)
              simp [ptreeConstructorNameHOL, PtreeConversion.ptreeConstructorName,
                PtreeConversion.children, ParseTree.toGrammarTree, ParseTree.token,
                Misc.Grammar.destLf, CfgValidation.toGrammarTrees_eq_map, Option.map, h]
              cases hpt : PtreeConversion.ptreeUQConstructorName (ParseTree.node r l cs) <;>
                simp
          | cons c2 rest2 =>
            simp [ptreeConstructorNameHOL, PtreeConversion.ptreeConstructorName,
              PtreeConversion.children, ParseTree.toGrammarTree, ParseTree.token,
              PtreeConversion.ptreeUQConstructorName, CfgValidation.toGrammarTrees_eq_map]
      · simp [ptreeConstructorNameHOL, PtreeConversion.ptreeConstructorName,
        PtreeConversion.children, ParseTree.toGrammarTree, ParseTree.token,
        PtreeConversion.ptreeUQConstructorName, hn]


/-- `(isAlphaChar c && isUpperChar c)` is `isUpperChar c`. -/
theorem isAlphaChar_and_isUpperChar (c : HolChar) :
    (isAlphaChar c && isUpperChar c) = isUpperChar c := by
  by_cases h : isUpperChar c <;> simp [isAlphaChar, h]

/-- The `decide` form of `isAlphaChar c && isUpperChar c`. -/
theorem isAlphaChar_and_upper (c : HolChar) :
    (isAlphaChar c && isUpperChar c) = (65 ≤ c.toNat && c.toNat ≤ 90) := by
  rw [isAlphaChar_and_isUpperChar]
  rfl

/-- `"*"` is not the symbolic constructor name `"::"`. -/
theorem star_ne_cons : (ofString "*").explode ≠ [58, 58] := by
  decide

/-- A boolean `if` over two `Exp` options is a `some` of the `if`. -/
theorem ite_some_exp (b : Bool) (x y : AstHOL.Exp) :
    (if b = true then some x else some y) = some (if b then x else y) := by
  cases b <;> rfl

/-- A boolean `if` returning `true`/`c` is the `||` of the two. -/
theorem ite_some_bool (b c : Bool) :
    (if b then (some true : Option Bool) else some c) = some (b || c) := by
  cases b <;> rfl

/-- Deciding equality against the two-byte list `[58, 58]` splits into bytes. -/
theorem decide_cons_cons (c : HolChar) (rest : List HolChar) :
    decide (c :: rest = [58, 58]) = (decide (c = 58) && decide (rest = [58])) := by
  cases rest with
  | nil => simp [List.cons.injEq]
  | cons c' rest' => simp [List.cons.injEq]

/-- Structural equality of two `implode`s is equality of the byte lists. -/
theorem implode_beq (d e : List HolChar) :
    (MlString.implode d == MlString.implode e) = decide (d = e) := by
  rw [show (MlString.implode d == MlString.implode e) =
      decide (MlString.implode d = MlString.implode e) from rfl]
  simp

/-- `==` against `"::"` is deciding the exploded bytes against `[58, 58]`. -/
theorem beq_ofString_cons_cons (s : MlString) :
    (s == ofString "::") = decide (s.explode = [58, 58]) := by
  cases s with
  | implode d =>
    simp [implode_beq, ofString, MlString.explode] <;> rfl

/-- `isConstructorHOL` on an exploded name is the executed `constructorName`. -/
theorem isConstructorHOL_eq_constructorName (s : MlString) :
    isConstructorHOL s.explode = some (PtreeConversion.constructorName s) := by
  cases s with
  | implode d =>
    cases d with
    | nil =>
      simp [isConstructorHOL, isSymbolicConstructorHOL, ifMHOL, implode_beq,
        PtreeConversion.constructorName, PtreeConversion.uppercase, ofString, MlString.explode,
        Flapjack.oHD]
    | cons c rest =>
      simp [isConstructorHOL, isSymbolicConstructorHOL, ifMHOL, isAlphaChar_and_upper,
        ite_some_bool, implode_beq, PtreeConversion.constructorName, PtreeConversion.uppercase,
        ofString, MlString.explode, Flapjack.oHD]

/-- `isSymbolicConstructorHOL` on an exploded name is the executed `== "::"`. -/
theorem isSymbolicConstructorHOL_eq_beq (s : MlString) :
    isSymbolicConstructorHOL s.explode = some (s == ofString "::") := by
  cases s with
  | implode d =>
    simp [isSymbolicConstructorHOL, implode_beq, ofString, MlString.explode] <;> rfl


/-- The exact generic `ptree_OpID` twin agrees with the executable conversion. -/
theorem ptreeOpIDHOL_toGrammarTree (pt : CakeParser.ParseTree) :
    ptreeOpIDHOL (ParseTree.toGrammarTree pt) = PtreeConversion.ptreeOpID pt := by
  cases pt with
  | leaf _ =>
    simp [ptreeOpIDHOL, PtreeConversion.ptreeOpID, PtreeConversion.children,
      ParseTree.toGrammarTree]
  | node r l cs =>
    cases r with
    | inl rule =>
      cases rule with
      | nOpID =>
        cases cs with
        | nil =>
          simp [ptreeOpIDHOL, PtreeConversion.ptreeOpID, PtreeConversion.children,
            ParseTree.toGrammarTree, ParseTree.toGrammarTrees]
        | cons c rest =>
          cases rest with
          | nil =>
            cases c with
            | leaf sym l' =>
              cases sym with
              | inl rule' =>
                simp [ptreeOpIDHOL, PtreeConversion.ptreeOpID, PtreeConversion.children,
                  ParseTree.toGrammarTree, ParseTree.toGrammarTrees, ParseTree.toGrammarSymbol,
                  ParseTree.token]
              | inr tk =>
                cases tk <;>
                  simp [ptreeOpIDHOL, PtreeConversion.ptreeOpID, PtreeConversion.children,
                    ParseTree.toGrammarTree, ParseTree.toGrammarTrees, ParseTree.toGrammarSymbol,
                    ParseTree.token, CakeParser.destAlphaT, CakeParser.destSymbolT,
                    CakeParser.destLongidT, ifMHOL, isConstructorHOL_eq_constructorName,
                    isSymbolicConstructorHOL, ite_some_exp, beq_ofString_cons_cons]
            | node r' l' cs' =>
              simp [ptreeOpIDHOL, PtreeConversion.ptreeOpID, PtreeConversion.children,
                ParseTree.toGrammarTree, ParseTree.toGrammarTrees, ParseTree.token]
          | cons c2 rest2 =>
            simp [ptreeOpIDHOL, PtreeConversion.ptreeOpID, PtreeConversion.children,
              ParseTree.toGrammarTree, ParseTree.toGrammarTrees]
      | _ =>
        simp [ptreeOpIDHOL, PtreeConversion.ptreeOpID, PtreeConversion.children,
          ParseTree.toGrammarTree]
    | inr n =>
      simp [ptreeOpIDHOL, PtreeConversion.ptreeOpID, PtreeConversion.children,
        ParseTree.toGrammarTree]

end Flapjack.CakeParser.PtreeConversion.Exact
