import Flapjack.CakeParser.SexpPrint

/-! Regression observations from `cake_sexp_parser_probe.out`. These finite
examples do not prove the direct parser equivalent to HOL's PEG. -/
namespace Flapjack.Test.CakeSexpParserParity
open Flapjack.CakeParser.Sexp Flapjack.Basis.Pure.MlString

private def bytes (s : String) := (ofString s).explode
private def sym (s : String) : Sexp := .sym (bytes s)
private def str (s : String) : Sexp := .str (bytes s)
private def list (xs : List Sexp) : Sexp := xs.foldr .cons (sym "nil")
private def parseText (s : String) := parse (bytes s)

example : [parseText "nil", parseText "12345", parseText "alpha.beta",
    parseText "\"a\\\"b\"", parseText "'  x"] =
    [some (sym "nil"), some (.num 12345), some (sym "alpha.beta"),
     some (str "a\"b"), some (list [sym "quote", sym "x"])] := by native_decide

example : [parseText "()", parseText "(1 2 3)", parseText "(1 2 . 3)",
    parseText "(1 (2 . 3) . 4)", parseText "(1 . nil)", parseText "(1 . (2 3))"] =
    [some (sym "nil"), some (list [.num 1, .num 2, .num 3]),
     some (.cons (.num 1) (.cons (.num 2) (.num 3))),
     some (.cons (.num 1) (.cons (.cons (.num 2) (.num 3)) (.num 4))),
     some (list [.num 1]), some (list [.num 1, .num 2, .num 3])] := by native_decide

example : ["", "(1", "(. 1)", "(1 . 2 3)", "1abc", "\"\\q\"",
    "\"unterminated", "() ()"].map parseText = List.replicate 8 none := by native_decide

example : [parseText "  (a .b) \n", parseText "a.b", parseText ".a", parseText "(a.b)",
    parseText "123.4", parseText "''x", parseText "(1 . ())", parseText "(1 . 2)garbage",
    parseText "(1 . 2 . 3)", parseText "\"\\\\\"", parseText "\"a\nb\"", parseText "\"a\"b"] =
    [some (.cons (sym "a") (sym "b")), some (sym "a.b"), none,
     some (list [sym "a.b"]), none, some (list [sym "quote", list [sym "quote", sym "x"]]),
     some (list [.num 1]), none, none, some (str "\\"), none, none] := by native_decide

example : [parse [9, 10, 120, 13], parse [0], parse [127], parse [128],
    parse [34, 31, 34], parse [34, 126, 34], parse [120, 128]] =
    [some (sym "x"), none, none, none, none, some (str "~"), none] := by native_decide

-- The printer observations are captured from the pinned HOL `print_sexp`.
example : [render (sym "nil"), render (.num 12345), render (str "a\"b\\c"),
    render (list [.num 1, .num 2]), render (.cons (.num 1) (.num 2)),
    render (list [sym "quote", sym "x"]),
    render (.cons (sym "quote") (.cons (sym "x") (sym "tail"))),
    render (.cons (.str [0, 128]) (str "z"))] =
    [bytes "nil", bytes "12345", bytes "\"a\\\"b\\\\c\"", bytes "(1 2)",
     bytes "(1 . 2)", bytes "'x", bytes "(quote x . tail)",
     [40, 34, 0, 128, 34, 32, 46, 32, 34, 122, 34, 41]] := by native_decide

end Flapjack.Test.CakeSexpParserParity
