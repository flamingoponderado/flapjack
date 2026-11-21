(* Typed source-parsed captures of the `[local]` theorems of HOL's
   mc_multiwordScript.sml (HOL/examples/machine-code/multiword), for the Lean
   port beneath Flapjack/Misc/Multiword/Mc. The probe runs from the multiword
   directory and parses each statement from the pinned source text in the
   context of the built mc_multiword theory. *)
load "multiwordTheory";
load "mc_multiwordTheory";
open HolKernel Parse boolLib bossLib;
open multiwordTheory mc_multiwordTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;

val source_text =
  let
    val stream = TextIO.openIn "mc_multiwordScript.sml"
    val text = TextIO.inputAll stream
    val _ = TextIO.closeIn stream
  in text end;

val source_lines = String.fields (fn c => c = #"\n") source_text;

fun strip_leading s =
  Substring.string (Substring.dropl (fn c => c = #" " orelse c = #"\t")
    (Substring.full s));

fun decl_head line name kw =
  let
    val line' = strip_leading line
  in
    if not (String.isPrefix kw line') then NONE
    else
      let
        val rest = strip_leading (String.extract (line', String.size kw, NONE))
      in
        if String.isPrefix name rest andalso
           (String.size rest = String.size name orelse
            let val c = String.sub (rest, String.size name) in
              not (Char.isAlphaNum c) andalso c <> #"_"
            end)
        then SOME rest
        else NONE
      end
  end;

fun statement_of name =
  let
    fun scan [] = raise Fail ("missing declaration " ^ name)
      | scan (l :: rest) =
          (case decl_head l name "Theorem" of
             SOME _ => rest
           | NONE => scan rest)
    val body = scan source_lines
    fun take [] = []
      | take (l :: rest) =
          if String.isPrefix "Proof" (strip_leading l) then []
          else l :: take rest
    val stmt = String.concatWith "\n" (take body)
  in
    if String.size stmt = 0 then raise Fail ("empty statement " ^ name)
    else stmt
  end;

fun capture label name =
  let val tm = Parse.Term [QUOTE (statement_of name)]
  in (print (label ^ "="); print_term tm; print "\n") end;

val _ = print "mc_multiword_local_begin=1\n";
val _ = capture "mc_multiword_mc_full_cmp_eq_typed" "mc_full_cmp_eq";
val _ = print "mc_multiword_local_end=1\n";
