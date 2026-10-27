load "semanticPrimitivesTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "id_type="; print_type (type_of ``semanticPrimitives$v_to_id``); print "\n");
val _ = (print "chars_type="; print_type (type_of ``semanticPrimitives$v_to_char_list``); print "\n");
val _ = (print "word64_type="; print_type (type_of ``semanticPrimitives$v_to_word64_list``); print "\n");
val list_roundtrip = rhs (concl (EVAL ``semanticPrimitives$v_to_list
  (semanticPrimitives$list_to_v [Litv (IntLit 1); Litv (IntLit 2)])``));
val _ = (print "list_roundtrip="; print_term list_roundtrip; print "\n");
val malformed = rhs (concl (EVAL ``semanticPrimitives$v_to_list
  (Conv (SOME (TypeStamp «wrong» 1)) [])``));
val _ = (print "malformed="; print_term malformed; print "\n");
val chars = rhs (concl (EVAL ``semanticPrimitives$v_to_char_list
  (semanticPrimitives$list_to_v [Litv (Char #"a"); Litv (Char #"b")])``));
val _ = (print "chars="; print_term chars; print "\n");
val strings = rhs (concl (EVAL ``semanticPrimitives$vs_to_string [Litv (StrLit «a»); Litv (StrLit «b»)]``));
val _ = (print "strings="; print_term strings; print "\n");
val identifier = rhs (concl (EVAL ``semanticPrimitives$v_to_id
  (Conv (SOME (TypeStamp «Long» 4)) [Litv (StrLit «M»);
    Conv (SOME (TypeStamp «Short» 4)) [Litv (StrLit «x»)]])``));
val _ = (print "identifier="; print_term identifier; print "\n");
val word8 = rhs (concl (EVAL ``semanticPrimitives$v_to_word8_list
  (semanticPrimitives$list_to_v [Litv (Word8 (3w:word8)); Litv (Word8 (7w:word8))])``));
val _ = (print "word8="; print_term word8; print "\n");
val bad_word8 = rhs (concl (EVAL ``semanticPrimitives$v_to_word8_list
  (semanticPrimitives$list_to_v [Litv (Word8 (3w:word8)); Litv (IntLit 7)])``));
val _ = (print "bad_word8="; print_term bad_word8; print "\n");
