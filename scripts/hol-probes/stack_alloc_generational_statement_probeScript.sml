load "preamble"; load "stack_allocProofTheory";
open HolKernel Parse bossLib preamble;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val target = ``
  conf.gc_kind = Generational gen_sizes ==>
   word_gc_fun conf (roots,m,dm,s) =
     if ¬word_gc_fun_assum conf s then NONE else
     if word_gen_gc_can_do_partial gen_sizes s then
       (λ(roots1,i1,pa1,m1,c2).
          if c2 /\ theWord (s ' AllocSize) ≤₊ -1w * pa1 + theWord (s ' EndOfHeap)
                /\ theWord (s ' AllocSize) ≤₊ new_trig
                     (theWord (s ' EndOfHeap) - pa1)
                     (theWord (s ' AllocSize)) gen_sizes then
            SOME
              (TL roots1,m1,
               s |++
               [(CurrHeap,Word (theWord (s ' CurrHeap)));
                (OtherHeap,Word (theWord (s ' OtherHeap)));
                (NextFree,Word pa1);
                (GenStart,Word (pa1 + -1w * theWord (s ' CurrHeap)));
                (TriggerGC,Word (pa1 + new_trig (theWord (s ' EndOfHeap) - pa1)
                                         (theWord (s ' AllocSize)) gen_sizes));
                (Globals,HD roots1);
                (GlobReal,glob_real conf (theWord (s ' CurrHeap)) (HD roots1));
                (Temp 0w,Word 0w); (Temp 1w,Word 0w)])
          else NONE)
         ((λ(roots,i,pa,m,c1).
             (λ(b1,m,c2). (roots,i,b1,m,c1 ∧ c2))
               (memcpy
                  ((pa + -1w * theWord (s ' OtherHeap)) ⋙ shift (:α))
                  (theWord (s ' OtherHeap))
                  (theWord (s ' CurrHeap) + theWord (s ' GenStart)) m
                  dm))
            ((λ(roots,i,pa,m,c1).
                (λ(i,pa,m,c2).
                   (λ(i,pa,m,c3). (roots,i,pa,m,c2 ∧ c3))
                     (word_gen_gc_partial_move_data conf (dimword (:α))
                        (theWord (s ' OtherHeap),i,pa,
                         theWord (s ' CurrHeap),m,dm,
                         theWord (s ' GenStart),
                         -1w * theWord (s ' CurrHeap) +
                         theWord (s ' EndOfHeap))))
                  (word_gen_gc_partial_move_ref_list (dimword (:α)) conf
                     (theWord (s ' EndOfHeap),i,pa,
                      theWord (s ' CurrHeap),m,dm,c1,
                      theWord (s ' GenStart),
                      -1w * theWord (s ' CurrHeap) +
                      theWord (s ' EndOfHeap),
                      theWord (s ' CurrHeap) +
                      theWord (s ' HeapLength))))
               (word_gen_gc_partial_move_roots conf
                  (s ' Globals::roots,
                   theWord (s ' GenStart) ⋙ shift (:α),
                   theWord (s ' OtherHeap),theWord (s ' CurrHeap),m,dm,
                   theWord (s ' GenStart),
                   -1w * theWord (s ' CurrHeap) +
                   theWord (s ' EndOfHeap)))))
     else
      (let new_end = theWord (s ' OtherHeap) + theWord (s ' HeapLength) in
       let len = theWord (s ' HeapLength) ⋙ shift (:α) in
       let (w1,i1,pa1,ib',pb',m1,c1) =
              word_gen_gc_move conf
                (s ' Globals,0w,theWord (s ' OtherHeap),
                 len,new_end,theWord (s ' CurrHeap),m,dm) in
       let (ws2,i2,pa2,ib2,pb2:'a word,m2,c2) =
              word_gen_gc_move_roots conf
                (roots,i1,pa1,ib',pb',
                 theWord (s ' CurrHeap),m1,dm) in
       let (i3,pa3,ib3,pb3,m3,c3) =
             word_gen_gc_move_loop conf (w2n len)
               (theWord (s ' OtherHeap),i2,pa2,ib2,pb2,new_end,
                theWord (s ' CurrHeap),m2,dm) in
       let a = theWord (s ' AllocSize) in
       let s1 =
             s |++
             [(CurrHeap,Word (theWord (s ' OtherHeap)));
              (OtherHeap,Word (theWord (s ' CurrHeap)));
              (NextFree,Word pa3);
              (GenStart,Word (pa3 − theWord (s ' OtherHeap)));
              (TriggerGC,Word (pa3 + new_trig (pb3 - pa3) a gen_sizes));
              (EndOfHeap,Word pb3); (Globals,w1);
              (GlobReal,glob_real conf (theWord (s ' OtherHeap)) w1);
              (Temp 0w,Word 0w);
              (Temp 1w,Word 0w);
              (Temp 2w,Word 0w);
              (Temp 3w,Word 0w);
              (Temp 4w,Word 0w);
              (Temp 5w,Word 0w);
              (Temp 6w,Word 0w)]
       in
         if word_gc_fun_assum conf s /\ c1 /\ c2 /\ c3
         then SOME (ws2,m3,s1)
         else NONE)``;
val _ = print ("gen_word_gc_fun_thm_typed_statement=" ^ term_to_string target ^ "\n");
val _ = print ("gen_word_gc_fun_thm_free_vars=" ^ String.concatWith "," (map (fn v => #1 (dest_var v) ^ ":" ^ type_to_string (type_of v)) (free_vars target)) ^ "\n");
val target = ``
  s.gc_fun = word_gc_fun conf /\ conf.gc_kind = Generational gen_sizes ==>
   gc (s:('a,'c,'b)stackSem$state) =
   if LENGTH s.stack < s.stack_space then NONE else
     if ¬word_gc_fun_assum conf s.store then NONE else
     if word_gen_gc_can_do_partial gen_sizes s.store then
      (let unused = TAKE s.stack_space s.stack in
       let stack = DROP s.stack_space s.stack in
       let gs = theWord (s.store ' GenStart) in
       let other = theWord (s.store ' OtherHeap) in
       let curr = theWord (s.store ' CurrHeap) in
       let endh = theWord (s.store ' EndOfHeap) in
       let (w1,i1,pa1,m1,c1) = word_gen_gc_partial_move conf
              (s.store ' Globals,gs ⋙ shift (:α), other,curr,
               s.memory,s.mdomain,gs, endh - curr) in
       let (ws2,i1,pa1,m1,c2) = word_gen_gc_partial_move_roots_bitmaps conf
              (stack,s.bitmaps,i1,pa1,curr,m1,s.mdomain,gs,endh - curr) in
       let (i1,pa1,m1,c3) =
              word_gen_gc_partial_move_ref_list (dimword (:α)) conf
               (endh,i1,pa1,curr,m1,s.mdomain,c1 ∧ c2,gs,
                endh - curr, curr +theWord (s.store ' HeapLength)) in
       let (i1,pa1,m1,c4) = word_gen_gc_partial_move_data conf (dimword (:α))
               (other,i1,pa1,curr,m1,s.mdomain,gs, endh - curr) in
       let (b1,m1,c5) = memcpy ((pa1 - other) ⋙ shift (:α)) other (curr + gs) m1
                         s.mdomain in
       let s1 = s.store |++
                [(CurrHeap,Word curr);
                 (OtherHeap,Word other);
                 (NextFree,Word b1);
                 (GenStart,Word (b1 - curr));
                 (TriggerGC,Word (b1 + new_trig
                    (theWord (s.store ' EndOfHeap) - b1)
                    (theWord (s.store ' AllocSize)) gen_sizes));
                 (Globals,w1);
                 (GlobReal,glob_real conf (theWord (s.store ' CurrHeap)) w1);
                 (Temp 0w,Word 0w);
                 (Temp 1w,Word 0w)] in
       let c6 = ((theWord (s.store ' AllocSize) ≤₊
                  theWord (s.store ' EndOfHeap) - b1) /\
                 (theWord (s.store ' AllocSize) ≤₊ new_trig
                    (theWord (s.store ' EndOfHeap) - b1)
                    (theWord (s.store ' AllocSize)) gen_sizes)) in
         if word_gc_fun_assum conf s.store /\ c3 /\ c4 /\ c5 /\ c6
         then SOME (s with
              <| stack := unused ++ ws2; store := s1;
                 regs := FEMPTY; memory := m1|>) else NONE)
     else
      (let unused = TAKE s.stack_space s.stack in
       let stack = DROP s.stack_space s.stack in
       let new_end = theWord (s.store ' OtherHeap) + theWord (s.store ' HeapLength) in
       let len = theWord (s.store ' HeapLength) ⋙ shift (:α) in
       let (w1,i1,pa1,ib',pb',m1,c1) =
                word_gen_gc_move conf
                  (s.store ' Globals,0w,theWord (s.store ' OtherHeap),
                   len,new_end,theWord (s.store ' CurrHeap),s.memory,s.mdomain) in
       let (ws2,i2,pa2,ib2,pb2:'a word,m2,c2) =
                word_gen_gc_move_roots_bitmaps conf
                  (stack,s.bitmaps,i1,pa1,ib',pb',
                   theWord (s.store ' CurrHeap),m1,s.mdomain) in
       let (i3,pa3,ib3,pb3,m3,c3) =
               word_gen_gc_move_loop conf (w2n len)
                 (theWord (s.store ' OtherHeap),i2,pa2,ib2,pb2,new_end,
                  theWord (s.store ' CurrHeap),m2,s.mdomain) in
       let s1 =
               s.store |++
               [(CurrHeap,Word (theWord (s.store ' OtherHeap)));
                (OtherHeap,Word (theWord (s.store ' CurrHeap)));
                (NextFree,Word pa3);
                (GenStart,Word (pa3 + -1w * theWord (s.store ' OtherHeap)));
                (TriggerGC,Word (pa3 + new_trig
                   (pb3 - pa3) (theWord (s.store ' AllocSize)) gen_sizes));
                (EndOfHeap,Word pb3);
                (Globals,w1);
                (GlobReal,glob_real conf (theWord (s.store ' OtherHeap)) w1);
                (Temp 0w, Word 0w);
                (Temp 1w, Word 0w);
                (Temp 2w, Word 0w);
                (Temp 3w, Word 0w);
                (Temp 4w, Word 0w);
                (Temp 5w, Word 0w);
                (Temp 6w, Word 0w)]
       in
         if word_gc_fun_assum conf s.store /\ c1 /\ c2 /\ c3 then SOME (s with
              <| stack := unused ++ ws2; store := s1;
                 regs := FEMPTY; memory := m3|>) else NONE)``;
val _ = print ("gen_gc_thm_typed_statement=" ^ term_to_string target ^ "\n");
val _ = print ("gen_gc_thm_free_vars=" ^ String.concatWith "," (map (fn v => #1 (dest_var v) ^ ":" ^ type_to_string (type_of v)) (free_vars target)) ^ "\n");
