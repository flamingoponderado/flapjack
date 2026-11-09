module

public import Flapjack.Compiler.Backend.WordDepth

@[expose] public section

/-! The arithmetic runtime's computed call tree. -/
namespace Flapjack.Compiler.Backend.DataToWord

/-- The original `AnyArith_call_tree` computed from the unoptimized runtime
stubs. Its full typed original was captured by `data_sem_stack_probe`; the
numeric labels and branch order are retained. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "AnyArith_call_tree_def"]
def anyArithCallTree : WordDepth.CallTree :=
  (.branch (.call 12 .leaf)
    (.branch (.call 12 .leaf)
      (.branch (.branch (.call 12 (.call 11 .leaf))
          (.call 12 .leaf))
        (.branch (.call 12 (.call 39 .leaf))
          (.call 12 (.branch (.branch (.branch (.branch (.call 39 (.call 40 .leaf))
                    (.call 39 .leaf))
                  (.branch (.call 39 (.call 41 .leaf))
                    (.call 39 .leaf)))
                (.branch (.branch (.call 39 (.call 42 .leaf))
                    (.call 39 .leaf))
                  (.branch (.branch (.branch (.call 39 (.call 43 .leaf))
                        (.call 39 .leaf))
                      (.branch (.call 39 (.call 44 .leaf))
                        (.call 39 .leaf)))
                    (.branch (.call 39 (.call 45 .leaf))
                      (.call 39 .leaf)))))
              (.branch (.branch (.branch (.call 39 (.call 46 .leaf))
                    (.call 39 .leaf))
                  (.branch (.branch (.call 39 (.call 47 .leaf))
                      (.call 39 (.branch (.call 47 (.call 48 .leaf))
                          (.call 47 .leaf))))
                    (.branch (.call 39 (.call 45 .leaf))
                      (.call 39 .leaf))))
                (.branch (.branch (.branch (.branch (.call 39 (.call 46 .leaf))
                        (.call 39 .leaf))
                      (.branch (.call 39 (.call 49 .leaf))
                        (.call 39 .leaf)))
                    (.branch (.branch (.call 39 (.call 50 .leaf))
                        (.call 39 (.branch (.call 50 (.call 23 .leaf))
                            (.call 50 (.call 22 .leaf)))))
                      (.branch (.branch (.call 39 (.call 51 .leaf))
                          (.call 39 .leaf))
                        (.branch (.branch (.call 39 (.call 52 .leaf))
                            (.call 39 .leaf))
                          (.branch (.branch (.call 39 (.call 53 .leaf))
                              (.call 39 .leaf))
                            (.branch (.branch (.call 39 (.call 54 .leaf))
                                (.call 39 (.branch (.branch (.branch (.call 54 (.call 23 .leaf))
                                        (.call 54 (.call 22 .leaf)))
                                      (.branch (.call 54 (.call 55 .leaf))
                                        (.call 54 .leaf)))
                                    (.branch (.branch (.call 54 (.call 56 .leaf))
                                        (.call 54 .leaf))
                                      (.branch (.call 54 (.call 57 .leaf))
                                        (.call 54 .leaf))))))
                              (.branch (.branch (.call 39 (.call 58 .leaf))
                                  (.call 39 (.branch (.call 58 (.call 23 .leaf))
                                      (.call 58 (.call 22 .leaf)))))
                                (.branch (.branch (.call 39 (.call 45 .leaf))
                                    (.call 39 .leaf))
                                  (.branch (.call 39 (.call 59 .leaf))
                                    (.call 39 .leaf))))))))))
                  (.branch (.branch (.branch (.call 39 (.call 45 .leaf))
                        (.call 39 .leaf))
                      (.branch (.call 39 (.call 60 .leaf))
                        (.call 39 .leaf)))
                    (.branch (.branch (.call 39 (.call 61 .leaf))
                        (.call 39 .leaf))
                      (.branch (.call 39 (.call 45 .leaf))
                        (.call 39 .leaf))))))))))))

end Flapjack.Compiler.Backend.DataToWord
