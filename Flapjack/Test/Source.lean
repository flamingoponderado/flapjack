module

public import Flapjack.Test.Basics
public import Flapjack.Test.SourceSemantics
public import Flapjack.Test.SourceDeclarations
public import Flapjack.Test.Compile

import all Flapjack.Test.Basics
import all Flapjack.Test.SourceSemantics
import all Flapjack.Test.SourceDeclarations
import all Flapjack.Test.Compile

@[expose] public section

/-!
# Source-language regression tests

The front-end and source-semantics tests are kept behind one small aggregate
module so the complete suite does not need a long flat import list.
-/
