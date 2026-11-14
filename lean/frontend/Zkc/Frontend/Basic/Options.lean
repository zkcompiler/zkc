module

public import Std.Data.HashSet

@[expose] public section

set_option autoImplicit false

/-!
# Options and budgets

What a run is asked to do besides compile: what to trace, what to keep, and how long a
computation whose length depends on the program may go on. A budget counts steps of the
computation it bounds, never time, so the same program stops at the same place on every machine.
Running out of a budget is an incomplete check: it refuses nothing and proves nothing (SP10).
-/

namespace Zkc.Frontend

/-- A computation whose length the program decides, and which a budget bounds. -/
inductive Budget where
  /-- The depth of the chain of instantiations (SP7). -/
  | instantiationDepth
  /-- The default instances formed for one declaration (SP7). -/
  | defaultInstances
  /-- The iterations of one stepped loop, each typed on its own (TY10). -/
  | steppedIterations
  /-- The steps of the evaluation of one static term (TY2). -/
  | staticEvaluation
  deriving Inhabited, BEq, Hashable, Repr

namespace Budget

/-- What a budget bounds, as a message names it. -/
def describe : Budget → String
  | .instantiationDepth => "the depth of the chain of instantiations"
  | .defaultInstances => "the default instances of one declaration"
  | .steppedIterations => "the iterations of one stepped loop"
  | .staticEvaluation => "the steps of the evaluation of one static term"

/-- The rule of the reference that the bounded computation belongs to. -/
def rule : Budget → String
  | .instantiationDepth | .defaultInstances => "SP7"
  | .steppedIterations => "TY10"
  | .staticEvaluation => "TY2"

end Budget

/-- The bounds on the computations whose length the program decides. -/
structure Budgets where
  /-- The depth of the chain of instantiations (SP7). -/
  instantiationDepth : Nat := 256
  /-- The default instances formed for one declaration (SP7). -/
  defaultInstances : Nat := 4096
  /-- The iterations of one stepped loop, each typed on its own (TY10). -/
  steppedIterations : Nat := 1 <<< 20
  /-- The steps of the evaluation of one static term (TY2). -/
  staticEvaluation : Nat := 1 <<< 20
  deriving Inhabited

/-- The value of a budget. -/
def Budgets.limit (budgets : Budgets) : Budget → Nat
  | .instantiationDepth => budgets.instantiationDepth
  | .defaultInstances => budgets.defaultInstances
  | .steppedIterations => budgets.steppedIterations
  | .staticEvaluation => budgets.staticEvaluation

structure Options where
  budgets : Budgets := {}
  /-- The trace classes that are on: the name of a phase, or a class that a phase names
  (`elab.loop`, `emit.facts`). -/
  traces : Std.HashSet String := {}
  /-- Form the default instances of the public declarations that no root reached (SP7). -/
  defaultInstances : Bool := true
  /-- Stop after the first phase that logs an error. A tool that reports everything it can
  turns this off. -/
  stopAtErrors : Bool := false
  deriving Inhabited

namespace Options

def traces? (options : Options) (traceClass : String) : Bool := options.traces.contains traceClass

end Options

end Zkc.Frontend
