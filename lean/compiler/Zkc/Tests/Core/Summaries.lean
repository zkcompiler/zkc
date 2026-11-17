import Zkc.Core.Admission.Elaboration
import Zkc.Core.Transform.Assured
import Zkc.Core.Transform.Passes
import Zkc.Tests.Core.Facts
import Zkc.Tests.Core.Following
import Zkc.Tests.Core.Transform

/-!
Summaries of functions, on functions written by names over the vocabulary with a field of
`Tests/Core/Facts.lean`, each with its whole verdict, run by the kernel.

A function that divides by its second input, with the summary that requires that input to be at
least one, is admitted; with the empty summary it is refused at the division. A caller that guards
that its divisor is at least one and calls it is admitted; a caller that calls it on an input of
which nothing is known is refused at the call, with the callee's requirement. A callee whose
summary guarantees that its result is at most its input, the input less one after a guard, and a
caller that subtracts the result from the input: admitted, the guarantee learned where the call
returns; with the guarantee removed from the callee's summary, the caller is refused at the
subtraction; and the callee itself is refused at its exit under a guarantee that its body does not
establish. The dividing function satisfies its summary in every model, from the theorems
(`TypedFn.check_assured`, `checkFacts_holds`); the control, in the field of two elements of
`Tests/Core/Transform.lean`: on a divisor of zero, which the summary excludes, its process is the
stop `undefined`. A step from the dividing function admitted with an unused product to the same
function without it is accepted, and the two mean the same (`AssuredFn.step_same`). Elaboration
refuses a summary that names an application of a written operation, and one that names a position
out of range, by the rule `summary` at the definition; and a stored function with a summary goes
round trip in both directions.
-/

namespace Zkc.Core.SummariesTests

open FactsTests (field plus minus times quotient less negation natural verdict accepted anyNat)
open FollowingTests (noCallees noCallees_callees)
open TransformTests (twoModel refusal outcome accepted? ok_of_accepted)

/-- The place of an instruction of the definition with a key. -/
def at_ (definition instruction : Nat) : Place := ⟨⟨definition⟩, [], some ⟨instruction⟩, none⟩

/-- The place of a definition as a whole: its exit, and where elaboration refuses its header. -/
def whole (definition : Nat) : Place := ⟨⟨definition⟩, [], none, none⟩

/-- An application of a written operation refused at an instruction of a definition, with the
requirement that is not known and what is known of the values that it names. -/
def unjustifiedAt (definition instruction : Nat) (written : LocalRaw field)
    (requirement : Requirement (LocalRaw field)) (known : List (Option Range)) :
    ProgramRefusal field :=
  ⟨.domain, at_ definition instruction, .unjustified written requirement known⟩

/-! ## A function that divides by its second input -/

/-- The summary that requires the second input to be at least one. -/
def divisorAtLeastOne : Summary (LocalRaw field) := ⟨[.atLeast (.arg 1) 1], []⟩

/-- The quotient of the first input by the second, with the key 1. -/
def divideHeader : FnHeader field := ⟨⟨1⟩, [.nat, .nat], [.nat], false, none, divisorAtLeastOne⟩

/-- The same function with the empty summary. -/
def divideUnsummarized : FnHeader field :=
  ⟨⟨1⟩, [.nat, .nat], [.nat], false, none, Summary.empty⟩

/-- `x / y`. -/
def divideBody : Region (LocalRaw field) Unit := .mk [0, 1] [.op ⟨1⟩ [10] quotient [0, 1]] [10]

/-- Under its summary, the division is known to be inside its domain: admitted. -/
example : verdict [] divideHeader divideBody = accepted := by decide +kernel

/-- With the empty summary, nothing is known of the divisor but that it is a natural: refused at
the division, with its requirement and what was known of the divisor. -/
example : verdict [] divideUnsummarized divideBody =
    some (.inl [unjustifiedAt 1 1 quotient (.atLeast (.arg 1) 1) [anyNat]]) := by
  decide +kernel

/-! ## Callers of the dividing function -/

/-- A caller with the key 2, which can stop: it guards that its divisor is at least one. -/
def guardedCallerHeader : FnHeader field :=
  ⟨⟨2⟩, [.nat, .nat], [.nat], true, none, Summary.empty⟩

/-- `guard !(y < 1); divide(x, y)`. -/
def guardedCaller : Region (LocalRaw field) Unit := .mk [0, 1] [
  .op ⟨1⟩ [10] (natural 1) [],
  .op ⟨2⟩ [11] less [1, 10],
  .op ⟨3⟩ [12] negation [11],
  .guard ⟨4⟩ () 12 .refused,
  .op ⟨5⟩ [13] (.call ⟨1⟩) [0, 1]] [13]

/-- The guard teaches that the divisor is at least one, which is what the callee requires:
admitted. -/
example : verdict [divideHeader] guardedCallerHeader guardedCaller = accepted := by
  decide +kernel

/-- A caller with the key 2 that calls the dividing function on its inputs as they are. -/
def plainCallerHeader : FnHeader field := ⟨⟨2⟩, [.nat, .nat], [.nat], false, none, Summary.empty⟩

/-- `divide(x, y)`. -/
def plainCaller : Region (LocalRaw field) Unit :=
  .mk [0, 1] [.op ⟨1⟩ [10] (.call ⟨1⟩) [0, 1]] [10]

/-- Nothing is known of the divisor: refused at the call, with the callee's requirement and what
was known of the value that it names. -/
example : verdict [divideHeader] plainCallerHeader plainCaller =
    some (.inl [unjustifiedAt 2 1 (.call ⟨1⟩) (.atLeast (.arg 1) 1) [anyNat]]) := by
  decide +kernel

/-- The same call of the function with the empty summary asks nothing: admitted. -/
example : verdict [divideUnsummarized] plainCallerHeader plainCaller = accepted := by
  decide +kernel

/-! ## What a callee guarantees -/

/-- The summary that guarantees that the result is at most the input. -/
def resultAtMostInput : Summary (LocalRaw field) := ⟨[], [.le (.arg 1) (.arg 0)]⟩

/-- The summary that guarantees that the input is at most the result. -/
def inputAtMostResult : Summary (LocalRaw field) := ⟨[], [.le (.arg 0) (.arg 1)]⟩

/-- The decrement with the key 1, which can stop, under a summary. -/
def decrementHeader (summary : Summary (LocalRaw field)) : FnHeader field :=
  ⟨⟨1⟩, [.nat], [.nat], true, none, summary⟩

/-- `guard !(x < 1); x - 1`. -/
def decrement : Region (LocalRaw field) Unit := .mk [0] [
  .op ⟨1⟩ [10] (natural 1) [],
  .op ⟨2⟩ [11] less [0, 10],
  .op ⟨3⟩ [12] negation [11],
  .guard ⟨4⟩ () 12 .refused,
  .op ⟨5⟩ [13] minus [0, 10]] [13]

/-- The decrement establishes that its result, its input less one, is at most its input:
admitted under that guarantee. -/
example : verdict [] (decrementHeader resultAtMostInput) decrement = accepted := by
  decide +kernel

/-- It does not establish that its input is at most its result: refused at its exit by the rule
`guarantee`, with what was known of the input and of the result. -/
example : verdict [] (decrementHeader inputAtMostResult) decrement =
    some (.inl [⟨.guarantee, whole 1, .unestablished (.le (.arg 0) (.arg 1))
      [some ⟨1, none⟩, some ⟨0, none⟩]⟩]) := by
  decide +kernel

/-- A caller with the key 2, which can stop since its callee can. -/
def subtractingHeader : FnHeader field := ⟨⟨2⟩, [.nat], [.nat], true, none, Summary.empty⟩

/-- `r := decrement(x); x - r`. -/
def subtracting : Region (LocalRaw field) Unit := .mk [0] [
  .op ⟨1⟩ [10] (.call ⟨1⟩) [0],
  .op ⟨2⟩ [11] minus [0, 10]] [11]

/-- What the callee guarantees, that its result is at most its input, is learned where the call
returns, and the subtraction's requirement follows from it: admitted. -/
example : verdict [decrementHeader resultAtMostInput] subtractingHeader subtracting = accepted := by
  decide +kernel

/-- With the guarantee removed from the callee's summary, nothing relates the result to the input:
refused at the subtraction, with what was known of its two operands, in the order in which the
requirement names them. -/
example : verdict [decrementHeader Summary.empty] subtractingHeader subtracting =
    some (.inl [unjustifiedAt 2 2 minus (.le (.arg 1) (.arg 0)) [anyNat, anyNat]]) := by
  decide +kernel

/-! ## The dividing function satisfies its summary -/

/-- The dividing function, admitted: elaborated, and accepted by the check of facts under its
summary. -/
def divideFn : AssuredFn field [] divideHeader :=
  (accepted? (admitFn [] divideHeader divideBody)).get (by decide +kernel)

/-- In every model, the dividing function satisfies its summary (`Summary.Holds`): on valid inputs
of which the divisor is at least one, it never stops `undefined` and returns a valid value. It is
what admission carries (`TypedFn.check_assured`). -/
theorem divide_holds (M : Model field) :
    Summary.Holds (localSem M [] (noCallees M)) (fun _ _ => True) (localReading M)
      (LocalReturns M (noCallees M)) (ValidDyn M) (· = .undefined) divisorAtLeastOne
      (divideFn.fn.meaning M (noCallees M)) :=
  divideFn.assured.safe M (noCallees M) (noCallees_callees M)

/-- The same, from the theorem of the check of facts for a function under a summary
(`checkFacts_holds`, from `Analysis.analyse_holds`). -/
example (M : Model field) :
    Summary.Holds (localSem M [] (noCallees M)) (fun _ _ => True) (localReading M)
      (LocalReturns M (noCallees M)) (ValidDyn M) (· = .undefined) divisorAtLeastOne
      (divideFn.fn.meaning M (noCallees M)) :=
  checkFacts_holds (noCallees_callees M) ⟨1⟩ divisorAtLeastOne divideFn.fn.conditions.summary
    divideFn.fn.inputs divideFn.fn.body divideFn.fn.conditions.distinct (bounds := [])
    (by decide +kernel)

/-- The control: in the field of two elements, on the divisor zero, the dividing function's process
is the stop `undefined`... -/
example :
    divideFn.fn.meaning twoModel (noCallees twoModel) (.cons (5 : Nat) (.cons (0 : Nat) .nil)) =
      .halt .undefined := by
  rfl

/-- ...and the divisor zero is what the summary's requirement excludes. -/
example : ¬ FnHeader.Required twoModel (noCallees twoModel) divideHeader
    (.cons (5 : Nat) (.cons (0 : Nat) .nil)) := by
  intro required
  obtain ⟨vs, denoted, relation⟩ := required (.atLeast (.arg 1) 1) List.mem_cons_self
  obtain ⟨v, rfl, at1⟩ := DenotesAll.one denoted
  cases at1
  obtain ⟨x, read, positive⟩ := relation
  cases read
  exact absurd positive (by decide)

/-- On the divisor one, which the summary allows, it returns the quotient. -/
example :
    divideFn.fn.meaning twoModel (noCallees twoModel) (.cons (5 : Nat) (.cons (1 : Nat) .nil)) =
      .done (.cons (5 : Nat) .nil) := by
  rfl

/-! ## A step from the dividing function -/

/-- `x * x`, which nothing uses, then `x / y`. -/
def divideWithUnused : Region (LocalRaw field) Unit := .mk [0, 1] [
  .op ⟨1⟩ [10] times [0, 0],
  .op ⟨2⟩ [11] quotient [0, 1]] [11]

/-- What `removeUnused` gives: the product dropped. -/
def divideWithoutUnused : Region (LocalRaw field) Unit :=
  .mk [0, 1] [.op ⟨2⟩ [11] quotient [0, 1]] [11]

example : removeUnused [] divideWithUnused = divideWithoutUnused := by decide +kernel

/-- The dividing function with the unused product, admitted under its summary. -/
def divideWithUnusedFn : AssuredFn field [] divideHeader :=
  (accepted? (admitFn [] divideHeader divideWithUnused)).get (by decide +kernel)

/-- The step to the function without the product: accepted, with no loop. -/
example : outcome (admitFn [] divideHeader divideWithUnused) = .ok [] ∧
    outcome (divideWithUnusedFn.step divideWithoutUnused) = .ok [] := by
  decide +kernel

/-- What the step returned. -/
def divideStep : AssuredFn field [] divideHeader :=
  (accepted? (divideWithUnusedFn.step divideWithoutUnused)).get (by decide +kernel)

theorem divideStep_accepted : divideWithUnusedFn.step divideWithoutUnused = .ok divideStep :=
  ok_of_accepted (by decide +kernel)

/-- The two mean the same on every valid input that satisfies the summary's requirement, against
every callees (`AssuredFn.step_same`). -/
example : divideWithUnusedFn.fn.SameAs divideStep.fn := AssuredFn.step_same divideStep_accepted

/-! ## Summaries that elaboration refuses -/

/-- The first refusal of elaboration of a program; nothing when it elaborates. -/
def elaborationRefusal (named : NamedProgram field) : Option (ProgramRefusal field) :=
  match elaborateFunctions named with
  | .ok _ => none
  | .error refusals => refusals.head?

/-- The dividing function, by names, under a summary. -/
def divideNamed (summary : Summary (LocalRaw field)) : NamedProgram field :=
  ⟨[.fn ⟨1⟩ [.nat, .nat] [.nat] false none summary divideBody]⟩

/-- A requirement on the sum of the two inputs, an application of a written operation: refused by
the rule `summary` at the definition, with the requirement. -/
example : elaborationRefusal (divideNamed ⟨[.atLeast (.apply plus [0, 1]) 1], []⟩) =
    some ⟨.summary, whole 1, .requirement (.atLeast (.apply plus [0, 1]) 1)⟩ := by
  decide +kernel

/-- A requirement on the position 2, which is the result's, not an input's: refused by the rule
`summary`. -/
example : elaborationRefusal (divideNamed ⟨[.atLeast (.arg 2) 1], []⟩) =
    some ⟨.summary, whole 1, .requirement (.atLeast (.arg 2) 1)⟩ := by
  decide +kernel

/-- A guarantee on the position 3, beyond the two inputs and the result: refused by the rule
`summary`. -/
example : elaborationRefusal (divideNamed ⟨[], [.le (.arg 3) (.arg 0)]⟩) =
    some ⟨.summary, whole 1, .requirement (.le (.arg 3) (.arg 0))⟩ := by
  decide +kernel

/-- The position 2 in a guarantee is the result: elaborated. -/
example : elaborationRefusal (divideNamed ⟨[.atLeast (.arg 1) 1], [.le (.arg 2) (.arg 0)]⟩) =
    none := by
  decide +kernel

/-! ## The round trip of a stored function with a summary -/

/-- The dividing function with its summary, and a guarded caller of it. -/
def dividing : NamedProgram field :=
  ⟨[.fn ⟨1⟩ [.nat, .nat] [.nat] false none divisorAtLeastOne divideBody,
    .fn ⟨2⟩ [.nat, .nat] [.nat] true none Summary.empty guardedCaller]⟩

/-- Erased then elaborated: the erased form of what it elaborates to elaborates to the same typed
program. -/
example : (elaborateFunctions dividing).bind (fun p => elaborateFunctions (erase p)) =
    elaborateFunctions dividing := by
  rfl

/-- Elaborated then erased: it is the erased form of what it elaborates to, its summary
included. -/
example : (elaborateFunctions dividing).map erase = .ok dividing := by rfl

/-- The summary is in the header that elaboration gives. -/
example : (elaborateFunctions dividing).map (fun p => p.headers.fns.map (·.summary)) =
    .ok [Summary.empty, divisorAtLeastOne] := by
  decide +kernel

end Zkc.Core.SummariesTests
