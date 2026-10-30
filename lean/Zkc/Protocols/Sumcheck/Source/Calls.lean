module

public import Zkc.Protocols.Sumcheck.Source.Reduce
public import Zkc.Source.DeriveRegion
public import Zkc.Source.Structured.ClosedProjection

@[expose] public section

/-! Shared library instantiation for generated source root continuations.
The complete optional ABI, actual output mask and occurrence context are kept.
This does not select a root, a compiled artifact, or a security certificate. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.OriginalSumcheckCalls
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured ZkcExamples.Structured.OriginalSumcheckLibrary
open SumcheckVerifierBodies
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev realizeCall (payload : UnitPayload) (maximum : Nat) (context : ProtocolContext)
    (outputs : List (List Nat))
    (inputs : Values (Component (assignment F G)) reduceInputs) :=
  (OriginalSumcheckLibrary.reduce payload maximum context (context.roles 1) [] inputs).bind
    (fun result => .done (maskValues (context.roles 1) (context.mapScopes outputs) result))

theorem singleton_eta {Value : Ty → Type} {ty : Ty} (out : Values Value [ty]) :
    Values.cons (out.get .here) .nil = out := by
  cases out with | cons value out => cases out; rfl

theorem bind_mask_single_role {Value : Ty → Type} {types : List Ty} {I : PIR.Signature}
    (process : PIR.Process I (Values (Component Value) types)) (self : Nat) :
    process.bind (fun out => .done (maskValues self (List.replicate types.length [self]) out)) = process := by
  calc
    _ = process.bind PIR.Process.done := congrArg (PIR.Process.bind process)
      (funext fun out => congrArg PIR.Process.done (maskValues_single_role self out))
    _ = process := PIR.Process.bind_done _

end ZkcExamples.Structured.OriginalSumcheckCalls
