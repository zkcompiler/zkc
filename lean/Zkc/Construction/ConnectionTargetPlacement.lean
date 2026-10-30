module

public import Zkc.Construction.ConnectionCertificate

@[expose] public section

/-! Reusable target bodies, checked with placement parameters from the outset.

A family of `CheckedBody` values is proved once by the ordinary typed
alignment rules. Its parameters can describe caller scopes, typed arguments,
readbacks, physical offsets, occurrence contexts and enclosing frames. A use
references that family constant; it does not construct another body derivation.
The indices fix the exact source entry, earlier library, role, return projection
and target prefix. No semantic equation or simulation is an input to placement.

There is deliberately no universal renaming claim. A family must prove the
alignment and extent for every placement it admits. In particular, logical
read-only aliases need not be injective, while writes must retain the caller
prefix as required by `Alignment` and its simulation theorem. Application
admission, continuation sufficiency and current-history separation remain the
existing application constructor's checks.
-/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionTargetPlacement
open Zkc.Source Zkc.Source.Structured NormalForm ConnectionFrame ConnectionLibrary

/-- Static parameters of one body occurrence. Static occurrence contexts and
symbolic dynamic frames occupy different fields; neither substitutes for the
other. The prefix is the actual target instruction/checkpoint schedule. -/
structure Placement (key : CalleeKey) where
  context : ProtocolContext
  scope : Scope
  arguments : Values (Argument [] scope) key.pattern.scope
  frames : ScopedFrames scope
  layout : Layout scope
  outputs : List Original.Location
  history : Option Nat
  returns : ConnectionReturnProjection.Selection key.signature.outputs
  spine : ConnectionTargetPrefix.Prefix
  extent : Nat

/-- A checked body is indexed by an exact source entry, not just a compatible
signature. Define a reusable family with ordinary Lean parameters, returning
this type. Its two proofs are checked once in the family declaration. -/
structure CheckedBody {payload : UnitPayload} {key : CalleeKey}
    (entry : Entry payload key) (routing : Original.Routing)
    (selection : Selection payload.definitions entry.earlierKeys)
    (placement : Placement key) where
  alignment : ConnectionCertificate.Alignment routing placement.context payload.definitions
    entry.earlierKeys (selection := selection) key.signature.outputs key.role key.signature.outputScopes
    placement.outputs placement.history placement.frames placement.layout
    (ConnectionReturnProjection.form placement.returns
      (ConnectionSubstitution.form entry.form (fun binder => entryAt placement.arguments binder)))
    placement.spine.block
  physicalExtent : ConnectionTargetExtent.Extent placement.layout.length placement.extent placement.spine.block

/-- Exact association with an actual occurrence, checked independently of the
body proof. Equality may be reflexive or a separately proved syntactic
association; it cannot authorize changed operations or nominal domains. -/
def CheckedBody.place {payload : UnitPayload} {key : CalleeKey}
    {entry : Entry payload key} {routing : Original.Routing}
    {selection : Selection payload.definitions entry.earlierKeys}
    {pattern actual : Placement key}
    (body : CheckedBody entry routing selection pattern) (association : pattern = actual) :
    CheckedBody entry routing selection actual :=
  association ▸ body

theorem calculationCells_length {scope : Scope} {types : List Ty}
    (values : Values (Comp [] scope) types) :
    (ConnectionComputation.cells values).length = types.length := by
  induction values with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- A total auxiliary calculation extends storage with the normalizer's own
terms. It does not change source binders, occurrence paths or dynamic frames. -/
def Placement.afterCalculation {key : CalleeKey} (placement : Placement key)
    (operation : Calculation) (total : operation.op.total = true)
    (terms : Terms [] placement.scope operation.op.arguments) : Placement key :=
  { placement with layout := placement.layout ++
      ConnectionComputation.cells (NormalForm.calculation operation.op total terms) }

def Placement.prependCalculation {key : CalleeKey} (placement : Placement key)
    (operation : Calculation) (references : List Nat) : Placement key :=
  { placement with spine := .step (fun model => Domain.View.calculation model operation references
      (operation.op.results.map ValueSort.data)) placement.spine }

/-- Compose the existing calculation rule with a checked body. All input
readbacks, nominal sorts, writes and checkpoints are checked by that rule;
an auxiliary target instruction is never legalized by a metadata label. -/
def CheckedBody.prependCalculation {payload : UnitPayload} {key : CalleeKey}
    {entry : Entry payload key} {routing : Original.Routing}
    {selection : Selection payload.definitions entry.earlierKeys}
    (placement : Placement key) (operation : Calculation) (total : operation.op.total = true)
    (terms : Terms [] placement.scope operation.op.arguments) (references : List Nat)
    (inputsData : operation.op.arguments.all Domain.dataType = true)
    (outputsData : operation.op.results.all Domain.dataType = true)
    (readback : Readback placement.layout (ConnectionComputation.components terms)
      (references.map Original.Location.data))
    (body : CheckedBody entry routing selection (placement.afterCalculation operation total terms)) :
    CheckedBody entry routing selection (placement.prependCalculation operation references) where
  alignment := .calculation operation total terms references inputsData outputsData readback body.alignment
  physicalExtent := .sequence
    (.calculation placement.layout.length operation references (operation.op.results.map ValueSort.data))
    (by
      have size : (placement.afterCalculation operation total terms).layout.length =
          placement.layout.length + operation.op.results.length := by
        change (placement.layout ++ ConnectionComputation.cells
          (NormalForm.calculation operation.op total terms)).length = _
        rw [List.length_append, calculationCells_length]
      have extent := body.physicalExtent
      rw [size] at extent
      simpa only [Placement.afterCalculation, Placement.prependCalculation,
        ConnectionTargetPrefix.Prefix.block, List.length_map] using extent)

end Zkc.Construction.ConnectionTargetPlacement
