module

public import Zkc.Source.Structured.ContractInstantiation
public import ZkcExamples.Structured.SumcheckContractBindings

@[expose] public section

/-! Fixed logical table instantiation at the actual maintained Sumcheck call.
The source runtime operand is P's constructed table. The mathematical parameter
is explicitly inherited from the caller's fixed public table instead. -/
namespace ZkcExamples.Structured.SumcheckContractInstantiation
open Zkc.Source Zkc.Source.Structured SumcheckRelationContract SumcheckContractBindings

set_option smartUnfolding false

def childOwner : ContractBinding SumcheckSourceViews.imported where
  ownerIndex := ⟨1, by decide⟩
  protocolIndex := ⟨0, by decide⟩
  owner_eq := rfl

def childTable : BoundarySelector childOwner.protocol.signature vector :=
  ⟨.input .here, ⟨0, by decide⟩, by decide⟩
def childDimension : BoundarySelector childOwner.protocol.signature .index :=
  ⟨.input (.there .here), ⟨0, by decide⟩, by decide⟩
def childWidth : BoundarySelector childOwner.protocol.signature .index :=
  ⟨.input (.there (.there .here)), ⟨0, by decide⟩, by decide⟩
def childClaim : BoundarySelector childOwner.protocol.signature scalar :=
  ⟨.input (.there (.there (.there .here))), ⟨1, by decide⟩, by decide⟩
def childPoint : BoundarySelector childOwner.protocol.signature vector :=
  ⟨.output (.there (.there (.there (.there .here)))), ⟨1, by decide⟩, by decide⟩
def childValue : BoundarySelector childOwner.protocol.signature scalar :=
  ⟨.output (.there (.there (.there (.there (.there .here))))), ⟨1, by decide⟩, by decide⟩

def childInput : ApplicationBinding childOwner (childOwner.clause ⟨0, by decide⟩).subject where
  relation := ⟨⟨2, by decide⟩, rfl⟩
  selectors := .cons childTable (.cons childDimension (.cons childWidth (.cons childClaim .nil)))
  exactSelectors := rfl

abbrev callContext : List Ty :=
  [vector, .index, .index, .index, vector, scalar, .index,
    .service "random.bls12-381.fr/0"]

def publicReductionCall : CheckedApplication childOwner callContext where
  caller := publicOwner
  roles := [0, 1]
  site := "label_726564756365"
  operands := .cons .here (.cons (.there .here) (.cons (.there (.there .here))
    (.cons (.there (.there (.there (.there (.there .here)))))
      (.cons (.there (.there (.there (.there (.there (.there .here))))))
        (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)))))
  occurrence := by
    iterate 5 apply ApplicationOccurrence.next
    exact ApplicationOccurrence.here _
  substitution := by unfold ValidSubstitution; decide +kernel

def noIterations : publicReductionCall.Iterations := fun index => Fin.elim0 index

variable {F G : Type} {invocation : InvocationCoordinate}

/-- The vector comes from the caller's shared parameter assignment. Dimension
and scalar width are supplied by the fixed mathematical experiment. -/
def inheritPublicTable (dimension : Nat) :
    AssignmentInstantiation (assignment F G) publicReductionCall where
  parameters := fun type selector => match type with
    | .vector domain => if same : domain = "bls12-381.fr" then
        if selector.erase = childTable.erase then same.symm ▸ .parameter publicTable else .unavailable
      else .unavailable
    | .index => if selector.erase = childDimension.erase then .supplied dimension
        else if selector.erase = childWidth.erase then .supplied 1 else .unavailable
    | _ => .unavailable
  witnesses := fun _ _ => .unavailable

theorem inherited_table (raw : List F) (dimension : Nat) (context : ProtocolContext)
    (boundary : BoundaryValuation (assignment F G) publicOwner.protocol.inputs publicOwner.protocol.outputs) :
    ((inheritPublicTable dimension).apply noIterations context boundary
      (fixedPublic (invocation := invocation) raw)).parameters vector childTable = some raw := rfl

/-- Agreement with V is an explicit premise of the public-table experiment.
No assumption about P's runtime table is used to inherit the logical table. -/
theorem inherited_table_agrees_with_verifier (raw : List F) (dimension : Nat)
    (context : ProtocolContext)
    (boundary : BoundaryValuation (assignment F G) publicOwner.protocol.inputs publicOwner.protocol.outputs)
    (same : publicTable.read context boundary = some raw) :
    ((inheritPublicTable dimension).apply noIterations context boundary
      (fixedPublic (invocation := invocation) raw)).parameters vector childTable =
      publicTable.read context boundary := by rw [inherited_table, same]

/-- The exact child clause receives the inherited table, while its statement
still reads V's actual claim at the child boundary. -/
theorem child_input_read (raw : List F) (dimension : Nat) (claim : F)
    (context : ProtocolContext)
    (callerBoundary : BoundaryValuation (assignment F G) publicOwner.protocol.inputs publicOwner.protocol.outputs)
    (childBoundary : BoundaryValuation (assignment F G) childOwner.protocol.inputs childOwner.protocol.outputs)
    (present : childClaim.read (ProtocolContext.enter context publicReductionCall.site [0, 1])
      childBoundary = some claim) :
    childInput.read (ProtocolContext.enter context publicReductionCall.site [0, 1]) childBoundary
      ((inheritPublicTable dimension).apply noIterations context callerBoundary
        (fixedPublic (invocation := invocation) raw)) =
      some (.cons raw (.cons dimension (.cons 1 (.cons claim .nil)))) := by
  change RoleFamily.sequence (Value := assignment F G)
    (Values.cons (ty := vector) (some raw) (.cons (ty := Ty.index) (some dimension)
      (.cons (ty := Ty.index) (some 1) (.cons (ty := scalar)
        (childClaim.read (ProtocolContext.enter context publicReductionCall.site [0, 1]) childBoundary) .nil)))) = _
  rw [present]
  rfl

theorem child_claim_at_call
    (environment : Nat → Environment (Component (assignment F G)) callContext)
    (returned : Nat → Values (Component (assignment F G)) childOwner.protocol.outputs) :
    childClaim.read (ProtocolContext.enter {} publicReductionCall.site [0, 1])
      (publicReductionCall.boundary {} environment returned) =
      environment 1 (.there (.there (.there (.there (.there .here))))) := by
  exact publicReductionCall.input_substitution {} environment returned childClaim _ rfl

variable [CommRing F]

/-- The residual uses the same experiment table selected before the call. Only
V's actual returned point/value are read; the table cannot be replaced by P's
returned residual. The caller must still prove its terminal check uses this. -/
theorem child_residual_at_call (remaining count : Nat)
    (table : Zkc.Polynomial.Multilinear.Table F (remaining + count))
    (environment : Nat → Environment (Component (assignment F G)) callContext)
    (returned : Nat → Values (Component (assignment F G)) childOwner.protocol.outputs) :
    (∃ point claim,
      childPoint.read (ProtocolContext.enter {} publicReductionCall.site [0, 1])
        (publicReductionCall.boundary {} environment returned) = some point ∧
      childValue.read (ProtocolContext.enter {} publicReductionCall.site [0, 1])
        (publicReductionCall.boundary {} environment returned) = some claim ∧
      Residual remaining count table point claim) ↔
    ∃ point claim,
      (returned 1).get (.there (.there (.there (.there .here)))) = some point ∧
      (returned 1).get (.there (.there (.there (.there (.there .here))))) = some claim ∧
      Residual remaining count table point claim := by
  erw [publicReductionCall.output_substitution {} environment returned childPoint _ rfl,
    publicReductionCall.output_substitution {} environment returned childValue _ rfl]
  rfl

end ZkcExamples.Structured.SumcheckContractInstantiation
