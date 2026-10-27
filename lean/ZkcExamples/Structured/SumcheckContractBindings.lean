module

public import Zkc.Source.Structured.ContractMeaning
public import Zkc.Source.DeriveRegion
public import Zkc.Source.Structured.ContractElaboration
public import ZkcExamples.Structured.SumcheckRelationContract
public import ZkcExamples.Structured.SumcheckSourceViews
public import ZkcExamples.Structured.SumcheckReduceViews
public import Zkc.Polynomial.Multilinear.Restriction
public import Zkc.Protocols.Sumcheck.Multilinear.Reduction

@[expose] public section

/-! Checked declarations for the maintained public-table target and reduction.
The Reduce declaration authors a mathematical Pending continuation. Its
probabilistic discharge remains an explicit external experiment request.
One original mathematical table is fixed before interaction and is reused by
the source sum formula and by the request's returned-point predicate. -/
namespace ZkcExamples.Structured.SumcheckContractBindings
open Zkc.Source Zkc.Source.Structured
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open SumcheckRelationContract

set_option smartUnfolding false

def publicOwner : ContractBinding SumcheckSourceViews.imported := by bind_contract

def reductionOwner : ContractBinding SumcheckReduceViews.imported where
  ownerIndex := ⟨1, by decide⟩
  protocolIndex := ⟨0, by decide⟩
  owner_eq := rfl

def reductionRoot : ContractBinding SumcheckReduceViews.imported := by bind_contract

def residualRootPoint : BoundarySelector reductionRoot.protocol.signature vector :=
  ⟨.output (.there (.there .here)), ⟨1, by decide⟩, by decide⟩
def residualRootValue : BoundarySelector reductionRoot.protocol.signature scalar :=
  ⟨.output (.there (.there (.there .here))), ⟨1, by decide⟩, by decide⟩

/-- The retained wrapper calls Reduce after constructing its P-owned Table.
The occurrence proof traverses the actual body, with its exact ordered operands. -/
def reductionCall : CheckedApplication reductionOwner
    [vector, scalar, vector, .index, .index, .index, vector, .index, scalar, .index,
      .service "random.bls12-381.fr/0"] where
  caller := reductionRoot
  roles := [0, 1]
  site := "s5"
  operands := (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) .nil)))))))
  occurrence := by
    iterate 7 apply ApplicationOccurrence.next
    exact ApplicationOccurrence.here _
  substitution := by unfold ValidSubstitution; decide +kernel

def inputShapeClause : ContractClause := publicOwner.clause (publicOwner.namedClause "shape")

def publicClause : ContractClause := publicOwner.clause (publicOwner.namedClause "public_sum")
def reductionClause : ContractClause := reductionOwner.clause (reductionOwner.namedClause "initial_sum")

theorem public_inventory : publicOwner.contract.clauses = [inputShapeClause, publicClause] := rfl
theorem reduction_inventory : reductionOwner.contract.clauses =
    [reductionOwner.clause (reductionOwner.namedClause "shape"), reductionClause] := rfl
theorem input_shape_kind : inputShapeClause.kind = .input := rfl
theorem input_shape_has_no_decision : inputShapeClause.decision = none := rfl
theorem input_shape_has_no_residual : inputShapeClause.residual = none := rfl
theorem public_kind : publicClause.kind = .target := rfl
theorem reduction_kind : reductionClause.kind = .continuation := rfl
theorem reduction_has_no_decision : reductionClause.decision = none := rfl
/-- The current source explicitly carries the Pending relation to its outputs. -/
theorem reduction_has_source_residual : ∃ residual, reductionClause.residual = some residual :=
  ⟨_, rfl⟩

def inputShapeApplication : ApplicationBinding publicOwner inputShapeClause.subject := by bind_contract

def publicApplication : ApplicationBinding publicOwner publicClause.subject := by bind_contract

def publicTable : BoundarySelector publicOwner.protocol.signature vector :=
  publicApplication.selectors.get .here
def publicClaim : BoundarySelector publicOwner.protocol.signature scalar :=
  publicApplication.selectors.get (.there .here)
def publicDecision : BoundarySelector publicOwner.protocol.signature .boolean :=
  ⟨.output .here, ⟨1, by decide⟩, by decide⟩

theorem public_decision_bound : publicClause.decision = some publicDecision.erase := rfl

def reductionApplication : ApplicationBinding reductionOwner reductionClause.subject := by bind_contract

def reductionTable : BoundarySelector reductionOwner.protocol.signature vector :=
  reductionApplication.selectors.get .here
def reductionDimension : BoundarySelector reductionOwner.protocol.signature .index :=
  reductionApplication.selectors.get (.there .here)
def reductionWidth : BoundarySelector reductionOwner.protocol.signature .index :=
  reductionApplication.selectors.get (.there (.there .here))
def reductionInitialPoint : BoundarySelector reductionOwner.protocol.signature vector :=
  reductionApplication.selectors.get (.there (.there (.there .here)))
def reductionClaim : BoundarySelector reductionOwner.protocol.signature scalar :=
  reductionApplication.selectors.get (.there (.there (.there (.there .here))))
def reductionPoint : BoundarySelector reductionOwner.protocol.signature vector :=
  ⟨.output (.there (.there (.there (.there .here)))), ⟨1, by decide⟩, by decide⟩
def reductionValue : BoundarySelector reductionOwner.protocol.signature scalar :=
  ⟨.output (.there (.there (.there (.there (.there .here))))), ⟨1, by decide⟩, by decide⟩

def inputShapeFormula : FormulaBinding SumcheckSourceViews.imported inputShapeApplication.relation := by bind_contract

def publicFormula : FormulaBinding SumcheckSourceViews.imported publicApplication.relation := by bind_contract

def reductionFormula : FormulaBinding SumcheckReduceViews.imported reductionApplication.relation := by bind_contract

set_option maxRecDepth 20000 in
theorem sourceBodies : Bodies SumcheckSourceViews.unit.definitions where
  add := by exact_body SumcheckSourceViews.sumAddDefinition
  step := by exact_body SumcheckSourceViews.sumStepDefinition
  total := by exact_body SumcheckSourceViews.sumTotalDefinition

set_option maxRecDepth 20000 in
theorem reductionBodies : Bodies SumcheckReduceViews.unit.definitions where
  add := by exact_body SumcheckReduceViews.sumAddDefinition
  step := by exact_body SumcheckReduceViews.sumStepDefinition
  total := by exact_body SumcheckReduceViews.sumTotalDefinition

variable {F G : Type} {invocation : InvocationCoordinate}

/-- Explicit fixed experiment assignment, shared by the initial formula and
external residual request. It does not read or replace P's runtime table. -/
def fixedReduction (raw : List F) (dimension : Nat) : LogicalAssignments (assignment F G) reductionOwner invocation where
  parameters := fun type selector => match type with
    | .vector _ => if selector.erase = reductionTable.erase then some raw else none
    | .index => if selector.erase = reductionDimension.erase then some dimension
        else if selector.erase = reductionWidth.erase then some 1 else none
    | _ => none
  witnesses := fun _ _ => none

def fixedPublic (raw : List F) : LogicalAssignments (assignment F G) publicOwner invocation where
  parameters := fun type selector => match type with
    | .vector _ => if selector.erase = publicTable.erase then some raw else none
    | _ => none
  witnesses := fun _ _ => none

theorem public_application_read (raw : List F) (claim : F) (context : ProtocolContext)
    (boundary : BoundaryValuation (assignment F G) publicOwner.protocol.inputs publicOwner.protocol.outputs)
    (present : publicClaim.read context boundary = some claim) :
    publicApplication.read context boundary (fixedPublic (invocation := invocation) raw) = some (.cons raw (.cons claim .nil)) := by
  change RoleFamily.sequence (Value := assignment F G) (Values.cons (ty := vector) (some raw) (.cons (ty := scalar) (publicClaim.read context boundary) .nil)) = _
  rw [present]
  rfl

theorem reduction_application_read (raw : List F) (dimension : Nat) (claim : F)
    (context : ProtocolContext)
    (boundary : BoundaryValuation (assignment F G)
      reductionOwner.protocol.inputs reductionOwner.protocol.outputs)
    (present : reductionClaim.read context boundary = some claim)
    (empty : reductionInitialPoint.read context boundary = some []) :
    reductionApplication.read context boundary (fixedReduction (invocation := invocation) raw dimension) =
      some (.cons raw (.cons dimension (.cons 1 (.cons [] (.cons claim .nil))))) := by
  change RoleFamily.sequence (Value := assignment F G) (Values.cons (ty := vector) (some raw) (.cons (ty := Ty.index) (some dimension)
    (.cons (ty := Ty.index) (some 1) (.cons (ty := vector) (reductionInitialPoint.read context boundary)
      (.cons (ty := scalar) (reductionClaim.read context boundary) .nil))))) = _
  rw [present, empty]
  rfl

/-- Unlike the residual experiment parameter, the complete public target must
agree with the actual V table. This premise is explicit and never inferred from
the `parameter` purpose string. -/
theorem public_assignment_agrees (raw : List F) (context : ProtocolContext)
    (boundary : BoundaryValuation (assignment F G) publicOwner.protocol.inputs publicOwner.protocol.outputs)
    (same : publicTable.read context boundary = some raw) :
    publicApplication.Agrees context boundary (fixedPublic (invocation := invocation) raw) := by
  change (Values.cons (some raw) (.cons (publicClaim.read context boundary) .nil) :
    Values (Component (assignment F G)) [vector, scalar]) =
    Values.cons (publicTable.read context boundary) (.cons (publicClaim.read context boundary) .nil)
  rw [same]

/-- Acceptance observes the exact retained target selector at V's boundary. -/
def publicAccepts (outputs : Values (Component (assignment F G)) publicOwner.protocol.outputs) : Prop :=
  publicDecision.read {} {
    inputs := fun _ => Values.absent (assignment F G) _
    outputs := fun self => if self = 1 then outputs else Values.absent (assignment F G) _
  } = some true

theorem public_accepts_iff (outputs : Values (Component (assignment F G)) publicOwner.protocol.outputs) :
    publicAccepts outputs ↔ outputs.get .here = some true := Iff.rfl

variable [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- The pure input formula is total over the independent natural/list model. -/
theorem input_shape_formula_equation (raw : List F) (rounds : Nat) :
    inputShapeFormula.invokeRelation (F := F) (G := G) (.cons raw (.cons rounds .nil)) =
      .done (.cons (decide (raw.length = 2 ^ rounds ∧ rounds ≤ 2)) .nil) := by
  exact (inputShapeFormula.invokeRelation_body_view shapeBody (by kernel_rfl)
    (.cons raw (.cons rounds .nil))).trans (shape_equation _ raw rounds)

/-- No existential table is introduced by interpreting the formula. -/
def PublicTruth (raw : List F) (claim : F) : Prop :=
  publicFormula.invokeRelation (F := F) (G := G) (.cons raw (.cons claim .nil)) =
    .done (.cons true .nil)

def ReductionTruth (raw : List F) (dimension : Nat) (claim : F) : Prop :=
  reductionFormula.invokeRelation (F := F) (G := G)
    (.cons raw (.cons dimension (.cons 1 (.cons [] (.cons claim .nil))))) = .done (.cons true .nil)

set_option backward.isDefEq.respectTransparency false in
theorem public_formula_equation (raw : List F) (claim : F) (bounded : raw.length < indexLimit) :
    publicFormula.invokeRelation (F := F) (G := G) (.cons raw (.cons claim .nil)) =
      .done (.cons (decide (claim = raw.sum)) .nil) := by
  change publicFormula.process (.cons raw (.cons claim .nil)) = _
  rw [publicFormula.process_eq_body]
  have totalLaw :
      (meaning F G (closedMeanings SumcheckSourceViews.unit.definitions)).OperationLaw
        (fun op => .call op .done) (.invoke totalHelper) (.cons raw .nil) .nil
        (.done (.cons raw.sum .nil)) := by
    apply RegionMeaning.OperationLaw.identity
    exact total_equation SumcheckSourceViews.unit.linked sourceBodies raw bounded
  have derived : Region.Derivation
      (meaning F G (closedMeanings SumcheckSourceViews.unit.definitions))
      (fun op => .call op .done) publicFormula.definition.body
      (Values.cons raw (.cons claim .nil)).get (.done (.cons (decide (claim = raw.sum)) .nil)) := by
    derive_region using (first
      | exact totalLaw
      | (apply RegionMeaning.OperationLaw.identity; rfl))
  exact derived.sound_identity

set_option maxRecDepth 20000 in
theorem reduction_formula_equation (raw : List F) (dimension width : Nat)
    (point : List F) (claim : F) (bounded : (restrictPrefixValues raw point).length < indexLimit) :
    reductionFormula.invokeRelation (F := F) (G := G)
      (.cons raw (.cons dimension (.cons width (.cons point (.cons claim .nil))))) =
      .done (.cons (decide (claim = (restrictPrefixValues raw point).sum)) .nil) := by
  exact pending_equation (F := F) (G := G) SumcheckReduceViews.unit.linked reductionBodies
    (by exact_body SumcheckReduceViews.pendingFormulaDefinition)
    (by exact_body SumcheckReduceViews.valuesDefinition) raw dimension width point claim bounded

variable {sourceEnvironment : RelationEnvironment SumcheckSourceViews.imported F G}
variable {reductionEnvironment : RelationEnvironment SumcheckReduceViews.imported F G}

/-- Formula interpretation retains its capacity domain and actual source body. -/
def publicTarget : InterpretedApplication publicOwner publicClause.subject F G sourceEnvironment where
  binding := publicApplication
  interpretation := .formula publicFormula rfl
    (fun args => (args.get .here).length < indexLimit)
    (fun args => args.get (.there .here) = (args.get .here).sum) inferInstance

/-- The new input clause retains its exact shape and repeat-bound predicate. -/
def inputShape : InterpretedApplication publicOwner inputShapeClause.subject F G sourceEnvironment where
  binding := inputShapeApplication
  interpretation := .formula inputShapeFormula rfl (fun _ => True)
    (fun args => (args.get .here).length = 2 ^ (args.get (.there .here)) ∧
      args.get (.there .here) ≤ 2) inferInstance

def reductionInput : InterpretedApplication reductionOwner reductionClause.subject F G reductionEnvironment where
  binding := reductionApplication
  interpretation := .formula reductionFormula rfl
    (fun args => (restrictPrefixValues (args.get .here)
      (args.get (.there (.there (.there .here))))).length < indexLimit)
    (fun args => args.get (.there (.there (.there (.there .here)))) =
      (restrictPrefixValues (args.get .here) (args.get (.there (.there (.there .here))))).sum) inferInstance

/-- Every current declaration is interpreted, including shape and residual. -/
def reductionShapeClause : ContractClause := reductionOwner.clause (reductionOwner.namedClause "shape")
def reductionShapeApplication : ApplicationBinding reductionOwner reductionShapeClause.subject := by bind_contract
def reductionShapeFormula : FormulaBinding SumcheckReduceViews.imported reductionShapeApplication.relation := by bind_contract

def reductionShape : InterpretedApplication reductionOwner reductionShapeClause.subject F G reductionEnvironment where
  binding := reductionShapeApplication
  interpretation := .formula reductionShapeFormula rfl (fun _ => True)
    (fun args => args.get (.there (.there .here)) = 1 ∧
      (args.get .here).length = 2 ^ (args.get (.there .here))) inferInstance

def reductionResidual : RelationApplication := reductionClause.residual.get (by decide)
def reductionResidualApplication : ApplicationBinding reductionOwner reductionResidual := by bind_contract
def reductionResidualFormula : FormulaBinding SumcheckReduceViews.imported reductionResidualApplication.relation := by bind_contract

def reductionOutput : InterpretedApplication reductionOwner reductionResidual F G reductionEnvironment where
  binding := reductionResidualApplication
  interpretation := .formula reductionResidualFormula rfl
    (fun args => (restrictPrefixValues (args.get .here)
      (args.get (.there (.there (.there .here))))).length < indexLimit)
    (fun args => args.get (.there (.there (.there (.there .here)))) =
      (restrictPrefixValues (args.get .here) (args.get (.there (.there (.there .here))))).sum) inferInstance

theorem reduction_shape_formula_law :
    (reductionShape (F := F) (G := G) (reductionEnvironment := reductionEnvironment)).interpretation.FormulaLaw := by
  intro args _
  cases args with | cons raw rest => ?_
  cases rest with | cons dimension rest => ?_
  cases rest with | cons width rest => ?_
  cases rest
  exact tableShape_equation (F := F) (G := G) SumcheckReduceViews.unit.linked
    (by exact_body SumcheckReduceViews.tableShapeFormulaDefinition)
    (by exact_body SumcheckReduceViews.widthDefinition)
    (by exact_body SumcheckReduceViews.valuesDefinition)
    (by exact_body SumcheckReduceViews.variablesDefinition) raw dimension width

theorem reduction_residual_formula_law :
    (reductionOutput (F := F) (G := G) (reductionEnvironment := reductionEnvironment)).interpretation.FormulaLaw := by
  intro args bounded
  cases args with | cons raw rest => ?_
  cases rest with | cons dimension rest => ?_
  cases rest with | cons width rest => ?_
  cases rest with | cons point rest => ?_
  cases rest with | cons claim rest => ?_
  cases rest
  exact pending_equation (F := F) (G := G) SumcheckReduceViews.unit.linked reductionBodies
    (by exact_body SumcheckReduceViews.pendingFormulaDefinition)
    (by exact_body SumcheckReduceViews.valuesDefinition) raw dimension width point claim bounded

theorem public_formula_law : (publicTarget (F := F) (G := G) (sourceEnvironment := sourceEnvironment)).interpretation.FormulaLaw := by
  intro args bounded
  cases args with | cons raw rest => ?_
  cases rest with | cons claim rest => ?_
  cases rest
  exact public_formula_equation raw claim bounded

theorem input_shape_formula_law :
    (inputShape (F := F) (G := G) (sourceEnvironment := sourceEnvironment)).interpretation.FormulaLaw := by
  intro args _
  cases args with | cons raw rest => ?_
  cases rest with | cons rounds rest => ?_
  cases rest
  exact input_shape_formula_equation raw rounds

theorem reduction_formula_law : (reductionInput (F := F) (G := G) (reductionEnvironment := reductionEnvironment)).interpretation.FormulaLaw := by
  intro args bounded
  cases args with | cons raw rest => ?_
  cases rest with | cons dimension rest => ?_
  cases rest with | cons width rest => ?_
  cases rest with | cons point rest => ?_
  cases rest with | cons claim rest => ?_
  cases rest
  exact reduction_formula_equation raw dimension width point claim bounded

set_option backward.isDefEq.respectTransparency false in
theorem public_target_holds_iff (raw : List F) (claim : F) (context : ProtocolContext)
    (boundary : BoundaryValuation (assignment F G) publicOwner.protocol.inputs publicOwner.protocol.outputs)
    (present : publicClaim.read context boundary = some claim) :
    (publicTarget (sourceEnvironment := sourceEnvironment)).Holds context boundary (fixedPublic (invocation := invocation) raw) ↔ PublicTruth (G := G) raw claim := by
  change (∃ args, publicApplication.read context boundary (fixedPublic (invocation := invocation) raw) = some args ∧
    publicFormula.invokeRelation args = .done (.cons true .nil)) ↔ _
  rw [public_application_read raw claim context boundary present]
  simp only [Option.some.injEq, exists_eq_left']
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem reduction_input_holds_iff (raw : List F) (dimension : Nat) (claim : F) (context : ProtocolContext)
    (boundary : BoundaryValuation (assignment F G) reductionOwner.protocol.inputs reductionOwner.protocol.outputs)
    (present : reductionClaim.read context boundary = some claim)
    (empty : reductionInitialPoint.read context boundary = some []) :
    (reductionInput (reductionEnvironment := reductionEnvironment)).Holds context boundary (fixedReduction (invocation := invocation) raw dimension) ↔
      ReductionTruth (G := G) raw dimension claim := by
  change (∃ args, reductionApplication.read context boundary (fixedReduction (invocation := invocation) raw dimension) = some args ∧
    reductionFormula.invokeRelation args = .done (.cons true .nil)) ↔ _
  rw [reduction_application_read raw dimension claim context boundary present empty]
  simp only [Option.some.injEq, exists_eq_left']
  rfl

theorem public_truth_iff (raw : List F) (claim : F) (bounded : raw.length < indexLimit) :
    PublicTruth (G := G) raw claim ↔ claim = raw.sum := by
  unfold PublicTruth
  rw [public_formula_equation raw claim bounded]
  constructor
  · intro equality
    have output := congrArg (fun values => values.get .here) (PIR.Process.done.inj equality)
    exact of_decide_eq_true output
  · intro equality
    simp [equality]

theorem reduction_truth_iff (raw : List F) (dimension : Nat) (claim : F)
    (bounded : raw.length < indexLimit) :
    ReductionTruth (G := G) raw dimension claim ↔ claim = raw.sum := by
  unfold ReductionTruth
  rw [reduction_formula_equation raw dimension 1 [] claim bounded, restrictPrefixValues_nil]
  constructor
  · intro equality
    have output := congrArg (fun values => values.get .here) (PIR.Process.done.inj equality)
    exact of_decide_eq_true output
  · intro equality
    simp [equality]

/-- External residual request over the same original table. The existential only
decodes the returned ordered coordinates; it cannot select another table. -/
def Residual (remaining count : Nat) (table : Table F (remaining + count))
    (point : List F) (claim : F) : Prop :=
  ∃ coordinates : Fin count → F, List.ofFn coordinates = point ∧
    Zkc.Protocols.Sumcheck.Multilinear.ResidualClaim count table coordinates claim

/-- In the reduction interface, only V's returned point/value discharge the
request. P's returned residual table is never substituted for the fixed table. -/
def ResidualAt (remaining count : Nat) (table : Table F (remaining + count))
    (context : ProtocolContext)
    (boundary : BoundaryValuation (assignment F G)
      reductionOwner.protocol.inputs reductionOwner.protocol.outputs) : Prop :=
  ∃ point claim, reductionPoint.read context boundary = some point ∧
    reductionValue.read context boundary = some claim ∧ Residual remaining count table point claim

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The initial statement is the actual V claim operand at the call site. The
fixed table remains a logical parameter and is not inferred from P's operand. -/
theorem reduction_claim_at_call
    (environment : Nat → Environment (Component (assignment F G))
      [vector, scalar, vector, .index, .index, .index, vector, .index, scalar, .index,
        .service "random.bls12-381.fr/0"])
    (returned : Nat → Values (Component (assignment F G)) reductionOwner.protocol.outputs) :
    reductionClaim.read (ProtocolContext.enter {} "s5" [0, 1])
      (reductionCall.boundary {} environment returned) =
      environment 1 (.there .here) := by
  exact reductionCall.input_substitution {} environment returned reductionClaim _ rfl

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- Generic checked-call substitution performs the residual output binding.
The result uses the callee's actual V tuple at the entered role, with no new
table and no equality between P and V components. -/
theorem residual_at_call (remaining count : Nat) (table : Table F (remaining + count))
    (environment : Nat → Environment (Component (assignment F G))
      [vector, scalar, vector, .index, .index, .index, vector, .index, scalar, .index,
        .service "random.bls12-381.fr/0"])
    (returned : Nat → Values (Component (assignment F G)) reductionOwner.protocol.outputs) :
    ResidualAt remaining count table (ProtocolContext.enter {} "s5" [0, 1])
      (reductionCall.boundary {} environment returned) ↔
      ∃ point claim, (returned 1).get (.there (.there (.there (.there .here)))) = some point ∧
        (returned 1).get (.there (.there (.there (.there (.there .here))))) = some claim ∧
        Residual remaining count table point claim := by
  unfold ResidualAt
  erw [reductionCall.output_substitution {} environment returned reductionPoint _ rfl,
    reductionCall.output_substitution {} environment returned reductionValue _ rfl]
  rfl

/-- A caller must supply this terminal law before an acceptance claim can use
the reduction. A residual-only theorem does not manufacture a Boolean decision. -/
def TerminalObligation {A : Type} (accepts : A → Prop)
    (remaining count : Nat) (table : Table F (remaining + count))
    (point : A → List F) (claim : A → F) : Prop :=
  ∀ result, accepts result → Residual remaining count table (point result) (claim result)

end ZkcExamples.Structured.SumcheckContractBindings
