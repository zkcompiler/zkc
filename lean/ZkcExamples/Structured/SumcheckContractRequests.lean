module

public import Zkc.Source.Structured.ContractObligations
public import Zkc.Source.Structured.ContractApplication
public import ZkcExamples.Structured.SumcheckContractInterpretations
public import ZkcExamples.Structured.SumcheckContractInstantiation
public import ZkcExamples.Structured.SumcheckSourceVerifier
public import ZkcExamples.Structured.SumcheckReduceVerifier

@[expose] public section

/-! Requests at the actual masked component and application boundaries. The
public table is V's fixed input; Reduce's mathematical table is inherited from
that parameter, independently of its P-owned runtime operand. -/
namespace ZkcExamples.Structured.SumcheckContractRequests
open Zkc.Source Zkc.Source.Structured
open SumcheckRelationContract SumcheckContractBindings SumcheckContractInterpretations
open SumcheckContractInstantiation
open Zkc.Polynomial Zkc.Polynomial.Multilinear

set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]
variable {sourceEnvironment : RelationEnvironment SumcheckSourceViews.imported F G}

abbrev rootInvocation : InvocationCoordinate := ⟨1, []⟩

def publicInput (raw : List F) (claim : F) (count handle : Nat) : ComponentInput publicOwner F G :=
  ⟨{}, 1, SumcheckSourceVerifier.sourceRootInputs (some raw) (some claim) (some count) (some handle)⟩

theorem public_process (raw : List F) (claim : F) (count handle : Nat) :
    ((publicInput (G := G) raw claim count handle).process.interpret forgetSites) =
      SumcheckSourceViews.imported.program.participant F G 1
        (SumcheckSourceVerifier.sourceRootInputs (some raw) (some claim) (some count) (some handle)) := rfl

def publicCount : BoundarySelector publicOwner.protocol.signature .index :=
  ⟨.input (.there (.there .here)), ⟨1, by decide⟩, by decide⟩

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem public_count_read (raw : List F) (claim : F) (count handle : Nat) (outcome) :
    publicCount.read {} ((publicInput (G := G) raw claim count handle).boundary outcome) = some count := rfl

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem public_table_read (raw : List F) (claim : F) (count handle : Nat) (outcome) :
    publicTable.read {} ((publicInput (G := G) raw claim count handle).boundary outcome) = some raw := rfl

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem public_claim_read (raw : List F) (claim : F) (count handle : Nat) (outcome) :
    publicClaim.read {} ((publicInput (G := G) raw claim count handle).boundary outcome) = some claim := rfl

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem public_agrees (raw : List F) (claim : F) (count handle : Nat) (outcome) :
    publicApplication.Agrees {} ((publicInput (G := G) raw claim count handle).boundary outcome)
      (fixedPublic (invocation := rootInvocation) raw) :=
  public_assignment_agrees raw {} _ (public_table_read raw claim count handle outcome)

def publicSelection : SelectedApplication publicOwner F G sourceEnvironment :=
  publicContract.select (.subject ⟨0, by decide⟩)

def publicUse (raw : List F) (claim : F) (count handle : Nat) (outcome) :
    ApplicationUse (publicSelection (sourceEnvironment := sourceEnvironment)) {}
      ((publicInput raw claim count handle).boundary outcome)
      (fixedPublic (invocation := rootInvocation) raw) where
  arguments := .cons raw (.cons claim .nil)
  read := by
    change publicApplication.read {} _ (fixedPublic (invocation := rootInvocation) raw) = _
    unfold ApplicationBinding.read
    rw [public_agrees raw claim count handle outcome]
    change RoleFamily.sequence (Values.cons
      (publicTable.read {} ((publicInput raw claim count handle).boundary outcome))
      (.cons (publicClaim.read {} ((publicInput raw claim count handle).boundary outcome)) .nil)) = _
    rw [public_table_read, public_claim_read]
    rfl

theorem public_translation (raw : List F) (claim : F) (count handle : Nat) (outcome)
    (bounded : raw.length < indexLimit) :
    (publicUse (G := G) (sourceEnvironment := sourceEnvironment) raw claim count handle outcome).Translation :=
  ⟨public_formula_law, bounded⟩

/-- Pre-run input refutation. Inputs are identical at every possible outcome;
choosing a stopped boundary here supplies no output or terminal evidence. -/
def publicRefutation (raw : List F) (claim : F) (count handle : Nat) :=
  ContractRequest.relation (publicSelection (G := G) (sourceEnvironment := sourceEnvironment))
    (publicUse raw claim count handle (.stopped .incomplete)) .refutation

theorem public_false_sum (raw : List F) (claim : F) (count handle : Nat)
    (refuted : (publicRefutation (G := G) (sourceEnvironment := sourceEnvironment) raw claim count handle).Meaning)
    (translation : (publicUse (G := G) (sourceEnvironment := sourceEnvironment)
      raw claim count handle (.stopped .incomplete)).Translation) : claim ≠ raw.sum := by
  intro equality
  exact refuted (((publicUse raw claim count handle (.stopped .incomplete)).equivalence translation).mpr equality)

theorem public_accepts (raw : List F) (claim : F) (count handle : Nat) (outcome) :
    (publicInput (G := G) raw claim count handle).returnedEvent
      ((publicContract (sourceEnvironment := sourceEnvironment)).Accepts {} ⟨0, by decide⟩) outcome ↔
    BoundaryValuation.ReturnedSatisfies (fun outputs => outputs.get .here = some true) outcome := by
  cases outcome with
  | stopped reason => rfl
  | returned results =>
    change (∃ selector, ∃ selected : some publicDecision.erase = some selector, _) ↔ _
    constructor
    · rintro ⟨selector, selected, accepted⟩
      cases Option.some.inj selected
      exact accepted
    · intro accepted
      exact ⟨_, rfl, accepted⟩

/-- A typed residual request decodes only the fixed raw parameter. There is no
existential choice of another table. Dimension and count are typed parameters;
only the selected V point/value outputs are observed. -/
def residualTerminal {snapshot : Snapshot} {imported : Imported snapshot}
    (owner : ContractBinding imported)
    (raw : AssignmentSource (assignment F G) owner vector) (remaining count : Nat)
    (point : BoundarySelector owner.protocol.signature vector)
    (value : BoundarySelector owner.protocol.signature scalar)
    (pointOutput : point.port.direction = .output) (valueOutput : value.port.direction = .output) :
    ExternalTerminal owner F G where
  parameterTypes := [vector, .index, .index]
  parameters := .cons raw (.cons (.supplied remaining) (.cons (.supplied count) .nil))
  outputTypes := [vector, scalar]
  nonempty := by decide
  outputs := .cons ⟨point, pointOutput⟩ (.cons ⟨value, valueOutput⟩ .nil)
  meaning := fun parameters outputs =>
    match ofList? (parameters.get (.there .here) + parameters.get (.there (.there .here)))
        (parameters.get .here) with
    | none => False
    | some table => Residual (parameters.get (.there .here))
        (parameters.get (.there (.there .here))) table (outputs.get .here) (outputs.get (.there .here))

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem residual_terminal_iff {snapshot : Snapshot} {imported : Imported snapshot}
    {owner : ContractBinding imported} {invocation : InvocationCoordinate}
    (source : AssignmentSource (assignment F G) owner vector) (remaining count : Nat)
    (point : BoundarySelector owner.protocol.signature vector)
    (value : BoundarySelector owner.protocol.signature scalar)
    (pointOutput : point.port.direction = .output) (valueOutput : value.port.direction = .output)
    (context : ProtocolContext) (boundary : ContractBoundaryValues owner F G)
    (assignments : LogicalAssignments (assignment F G) owner invocation)
    (raw : List F) (same : source.read context boundary assignments = some raw)
    (table : Table F (remaining + count)) (decoded : ofList? (remaining + count) raw = some table) :
    (residualTerminal owner source remaining count point value pointOutput valueOutput).Holds
      context boundary assignments ↔
      ∃ coordinates claim, point.read context boundary = some coordinates ∧
        value.read context boundary = some claim ∧ Residual remaining count table coordinates claim := by
  have parameterRead : RoleFamily.sequence (ExternalTerminal.readParameters context boundary assignments
      (residualTerminal owner source remaining count point value pointOutput valueOutput).parameters) =
      some (.cons raw (.cons remaining (.cons count .nil))) := by
    change (source.read context boundary assignments >>= fun xs =>
      some (Values.cons (ty := vector) xs (.cons (ty := Ty.index) remaining (.cons (ty := Ty.index) count .nil)))) = _
    rw [same]
    rfl
  have outputsRead : RoleFamily.sequence (ExternalTerminal.readOutputs context boundary
      (residualTerminal owner source remaining count point value pointOutput valueOutput).outputs) =
      (point.read context boundary >>= fun p => value.read context boundary >>= fun v =>
        some (Values.cons (ty := vector) p (.cons (ty := scalar) v .nil))) := by
    change RoleFamily.sequence (Values.cons (point.read context boundary)
      (.cons (value.read context boundary) .nil)) = _
    generalize point.read context boundary = op
    generalize value.read context boundary = ov
    cases op <;> cases ov <;> rfl
  unfold ExternalTerminal.Holds
  rw [parameterRead]
  simp only [outputsRead]
  constructor
  · rintro ⟨parameters, outputs, equalParameters, outputRead, truth⟩
    cases Option.some.inj equalParameters
    cases outputs with | cons coordinates rest => ?_
    cases rest with | cons claim rest => ?_
    cases rest
    change (point.read context boundary >>= fun p => value.read context boundary >>= fun v =>
      some (Values.cons p (.cons v .nil))) = some (.cons coordinates (.cons claim .nil)) at outputRead
    rcases Option.bind_eq_some_iff.mp outputRead with ⟨p, hp, hv⟩
    rcases Option.bind_eq_some_iff.mp hv with ⟨v, hv, equalOutputs⟩
    cases Option.some.inj equalOutputs
    refine ⟨_, _, hp, hv, ?_⟩
    change (match ofList? (remaining + count) raw with
      | none => False | some t => Residual remaining count t coordinates claim) at truth
    rw [decoded] at truth
    exact truth
  · rintro ⟨coordinates, claim, hp, hv, truth⟩
    refine ⟨_, .cons coordinates (.cons claim .nil), rfl, ?_, ?_⟩
    · change (point.read context boundary >>= fun p => value.read context boundary >>= fun v =>
        some (Values.cons p (.cons v .nil))) = _
      rw [hp]
      change (value.read context boundary >>= fun v => some (Values.cons coordinates (.cons v .nil))) = _
      rw [hv]
      rfl
    · change (match ofList? (remaining + count) raw with
        | none => False | some t => Residual remaining count t coordinates claim)
      rw [decoded]
      exact truth

/-- Reduce's initial_sum formula in the very snapshot called by public Sumcheck. -/
def originalChildFormula : Function :=
  (SumcheckSourceData.snapshot.definitions.filterMap fun
    | .function definition => some definition | _ => none).get ⟨10, by decide +kernel⟩

def childFormula : FormulaBinding SumcheckSourceViews.imported childInput.relation where
  original := originalChildFormula
  original_mem := by structured_mem
  formula_kind := rfl
  formula_eq := rfl
  math_kind := rfl
  inputs_eq := rfl
  outputs_eq := rfl
  helperIndex := ⟨SumcheckSourceViews.unit.definitions.findIdx (fun d => d.helper == tableSumHelper),
    by decide +kernel⟩
  signature_eq := rfl

def childSelection : SelectedApplication childOwner F G sourceEnvironment where
  selection := .subject ⟨0, by decide⟩
  interpreted := {
    binding := childInput
    interpretation := .formula childFormula rfl
      (fun args => (args.get .here).length < indexLimit)
      (fun args => args.get (.there (.there (.there .here))) = (args.get .here).sum) inferInstance }

theorem child_formula_law :
    (childSelection (G := G) (sourceEnvironment := sourceEnvironment)).interpreted.interpretation.FormulaLaw := by
  intro args bounded
  cases args with | cons raw rest => ?_
  cases rest with | cons dimension rest => ?_
  cases rest with | cons width rest => ?_
  cases rest with | cons claim rest => ?_
  cases rest
  exact tableSum_equation (F := F) (G := G) SumcheckSourceViews.unit.linked sourceBodies
    (by exact_body SumcheckSourceViews.tableSumFormulaDefinition)
    (by exact_body SumcheckSourceViews.valuesDefinition) raw dimension width claim bounded

/-- The verifier's evaluated SSA environment at the maintained call. The three
P-owned table components are absent. The surviving public raw vector is V's. -/
def publicCallEnvironment (raw : List F) (claim : F) (count handle : Nat) :
    Environment (Component (assignment F G)) callContext :=
  SumcheckSourceVerifier.callEnvironment (some raw) (some claim) (some count) (some handle)

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem public_call_inputs (raw : List F) (claim : F) (count handle : Nat) :
    publicReductionCall.operands.eval (publicCallEnvironment (G := G) raw claim count handle) =
      SumcheckSourceVerifier.childInputs (some claim) (some count) (some handle) := rfl

def childProcess (raw : List F) (claim : F) (count handle : Nat) :=
  (publicReductionCall.componentInput {} 1 (publicCallEnvironment (G := G) raw claim count handle)).process.interpret
    forgetSites

/-- This request's component is the actual maximum-two callee in the Source
snapshot. The equation preserves the exact six-slot returned tuple and stops. -/
theorem child_present (raw : List F) (claim : F) (count handle : Nat) (admitted : count ≤ 2) :
    childProcess (G := G) raw claim count handle =
      (PIR.repeatN count (SumcheckVerifierLaws.roundPresent SumcheckSourceVerifier.childContext handle)
        ([], claim)).bind (fun pc => .done (SumcheckVerifierPrelude.reduceResults (some pc.1, some pc.2))) := by
  change (invokeProtocol (SumcheckSourceViews.unit.protocolTable F G) SumcheckSourceBodies.reduceSignature
    SumcheckSourceVerifier.childContext 1 (SumcheckSourceVerifier.childInputs (some claim) (some count) (some handle))).interpret
    forgetSites = _
  rw [SumcheckSourceViews.unit.protocolTable_forgetSites]
  rw [SumcheckSourceVerifier.reduce_invoke_plain]
  change SumcheckVerifierPrelude.reduceDenote 2 SumcheckSourceViews.unit SumcheckSourceVerifier.childContext 1
    (SumcheckVerifierPrelude.reduceArguments none none none (some claim) (some count) (some handle)) = _
  rw [SumcheckVerifierPrelude.reduce_optional SumcheckSourceViews.unit SumcheckSourceVerifier.helperBodies
    SumcheckSourceVerifier.childContext 1 rfl (by decide)]
  simp only [SumcheckVerifierPrelude.admittedRounds, admitted, ↓reduceIte]
  rw [SumcheckVerifierLaws.repeat_present SumcheckSourceVerifier.childContext handle count ([], claim)]
  exact PIR.Proc.bind_assoc _ _ _

/-- For the complete public-table experiment, dimension comes from V's actual
count input. Missing count remains unavailable; width is explicitly scalar. -/
def inheritPublicInputs : AssignmentInstantiation (assignment F G) publicReductionCall where
  parameters := fun type selector => match type with
    | .vector domain => if same : domain = "bls12-381.fr" then
        if selector.erase = childTable.erase then same.symm ▸ .parameter publicTable else .unavailable
      else .unavailable
    | .index => if selector.erase = childDimension.erase then .boundary publicCount
        else if selector.erase = childWidth.erase then .supplied 1 else .unavailable
    | _ => .unavailable
  witnesses := fun _ _ => .unavailable

def childAssignments (raw : List F) (claim : F) (count handle : Nat) :=
  inheritPublicInputs.apply noIterations {}
    ((publicInput (G := G) raw claim count handle).boundary (.stopped .incomplete))
    (fixedPublic (invocation := rootInvocation) raw)

def childBoundary (raw : List F) (claim : F) (count handle : Nat) (outcome) :=
  publicReductionCall.boundaryOfOutcome {} 1 (publicCallEnvironment (G := G) raw claim count handle) outcome

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem child_claim_read (raw : List F) (claim : F) (count handle : Nat) (outcome) :
    childClaim.read SumcheckSourceVerifier.childContext
      (childBoundary (G := G) raw claim count handle outcome) = some claim := by
  exact publicReductionCall.boundaryOfOutcome_input {} 1 _ outcome childClaim
    (.there (.there (.there .here))) rfl rfl

def childUse (raw : List F) (claim : F) (count handle : Nat) (outcome) :
    ApplicationUse (childSelection (G := G) (sourceEnvironment := sourceEnvironment))
      SumcheckSourceVerifier.childContext (childBoundary raw claim count handle outcome)
      (childAssignments raw claim count handle) where
  arguments := .cons raw (.cons count (.cons 1 (.cons claim .nil)))
  read := by
    change RoleFamily.sequence (Values.cons (ty := vector) (some raw)
      (.cons (ty := Ty.index) (publicCount.read {} ((publicInput raw claim count handle).boundary (.stopped .incomplete)))
        (.cons (ty := Ty.index) (some 1) (.cons (ty := scalar)
          (childClaim.read SumcheckSourceVerifier.childContext (childBoundary raw claim count handle outcome)) .nil)))) = _
    rw [public_count_read, child_claim_read]
    rfl

def childRefutation (raw : List F) (claim : F) (count handle : Nat) (outcome) :=
  ContractRequest.relation (childSelection (G := G) (sourceEnvironment := sourceEnvironment))
    (childUse raw claim count handle outcome) .refutation

/-- Refutation is transported to the retained callee clause with inherited
parameters and the actual claim operand. It is not an all-inputs assumption. -/
theorem child_refutation (raw : List F) (claim : F) (count handle : Nat) (outcome)
    (refuted : (publicRefutation (G := G) (sourceEnvironment := sourceEnvironment) raw claim count handle).Meaning)
    (translation : (publicUse (G := G) (sourceEnvironment := sourceEnvironment)
      raw claim count handle (.stopped .incomplete)).Translation) :
    (childRefutation (G := G) (sourceEnvironment := sourceEnvironment) raw claim count handle outcome).Proof := by
  exact ⟨⟨child_formula_law, translation.domain⟩, public_false_sum raw claim count handle refuted translation⟩

/-- This child request already carries the mathematical refutation transported
from the caller. Its translation certifies the source association; no second
formula round trip is needed by the probabilistic theorem. -/
theorem child_false_sum (raw : List F) (claim : F) (count handle : Nat) (outcome)
    (refuted : (childRefutation (G := G) (sourceEnvironment := sourceEnvironment) raw claim count handle outcome).Proof) :
    claim ≠ raw.sum := refuted.2

def childTerminal (remaining count : Nat) : ExternalTerminal childOwner F G :=
  residualTerminal childOwner (.parameter childTable) remaining count childPoint childValue rfl rfl

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem child_terminal_iff (raw : List F) (claim : F) (count handle : Nat)
    (table : Table F (0 + count)) (decoded : ofList? (0 + count) raw = some table)
    (point : List F) (value : F) :
    (childTerminal (G := G) 0 count).Holds SumcheckSourceVerifier.childContext
      (childBoundary raw claim count handle
        (.returned (SumcheckVerifierPrelude.reduceResults (some point, some value))))
      (childAssignments raw claim count handle) ↔ Residual 0 count table point value := by
  refine (residual_terminal_iff (.parameter childTable) 0 count childPoint childValue rfl rfl
    _ _ _ raw (by rfl) table decoded).trans ?_
  change (∃ p v, some point = some p ∧ some value = some v ∧ Residual 0 count table p v) ↔ _
  constructor
  · rintro ⟨p, v, hp, hv, truth⟩
    cases Option.some.inj hp
    cases Option.some.inj hv
    exact truth
  · intro truth
    exact ⟨point, value, rfl, rfl, truth⟩

variable {reductionEnvironment : RelationEnvironment SumcheckReduceViews.imported F G}

def reductionRootInput (proverValues : Option (List F)) (proverDimension : Option Nat)
    (claim : F) (count handle : Nat) : ComponentInput reductionRoot F G :=
  ⟨{}, 1, SumcheckReduceVerifier.reduceRootInputs proverValues proverDimension
    (some claim) (some count) (some handle)⟩

def reductionCallEnvironment (claim : F) (count handle : Nat) :
    Environment (Component (assignment F G))
      [vector, .index, .index, .index, vector, .index, scalar, .index,
        .service "random.bls12-381.fr/0"] :=
  (Values.cons none (.cons none (.cons none (.cons (some 1) (.cons none (.cons none
    (.cons (some claim) (.cons (some count) (.cons (some handle) .nil))))))))).get

def reductionBoundary (claim : F) (count handle : Nat) (outcome) :=
  reductionCall.boundaryOfOutcome {} 1 (reductionCallEnvironment (G := G) claim count handle) outcome

def reductionSelection : SelectedApplication reductionOwner F G reductionEnvironment :=
  reductionContract.select (.subject ⟨0, by decide⟩)

def reductionUse (raw : List F) (dimension : Nat) (claim : F) (count handle : Nat) (outcome) :
    ApplicationUse (reductionSelection (G := G) (reductionEnvironment := reductionEnvironment))
      (ProtocolContext.enter {} "s3" [0, 1]) (reductionBoundary claim count handle outcome)
      (fixedReduction (invocation := reductionCall.childInvocation rootInvocation (fun index => Fin.elim0 index)) raw dimension) where
  arguments := .cons raw (.cons dimension (.cons 1 (.cons claim .nil)))
  read := reduction_application_read raw dimension claim _ _
    (reductionCall.boundaryOfOutcome_input {} 1 _ outcome reductionClaim
      (.there (.there (.there .here))) rfl rfl)

def reductionRefutation (raw : List F) (dimension : Nat) (claim : F) (count handle : Nat) :=
  ContractRequest.relation (reductionSelection (G := G) (reductionEnvironment := reductionEnvironment))
    (reductionUse raw dimension claim count handle (.stopped .incomplete)) .refutation

theorem reduction_false_sum (raw : List F) (dimension : Nat) (claim : F) (count handle : Nat)
    (refuted : (reductionRefutation (G := G) (reductionEnvironment := reductionEnvironment)
      raw dimension claim count handle).Meaning)
    (translation : (reductionUse (G := G) (reductionEnvironment := reductionEnvironment)
      raw dimension claim count handle (.stopped .incomplete)).Translation) : claim ≠ raw.sum := by
  intro equality
  exact refuted (((reductionUse raw dimension claim count handle (.stopped .incomplete)).equivalence translation).mpr equality)

def wrapperTerminal (raw : List F) (remaining count : Nat) : ExternalTerminal reductionRoot F G :=
  residualTerminal reductionRoot (.supplied raw) remaining count residualRootPoint residualRootValue rfl rfl

def wrapperAssignments : LogicalAssignments (assignment F G) reductionRoot rootInvocation :=
  ⟨fun _ _ => none, fun _ _ => none⟩

def wrapperRequest (raw : List F) (remaining count : Nat)
    (boundary : ContractBoundaryValues reductionRoot F G) :
    ContractRequest reductionRoot F G reductionEnvironment rootInvocation {} boundary wrapperAssignments :=
  .terminal (wrapperTerminal raw remaining count)

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem wrapper_terminal_iff (raw : List F) (remaining count : Nat)
    (table : Table F (remaining + count)) (decoded : ofList? (remaining + count) raw = some table)
    (proverValues : Option (List F)) (proverDimension : Option Nat) (claim : F) (handle : Nat)
    (outputs : Values (Component (assignment F G)) reductionRoot.protocol.outputs) :
    (wrapperTerminal raw remaining count).Holds {}
      ((reductionRootInput proverValues proverDimension claim count handle).boundary (.returned outputs))
      (wrapperAssignments (G := G)) ↔
      match outputs.get (.there (.there .here)), outputs.get (.there (.there (.there .here))) with
      | some point, some value => Residual remaining count table point value
      | _, _ => False := by
  refine (residual_terminal_iff (.supplied raw) remaining count residualRootPoint residualRootValue rfl rfl
    _ _ _ raw rfl table decoded).trans ?_
  change (∃ p v, outputs.get (.there (.there .here)) = some p ∧
    outputs.get (.there (.there (.there .here))) = some v ∧ Residual remaining count table p v) ↔ _
  generalize outputs.get (.there (.there .here)) = op
  generalize outputs.get (.there (.there (.there .here))) = ov
  cases op <;> cases ov <;> simp

end ZkcExamples.Structured.SumcheckContractRequests
