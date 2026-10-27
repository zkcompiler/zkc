module

public import ZkcExamples.Construction.TableMembershipArtifacts
public import ZkcExamples.Structured.TableContractBindings
public import Zkc.Construction.DomainBinding
public import Zkc.Construction.DomainViewLaws
public import Zkc.Construction.AuthoredPairExecution
public import Zkc.Construction.RetainedTarget

@[expose] public section

/-! The actual deterministic CheckMembership construction. The source target,
whole native artifacts and full nominal Process are checked independently.
The laws below retain eager finite-scan exhaustion and every public query field.
They do not assert byte-codec or native-runtime realization. -/
set_option autoImplicit false
set_option smartUnfolding false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
noncomputable section
namespace ZkcExamples.Construction.TableMembership
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured
open TableMembershipBodies TableMembershipViews TableMembershipLaws

abbrev program := TableMembershipViews.program
abbrev imported := TableMembershipViews.imported
abbrev snapshot := TableMembershipData.snapshot
abbrev artifacts := TableMembershipArtifacts.artifacts
abbrev producer := artifacts.producer
abbrev validator := artifacts.validator

def context : Context := Context.plain snapshot.entry ["role00000000", "role00000001"] 0 1

theorem actual_context : exportContext snapshot validator = some context := by kernel_rfl

def selected : AuthoredPair.Selection snapshot :=
  (AuthoredPair.select snapshot artifacts "selected_rows").toOption.get (by decide +kernel)

theorem admitted : AuthoredPair.Admitted imported selected artifacts := ⟨by decide +kernel⟩

def selection : Selection program.payload.entry.outputs :=
  (select imported validator).get (by decide +kernel)

theorem selection_exact : select imported validator = some selection := (Option.some_get _).symm

theorem selection_checked : selection.check imported validator = true := by decide +kernel

def target : RetainedTarget imported validator.policy selection.publics where
  owner := TableContractBindings.membershipOwner
  entry := rfl
  clauseIndex := TableContractBindings.membershipOwner.namedClause "selected_rows"
  target := rfl
  noResidual := rfl
  decision := rfl
  application := TableContractBindings.membershipApplication
  booleanOutput := rfl
  publicTypes := rfl
  publicArity := rfl
  supported := by decide +kernel

theorem selected_target : target.owner.clause target.clauseIndex = selected.target := by kernel_rfl

theorem plain_abi : producer.inputs = [] ∧ producer.outputs = [] ∧
    validator.inputs = [.data vector, .data (.sequence query)] ∧
    validator.outputs = [.data .boolean] ∧ validator.returned = [2] := ⟨rfl, rfl, rfl, rfl, rfl⟩

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev model := ringModel F G
abbrev carriers := uniformCarriers F G

/-- Every raw environment and every reply has the same complete Process view,
including malformed input refusal and the final physical frame. -/
def validatorView : Domain.Binding.Meaning (carriers (F := F) (G := G)) :=
  Domain.View.participant validator.inputs validator.outputs validator.returned
    (Domain.View.sequence
      (Domain.View.helper model program checkMembershipHelper.name [0, 1] [.data .boolean])
      Domain.View.empty)

theorem validator_binding (env : Domain.Environment (carriers (F := F) (G := G))) :
    Domain.participant model program context validator env = validatorView env := by
  apply Domain.Correspondence.participant
  exact Domain.Correspondence.sequence
    (Domain.Correspondence.helper _ _ _) Domain.Correspondence.empty

/-- Reusable whole-process certificate on the exact admitted imported source.
This is a model-level implementation binding, not a security receipt. -/
theorem process_certificate : Zkc.Verification.Certificate imported
    (fun source => Domain.participant (model (F := F) (G := G)) source context validator)
    (fun actual => ∀ env, actual env = validatorView env) :=
  Domain.Binding.certificate imported model context validator validatorView validator_binding

/-- Both property consumers use precisely this one all-answer binding. -/
theorem property_binding (env : Domain.Environment (carriers (F := F) (G := G)))
    (complete sound : PIR.Process (Domain.effects carriers) (Domain.Result carriers) → Prop)
    (hc : complete (validatorView env)) (hs : sound (validatorView env)) :
    complete (Domain.participant model program context validator env) ∧
      sound (Domain.participant model program context validator env) :=
  Domain.Binding.both validator_binding complete sound env hc hs

/-- Source helpers are the exact retained closure, including realizations. -/
theorem check_equation (table : List F) (queries : List (QueryValue F)) :
    invoke (meanings (F := F) (G := G)) checkMembershipHelper (.cons table (.cons queries .nil)) =
      if Admissible table queries then
        .done (.cons (PIR.Relation.Table.membership table (queries.map decodeQuery)) .nil)
      else .halt .exhausted := by
  rw [Associations.checkMembership_association.invoke unit.linked]
  change (invoke (meanings (F := F) (G := G)) realizationHelper
    (.cons table (.cons queries .nil))).bind _ = _
  rw [Associations.realization_association.invoke unit.linked]
  change ((invoke (meanings (F := F) (G := G)) membershipHelper
    (.cons table (.cons queries .nil))).bind _).bind _ = _
  rw [membership_equation]
  split <;> rfl

/-- The runtime ABI packs the actual nominal product, with both fields even
when `active` is false. No per-protocol flattening or transcript is present. -/
def inputs (table : List F) (queries : List (QueryValue F)) : Domain.Environment (carriers (F := F) (G := G)) :=
  [.data ⟨vector, by decide, table⟩, .data ⟨.sequence query, by decide, queries⟩]

theorem inputs_encoded (table : List F) (queries : List (QueryValue F)) :
    Domain.encodeValues (Values.cons table (Values.cons queries
      Values.nil) : Values (assignment F G) checkMembershipHelper.inputs) = some (inputs table queries) := by
  kernel_rfl

/-- Exact actual helper outcome on the aggregate ABI, including exhaustion. -/
theorem helper_equation (table : List F) (queries : List (QueryValue F)) :
    Domain.callHelper (model (F := F) (G := G)) program checkMembershipHelper.name [.data .boolean] (inputs table queries) =
      if Admissible table queries then
        .returned [.data (.boolean (PIR.Relation.Table.membership table (queries.map decodeQuery)))]
      else .stopped .exhausted := by
  have invoked : invoke (Domain.helperTable (model (F := F) (G := G)) program) checkMembershipHelper
      (.cons table (.cons queries .nil)) =
      if Admissible table queries then
        .done (.cons (PIR.Relation.Table.membership table (queries.map decodeQuery)) .nil)
      else .halt .exhausted := by
    rw [Domain.Binding.helperTable_ringModel]
    exact check_equation table queries
  have law := Domain.Binding.callHelper_of_invoke_not_refused (model (F := F) (G := G)) program checkMembershipHelper
    (.cons table (.cons queries .nil)) _ invoked (by split <;> intro impossible <;> cases impossible)
    (inputs (G := G) table queries) (inputs_encoded (G := G) table queries)
  change Domain.callHelper _ _ _ [.data .boolean] _ = _ at law
  by_cases bounded : Admissible table queries
  · rw [ite_eq_left bounded] at law ⊢
    exact law
  · rw [ite_eq_right bounded] at law ⊢
    exact law

/-- The full actual validator Process, with pre/post physical checkpoints and
all returns. No proof or oracle behavior is assumed by this equation. -/
theorem validator_equation (table : List F) (queries : List (QueryValue F)) :
    Domain.participant (model (F := F) (G := G)) program context validator (inputs table queries) =
      if Admissible table queries then
        let decision := PIR.Relation.Table.membership table (queries.map decodeQuery)
        let final := inputs table queries ++ [.data (.boolean decision)]
        .call (.checkpoint (inputs table queries)) (fun _ =>
          .call (.checkpoint (inputs table queries)) (fun _ =>
            .call (.checkpoint final) (fun _ => .done ⟨[.data (.boolean decision)], final⟩)))
      else .call (.checkpoint (inputs table queries)) (fun _ =>
        .call (.checkpoint (inputs table queries)) (fun _ => .halt .exhausted)) := by
  have readInputs : Domain.read (inputs (G := G) table queries) [0, 1] =
      some (inputs table queries) := by kernel_rfl
  have shape : Domain.sortsMatch validator.inputs (inputs (G := G) table queries) = true := by kernel_rfl
  have head : Domain.View.helper (model (F := F) (G := G)) program checkMembershipHelper.name
      [0, 1] [.data .boolean] (inputs table queries) =
      if Admissible table queries then
        .done (inputs table queries ++ [.data (.boolean
          (PIR.Relation.Table.membership table (queries.map decodeQuery)))])
      else .halt .exhausted := by
    unfold Domain.View.helper
    rw [readInputs]
    change (match Domain.callHelper (model (F := F) (G := G)) program checkMembershipHelper.name
      [.data .boolean] (inputs table queries) with
      | .returned results => Domain.View.append [.data .boolean] (inputs table queries) results
      | .stopped reason => .halt reason) = _
    rw [helper_equation]
    by_cases bounded : Admissible table queries
    · simp only [ite_eq_left bounded]
      exact Domain.View.append_eq _ _ _ (by kernel_rfl)
    · simp only [ite_eq_right bounded]
  by_cases bounded : Admissible table queries
  · rw [ite_eq_left bounded] at head ⊢
    rw [validator_binding]
    unfold validatorView Domain.View.participant
    simp only [shape, ↓reduceIte, Domain.View.sequence]
    rw [head]
    kernel_rfl
  · rw [ite_eq_right bounded] at head ⊢
    rw [validator_binding]
    unfold validatorView Domain.View.participant
    simp only [shape, ↓reduceIte, Domain.View.sequence]
    rw [head]
    kernel_rfl

/-- Runtime execution returns this complete frame, without a transcript slot. -/
def result (table : List F) (queries : List (QueryValue F)) : Domain.Result (carriers (F := F) (G := G)) :=
  let decision := PIR.Relation.Table.membership table (queries.map decodeQuery)
  ⟨[.data (.boolean decision)], inputs table queries ++ [.data (.boolean decision)]⟩

theorem validate_equation {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    (table : List F) (queries : List (QueryValue F)) (proof : Domain.Proof carriers)
    (oracle : Domain.Oracle m carriers S) (state : S) :
    Domain.validate (model (F := F) (G := G)) program context validator (inputs table queries)
      proof oracle state =
      if Admissible table queries then
        pure ⟨.returned (result table queries), ⟨(result table queries).environment, proof, state⟩, []⟩
      else pure ⟨.stopped .exhausted, ⟨inputs table queries, proof, state⟩, []⟩ := by
  unfold Domain.validate
  rw [validator_equation]
  by_cases bounded : Admissible table queries
  · simp only [ite_eq_left bounded]
    rw [Domain.validator_eq_direct]
    rfl
  · simp only [ite_eq_right bounded]
    rw [Domain.validator_eq_direct]
    rfl

/-- There is no prover action or transcript on the deterministic table path. -/
theorem producer_equation :
    Domain.participant (model (F := F) (G := G)) program context producer [] =
      .call (.checkpoint []) (fun _ => .done ⟨[], []⟩) := by kernel_rfl

set_option smartUnfolding true in
theorem produce_equation {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    (oracle : Domain.Oracle m (carriers (F := F) (G := G)) S) (state : S) :
    Domain.produce model program context producer [] oracle state =
      pure ⟨.returned ⟨[], []⟩, ⟨[], [], state⟩, []⟩ := by
  unfold Domain.produce
  rw [producer_equation]
  simp only [Domain.run, PIR.Process.runM, Domain.handler, pure_bind, PIR.Execution.followM]
  rfl

theorem pair_equation {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    (table : List F) (queries : List (QueryValue F))
    (oracle : Domain.Oracle m carriers S) (state : S) :
    Domain.executePair (model (F := F) (G := G)) program context producer validator [] (inputs table queries)
      oracle state =
      if Admissible table queries then
        pure ⟨⟨.returned ⟨[], []⟩, ⟨[], [], state⟩, []⟩,
          some ⟨.returned (result table queries), ⟨(result table queries).environment, [], state⟩, []⟩⟩
      else pure ⟨⟨.returned ⟨[], []⟩, ⟨[], [], state⟩, []⟩,
          some ⟨.stopped .exhausted, ⟨inputs table queries, [], state⟩, []⟩⟩ := by
  unfold Domain.executePair
  rw [produce_equation]
  simp only [pure_bind]
  rw [validate_equation]
  by_cases bounded : Admissible table queries
  · simp only [ite_eq_left bounded, pure_bind]
  · simp only [ite_eq_right bounded, pure_bind]

def statement (table : List F) (queries : List (QueryValue F)) : Values (assignment F G) selection.publics :=
  .cons table (.cons queries .nil)

theorem target_arguments (table : List F) (queries : List (QueryValue F))
    (witness : target.Witness F G) :
    target.arguments (statement table queries) witness = some (.cons table (.cons queries .nil)) := by
  kernel_rfl

/-- Truth of the exact retained target includes successful bounded formula
execution. There is no weakened false-only relation or erased inactive value. -/
theorem target_holds_iff (table : List F) (queries : List (QueryValue F))
    (witness : target.Witness F G) :
    target.Holds TableContractBindings.membershipFormula (statement table queries) witness ↔
      Admissible table queries ∧ PIR.Relation.Table.membership table (queries.map decodeQuery) = true := by
  rw [target.holds_iff_of_arguments TableContractBindings.membershipFormula (statement table queries) witness
    (.cons table (.cons queries .nil)) (target_arguments table queries witness)]
  change TableContractBindings.membershipFormula.invokeRelation (.cons table (.cons queries .nil)) =
    .done (.cons true .nil) ↔ _
  rw [TableContractBindings.membership_formula_equation]
  by_cases bounded : Admissible table queries
  · rw [ite_eq_left bounded]
    cases decision : PIR.Relation.Table.membership table (queries.map decodeQuery) with
    | false =>
        constructor
        · intro impossible
          have values := PIR.Process.done.inj impossible
          have wrong : false = true := congrArg (fun values => values.get .here) values
          cases wrong
        · intro wrong
          cases wrong.2
    | true => exact ⟨fun _ => ⟨bounded, rfl⟩, fun _ => rfl⟩
  · rw [ite_eq_right bounded]
    constructor
    · intro impossible; cases impossible
    · intro wrong; exact False.elim (bounded wrong.1)

/-- Deterministic false-input rejection holds under every reply at every
checkpoint. An empty charge schedule is not used as a rejection premise. -/
theorem false_input_rejected (table : List F) (queries : List (QueryValue F))
    (falseInput : target.FalseStatement (G := G) TableContractBindings.membershipFormula (statement table queries)) :
    PIR.Yields (fun output => Domain.acceptanceAt 0 output.values ≠ some true)
      (Domain.participant (model (F := F) (G := G)) program context validator (inputs table queries)) := by
  rw [validator_equation]
  by_cases bounded : Admissible table queries
  · rw [ite_eq_left bounded]
    intro _ _ _ accepted
    have decision : PIR.Relation.Table.membership table (queries.map decodeQuery) = true := by
      simpa only [Domain.acceptanceAt, List.getElem?_cons_zero, Option.some.injEq] using accepted
    exact falseInput ⟨fun _ _ => none, (target_holds_iff table queries _).mpr ⟨bounded, decision⟩⟩
  · rw [ite_eq_right bounded]
    intro _ _
    trivial

/-- Actual complete paired execution for every true retained target. The
producer succeeds, no proof is left, and the original Boolean output is kept. -/
theorem completeness {S : Type} (table : List F) (queries : List (QueryValue F))
    (witness : target.Witness F G) (truth : target.Holds TableContractBindings.membershipFormula (statement table queries) witness)
    (oracle : Domain.Oracle Id carriers S) (state : S) :
    Domain.PairExecution.Success 0
      (Domain.executePair (m := Id) (model (F := F) (G := G)) program context producer validator [] (inputs table queries)
        oracle state) := by
  obtain ⟨bounded, decision⟩ := (target_holds_iff table queries witness).mp truth
  rw [pair_equation, ite_eq_left bounded]
  refine ⟨⟨[], []⟩, _, result table queries, rfl, rfl, rfl, rfl, ?_⟩
  change some (PIR.Relation.Table.membership table (queries.map decodeQuery)) = some true
  rw [decision]

/-- Preparation uses the same actual source tuple for both participants. -/
theorem preparation (table : List F) (queries : List (QueryValue F)) (history : Domain.History carriers) :
    AuthoredPair.prepare imported selected (model (F := F) (G := G))
      (.cons table (.cons queries .nil)) history = some ([], inputs table queries) := by kernel_rfl

/-- The public pair runner uses the admitted artifacts and the actual original
input tuple. Its preparation adds no transcript even when a history is supplied. -/
theorem admitted_execution {m : Type → Type} [Monad m] {S : Type}
    (table : List F) (queries : List (QueryValue F)) (history : Domain.History carriers)
    (oracle : Domain.Oracle m carriers S) (state : S) :
    AuthoredPair.execute imported selected (model (F := F) (G := G))
      (.cons table (.cons queries .nil)) history oracle state =
      Domain.executePair model program context producer validator [] (inputs table queries) oracle state := by
  kernel_rfl

theorem admitted_completeness {S : Type} (table : List F) (queries : List (QueryValue F))
    (witness : target.Witness F G) (truth : target.Holds TableContractBindings.membershipFormula (statement table queries) witness)
    (history : Domain.History carriers) (oracle : Domain.Oracle Id carriers S) (state : S) :
    Domain.PairExecution.Success 0
      (AuthoredPair.execute (m := Id) imported selected (model (F := F) (G := G))
        (.cons table (.cons queries .nil)) history oracle state) := by
  rw [admitted_execution]
  exact completeness table queries witness truth oracle state

/-- Completeness has an actual related input. Empty queries legitimately skip
all table scans, as specified by the existing eager finite computation law. -/
theorem related_input_exists : ∃ witness : target.Witness F G,
    target.Holds TableContractBindings.membershipFormula (statement [] []) witness := by
  refine ⟨fun _ _ => none, (target_holds_iff [] [] _).mpr ?_⟩
  refine ⟨?_, rfl⟩
  constructor
  · change 0 < indexLimit
    decide
  · exact Or.inl rfl

/-- Nonvacuity also holds with a selected row and a nonempty table. -/
theorem related_nonempty_input_exists : ∃ witness : target.Witness F G,
    target.Holds TableContractBindings.membershipFormula (statement [0] [(true, (0, ()))]) witness := by
  refine ⟨fun _ _ => none, (target_holds_iff _ _ _).mpr ⟨?_, ?_⟩⟩
  · exact ⟨by change 1 < indexLimit; decide, Or.inr (by change 1 < indexLimit; decide)⟩
  · simp [PIR.Relation.Table.membership, PIR.Relation.Table.contains, decodeQuery]

/-- The mathematical selected-membership target agrees with the retained
formula on its explicit operational domain. The mathematical target is not
redefined to include resource admission. -/
theorem target_agreement (table : List F) (queries : List (QueryValue F))
    (bounded : Admissible table queries) (witness : target.Witness F G) :
    target.Holds TableContractBindings.membershipFormula (statement table queries) witness ↔
      PIR.Relation.Table.Membership table (queries.map decodeQuery) := by
  rw [target_holds_iff]
  exact ⟨fun truth => (PIR.Relation.Table.membership_exact _ _).mp truth.2,
    fun truth => ⟨bounded, (PIR.Relation.Table.membership_exact _ _).mpr truth⟩⟩

theorem membership_completeness {S : Type} (table : List F) (queries : List (QueryValue F))
    (bounded : Admissible table queries)
    (truth : PIR.Relation.Table.Membership table (queries.map decodeQuery))
    (history : Domain.History carriers) (oracle : Domain.Oracle Id carriers S) (state : S) :
    Domain.PairExecution.Success 0
      (AuthoredPair.execute (m := Id) imported selected (model (F := F) (G := G))
        (.cons table (.cons queries .nil)) history oracle state) := by
  let witness : target.Witness F G := fun _ _ => none
  exact admitted_completeness table queries witness ((target_agreement table queries bounded witness).mpr truth)
    history oracle state

/-- Mathematical false inputs reject even when resource admission fails. -/
theorem membership_false_rejected (table : List F) (queries : List (QueryValue F))
    (falseInput : ¬ PIR.Relation.Table.Membership table (queries.map decodeQuery)) :
    PIR.Yields (fun output => Domain.acceptanceAt 0 output.values ≠ some true)
      (Domain.participant (model (F := F) (G := G)) program context validator (inputs table queries)) := by
  apply false_input_rejected
  rintro ⟨witness, truth⟩
  obtain ⟨bounded, _⟩ := (target_holds_iff table queries witness).mp truth
  exact falseInput ((target_agreement table queries bounded witness).mp truth)

/-- A forged public challenge is refused by the actual plain construction
checker, even if the attacker supplies a transcript-looking instruction. -/
theorem forged_challenge_refused (template : Template) :
    check context { validator with instructions :=
      [⟨.challenge "" "koala-bear" template, [0, 1], [.data (.field "koala-bear")], []⟩] } =
      .error "construction-plain-challenge" := by kernel_rfl

end ZkcExamples.Construction.TableMembership
