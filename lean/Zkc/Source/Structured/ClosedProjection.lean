module

public import Zkc.Source.Structured.ClosedProfile
public import Zkc.Source.Structured.OpenLaws
public import Zkc.Source.Structured.Interpretation

@[expose] public section

/-! A syntactic closed-root projection has a semantic equation over the same
values and site observations. Site marks and stops are retained. This does not
change the scalar or group value assignment. -/

namespace Zkc.Source.Structured

/-- Calculations have no nested callbacks in either operation family. -/
def calculationBodies (op : Op) (allowed : op.isCalculation = true) :
    Regions dialect op.regions := by
  rw [op.calculation_no_regions allowed]
  exact .nil

/-- A typed witness of the actual closed-root syntax transformation. It contains
only constructor evidence, never a premise asserting the desired meaning. -/
inductive ClosedProjection : {inputs outputs : List Ty} →
    Region protocolDialect inputs outputs → Region dialect inputs outputs → Prop where
  | ret {inputs outputs} (refs : Operands inputs outputs) : ClosedProjection (.ret refs) (.ret refs)
  | calculate {inputs outputs} (op : Op) (allowed : op.isCalculation = true)
      (closedValues : op.closedValues = true) (args : Operands inputs op.arguments)
      {source : Region protocolDialect (op.results ++ inputs) outputs}
      {target : Region dialect (op.results ++ inputs) outputs}
      (next : ClosedProjection source target) :
      ClosedProjection (.letOp (.calculate op allowed) args .nil source)
        (.letOp op args (calculationBodies op allowed) target)
  | localCall {inputs outputs} (helper : Helper) (kind : helper.kind = .local)
      (site : String) (args : Operands inputs helper.inputs)
      {source : Region protocolDialect (helper.outputs ++ inputs) outputs}
      {target : Region dialect (helper.outputs ++ inputs) outputs}
      (next : ClosedProjection source target) :
      ClosedProjection (.letOp (.localCall helper kind 0 site) args .nil source)
        (.letOp (.invoke helper) args .nil target)
  | guard {inputs outputs} (site : String) (args : Operands inputs [Ty.boolean])
      {source : Region protocolDialect inputs outputs} {target : Region dialect inputs outputs}
      (next : ClosedProjection source target) :
      ClosedProjection (.letOp (.guard 0 site) args .nil source)
        (.letOp .guard args .nil target)
  | mark {inputs outputs} (site : String) (args : Operands inputs [])
      {source : Region protocolDialect inputs outputs} {target : Region dialect inputs outputs}
      (next : ClosedProjection source target) :
      ClosedProjection (.letOp (.mark site) args .nil source)
        (.letOp (.mark site) args .nil target)
  | bind {inputs mid outputs}
      {sourceBody : Region protocolDialect inputs mid} {targetBody : Region dialect inputs mid}
      {sourceNext : Region protocolDialect (mid ++ inputs) outputs}
      {targetNext : Region dialect (mid ++ inputs) outputs}
      (body : ClosedProjection sourceBody targetBody) (next : ClosedProjection sourceNext targetNext) :
      ClosedProjection (.bind sourceBody sourceNext) (.bind targetBody targetNext)

private theorem calculationBodies_erase (op : Op) (allowed : op.isCalculation = true) :
    (calculationBodies op allowed).erase = .nil := by
  cases op <;> first | rfl | simp [Op.isCalculation] at allowed

/-- The typed relation certifies the very transformation used by closed admission. -/
theorem ClosedProjection.exact {inputs outputs}
    {source : Region protocolDialect inputs outputs} {target : Region dialect inputs outputs}
    (projection : ClosedProjection source target) :
    closedRootTree source.erase = .ok target.erase := by
  induction projection with
  | ret refs => rfl
  | calculate op allowed closedValues args next ih =>
    simp [Region.erase, Regions.erase, closedRootTree, ProtocolOp.closed, closedValues, ih,
      calculationBodies_erase, ProtocolOp.results]
    rfl
  | localCall helper kind site args next ih =>
    simp [Region.erase, Regions.erase, closedRootTree, ProtocolOp.closed, ih, ProtocolOp.results, Op.results]
    rfl
  | guard site args next ih =>
    simp [Region.erase, Regions.erase, closedRootTree, ProtocolOp.closed, ih, ProtocolOp.results, Op.results]
    rfl
  | mark site args next ih =>
    simp [Region.erase, Regions.erase, closedRootTree, ProtocolOp.closed, ih, ProtocolOp.results, Op.results]
    rfl
  | bind body next bodyIH nextIH =>
    simp [Region.erase, closedRootTree, bodyIH, nextIH]
    rfl

/-- Every successful raw projection of a typed protocol body has a typed witness. -/
theorem ClosedProjection.exists_of_exact {inputs outputs}
    (source : Region protocolDialect inputs outputs) (raw : RawRegion Ty Op)
    (projected : closedRootTree source.erase = .ok raw) :
    ∃ target, ClosedProjection source target := by
  induction source using Region.rec (motive_2 := fun _ _ => True) generalizing raw with
  | ret refs => exact ⟨.ret refs, .ret refs⟩
  | stop reason => simp [Region.erase, closedRootTree] at projected
  | letOp op args bodies next bodiesIH nextIH =>
    cases op with
    | calculate op allowed =>
      cases bodies
      by_cases closedValues : op.closedValues = true
      · cases step : closedRootTree next.erase with
        | error error => simp [Region.erase, Regions.erase, closedRootTree, ProtocolOp.closed,
            closedValues, step, Functor.map, Except.map] at projected; cases projected
        | ok tail =>
          obtain ⟨target, relation⟩ := nextIH tail step
          exact ⟨_, .calculate op allowed closedValues args relation⟩
      · simp [Region.erase, Regions.erase, closedRootTree, ProtocolOp.closed, closedValues] at projected; cases projected
    | localCall helper kind owner site =>
      cases bodies
      cases owner with
      | zero =>
        cases step : closedRootTree next.erase with
        | error error => simp [Region.erase, Regions.erase, closedRootTree, ProtocolOp.closed,
            step, Functor.map, Except.map] at projected; cases projected
        | ok tail =>
          obtain ⟨target, relation⟩ := nextIH tail step
          exact ⟨_, .localCall helper kind site args relation⟩
      | succ owner => simp [Region.erase, Regions.erase, closedRootTree, ProtocolOp.closed] at projected; cases projected
    | guard owner site =>
      cases bodies
      cases owner with
      | zero =>
        cases step : closedRootTree next.erase with
        | error error => simp [Region.erase, Regions.erase, closedRootTree, ProtocolOp.closed,
            step, Functor.map, Except.map] at projected; cases projected
        | ok tail =>
          obtain ⟨target, relation⟩ := nextIH tail step
          exact ⟨_, .guard site args relation⟩
      | succ owner => simp [Region.erase, Regions.erase, closedRootTree, ProtocolOp.closed] at projected; cases projected
    | mark site =>
      cases bodies
      cases step : closedRootTree next.erase with
      | error error => simp [Region.erase, Regions.erase, closedRootTree, ProtocolOp.closed,
          step, Functor.map, Except.map] at projected; cases projected
      | ok tail =>
        obtain ⟨target, relation⟩ := nextIH tail step
        exact ⟨_, .mark site args relation⟩
    | «repeat» spec site =>
      cases bodies with
      | cons body rest =>
        simp [Region.erase, Regions.erase, closedRootTree] at projected
    | exchange | restrict | draw | statement | protocolApply =>
      cases bodies
      simp [Region.erase, Regions.erase, closedRootTree, ProtocolOp.closed] at projected; cases projected
  | bind body next bodyIH nextIH =>
    cases first : closedRootTree body.erase with
    | error error => simp [Region.erase, closedRootTree, first] at projected; cases projected
    | ok head =>
      cases second : closedRootTree next.erase with
      | error error => simp [Region.erase, closedRootTree, first, second,
          Functor.map, Except.map] at projected; cases projected
      | ok tail =>
        obtain ⟨targetBody, bodyRelation⟩ := bodyIH head first
        obtain ⟨targetNext, nextRelation⟩ := nextIH tail second
        exact ⟨_, .bind bodyRelation nextRelation⟩
  | nil => trivial
  | cons => trivial

/-- Raw projection and typed formation determine the same closed body. -/
theorem ClosedProjection.of_exact {inputs outputs}
    (source : Region protocolDialect inputs outputs) (target : Region dialect inputs outputs)
    (projected : closedRootTree source.erase = .ok target.erase) :
    ClosedProjection source target := by
  obtain ⟨candidate, relation⟩ := exists_of_exact source target.erase projected
  have erased := Except.ok.inj (relation.exact.symm.trans projected)
  have formed := candidate.elaborate_erase
  rw [erased, target.elaborate_erase] at formed
  have same : target = candidate := Except.ok.inj formed
  rw [same]
  exact relation

/-- Inversion records the exact checked subject, signatures, projected tree and
complete singleton port scopes. No availability-soundness premise is needed. -/
theorem ClosedProgram.projection_data (program : ClosedProgram) :
    program.payload.definitions = program.subject.payload.definitions ∧
    program.payload.entry.inputs = program.subject.payload.entry.inputs ∧
    program.payload.entry.outputs = program.subject.payload.entry.outputs ∧
    closedRootTree program.subject.payload.entry.raw = .ok program.payload.entry.raw ∧
    program.subject.payload.entry.inputScopes =
      List.replicate program.subject.payload.entry.inputs.length [0] ∧
    program.subject.payload.entry.outputScopes =
      List.replicate program.subject.payload.entry.outputs.length [0] := by
  rcases program with ⟨subject, payload, projected⟩
  change payload.definitions = subject.payload.definitions ∧
    payload.entry.inputs = subject.payload.entry.inputs ∧
    payload.entry.outputs = subject.payload.entry.outputs ∧
    closedRootTree subject.payload.entry.raw = .ok payload.entry.raw ∧
    subject.payload.entry.inputScopes = List.replicate subject.payload.entry.inputs.length [0] ∧
    subject.payload.entry.outputScopes = List.replicate subject.payload.entry.outputs.length [0]
  unfold Program.closedPayload at projected
  dsimp only at projected
  split at projected
  · cases projected
  · split at projected
    · cases projected
    · rename_i scopes
      have scopes : subject.payload.entry.inputScopes =
          List.replicate subject.payload.entry.inputs.length [0] ∧
          subject.payload.entry.outputScopes =
          List.replicate subject.payload.entry.outputs.length [0] := by
        simpa only [not_or, not_not] using scopes
      split at projected
      · cases projected
      · cases tree : closedRootTree subject.payload.entry.raw with
        | error error => simp [tree] at projected; cases projected
        | ok raw =>
          simp only [tree] at projected
          dsimp only [Bind.bind, Except.bind] at projected
          split at projected
          · cases projected
          · split at projected
            · cases projected
              exact ⟨rfl, rfl, rfl, rfl, scopes⟩
            · cases projected

/-- The stored closed body, transported only across its checked port equalities. -/
def ClosedProgram.projectedBody (program : ClosedProgram) :
    Region dialect program.subject.payload.entry.inputs program.subject.payload.entry.outputs :=
  program.projection_data.2.1 ▸ program.projection_data.2.2.1 ▸ program.payload.entry.body

private theorem erase_port_transport {inputs outputs ins outs : List Ty}
    (inputEq : inputs = ins) (outputEq : outputs = outs)
    (body : Region dialect inputs outputs) :
    (inputEq ▸ outputEq ▸ body).erase = body.erase := by
  cases inputEq
  cases outputEq
  rfl

theorem ClosedProgram.projectedBody_erase (program : ClosedProgram) :
    program.projectedBody.erase = program.payload.entry.raw := by
  rw [projectedBody, erase_port_transport]
  exact RawRegion.erase_of_elaborate (dialect := dialect) _ program.payload.entry.formed

/-- Closed admission yields the syntactic relation, without any meaning premise. -/
theorem ClosedProgram.root_projection (program : ClosedProgram) :
    ClosedProjection program.subject.payload.entry.body program.projectedBody := by
  apply ClosedProjection.of_exact
  rw [program.projectedBody_erase,
    RawRegion.erase_of_elaborate (dialect := protocolDialect) _ program.subject.payload.entry.formed]
  exact program.projection_data.2.2.2.1

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The projected selected tree contains no retained application reference. -/
theorem ClosedProjection.protocols_empty {inputs outputs}
    {source : Region protocolDialect inputs outputs} {target : Region dialect inputs outputs}
    (projection : ClosedProjection source target) :
    source.erase.operations.flatMap ProtocolOp.protocols = [] := by
  induction projection <;>
    simp_all [Region.erase, Regions.erase, RawRegion.operations, RawRegions.operations,
      ProtocolOp.protocols, List.flatMap_append]
  all_goals assumption

/-- Dormant declarations may contain applies; only this projected tree is independent. -/
theorem ClosedProjection.protocol_table_independent {inputs outputs}
    {source : Region protocolDialect inputs outputs} {target : Region dialect inputs outputs}
    (projection : ClosedProjection source target) (tables : OpenTables F G)
    (left right : ProtocolTable (assignment F G) (observedInterface F G))
    (self : Nat) (context : ProtocolContext := {}) :
    source.denote (participantMeaning tables self left context) =
      source.denote (participantMeaning tables self right context) := by
  apply protocol_region_table_congr
  · intros; rfl
  · intros; rfl
  · intro signature used
    rw [projection.protocols_empty] at used
    cases used

private theorem calculation_present (tables : OpenTables F G) (adequate : tables.Adequate)
    (op : Op) (allowed : op.isCalculation = true) (args : Values (assignment F G) op.arguments) :
    protocolOperation tables 0 (.calculate op allowed) args.present .nil =
      (Evaluation.operation (observedSites F G) tables.closed op args
        ((calculationBodies op allowed).denote (Evaluation.meaning (observedSites F G) tables.closed))).bind
        fun results => .done results.present := by
  have law := Evaluation.componentOperation_adequate (observedSites F G) tables adequate
    op args ((calculationBodies op allowed).denote (Evaluation.meaning (observedSites F G) tables.closed))
  apply Eq.trans ?_ law
  cases op <;> first | rfl | simp [Op.isCalculation] at allowed

set_option backward.isDefEq.respectTransparency false in
/-- All-present root execution agrees with the projected closed body in the
same observed interface. Effects, stops, and reply continuations are preserved. -/
theorem ClosedProjection.denote_present {inputs outputs}
    {source : Region protocolDialect inputs outputs} {target : Region dialect inputs outputs}
    (projection : ClosedProjection source target) (tables : OpenTables F G)
    (adequate : tables.Adequate) (env : Environment (assignment F G) inputs) :
    source.denote (participantMeaning tables 0) (fun ref => some (env ref)) =
      (target.denote (Evaluation.meaning (observedSites F G) tables.closed) env).bind
        fun results => .done results.present := by
  induction projection with
  | ret refs => simp only [Region.denote, Operands.eval_present, PIR.Process.bind]
  | calculate op allowed closedValues args next ih =>
    change (protocolOperation tables 0 (.calculate op allowed)
      (args.eval (fun ref => some (env ref))) .nil).bind _ = _
    rw [show args.eval (fun ref => some (env ref)) = (args.eval env).present from
      Operands.eval_present env args, calculation_present tables adequate]
    simp only [Region.denote, PIR.Process.bind_assoc, PIR.Process.bind, Environment.prepend_present]
    congr 1
    funext values
    exact ih _
  | localCall helper kind site args next ih =>
    change (Participant.owned 0 0 (invoke tables.closed helper)
      (args.eval (fun ref => some (env ref)))).bind _ = _
    rw [show args.eval (fun ref => some (env ref)) = (args.eval env).present from
      Operands.eval_present env args, Participant.owned_present]
    simp only [Region.denote, PIR.Process.bind_assoc, PIR.Process.bind, Environment.prepend_present]
    change (invoke tables.closed helper (args.eval env)).bind _ =
      (invoke tables.closed helper (args.eval env)).bind _
    congr 1
    funext values
    exact ih _
  | guard site args next ih =>
    have operation : ∀ (values : Values (assignment F G) [Ty.boolean]),
        protocolOperation tables 0 (.guard 0 site) values.present .nil =
        (Evaluation.operation (observedSites F G) tables.closed .guard values .nil).bind
          (fun results => .done results.present) := by
      intro values
      cases values with
      | cons condition rest => cases rest; cases condition <;> rfl
    change (protocolOperation tables 0 (.guard 0 site)
      (args.eval (fun ref => some (env ref))) .nil).bind _ = _
    rw [show args.eval (fun ref => some (env ref)) = (args.eval env).present from
      Operands.eval_present env args, operation]
    simp only [Region.denote, PIR.Process.bind_assoc, PIR.Process.bind, Environment.prepend_present]
    congr 1
    funext values
    exact ih _
  | mark site args next ih =>
    cases args
    simp only [Region.denote, participantMeaning, participantMeaningWith, protocolOperationWith, Evaluation.meaning,
      Evaluation.operation, observedSites, Operands.eval, Regions.denote, PIR.Process.bind, Environment.prepend, qualify_root]
    congr 1
    funext reply
    exact ih _
  | bind body next bodyIH nextIH =>
    simp only [Region.denote, bodyIH, PIR.Process.bind_assoc, PIR.Process.bind,
      Environment.prepend_present, nextIH]

/-- A complete one-role port scope preserves every ordered component. -/
theorem maskValues_single_role {Value : Ty → Type} {types : List Ty}
    (self : Nat) (values : Values (Component Value) types) :
    maskValues self (List.replicate types.length [self]) values = values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp [maskValues, List.replicate_succ, Participant.restrict, ih]

/-- The explicit checked closed view is semantically tied to the actual subject.
The checked view supplies complete singleton scopes, including for manually
formed Programs. Both sides use identical values, tables and site observations. -/
theorem ClosedProgram.observed_projected (program : ClosedProgram)
    (args : Values (assignment F G) program.subject.payload.entry.inputs) :
    program.subject.observed F G 0 args.present =
      (program.projectedBody.denote
        (Evaluation.meaning (observedSites F G) (program.subject.payload.tables F G).closed)
        args.get).bind fun results => .done results.present := by
  have inputScopes := program.projection_data.2.2.2.2.1
  have outputScopes := program.projection_data.2.2.2.2.2
  have env : @Eq (Environment (Component (assignment F G)) program.subject.payload.entry.inputs)
      args.present.get (fun ref => some (args.get ref)) := by
    funext ty ref
    exact Values.get_present args ref
  rw [program.subject.observed_entry]
  unfold CheckedProtocol.observed CheckedProtocol.denoteWith
  dsimp only [CheckedProtocol.signature]
  simp only [ProtocolContext.mapScopes_root]
  rw [program.root_projection.protocol_table_independent _ _ [], inputScopes, maskValues_single_role, env,
    program.root_projection.denote_present _ program.subject.payload.tables_adequate,
    PIR.Process.bind_assoc]
  simp only [PIR.Process.bind, outputScopes, maskValues_single_role]

/-- Forgetting internal site marks commutes with the checked projection equation.
This retains every participant action and stop; no provider policy is assumed. -/
theorem ClosedProgram.participant_projected (program : ClosedProgram)
    (args : Values (assignment F G) program.subject.payload.entry.inputs) :
    program.subject.participant F G 0 args.present =
      ((program.projectedBody.denote
        (Evaluation.meaning (observedSites F G) (program.subject.payload.tables F G).closed)
        args.get).interpret forgetSites).bind fun results => .done results.present := by
  rw [Program.participant, program.observed_projected args,
    PIR.Process.interpret_bind]
  rfl

/-- Input transport uses the exact checked port equality, with no value conversion. -/
def ClosedProgram.closedInputs (program : ClosedProgram) {Value : Ty → Type}
    (args : Values Value program.subject.payload.entry.inputs) :
    Values Value program.payload.entry.inputs := program.projection_data.2.1.symm ▸ args

/-- Output transport likewise changes only the type-list equality witness. -/
def ClosedProgram.subjectOutputs (program : ClosedProgram) {Value : Ty → Type}
    (results : Values Value program.payload.entry.outputs) :
    Values Value program.subject.payload.entry.outputs := program.projection_data.2.2.1 ▸ results

private theorem denote_port_transport {I : PIR.Signature} {inputs outputs ins outs : List Ty}
    (inputEq : inputs = ins) (outputEq : outputs = outs)
    (body : Region dialect inputs outputs) (meaning : RegionMeaning dialect I)
    (args : Values meaning.Value ins) :
    (inputEq ▸ outputEq ▸ body).denote meaning args.get =
      (body.denote meaning (inputEq.symm ▸ args).get).bind
        fun results => .done (outputEq ▸ results) := by
  cases inputEq
  cases outputEq
  exact (PIR.Process.bind_done _).symm

theorem ClosedProgram.projectedBody_denote (program : ClosedProgram)
    (args : Values (assignment F G) program.subject.payload.entry.inputs) :
    program.projectedBody.denote
      (Evaluation.meaning (observedSites F G) (program.subject.payload.tables F G).closed) args.get =
      (Evaluation.payloadDenote (observedSites F G) program.payload (program.closedInputs args)).bind
        fun results => .done (program.subjectOutputs results) := by
  rw [projectedBody, denote_port_transport]
  unfold Evaluation.payloadDenote Evaluation.payloadMeanings closedInputs subjectOutputs
  rw [program.subject.payload.tables_closed, program.projection_data.1]

/-- The actual participant equals the explicit closed denotation, lifted to the
participant interface, with all results present. F/G and every mathematical
value are identical on both sides; only checked port equalities are transported.
The checked view certifies one-role scopes, including for manually formed Programs. -/
theorem ClosedProgram.participant_eq_denote (program : ClosedProgram)
    (args : Values (assignment F G) program.subject.payload.entry.inputs) :
    program.subject.participant F G 0 args.present =
      ((program.denote F G (program.closedInputs args)).interpret closedLift).bind
        fun results => .done (program.subjectOutputs results).present := by
  have sites : SiteObservations.Interprets (forgetSites (F := F) (G := G))
      (observedSites F G) (.silent (participantInterface F G)) := by
    intro site
    rfl
  have erased := Evaluation.payloadDenote_interpret forgetSites sites program.payload
    (program.closedInputs args)
  have lifted := Evaluation.payloadDenote_interpret
    (closedLift (I := participantInterface F G)) SiteObservations.closed_interpret
    program.payload (program.closedInputs args)
  rw [program.participant_projected args,
    program.projectedBody_denote args, PIR.Process.interpret_bind, erased, ← lifted,
    PIR.Process.bind_assoc]
  rfl

end Zkc.Source.Structured
