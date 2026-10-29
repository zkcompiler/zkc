module

public import Zkc.Construction.SourceConnection
public import Zkc.Construction.ConnectionOutputSelection
public import Zkc.Construction.Uniform.ScalarObservation
public import Zkc.Source.Structured.CommonAdapter

@[expose] public section

/-! Retained scalar execution transport from the same checked connection as
nominal clients. Common is a derived observation of that source, never an
independent compiler interpretation. No protocol names occur in this bridge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Construction.ScalarConnection
open Zkc.Source Zkc.Source.Structured
open Uniform Uniform.DomainAdapter
attribute [local implicit_reducible] CheckedProtocol.signature
variable {F G : Type}

/-- Erasure is the existing source denotation's generic naturality law. -/
theorem scalar_participant [CommRing F] [DecidableEq F] [AddCommGroup G]
    [Module F G] [DecidableEq G] (program : Program) (self : Nat)
    (inputs : Values (Component (assignment F G)) program.payload.entry.inputs) :
    ((Occurrence.participant (ringModel F G) program self inputs).interpret Occurrence.erase).interpret
      CommonAdapter.project =
      (program.participant F G self inputs).interpret CommonAdapter.project :=
  congrArg (fun process => process.interpret CommonAdapter.project)
    ((Occurrence.participant_erase (ringModel F G) program self inputs).trans
      (Program.participant_eq_participantOn (F := F) (G := G) program self inputs).symm)

/-- Reindex an imported connection by the independently computed canonical ABI.
This avoids reducing the certificate's proof term to inspect its input fields. -/
theorem canonicalize {program : Program} {routing : Original.Routing} {role : Nat}
    {abi expected : Original.InputABI} {artifact : Participant}
    (connection : SourceConnection.Connected program routing role abi artifact)
    (canonical : SourceConnection.canonicalABI program role artifact = .ok expected) :
    SourceConnection.Connected program routing role expected artifact := by
  have same : abi = expected := Except.ok.inj (connection.canonical.symm.trans canonical)
  simpa only [same] using connection

private theorem acceptance_eq (position : Nat) (result : Domain.Result (uniformCarriers F G)) :
    ScalarVerifier.acceptance position result = Domain.acceptanceAt position result.values := by
  unfold ScalarVerifier.acceptance Domain.acceptanceAt
  cases result.values[position]? with
  | none => rfl
  | some value =>
    cases value with
    | transcript | indices => rfl
    | data payload =>
      cases payload with
      | mk ty allowed contents => cases ty <;> rfl

/-- The old scalar observation selects the first public Boolean. This is an
output observation, after full nominal return correspondence is established. -/
theorem acceptance_first (result : Domain.Result (uniformCarriers F G)) :
    ScalarVerifier.acceptance 0 result = SourceProcess.acceptance result.values := by
  unfold ScalarVerifier.acceptance SourceProcess.acceptance
  cases result.values with
  | nil => rfl
  | cons head tail =>
    cases head with
    | transcript | indices => rfl
    | data payload =>
      rcases payload with ⟨ty, allowed, value⟩
      cases ty <;> rfl

section Fold
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Full source-return observation of the nominal source fold, with every stop,
reply, malformed proof head, unread suffix and opaque oracle-history prefix. -/
theorem fold_transform {A B : Type} {routing : Original.Routing} {repeated : Bool}
    (mode : routing.mode = .validator) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (noLocal : routing.locals = [])
    {source : PIR.Process (Occurrence.signature (uniformCarriers F G)) A}
    (covered : Original.RouteCoverage routing [] [] source)
    (supported : ScalarSupport.Supported repeated source)
    (project : A → B) (challenge : History F G → m F)
    (initial : History F G) (proof : Proof F G) :
    runK (ScalarProjection.key repeated) initial challenge (Original.fold routing source ⟨[], []⟩)
      proof (fun result unread => pure (.returned (project result.1), unread)) =
    transform routing.context challenge
      (((source.interpret Occurrence.erase).interpret CommonAdapter.project).bind
        fun value => .done (project value)) initial proof := by
  rw [← ScalarProjection.runK_operations]
  have observed := Classical.choice (ScalarObservation.simulation mode replacement profile noLocal covered supported
    (by intro _; rfl) [])
  have transported := LoopedSourceProcess.simulation_runK observed SourceProcess.legacyOrigin initial challenge proof
    (fun scalar unread => pure (.returned (project scalar.1), unread))
    (fun nominal unread => pure (.returned (project nominal.1), unread))
    (by intro scalar nominal unread related; rw [related.1])
  exact transported.symm.trans
    (SourceProcess.sourceView_transform_map routing.context challenge _ project initial proof)

end Fold

section Connected
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {program : Program} {routing : Original.Routing} {role : Nat}
  {abi : Original.InputABI} {artifact : Participant}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

omit [LawfulMonad m] in
/-- Generic full-return transport consumes Connected.simulation directly.
The consumer must respect its complete return contract; no input or runtime
restrictions are introduced, and the actual artifact fixes the key mapping. -/
theorem runK {R : Type}
    (connection : SourceConnection.Connected program routing role abi artifact)
    (physical : Domain.Environment (uniformCarriers F G))
    (challenge : History F G → m F) (initial : History F G) (proof : Proof F G)
    (sourceNext : (Values (Component (assignment F G)) program.payload.entry.outputs ×
      Original.State (uniformCarriers F G)) → Proof F G → m (PIR.Outcome R × Proof F G))
    (targetNext : Domain.Result (uniformCarriers F G) → Proof F G → m (PIR.Outcome R × Proof F G))
    (agree : ∀ source target unread,
      Original.CompleteReturns program.payload.entry.signature routing.context role artifact source target →
      sourceNext source unread = targetNext target unread) :
    DomainAdapter.runK (ScalarVerifier.origin artifact) initial challenge
      (SourceConnection.source program routing role abi artifact (ringModel F G) physical) proof sourceNext =
    DomainAdapter.runK (ScalarVerifier.origin artifact) initial challenge
      (Domain.participant (ringModel F G) program routing.context artifact physical) proof targetNext :=
  LoopedSourceProcess.simulation_runK (Classical.choice (connection.simulation (ringModel F G) physical))
    (ScalarVerifier.origin artifact) initial challenge proof sourceNext targetNext agree

/-- The selected retained scalar equation is a consequence of the complete
checked connection, its independent coverage, and scalar-fragment support.
All mechanical source/artifact/routing matching remains in Connected. -/
theorem transform
    (connection : SourceConnection.Connected program routing role abi artifact)
    (mode : routing.mode = .validator) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (noLocal : routing.locals = [])
    (physical : Domain.Environment (uniformCarriers F G))
    (inputs : Values (Component (assignment F G)) program.payload.entry.inputs)
    (decoded : abi.read physical program.payload.entry.inputs = some inputs)
    (emptyHistory : ConnectionInputs.inputHistory routing.context artifact.inputs physical = [])
    (supported : ScalarSupport.Supported (ScalarProjection.iterations artifact)
      (Occurrence.participant (ringModel F G) program role inputs))
    (output : Var program.payload.entry.outputs .boolean)
    (visible : inScope role program.payload.entry.outputScopes output = true)
    (challenge : History F G → m F) (initial : History F G) (proof : Proof F G) :
    DomainAdapter.runK (ScalarVerifier.origin artifact) initial challenge
      (Domain.participant (ringModel F G) program routing.context artifact physical) proof
      (fun result unread => pure (.returned
        (ScalarVerifier.acceptance (scopePosition role program.payload.entry.outputScopes output) result), unread)) =
    Zkc.Construction.transform routing.context challenge
      (((program.participant F G role inputs).bind fun outputs => .done (outputs.get output)).interpret
        CommonAdapter.project) initial proof := by
  have transport := runK connection physical challenge initial proof
    (fun source unread => pure (.returned (source.1.get output), unread))
    (fun target unread => pure (.returned
      (ScalarVerifier.acceptance (scopePosition role program.payload.entry.outputScopes output) target), unread))
    (by
      intro source target unread related
      have same : source.1.get output = ScalarVerifier.acceptance
          (scopePosition role program.payload.entry.outputScopes output) target := by
        simpa only [acceptance_eq] using
          ConnectionOutputSelection.acceptance_agree output visible related
      rw [same])
  rw [← transport, connection.source_eq_fold]
  have occurrence : SourceConnection.occurrence program role abi (ringModel F G) physical =
      Occurrence.participant (ringModel F G) program role inputs := by
    simp only [SourceConnection.occurrence, decoded]
  rw [occurrence]
  have covered := Classical.choice (connection.coverage (ringModel F G) physical)
  rw [occurrence] at covered
  have initialState : SourceConnection.initial routing artifact physical = ⟨[], []⟩ := by
    simp only [SourceConnection.initial, emptyHistory]
  rw [initialState, ← ScalarProjection.key_artifact]
  have folded := fold_transform mode replacement profile noLocal covered supported
    (fun outputs => outputs.get output) challenge initial proof
  rw [scalar_participant] at folded
  simpa only [PIR.Process.interpret_bind, PIR.Process.interpret] using folded

end Connected
end Zkc.Construction.ScalarConnection
