import Zkc.Construction.ConnectionOutputs
import Zkc.Construction.ConnectionRouting

/-! Negative controls for the connection's meaning, before certificate search.
All examples are carrier-polymorphic; numeric host values do not identify
nominal domains. These are semantic boundary tests, not security claims. -/
set_option autoImplicit false
noncomputable section
namespace Tests.ConnectionContracts
open Zkc.Source Zkc.Source.Structured Zkc.Construction Original

private def signature : ProtocolSignature :=
  ⟨"Root", ["P", "V"], [], [.boolean, .index], [], [[1], [1]]⟩
private def context : Context := Context.plain "Root" ["P", "V"] 0 1
private def policy : Policy :=
  ⟨"Root", "P", "V", 0, "", [], [], [], "fixture", "fixture"⟩
private def artifact : Participant where
  source := "fixture"
  candidate := "fixture"
  symbol := "validator"
  policy := policy
  inputs := []
  outputs := [.data .boolean, .data .index]
  instructions := []
  returned := [0, 1]

variable {carriers : Carriers}
private def source (value : Nat) : Values (Component carriers.Value) signature.outputs × State carriers :=
  ⟨.cons (some true) (.cons (some value) .nil), {}⟩
private def target (value : Nat) : Domain.Result carriers :=
  let values := [.data (.boolean true), .data (.index value)]
  ⟨values, values⟩

private theorem complete (value : Nat) :
    CompleteReturns signature context 1 artifact (source value) (target (carriers := carriers) value) := by
  constructor
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · rfl
  · rfl
  · rfl

-- Changing a non-Boolean output preserves acceptance but violates the contract.
example (expected changed : Nat) (different : expected ≠ changed) :
    ¬ CompleteReturns signature context 1 artifact (source expected)
      (target (carriers := carriers) changed) := by
  intro related
  have same := (complete (carriers := carriers) expected).values_unique related
  have decoded := congrArg (fun values => (values[1]?).bind (Domain.Value.decode .index)) same
  exact different (Option.some.inj decoded)

-- An extra physical output is not an unconstrained auxiliary value.
example (value : Nat) :
    ¬ CompleteReturns signature context 1 artifact (source value)
      { target (carriers := carriers) value with
        values := (target value).values ++ [.data (.boolean true)] } := by
  intro related
  have impossible : (3 : Nat) = 2 := related.arity
  contradiction

-- A hidden role component cannot be silently exported or forgotten as present.
example (value : Nat) :
    roleOutputValues (carriers := carriers) 0 signature.outputScopes (source value).1 = none := rfl

-- Reaching the root return with an unclosed source repeat is rejected.
example (value : Nat) :
    ¬ CompleteReturns signature context 1 artifact
      ((source (carriers := carriers) value).1, ⟨[⟨"outer", 2⟩], []⟩) (target value) := by
  intro related
  have impossible := related.frames
  contradiction

/-- A producer's two vector outputs have the same nominal sort. Swapping
them still violates the complete source return, independently of acceptance. -/
private def producerSignature : ProtocolSignature :=
  ⟨"Producer", ["P", "V"], [], [.vector "f", .index, .index, .vector "f"], [],
    [[0], [0], [0], [0]]⟩
private def producerArtifact : Participant :=
  { artifact with
    symbol := "producer"
    outputs := [.data (.vector "f"), .data .index, .data .index, .data (.vector "f")]
    returned := [0, 1, 2, 3] }
private def producerSource (raw point : List (carriers.Field "f")) (dimension width : Nat) :
    Values (Component carriers.Value) producerSignature.outputs × State carriers :=
  ⟨.cons (some raw) (.cons (some dimension) (.cons (some width) (.cons (some point) .nil))), {}⟩
private def producerTarget (raw point : List (carriers.Field "f")) (dimension width : Nat) :
    Domain.Result carriers :=
  let values := [.data (.vector "f" raw), .data (.index dimension),
    .data (.index width), .data (.vector "f" point)]
  ⟨values, values⟩

private theorem producerComplete (raw point : List (carriers.Field "f")) (dimension width : Nat) :
    CompleteReturns producerSignature context 0 producerArtifact
      (producerSource raw point dimension width) (producerTarget raw point dimension width) := by
  constructor
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · rfl
  · rfl
  · rfl

theorem wrong_producer_slot (raw point : List (carriers.Field "f")) (dimension width : Nat)
    (different : raw ≠ point) :
    ¬ CompleteReturns producerSignature context 0 producerArtifact
      (producerSource raw point dimension width) (producerTarget point raw dimension width) := by
  intro related
  have same := (producerComplete raw point dimension width).values_unique related
  have decoded := congrArg (fun values => (values[0]?).bind (Domain.Value.decode (.vector "f"))) same
  exact different (Option.some.inj decoded)

theorem wrong_producer_simulation (raw point : List (carriers.Field "f")) (dimension width : Nat)
    (different : raw ≠ point) :
    ¬ Nonempty (Simulation (carriers := carriers) (CompleteReturns producerSignature context 0 producerArtifact)
      (fun _ _ => True) (.done (producerSource raw point dimension width))
      (.done (producerTarget point raw dimension width))) := by
  rintro ⟨simulation⟩
  cases simulation with
  | done returned => exact wrong_producer_slot raw point dimension width different returned

#print axioms wrong_producer_slot
#print axioms wrong_producer_simulation

private def snapshot : Snapshot where
  source := "sha256:0000000000000000000000000000000000000000000000000000000000000000"
  entry := "Root"
  domains := []
  relations := []
  bindings := []
  definitions := []
  contracts := []
  catalogue := ⟨[], [], []⟩
private def missingRoutes : Routing :=
  ⟨snapshot, context, .validator, 0, [], [], [], []⟩

-- A missing route may make the fold refuse, but cannot satisfy source coverage.
example : IsEmpty (RouteCoverage (carriers := carriers) missingRoutes [] []
    (.call (.action (.receive .boolean "message" 0)) fun value => .done value)) := by
  constructor
  intro covered
  have required := covered.action_required
  obtain ⟨_, origin, found⟩ := required
  change none = some origin at found
  cases found

-- Both symbolic nested coordinates remain in the coverage judgment.
example (outer inner : Nat) :
    RouteCoverage (carriers := carriers) missingRoutes [] []
      (Occurrence.iterations.within "outer" outer
        (Occurrence.iterations.within "inner" inner (.done ()))) :=
  (RouteCoverage.done _ ()).within "inner" inner |>.within "outer" outer

end Tests.ConnectionContracts
