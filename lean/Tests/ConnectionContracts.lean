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
