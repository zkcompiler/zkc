module

public import ZkcExamples.Construction.GkrSourceProtocol
public import Zkc.Construction.Uniform.LoopedSourceProcess
public import ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingHelpers

@[expose] public section

/-! The full GKR artifact calls the exact closed source dependency fold.
These certificates preserve returned values, rejection and exhaustion without
shape, dimension, relation-validity or successful-evaluation assumptions. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Construction.GkrDomainHelpers
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform Zkc.Construction.Uniform.LoopedSourceProcess
open ZkcExamples.Structured
open GkrSourceProtocol
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The scalar source retains the same closed helper, including all stops. -/
theorem source_helper (entry : Helper) (arguments : Values (assignment F G) entry.inputs) :
    helper entry arguments =
      ((invoke (closedMeanings program.payload.definitions) entry arguments).interpret
        (closedLift (I := participantInterface F G))).interpret CommonAdapter.project := by
  unfold helper GkrSourceVerifier.closed
  rw [SumcheckVerifierHelpers.closed_invoke_plain]
  rfl

def HelperReturns {tys : List Ty} (encode : Values (assignment F G) tys → Domain.Environment (uniformCarriers F G))
    (env : Domain.Environment (uniformCarriers F G)) (suffix : Domain.History (uniformCarriers F G))
    (source : Values (assignment F G) tys × Domain.History (uniformCarriers F G))
    (actual : Domain.Environment (uniformCarriers F G)) : Prop :=
  ∃ result, source = (result, suffix) ∧ actual = env ++ encode result

/-- Entire helper signature and membership, ABI encoding and every outcome.
The pure source call is not replaced by a mathematical successful case. -/
def helper_binding (entry : Helper)
    (present : entry ∈ program.payload.definitions.map CheckedDefinition.helper)
    (arguments : Values (assignment F G) entry.inputs)
    (encoded : Domain.Environment (uniformCarriers F G))
    (encoding : Domain.encodeValues arguments = some encoded)
    (encode : Values (assignment F G) entry.outputs → Domain.Environment (uniformCarriers F G))
    (outputEncoding : ∀ result, Domain.encodeValues result = some (encode result))
    (outputSorts : ∀ result, Domain.sortsMatch (entry.outputs.map ValueSort.data) (encode result) = true)
    (env : Domain.Environment (uniformCarriers F G)) (refs : List Nat)
    (read : Domain.read env refs = some encoded) (suffix : Domain.History (uniformCarriers F G)) :
    Original.Simulation (HelperReturns encode env suffix) (fun _ _ => True)
      (SourceProcess.sourceView context (helper entry arguments) suffix)
      ((Domain.View.helper (ringModel F G) program entry.name refs
        (entry.outputs.map ValueSort.data) env).interpret operations) := by
  rw [source_helper]
  cases computed : invoke (closedMeanings (F := F) (G := G) program.payload.definitions) entry arguments with
  | done result =>
      have nominal := ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers.call_return program entry arguments
        result computed encoded (encode result) encoding (outputEncoding result)
      simp only [Domain.View.helper, read, nominal, Domain.View.append, outputSorts,
        ite_true, PIR.Process.interpret, SourceProcess.sourceView]
      exact .done ⟨result, rfl, rfl⟩
  | halt reason =>
      have nominal := ZkcExamples.Structured.SumcheckArtifacts.ArtifactBinding.helper_stopped program entry arguments
        present encoded encoding reason computed
      simp only [Domain.View.helper, read, nominal, PIR.Process.interpret, SourceProcess.sourceView]
      exact .halt reason
  | call operation _ => exact nomatch operation

/-- Uniform data encodings for the two result types used by the full root. -/
def fieldResult (result : Values (assignment F G) [.field "bls12-381.fr"]) :
    Domain.Environment (uniformCarriers F G) := [.data (.field "bls12-381.fr" (result.get .here))]
def vectorResult (result : Values (assignment F G) [.vector "bls12-381.fr"]) :
    Domain.Environment (uniformCarriers F G) := [.data (.vector "bls12-381.fr" (result.get .here))]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem fieldEncoding (result : Values (assignment F G) [.field "bls12-381.fr"]) :
    Domain.encodeValues result = some (fieldResult result) := by cases result with | cons value rest => cases rest; rfl
omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem vectorEncoding (result : Values (assignment F G) [.vector "bls12-381.fr"]) :
    Domain.encodeValues result = some (vectorResult result) := by cases result with | cons value rest => cases rest; rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem fieldSorts (result : Values (assignment F G) [.field "bls12-381.fr"]) :
    Domain.sortsMatch [.data (.field "bls12-381.fr")] (fieldResult result) = true := rfl
omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem vectorSorts (result : Values (assignment F G) [.vector "bls12-381.fr"]) :
    Domain.sortsMatch [.data (.vector "bls12-381.fr")] (vectorResult result) = true := rfl

theorem empty : Domain.callHelper (ringModel F G) program "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f"
    [.data (.vector "bls12-381.fr")] [] = .returned [.data (.vector "bls12-381.fr" [])] :=
  ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers.call_return (F := F) (G := G) program GkrSourceBodies.emptyHelper .nil (.cons [] .nil)
    GkrSourceLaws.empty_equation _ _ rfl rfl

theorem append (point : List F) (scalar : F) :
    Domain.callHelper (ringModel F G) program "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d"
      [.data (.vector "bls12-381.fr")]
      [.data (.vector "bls12-381.fr" point), .data (.field "bls12-381.fr" scalar)] =
    .returned [.data (.vector "bls12-381.fr" (point ++ [scalar]))] :=
  ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers.call_return (F := F) (G := G) program GkrSourceBodies.appendHelper
    (.cons point (.cons scalar .nil)) (.cons (point ++ [scalar]) .nil)
    (GkrSourceLaws.append_equation point scalar) _ _ rfl rfl

end ZkcExamples.Construction.GkrDomainHelpers
