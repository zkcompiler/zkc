import Zkc.Protocols.CorrelatedSetup.Preparation
import Zkc.Source.Arithmetic
import Zkc.Semantics.Preparation

/-! Shared source/candidate checking on a persistent correlated service. -/

set_option autoImplicit false

namespace Tests.CorrelatedPreparation

open Zkc.Source Zkc.Compiler Zkc.Source.Arithmetic Zkc.Modules
open Zkc.Protocols.CorrelatedSetup

abbrev F := ZMod 7
def setup : Setup F := ⟨2, 3, 4, 5, 6⟩
def witness : Witness F := ⟨1, 1, by decide⟩
def publication : Triple F := (0, 0, 0)

/-- Each invocation makes a real partially delivered request. Later requests
may depend on an earlier response through the typed input operand. -/
def invoke (challenge : F) : PIR.Proc (Execution.sig F) F :=
  .call (.request ⟨setup.star, challenge, true⟩) .done

def raw : RawProgram Ty Op :=
  .letOp .invoke [0] (.letOp .invoke [0] (.letOp .invoke [0] (.ret 0)))

def source : Program language [.scalar] .scalar :=
  (raw.elaborate (language := language) [.scalar] .scalar).toOption.get (by decide)

def expected : RawProgram Ty Op :=
  .letOp .invoke [0] (.letOp .invoke [0] (.letOp .invoke [0] (.ret 0)))

example : (checkTransformation
    (Preparation.rule (interpretation invoke) setup witness publication [.scalar] .scalar)
    source () expected).isSome = true := by decide

def wrong : RawProgram Ty Op :=
  .letOp .invoke [0] (.letOp .invoke [1] (.letOp .invoke [0] (.ret 0)))

example : (checkTransformation
    (Preparation.rule (interpretation invoke) setup witness publication [.scalar] .scalar)
    source () wrong).isSome = false := by decide

def inputs : Values (Value F) [.scalar] := .cons 1 .nil
def run (tape : List F) : PIR.Execution (Preparation.State F) (Service.Event F) F :=
  (source.denote (interpretation invoke) inputs.get).run
    (Preparation.handler setup witness publication) (Preparation.initial Service.empty tape)

example : (run [0, 1]).outcome = .stopped .exhausted := by decide
example : (run [0, 1]).state.tape = [] := by decide
example : (run [0, 1]).state.coefficients publication = some (2, 0) := by decide
example : (run [0, 1]).events =
    [.response ⟨6, 1, true⟩ 1 none none, .response ⟨6, 1, true⟩ 6 none none] := by decide

example : (run [0, 1, 2, 3]).outcome = .returned 0 := by decide
example : (run [0, 1, 2, 3]).state.tape = [3] := by decide
example : (run [0, 1, 2, 3]).events.length = 3 := by decide

/-- Equal coefficients do not permit response reuse across distinct masks. -/
example : Service.actualResponse setup (byPrefix setup witness publication) ⟨6, 1, true⟩ 0 ≠
    Service.actualResponse setup (byPrefix setup witness publication) ⟨6, 1, true⟩ 1 := by decide

theorem full_execution (tape : List F) :
    PIR.Related (Preparation.Rel setup witness) (fun event => [event]) (fun event => [event])
      ((source.denote (interpretation invoke) inputs.get).run
        (Execution.handler setup witness publication) (Service.empty, tape)) (run tape) :=
  Preparation.run_refines setup witness publication _ _ _
    ⟨rfl, rfl, ImmutableCache.empty_valid _⟩

def stop : PIR.Proc (Execution.sig F) Unit := .call .stop .done

example : (stop.run (Preparation.handler setup witness publication)
    (Preparation.initial Service.empty [1, 2])).state.tape = [1, 2] := by decide

/-- Reusing immutable request parameters still makes two actual service calls.
The returned masked responses themselves are never preparation values. -/
def parameterProvider (challenge : F) : F × Nat := (challenge * challenge, 5)
def parameterPrices : Zkc.Modules.Preparation.Prices F F := ⟨fun _ _ => 1, fun _ _ => 1⟩

def preparedRequests : PIR.Proc (PIR.Preparation.signature F F (Execution.sig F)) (F × F) :=
  .call (.prepare 1) fun challenge =>
    .call (.external (.request ⟨setup.star, challenge, true⟩)) fun first =>
      .call (.prepare 1) fun challenge =>
        .call (.external (.request ⟨setup.star, challenge, true⟩)) fun second =>
          .done (first, second)

def runPrepared (mode : Zkc.Modules.Preparation.Mode) (tape : List F) :=
  preparedRequests.run
    (PIR.Preparation.handler parameterProvider parameterPrices mode
      (Execution.handler setup witness publication)) (Zkc.Modules.Preparation.empty, Service.empty, tape)

theorem parameter_reuse (tape : List F) :
    PIR.Related (PIR.Preparation.StateRel parameterProvider) PIR.Preparation.view PIR.Preparation.view
      (runPrepared .direct tape) (runPrepared .memo tape) :=
  PIR.Preparation.contextual_memo parameterProvider parameterPrices
    (Execution.handler setup witness publication) preparedRequests _ _
    ⟨ImmutableCache.empty_valid parameterProvider, ImmutableCache.empty_valid parameterProvider, rfl⟩

theorem distinct_responses :
    (runPrepared .memo [0, 1, 2]).outcome = .returned (1, 6) ∧
    (runPrepared .memo [0, 1, 2]).state.2.2 = [2] ∧
    (runPrepared .memo [0, 1, 2]).state.2.1.events.length = 2 := by decide

theorem cached_parameter_does_not_avoid_exhaustion :
    (runPrepared .memo [0]).outcome = .stopped .exhausted ∧
    (runPrepared .memo [0]).state.2.2 = [] ∧
    (runPrepared .memo [0]).state.2.1.events.length = 1 := by decide

end Tests.CorrelatedPreparation
