module

public import ZkcSecurity.Bindings.Transcript.ServiceReading
public import ZkcSecurity.Bindings.Transcript.ServiceSampling
public import ZkcSecurity.ProgramLogic.Honest.Honest

@[expose] public section

/-! Typed source readings use the existing exact experiment and cache laws.
The deterministic table controls preserve repeated queries, not just decoded
marginals. The optional finite sampling instances are separate assumptions. -/
set_option autoImplicit false
namespace TestsSecurity.IndexServices
open Zkc.Source Zkc.Construction ZkcSecurity.FiatShamir
open ZkcSecurity.FiatShamir.DomainReduction OracleComp OracleSpec

abbrev carriers := Structured.uniformCarriers (Fin 2) Unit
abbrev contract := "random.scalar/0"
def replacement : Replacement := ⟨0, contract, some (.draw "scalar"), "suite", []⟩
def context : Context := ⟨⟨"entry", ["producer", "validator"], 0, 1⟩, .fiatShamir replacement⟩
abbrev scalarOrigin := context.query "query" (.sampleIndex 8)
abbrev blockOrigin := context.query "query" (.sampleIndices 8 3)

def scalarActual (history : Domain.History carriers) :=
  Domain.requestValue scalarOrigin (.sampleIndex 8) (.query history scalarOrigin)
def scalarSource : PIR.Process (Domain.Actions carriers) Nat :=
  Structured.serviceAction (.query "query" (.sampleIndex contract) (.cons 17 (.cons 8 .nil)))
def blockActual (history : Domain.History carriers) :=
  Domain.requestValue blockOrigin (.sampleIndices 8 3) (.query history blockOrigin)
def blockSource : PIR.Process (Domain.Actions carriers) (List Nat) :=
  Structured.serviceAction (.query "query" (.sampleIndices contract)
    (.cons 17 (.cons 8 (.cons 3 .nil))))

theorem scalar_bridge (history : Domain.History carriers) :
    Bridge (Domain.interface context) (fun _ _ => True) history (scalarActual history) scalarSource :=
  Service.source_bridge (Domain.interface context) history scalarOrigin (.sampleIndex 8)
    (by decide) rfl scalarSource
    (Service.source_index context replacement rfl "query" contract rfl 17 8 (by decide) (by decide) history)

theorem block_bridge (history : Domain.History carriers) :
    Bridge (Domain.interface context) (fun _ _ => True) history (blockActual history) blockSource :=
  Service.source_bridge (Domain.interface context) history blockOrigin (.sampleIndices 8 3)
    (by decide) rfl blockSource
    (Service.source_block context replacement rfl "query" contract rfl 17 8 3 (by decide) (by decide) history)

abbrev Spec := OracleSpec.ofFn (Typed.ByLast (@Domain.Raw carriers))

/-- The adversary revisits the same scalar key twice before the endpoint runs. -/
def repeatedQuery : OracleComp Spec (Domain.Proof carriers) := do
  let _ ← Typed.ask (Raw := @Domain.Raw carriers) (R := Typed.ByLast Domain.Raw) [] (.challenge scalarOrigin)
  let _ ← Typed.ask (Raw := @Domain.Raw carriers) (R := Typed.ByLast Domain.Raw) [] (.challenge scalarOrigin)
  pure []

theorem repeated_log (table : (key : Domain.History carriers) → Typed.ByLast Domain.Raw key) :
    tableQueryLog repeatedQuery table =
      [⟨[.challenge scalarOrigin], table [.challenge scalarOrigin]⟩,
       ⟨[.challenge scalarOrigin], table [.challenge scalarOrigin]⟩] := by
  simp [repeatedQuery, Typed.ask, Typed.answer, bind_map_left, Typed.tableQueryLog_map]

/-- Exact computation transport retains the adversary's two cache visits and
the endpoint's query at the complete supplied history. -/
theorem scalar_experiment (history : Domain.History carriers) (environment : Domain.Environment carriers) :
    (repeatedQuery >>= fun proof => (fun result => (result.outcome, result.state.proof)) <$>
      Domain.run .validator (ZkcSecurity.Endpoint.Domain.Compiled.oracle
        (Typed.ask (R := Typed.ByLast Domain.Raw))) (scalarActual history) ⟨environment, proof, ()⟩) =
      Typed.fixedExperiment (Domain.interface context) scalarSource history repeatedQuery :=
  (scalar_bridge history).computation environment repeatedQuery

theorem block_experiment (history : Domain.History carriers) (environment : Domain.Environment carriers) :
    (repeatedQuery >>= fun proof => (fun result => (result.outcome, result.state.proof)) <$>
      Domain.run .validator (ZkcSecurity.Endpoint.Domain.Compiled.oracle
        (Typed.ask (R := Typed.ByLast Domain.Raw))) (blockActual history) ⟨environment, proof, ()⟩) =
      Typed.fixedExperiment (Domain.interface context) blockSource history repeatedQuery :=
  (block_bridge history).computation environment repeatedQuery

noncomputable instance : DecidableEq (Domain.Event carriers) := Classical.decEq _
noncomputable instance rawSampleable (event : Domain.Event carriers) : SampleableType (Domain.Raw event) :=
  ServiceSampling.raw carriers (fun _ => inferInstance) event

/-- The actual VCVio memoized oracle retains an existing scalar or block
answer and the complete cache. This specializes no new sampling engine. -/
theorem cached_reply (origin : Origin) (cache : Spec.QueryCache)
    (reply : Typed.ByLast (@Domain.Raw carriers) [.challenge origin])
    (found : cache [.challenge origin] = some reply) :
    (Spec.randomOracle [.challenge origin]).run cache = pure (reply, cache) :=
  Honest.cached [.challenge origin] cache reply found

end TestsSecurity.IndexServices
