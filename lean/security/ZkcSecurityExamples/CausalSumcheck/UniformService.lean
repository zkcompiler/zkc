module

public import ZkcSecurity.ProgramLogic.Oracle.StructuredUniform
public import Zkc.Protocols.Sumcheck.Source.VerifierProcess

@[expose] public section

/-! The concrete uniform service at the actual Sumcheck challenge route. -/

namespace ZkcSecurity.Examples.CausalSumcheck.UniformService

open OracleComp OracleSpec
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured
open ZkcSecurity.VCVio.Execution ZkcSecurity.VCVio.StructuredUniform

variable {F G S E : Type}

/-- The challenge route in an actual entered Sumcheck child context. -/
def queryKey (context : ProtocolContext) (handle : Nat) : Key :=
  (SumcheckVerifierLaws.challengeSite context,
    "bls12-381.fr", handle)

variable [SampleableType F]
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (before : Key → Phase S E Unit) (after : Key → F → Phase S E Unit)

/-- Installing the singleton actual route discharges membership internally. -/
theorem withUniformQueries_queryKey (context : ProtocolContext) (handle : Nat) (s : S) :
    (participantActions F G (.query (queryKey context handle).1
      (queryKey context handle).2.1 (.cons handle .nil))).runM
        (withUniformQueries network [queryKey context handle] before after) s =
      freshQuery (before (queryKey context handle)) (after (queryKey context handle)) s := by
  exact withUniformQueries_query network [queryKey context handle] before after _ _ handle
    (by simp [queryKey]) s


end ZkcSecurity.Examples.CausalSumcheck.UniformService
