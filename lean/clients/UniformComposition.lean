import ZkcArkLibExamples.CausalSumcheck.SourceVerifier

/-! Standalone reuse of the concrete service with arbitrary network behavior. -/

open Zkc.Source Zkc.Source.Structured
open ZkcSecurity.VCVio.Execution
open ZkcSecurity.VCVio.StructuredUniform
open ZkcSecurity.Examples.CausalSumcheck.UniformService

theorem configuredQuery {F G S E : Type} [SampleableType F]
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (before : Key → Phase S E Unit) (after : Key → F → Phase S E Unit)
    (context : ProtocolContext) (handle : Nat) (initial : S) :
    (participantActions F G (.query (queryKey context handle).1
      (queryKey context handle).2.1 (.cons handle .nil))).runM
        (withUniformQueries network [queryKey context handle] before after) initial =
      freshQuery (before (queryKey context handle)) (after (queryKey context handle)) initial :=
  withUniformQueries_queryKey network before after context handle initial

open Zkc.Polynomial.Multilinear
open ZkcSecurity.ArkLib.Sumcheck.Multilinear
open ZkcSecurity.Examples.CausalSumcheck.Iteration
open ZkcExamples.Structured
open scoped ENNReal

/-- Standalone reuse of the shared-process bound, without a freshness premise. -/
theorem sharedProcessPublicTableBound {F G S E : Type}
    [Field F] [DecidableEq F] [Fintype F] [SampleableType F]
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (before : Key → Phase S E Unit) (after : Key → F → Phase S E Unit)
    (context : ProtocolContext) (handle n : Nat) (raw : List F) (table : Table F n)
    (decoded : ofList? n raw = some table) (claim : F) (wrong : claim ≠ raw.sum)
    (initial : S) :
    mass (do
      let e ← (PIR.repeatN n (SumcheckVerifierLaws.roundPresent context handle)
        ([], claim)).runM
        (withUniformQueries network [queryKey context handle] before after) initial
      pure (Causal.accepts (Causal.rawTerminal n raw) e)) ≤
        (n : ENNReal) / Fintype.card F :=
  repeat_uniform_publicTable_soundness network before after context handle n
    raw table decoded claim wrong initial

/-- Reduction is an external-table residual observation, not a Boolean check. -/
theorem sharedProcessResidualBound {F G S E : Type}
    [Field F] [DecidableEq F] [Fintype F] [SampleableType F]
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (before : Key → Phase S E Unit) (after : Key → F → Phase S E Unit)
    (context : ProtocolContext) (handle remaining n : Nat)
    (table : Table F (remaining + n)) (claim : F)
    (wrong : claim ≠ booleanSum table) (initial : S) :
    mass (do
      let e ← (PIR.repeatN n (SumcheckVerifierLaws.roundPresent context handle)
        ([], claim)).runM
        (withUniformQueries network [queryKey context handle] before after) initial
      pure (Causal.accepts (Causal.residualTerminal remaining n table) e)) ≤
        (n : ENNReal) / Fintype.card F :=
  repeat_uniform_residual_soundness network before after context handle remaining n
    table claim wrong initial

open ZkcSecurity.Examples.CausalSumcheck.SourceVerifier

theorem importedSourceReturnedTrueBound {F G S E : Type}
    [Field F] [DecidableEq F] [Fintype F] [SampleableType F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (before : Key → Phase S E Unit) (after : Key → F → Phase S E Unit)
    (n : Nat) (rawV : List F)
    (table : Table F n) (decoded : ofList? n rawV = some table)
    (claim : F) (falseClaim : claim ≠ rawV.sum) (handle : Nat) (s : S) :
    mass (do
      let e ← (SumcheckSourceViews.imported.program.participant F G 1
        (SumcheckSourceVerifier.sourceRootInputs (some rawV) (some claim) (some n)
          (some handle))).runM
            (withUniformQueries network [queryKey SumcheckSourceVerifier.childContext handle]
              before after) s
      pure (returnedSatisfies (fun outputs => outputs.get .here = some true) e)) ≤
        (n : ENNReal) / Fintype.card F :=
  source_returned_true_bound network before after n rawV table decoded claim falseClaim handle s

theorem importedReductionResidualBound {F G S E : Type}
    [Field F] [DecidableEq F] [Fintype F] [SampleableType F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (before : Key → Phase S E Unit) (after : Key → F → Phase S E Unit)
    (xs : Option (List F)) (dimension : Option Nat)
    (remaining n : Nat) (table : Table F (remaining+n))
    (claim : F) (falseClaim : claim ≠ booleanSum table) (handle : Nat) (s : S) :
    mass (do
      let e ← (SumcheckReduceViews.imported.program.participant F G 1
        (SumcheckReduceVerifier.reduceRootInputs xs dimension (some claim) (some n)
          (some handle))).runM
            (withUniformQueries network [queryKey (ProtocolContext.enter {} "s5" [0,1]) handle]
              before after) s
      pure (returnedSatisfies (residualObservation remaining n table) e)) ≤
        (n : ENNReal) / Fintype.card F :=
  reduction_residual_bound network before after xs dimension remaining n table claim falseClaim handle s

