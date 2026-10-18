module

public import ZkcSecurity.Examples.CausalSumcheck.Iteration
public import ZkcSecurity.VCVio.Composition
public import ZkcExamples.Structured.SumcheckCallBoundary
public import ZkcExamples.Structured.SumcheckSourceVerifier
public import ZkcExamples.Structured.SumcheckReduceVerifier
public import ZkcExamples.Structured.SumcheckContractRequests
public import ZkcExamples.Structured.SumcheckReductionRequests
public import Zkc.Polynomial.Coordinates
public import Zkc.Polynomial.Multilinear.ListRestriction

@[expose] public section

namespace ZkcSecurity.Examples.CausalSumcheck.SourceVerifier

open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcSecurity.ArkLib.Sumcheck.Multilinear
open ZkcSecurity.VCVio.Execution ZkcSecurity.VCVio.StructuredUniform
open ZkcSecurity.Examples.CausalSumcheck.UniformService
open ZkcSecurity.Examples.CausalSumcheck.Iteration
open scoped ENNReal

variable {F G S E : Type} [Field F] [DecidableEq F]

/-- Length is part of the terminal predicate even for malformed short points. -/
private theorem rawTerminal_iff_coordinates {n : Nat} (raw : List F)
    (table : Table F n) (decoded : ofList? n raw = some table)
    (point : List F) (claim : F) :
    Causal.rawTerminal n raw point claim ↔
      point.length = n ∧ extension n table (coordinates n point) = claim := by
  rw [Causal.rawTerminal_eq_table raw table decoded]
  constructor
  · rintro ⟨values, rfl, evaluation⟩
    exact ⟨List.length_ofFn, by simpa only [coordinates_ofFn] using evaluation⟩
  · rintro ⟨length, evaluation⟩
    exact ⟨coordinates n point, ofFn_coordinates point length, evaluation⟩

omit [Field F] [DecidableEq F] in
private theorem decoded_count_two_representable {n : Nat} (raw : List F)
    (table : Table F n) (decoded : ofList? n raw = some table)
    (admitted : n ≤ 2) : raw.length < indexLimit := by
  rw [ofList?_length raw table decoded]
  have size : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) admitted
  exact lt_of_le_of_lt size (by decide : 2 ^ 2 < indexLimit)

/-- This is a final value conversion; prior stopped records survive unchanged. -/
private theorem observation_bind_done {I : PIR.Signature} {A B : Type}
    (handler : PIR.MonadHandler ProbComp I S E) (process : PIR.Proc I A)
    (convert : A → B) (predicate : B → Prop) (s : S) :
    (do
      let e ← (process.bind (fun a => .done (convert a))).runM handler s
      pure (returnedSatisfies predicate e)) = (do
      let e ← process.runM handler s
      pure (returnedSatisfies (fun a => predicate (convert a)) e)) := by
  simp only [PIR.runM_bind, bind_assoc]
  apply bind_congr
  intro e
  cases e with
  | mk outcome state events =>
    cases outcome <;> simp [PIR.Execution.followM, PIR.Proc.runM, returnedSatisfies]

/-- The source terminal's actual Boolean output, after its checked equation. -/
abbrev checkedResult (n : Nat) (table : Table F n) (pc : List F × F) :
    Values (Component (assignment F G)) [.boolean] :=
  .cons (some (decide (pc.1.length = n ∧ extension n table (coordinates n pc.1) = pc.2))) .nil

/-- The observer reads V's two original outputs; Reduction has no Boolean checker. -/
def residualObservation (remaining n : Nat) (table : Table F (remaining + n))
    (outputs : Values (Component (assignment F G)) SumcheckReduceBodies.runSignature.outputs) :
    Prop :=
  match outputs.get (.there (.there .here)), outputs.get (.there (.there (.there .here))) with
  | some point, some claim => Causal.residualTerminal remaining n table point claim
  | _, _ => False

variable [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Exact process equation, retaining all interactions, stops and final output
conversion. Its subject includes admission of the exported complete snapshot. -/
theorem source_present (n : Nat) (admitted : n ≤ 2) (rawV : List F)
    (table : Table F n) (decoded : ofList? n rawV = some table)
    (claim : F) (handle : Nat) :
    SumcheckSourceViews.imported.program.participant F G 1
      (SumcheckSourceVerifier.sourceRootInputs (some rawV) (some claim) (some n) (some handle)) =
      (PIR.repeatN n (SumcheckVerifierLaws.roundPresent SumcheckSourceVerifier.childContext handle)
        ([], claim)).bind (fun pc => .done (checkedResult n table pc)) := by
  change SumcheckSourceViews.program.participant F G 1 _ = _
  rw [SumcheckSourceVerifier.verifier_checked n admitted rawV (some claim) (some handle)
    table decoded (decoded_count_two_representable rawV table decoded admitted)]
  rw [SumcheckVerifierLaws.repeat_present SumcheckSourceVerifier.childContext handle n ([], claim)]
  simp only [PIR.Proc.bind_assoc, PIR.Proc.bind]
  rfl

/-- The actual returned-present-true event equals the shared process terminal
observation. This equation needs no provider premise and keeps stops false. -/
theorem source_observation
    (handler : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (n : Nat) (admitted : n ≤ 2) (rawV : List F)
    (table : Table F n) (decoded : ofList? n rawV = some table)
    (claim : F) (handle : Nat) (s : S) :
    (do
      let e ← (SumcheckSourceViews.imported.program.participant F G 1
        (SumcheckSourceVerifier.sourceRootInputs (some rawV) (some claim) (some n)
          (some handle))).runM handler s
      pure (returnedSatisfies (fun outputs => outputs.get .here = some true) e)) = (do
      let e ← (PIR.repeatN n (SumcheckVerifierLaws.roundPresent
        SumcheckSourceVerifier.childContext handle) ([], claim)).runM handler s
      pure (Causal.accepts (Causal.rawTerminal n rawV) e)) := by
  change (do
    let e ← PIR.Proc.runM (A := Values (Component (assignment F G)) [.boolean]) handler
      (SumcheckSourceViews.imported.program.participant F G 1
        (SumcheckSourceVerifier.sourceRootInputs (some rawV) (some claim) (some n)
          (some handle))) s
    pure (returnedSatisfies
      (fun outputs : Values (Component (assignment F G)) [.boolean] =>
        outputs.get .here = some true) e)) = _
  rw [source_present n admitted rawV table decoded claim handle, observation_bind_done]
  apply bind_congr
  intro e
  cases e with
  | mk outcome state events =>
    cases outcome <;> simp [returnedSatisfies, Causal.accepts, checkedResult, Values.get,
      rawTerminal_iff_coordinates rawV table decoded]

/-- Full imported Sumcheck returned-true bound for arbitrary receive/send
behavior and all initial states. The concrete service discharges freshness and
routing; the source's actual checker and count admission are internal. -/
theorem source_returned_true_bound [Fintype F] [SampleableType F]
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
        (n : ENNReal) / Fintype.card F := by
  by_cases admitted : n ≤ 2
  · rw [source_observation _ n admitted rawV table decoded claim handle s]
    exact repeat_uniform_publicTable_soundness network before after
      SumcheckSourceVerifier.childContext handle n rawV table decoded claim falseClaim s
  · change mass (do
      let e ← PIR.Proc.runM (A := Values (Component (assignment F G)) [.boolean])
        (withUniformQueries network [queryKey SumcheckSourceVerifier.childContext handle]
          before after)
        (SumcheckSourceViews.program.participant F G 1
          (SumcheckSourceVerifier.sourceRootInputs (some rawV) (some claim) (some n)
            (some handle))) s
      pure (returnedSatisfies
        (fun outputs : Values (Component (assignment F G)) [.boolean] =>
          outputs.get .here = some true) e)) ≤ _
    rw [SumcheckSourceVerifier.verifier_excess (some rawV) (some claim) n (some handle)
      (Nat.lt_of_not_ge admitted)]
    simp [PIR.Proc.runM, returnedSatisfies]

section ContractComposition
set_option smartUnfolding false

omit [Field F] [DecidableEq F] in
private theorem decoded_reindex {n m : Nat} (same : n = m) (raw : List F)
    (table : Table F n) (decoded : ofList? n raw = some table) :
    ofList? m raw = some (same ▸ table) := by cases same; exact decoded

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem checked_reindex {n m : Nat} (same : n = m)
    (table : Table F n) (point : List F × F) :
    checkedResult m (same ▸ table) point (G := G) = checkedResult n table point := by
  cases same
  rfl

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- At complete reduction, the real checker implies the residual relation
against the same original table. A nonempty residual dimension would not justify
this conversion to one multilinear evaluation. -/
theorem checked_implies_residual (n : Nat) (table : Table F (0 + n))
    (point : List F) (value : F)
    (accepted : (checkedResult (0 + n) table (point, value)
      (G := G)).get .here = some true) :
    SumcheckContractBindings.Residual 0 n table point value := by
  have condition : point.length = 0 + n ∧
      extension (0 + n) table (coordinates (0 + n) point) = value :=
    of_decide_eq_true (Option.some.inj accepted)
  have length : point.length = n := condition.1.trans (Nat.zero_add n)
  refine ⟨coordinates n point, ofFn_coordinates point length,
    (Zkc.Protocols.Sumcheck.Multilinear.residualClaim_complete_iff table _ _).mpr ?_⟩
  have same : Quadratic.point n (coordinates n point) (Fin.elim0 : Fin 0 → F) =
      coordinates (0 + n) point := by
    apply List.ofFn_injective
    rw [ofFn_point, ofFn_coordinates point length, ofFn_coordinates point condition.1]
    simp
  rw [same]
  exact condition.2

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- A normalized complete residual output satisfies the typed request. The
arbitrary-tuple caller law below is independent of this normalization. -/
theorem checked_implies_terminal (raw : List F) (claim : F) (n handle : Nat)
    (table : Table F n) (decoded : ofList? n raw = some table)
    (point : List F) (value : F)
    (accepted : (checkedResult n table (point, value) (G := G)).get .here = some true) :
    (SumcheckContractRequests.childTerminal (G := G) 0 n).Holds
      SumcheckSourceVerifier.childContext
      (SumcheckContractRequests.childBoundary raw claim n handle
        (.returned (SumcheckVerifierPrelude.reduceResults (some point, some value))))
      (SumcheckContractRequests.childAssignments raw claim n handle) := by
  apply (SumcheckContractRequests.child_terminal_iff raw claim n handle
    ((Nat.zero_add n).symm ▸ table)
    (decoded_reindex (Nat.zero_add n).symm raw table decoded) point value).mpr
  apply checked_implies_residual (G := G) n _ point value
  rw [checked_reindex (G := G) (Nat.zero_add n).symm]
  exact accepted

/-- Typed observation of the actual callee's returned six-slot boundary. -/
def childResidualRequest (raw : List F) (claim : F) (count handle : Nat)
    (outputs : Values (Component (assignment F G)) SumcheckVerifierBodies.reduceOutputs) : Prop :=
  (SumcheckContractRequests.childTerminal (G := G) 0 count).Holds SumcheckSourceVerifier.childContext
    (SumcheckContractRequests.childBoundary raw claim count handle (.returned outputs))
    (SumcheckContractRequests.childAssignments raw claim count handle)

private theorem child_observation
    (handler : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (raw : List F) (claim : F) (n handle : Nat) (admitted : n ≤ 2) (s : S) :
    acceptance handler (SumcheckContractRequests.childProcess raw claim n handle) s
      (childResidualRequest raw claim n handle) =
    acceptance handler (PIR.repeatN n (SumcheckVerifierLaws.roundPresent SumcheckSourceVerifier.childContext handle)
      ([], claim)) s (fun pc => childResidualRequest (G := G) raw claim n handle
        (SumcheckVerifierPrelude.reduceResults (some pc.1, some pc.2))) := by
  change (do
    let e ← PIR.Proc.runM (A := Values (Component (assignment F G)) SumcheckVerifierBodies.reduceOutputs)
      handler (SumcheckContractRequests.childProcess raw claim n handle) s
    pure (returnedSatisfies (childResidualRequest raw claim n handle) e)) = _
  rw [SumcheckContractRequests.child_present raw claim n handle admitted]
  exact observation_bind_done handler _ _ _ s

/-- Residual soundness at the actual call in the Source snapshot. The callee
input clause is refuted through its typed read and formula translation. -/
private theorem child_residual_bound_admitted [Fintype F] [SampleableType F]
    {environment : RelationEnvironment SumcheckSourceViews.imported F G}
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (before : Key → Phase S E Unit) (after : Key → F → Phase S E Unit)
    (n : Nat) (admitted : n ≤ 2) (raw : List F) (table : Table F n)
    (decoded : ofList? n raw = some table) (claim : F) (handle : Nat)
    (refuted : (SumcheckContractRequests.childRefutation (G := G) (sourceEnvironment := environment)
      raw claim n handle (.stopped .incomplete)).Proof) (s : S) :
    mass (acceptance
      (withUniformQueries network [queryKey SumcheckSourceVerifier.childContext handle] before after)
      (SumcheckContractRequests.childProcess raw claim n handle) s
      (childResidualRequest raw claim n handle)) ≤ (n : ENNReal) / Fintype.card F := by
  rw [child_observation _ raw claim n handle admitted s]
  let table0 : Table F (0 + n) := (Nat.zero_add n).symm ▸ table
  have decoded0 : ofList? (0 + n) raw = some table0 :=
    decoded_reindex (Nat.zero_add n).symm raw table decoded
  have falseSum : claim ≠ booleanSum table0 := by
    rw [booleanSum_ofList? raw table0 decoded0]
    exact SumcheckContractRequests.child_false_sum raw claim n handle (.stopped .incomplete) refuted
  calc
    _ ≤ mass (acceptance _ _ s (fun pc : List F × F => Causal.residualTerminal 0 n table0 pc.1 pc.2)) :=
      acceptance_mono _ _ s _ _ (fun pc holds =>
        (SumcheckContractRequests.child_terminal_iff raw claim n handle table0 decoded0 pc.1 pc.2).mp holds)
    _ ≤ _ := by
      have bound := repeat_uniform_residual_soundness network before after
        SumcheckSourceVerifier.childContext handle 0 n table0 claim falseSum s
      have observation : (fun e : PIR.Execution S E (List F × F) =>
          returnedSatisfies (fun pc => Causal.residualTerminal 0 n table0 pc.1 pc.2) e) =
          Causal.accepts (Causal.residualTerminal 0 n table0) := by
        funext e
        cases e with | mk outcome state events => cases outcome <;> rfl
      simpa only [acceptance, observation] using bound

/-- The child interface handles all counts, including its own excess-count
refusal. The caller needs no implementation expansion or admission split. -/
theorem child_residual_bound [Fintype F] [SampleableType F]
    {environment : RelationEnvironment SumcheckSourceViews.imported F G}
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (before : Key → Phase S E Unit) (after : Key → F → Phase S E Unit)
    (n : Nat) (raw : List F) (table : Table F n)
    (decoded : ofList? n raw = some table) (claim : F) (handle : Nat)
    (refuted : (SumcheckContractRequests.childRefutation (G := G) (sourceEnvironment := environment)
      raw claim n handle (.stopped .incomplete)).Proof) (s : S) :
    mass (acceptance
      (withUniformQueries network [queryKey SumcheckSourceVerifier.childContext handle] before after)
      (SumcheckContractRequests.childProcess raw claim n handle) s
      (childResidualRequest raw claim n handle)) ≤ (n : ENNReal) / Fintype.card F := by
  by_cases admitted : n ≤ 2
  · exact child_residual_bound_admitted network before after n admitted raw table decoded claim handle refuted s
  · change mass (do
      let e ← PIR.Proc.runM (A := Values (Component (assignment F G)) SumcheckVerifierBodies.reduceOutputs)
        (withUniformQueries network [queryKey SumcheckSourceVerifier.childContext handle] before after)
        (SumcheckContractRequests.childProcess raw claim n handle) s
      pure (returnedSatisfies (childResidualRequest raw claim n handle) e)) ≤ _
    rw [SumcheckCallBoundary.child_excess raw claim n handle (Nat.lt_of_not_ge admitted)]
    simp [PIR.Proc.runM, returnedSatisfies]

/-- The actual caller terminal implies the typed child residual on every
returned six-slot tuple, at every intermediate state. The source shape guard
supplies the point length; there is no callee reachability premise. -/
theorem terminal_implies_request
    (handler : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (n : Nat) (raw : List F) (table : Table F n) (decoded : ofList? n raw = some table)
    (bounded : raw.length < indexLimit) (claim : F) (handle : Nat)
    (outputs : Values (Component (assignment F G)) SumcheckVerifierBodies.reduceOutputs)
    (state : S) (execution : PIR.Execution S E (Values (Component (assignment F G)) [.boolean]))
    (supported : execution ∈ support ((SumcheckCallBoundary.terminal raw outputs).runM handler state))
    (accepted : returnedSatisfies (fun result => result.get .here = some true) execution) :
    childResidualRequest raw claim n handle outputs := by
  unfold SumcheckCallBoundary.terminal at supported
  cases pointRead : outputs.get (.there (.there (.there (.there .here)))) with
  | none =>
    rw [pointRead, SumcheckVerifierTerminal.terminal_optional] at supported
    simp only [PIR.Proc.runM, support_pure, Set.mem_singleton_iff] at supported
    subst execution
    cases accepted
  | some point =>
    cases valueRead : outputs.get (.there (.there (.there (.there (.there .here))))) with
    | none =>
      rw [pointRead, valueRead, SumcheckVerifierTerminal.terminal_optional] at supported
      simp only [PIR.Proc.runM, support_pure, Set.mem_singleton_iff] at supported
      subst execution
      cases accepted
    | some value =>
      rw [pointRead, valueRead, SumcheckCallBoundary.terminal_present n raw table decoded bounded point value] at supported
      by_cases pointBound : point.length < indexLimit
      · rw [ite_eq_left pointBound] at supported
        simp only [PIR.Proc.runM, support_pure, Set.mem_singleton_iff] at supported
        subst execution
        apply (SumcheckCallBoundary.child_request_iff raw claim n handle
          ((Nat.zero_add n).symm ▸ table)
          (decoded_reindex (Nat.zero_add n).symm raw table decoded) outputs).mpr
        rw [pointRead, valueRead]
        apply checked_implies_residual (G := G) n _ point value
        rw [checked_reindex (G := G) (Nat.zero_add n).symm]
        exact accepted
      · rw [ite_eq_right pointBound] at supported
        simp only [PIR.Proc.runM, support_pure, Set.mem_singleton_iff] at supported
        subst execution
        cases accepted

/-- The caller accepts at most the child's residual mass for any replacement
child with the same returned ABI. Only the supplied interface bound is used;
no source identity or internal implementation of the replacement is required. -/
theorem caller_bound_of_child
    (handler : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (n : Nat) (raw : List F) (table : Table F n) (decoded : ofList? n raw = some table)
    (bounded : raw.length < indexLimit) (claim : F) (handle : Nat)
    (child : PIR.Proc (participantInterface F G)
      (Values (Component (assignment F G)) SumcheckVerifierBodies.reduceOutputs))
    (state : S) (error : ENNReal)
    (childBound : mass (acceptance handler child state (childResidualRequest raw claim n handle)) ≤ error) :
    mass (acceptance handler (child.bind (SumcheckCallBoundary.terminal raw)) state
      (fun result => result.get .here = some true)) ≤ error :=
  (ZkcSecurity.VCVio.Composition.acceptance_bind_le handler child (SumcheckCallBoundary.terminal raw) state
    (fun result => result.get .here = some true) (childResidualRequest raw claim n handle)
    (terminal_implies_request handler n raw table decoded bounded claim handle)).trans childBound

/-- Direct call-boundary composition: the linked root uses the callee's residual
interface and its actual owned terminal on arbitrary child returns. -/
theorem source_composed_bound [Fintype F] [SampleableType F]
    {environment : RelationEnvironment SumcheckSourceViews.imported F G}
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (before : Key → Phase S E Unit) (after : Key → F → Phase S E Unit)
    (n : Nat) (rawV : List F) (table : Table F n) (decoded : ofList? n rawV = some table)
    (bounded : rawV.length < indexLimit) (claim : F) (handle : Nat)
    (refuted : (SumcheckContractRequests.childRefutation (G := G) (sourceEnvironment := environment)
      rawV claim n handle (.stopped .incomplete)).Proof) (s : S) :
    mass (do
      let e ← (SumcheckSourceViews.imported.program.participant F G 1
        (SumcheckSourceVerifier.sourceRootInputs (some rawV) (some claim) (some n)
          (some handle))).runM
            (withUniformQueries network [queryKey SumcheckSourceVerifier.childContext handle]
              before after) s
      pure (returnedSatisfies (fun outputs => outputs.get .here = some true) e)) ≤
        (n : ENNReal) / Fintype.card F := by
  change mass (acceptance
    (withUniformQueries network [queryKey SumcheckSourceVerifier.childContext handle] before after)
    (SumcheckSourceViews.imported.program.participant F G 1
      (SumcheckSourceVerifier.sourceRootInputs (some rawV) (some claim) (some n) (some handle))) s
    (fun outputs => outputs.get .here = some true)) ≤ _
  rw [SumcheckCallBoundary.source_linked rawV claim n handle]
  exact caller_bound_of_child _ n rawV table decoded bounded claim handle _ s _
    (child_residual_bound network before after n rawV table decoded claim handle refuted s)

end ContractComposition

/-- Original Reduction root output selection after the shared source process.
Prover inputs are arbitrary; no association to the external table is imposed. -/
theorem reduction_present (xs : Option (List F)) (dimension : Option Nat)
    (n : Nat) (admitted : n ≤ 4) (claim : F) (handle : Nat) :
    SumcheckReduceViews.imported.program.participant F G 1
      (SumcheckReduceVerifier.reduceRootInputs xs dimension (some claim) (some n) (some handle)) =
      (PIR.repeatN n (SumcheckVerifierLaws.roundPresent
        (ProtocolContext.enter {} "s3" [0,1]) handle) ([], claim)).bind
          (fun pc => .done (SumcheckReduceVerifier.reduceRootResults (some pc.1, some pc.2))) := by
  change SumcheckReduceViews.program.participant F G 1 _ = _
  rw [SumcheckReduceVerifier.verifier_optional]
  simp only [SumcheckVerifierPrelude.admittedRounds, admitted, ↓reduceIte]
  rw [SumcheckVerifierLaws.repeat_present _ handle n ([], claim)]
  simp only [PIR.Proc.bind_assoc, PIR.Proc.bind]
  rfl

/-- Exact observation of the complete Reduction root, without a Boolean checker. -/
theorem reduction_observation
    (handler : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (xs : Option (List F)) (dimension : Option Nat)
    (remaining n : Nat) (admitted : n ≤ 4) (table : Table F (remaining+n))
    (claim : F) (handle : Nat) (s : S) :
    (do
      let e ← (SumcheckReduceViews.imported.program.participant F G 1
        (SumcheckReduceVerifier.reduceRootInputs xs dimension (some claim) (some n)
          (some handle))).runM handler s
      pure (returnedSatisfies (residualObservation remaining n table) e)) = (do
      let e ← (PIR.repeatN n (SumcheckVerifierLaws.roundPresent
        (ProtocolContext.enter {} "s3" [0,1]) handle) ([], claim)).runM handler s
      pure (Causal.accepts (Causal.residualTerminal remaining n table) e)) := by
  change (do
    let e ← PIR.Proc.runM
      (A := Values (Component (assignment F G)) SumcheckReduceBodies.runSignature.outputs) handler
      (SumcheckReduceViews.imported.program.participant F G 1
        (SumcheckReduceVerifier.reduceRootInputs xs dimension (some claim) (some n)
          (some handle))) s
    pure (returnedSatisfies (residualObservation remaining n table) e)) = _
  rw [reduction_present xs dimension n admitted claim handle, observation_bind_done]
  apply bind_congr
  intro e
  cases e with
  | mk outcome state events =>
    cases outcome <;> rfl

/-- Full imported Reduction residual bound against an external original table.
This root returns a reduced relation, not an acceptance Boolean. -/
theorem reduction_residual_bound [Fintype F] [SampleableType F]
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (before : Key → Phase S E Unit) (after : Key → F → Phase S E Unit)
    (xs : Option (List F)) (dimension : Option Nat)
    (remaining n : Nat) (table : Table F (remaining+n))
    (claim : F) (falseClaim : claim ≠ booleanSum table) (handle : Nat) (s : S) :
    mass (do
      let e ← (SumcheckReduceViews.imported.program.participant F G 1
        (SumcheckReduceVerifier.reduceRootInputs xs dimension (some claim) (some n)
          (some handle))).runM
            (withUniformQueries network [queryKey (ProtocolContext.enter {} "s3" [0,1]) handle]
              before after) s
      pure (returnedSatisfies (residualObservation remaining n table) e)) ≤
        (n : ENNReal) / Fintype.card F := by
  by_cases admitted : n ≤ 4
  · rw [reduction_observation _ xs dimension remaining n admitted table claim handle s]
    exact repeat_uniform_residual_soundness network before after
      (ProtocolContext.enter {} "s3" [0,1]) handle remaining n table claim falseClaim s
  · change mass (do
      let e ← PIR.Proc.runM
        (A := Values (Component (assignment F G)) SumcheckReduceBodies.runSignature.outputs)
        (withUniformQueries network [queryKey (ProtocolContext.enter {} "s3" [0,1]) handle]
          before after)
        (SumcheckReduceViews.program.participant F G 1
          (SumcheckReduceVerifier.reduceRootInputs xs dimension (some claim) (some n)
            (some handle))) s
      pure (returnedSatisfies (residualObservation remaining n table) e)) ≤ _
    rw [SumcheckReduceVerifier.verifier_excess xs dimension (some claim) n
      (Nat.lt_of_not_ge admitted) (some handle)]
    simp [PIR.Proc.runM, returnedSatisfies]

section ReductionRequests
set_option smartUnfolding false

/-- Typed terminal on the actual residual wrapper's returned boundary. -/
def wrapperResidualRequest (raw : List F) (remaining count : Nat)
    (xs : Option (List F)) (dimension : Option Nat) (claim : F) (handle : Nat)
    (outputs : Values (Component (assignment F G)) SumcheckReduceBodies.runSignature.outputs) : Prop :=
  (SumcheckContractRequests.wrapperTerminal raw remaining count).Holds {}
    ((SumcheckContractRequests.reductionRootInput xs dimension claim count handle).boundary (.returned outputs))
    SumcheckContractRequests.wrapperAssignments

/-- The wrapper event is exactly the checked child's request after its actual
return projection. The equality preserves stops, state and ordered interaction
in the shared source process; only the final observation is compared. -/
theorem reduction_request_observation
    (handler : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (xs : Option (List F)) (dimension : Option Nat) (remaining count : Nat)
    (admitted : count ≤ 4) (raw : List F) (table : Table F (remaining + count))
    (decoded : ofList? (remaining + count) raw = some table) (claim : F) (handle : Nat) (s : S) :
    acceptance handler (SumcheckReduceViews.imported.program.participant F G 1
      (SumcheckReduceVerifier.reduceRootInputs xs dimension (some claim) (some count) (some handle))) s
      (wrapperResidualRequest raw remaining count xs dimension claim handle) =
    acceptance handler (SumcheckReductionRequests.childProcess claim count handle) s
      (SumcheckReductionRequests.request raw remaining count claim handle) := by
  change (do
    let e ← PIR.Proc.runM (A := Values (Component (assignment F G)) SumcheckReduceBodies.runSignature.outputs)
      handler (SumcheckReduceViews.imported.program.participant F G 1
        (SumcheckReduceVerifier.reduceRootInputs xs dimension (some claim) (some count) (some handle))) s
    pure (returnedSatisfies (wrapperResidualRequest raw remaining count xs dimension claim handle) e)) =
    (do
    let e ← PIR.Proc.runM (A := Values (Component (assignment F G)) SumcheckVerifierBodies.reduceOutputs)
      handler (SumcheckReductionRequests.childProcess claim count handle) s
    pure (returnedSatisfies (SumcheckReductionRequests.request raw remaining count claim handle) e))
  rw [reduction_present xs dimension count admitted claim handle,
    SumcheckReductionRequests.child_present claim count handle admitted,
    observation_bind_done, observation_bind_done]
  apply bind_congr
  intro e
  cases e with | mk outcome state events => ?_
  cases outcome with
  | stopped reason => rfl
  | returned pc =>
    exact congrArg pure (propext (SumcheckReductionRequests.wrapper_request_iff raw remaining count claim handle
      table decoded xs dimension (SumcheckVerifierPrelude.reduceResults (some pc.1, some pc.2))))

/-- Residual-only source bound consuming the actual child clause and output
substitution. It requires no agreement with P's optional runtime table. -/
theorem reduction_typed_bound [Fintype F] [SampleableType F]
    {environment : RelationEnvironment SumcheckReduceViews.imported F G}
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (before : Key → Phase S E Unit) (after : Key → F → Phase S E Unit)
    (xs : Option (List F)) (dimension : Option Nat) (remaining count : Nat)
    (raw : List F) (table : Table F (remaining + count))
    (decoded : ofList? (remaining + count) raw = some table) (claim : F) (handle : Nat)
    (refuted : (SumcheckContractRequests.reductionRefutation (G := G) (reductionEnvironment := environment)
      raw (remaining + count) claim count handle).Meaning)
    (translation : (SumcheckContractRequests.reductionUse (G := G) (reductionEnvironment := environment)
      raw (remaining + count) claim count handle (.stopped .incomplete)).Translation) (s : S) :
    mass (acceptance
      (withUniformQueries network [queryKey (ProtocolContext.enter {} "s3" [0, 1]) handle] before after)
      (SumcheckReduceViews.imported.program.participant F G 1
        (SumcheckReduceVerifier.reduceRootInputs xs dimension (some claim) (some count) (some handle))) s
      (wrapperResidualRequest raw remaining count xs dimension claim handle)) ≤
        (count : ENNReal) / Fintype.card F := by
  by_cases admitted : count ≤ 4
  · rw [reduction_request_observation _ xs dimension remaining count admitted raw table decoded claim handle s]
    change mass (do
      let e ← PIR.Proc.runM (A := Values (Component (assignment F G)) SumcheckVerifierBodies.reduceOutputs)
        (withUniformQueries network [queryKey (ProtocolContext.enter {} "s3" [0, 1]) handle] before after)
        (SumcheckReductionRequests.childProcess claim count handle) s
      pure (returnedSatisfies (SumcheckReductionRequests.request raw remaining count claim handle) e)) ≤ _
    rw [SumcheckReductionRequests.child_present claim count handle admitted, observation_bind_done]
    have falseSum : claim ≠ booleanSum table := by
      rw [booleanSum_ofList? raw table decoded]
      exact SumcheckContractRequests.reduction_false_sum raw (remaining + count) claim count handle refuted translation
    calc
      _ ≤ mass (acceptance _ _ s (fun pc : List F × F => Causal.residualTerminal remaining count table pc.1 pc.2)) :=
        acceptance_mono _ _ s _ _ (fun pc holds =>
          (SumcheckReductionRequests.request_iff raw remaining count claim handle table decoded
            (SumcheckVerifierPrelude.reduceResults (some pc.1, some pc.2))).mp holds)
      _ ≤ _ := by
        have bound := repeat_uniform_residual_soundness network before after
          (ProtocolContext.enter {} "s3" [0, 1]) handle remaining count table claim falseSum s
        have observation : (fun e : PIR.Execution S E (List F × F) =>
            returnedSatisfies (fun pc => Causal.residualTerminal remaining count table pc.1 pc.2) e) =
            Causal.accepts (Causal.residualTerminal remaining count table) := by
          funext e
          cases e with | mk outcome state events => cases outcome <;> rfl
        simpa only [acceptance, observation] using bound
  · change mass (do
      let e ← PIR.Proc.runM (A := Values (Component (assignment F G)) SumcheckReduceBodies.runSignature.outputs)
        (withUniformQueries network [queryKey (ProtocolContext.enter {} "s3" [0, 1]) handle] before after)
        (SumcheckReduceViews.program.participant F G 1
          (SumcheckReduceVerifier.reduceRootInputs xs dimension (some claim) (some count) (some handle))) s
      pure (returnedSatisfies (wrapperResidualRequest raw remaining count xs dimension claim handle) e)) ≤ _
    rw [SumcheckReduceVerifier.verifier_excess xs dimension (some claim) count
      (Nat.lt_of_not_ge admitted) (some handle)]
    simp [PIR.Proc.runM, returnedSatisfies]

end ReductionRequests

end ZkcSecurity.Examples.CausalSumcheck.SourceVerifier
