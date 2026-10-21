module

public import ZkcArkLib.Examples.CausalSumcheck.SourceContracts
public import ZkcExamples.Structured.SumcheckLogicalContext
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-! The residual request through a port-independent logical context.

The request is the logical residual atom over one table binder and V's
returned point and value; its refutation premise is the logical initial atom
over the same binder and V's claim input. No raw vector parameter, decoding or
port-keyed assignment occurs. The `count / |F|` bound is the unchanged
`repeat_uniform_residual_soundness`, applied once through the retained root and
once through the separately exported repacked root. -/
namespace ZkcSecurity.Examples.CausalSumcheck.LogicalResidual

open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Logical ZkcExamples.Structured
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcSecurity.ArkLib.Sumcheck.Multilinear
open ZkcSecurity.VCVio.Execution ZkcSecurity.VCVio.StructuredUniform
open ZkcSecurity.Examples.CausalSumcheck.UniformService
open ZkcSecurity.Examples.CausalSumcheck.Iteration
open SumcheckContractBindings SumcheckContractRequests SumcheckLogicalContext
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxRecDepth 20000

variable {F G S E : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- A final value conversion; earlier stops and their states are unchanged. -/
theorem observation_bind_done {I : PIR.Signature} {A B : Type}
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

omit [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The logical refutation premise is exactly a false initial sum. -/
theorem false_initial_iff (remaining count : Nat) (table : Table F (remaining + count))
    (proverValues : Option (List F)) (proverDimension : Option Nat) (claim : F) (handle : Nat) :
    ¬ (initialAtom (remaining + count)).Holds (interpretation F G) {}
        ((reductionRootInput proverValues proverDimension claim count handle).boundary (.stopped .incomplete))
        (store (owner := reductionRoot) (invocation := rootInvocation) table) ↔
      claim ≠ booleanSum table :=
  not_congr (initial_iff (remaining + count) table proverValues proverDimension claim count handle _)

/-- The logical request on the retained root's returned boundary. -/
def retainedRequest (remaining count : Nat) (table : Table F (remaining + count))
    (input : ComponentInput reductionRoot F G) :
    PIR.Outcome (Values (Component (assignment F G)) reductionRoot.protocol.outputs) → Prop :=
  input.returnedEvent (fun boundary =>
    (residualAtom remaining count).Holds (interpretation F G) {} boundary
      (store (owner := reductionRoot) (invocation := rootInvocation) table))

omit [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem retained_request_iff (remaining count : Nat) (table : Table F (remaining + count))
    (proverValues : Option (List F)) (proverDimension : Option Nat) (claim : F) (handle : Nat)
    (execution : PIR.Execution S E (Values (Component (assignment F G)) reductionRoot.protocol.outputs)) :
    retainedRequest remaining count table
        (reductionRootInput proverValues proverDimension claim count handle) execution.outcome ↔
      returnedSatisfies (SourceVerifier.residualObservation remaining count table) execution := by
  cases execution with | mk outcome state events => ?_
  cases outcome with
  | stopped reason => rfl
  | returned outputs =>
    exact residual_iff remaining count table proverValues proverDimension claim handle outputs

/-- The retained root: arbitrary prover inputs, every network and initial
state. The premise is the refuted logical initial atom over the same binder. -/
theorem retained_bound [Fintype F] [SampleableType F]
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (before : Key → Phase S E Unit) (after : Key → F → Phase S E Unit)
    (proverValues : Option (List F)) (proverDimension : Option Nat)
    (remaining count : Nat) (table : Table F (remaining + count)) (claim : F) (handle : Nat)
    (falseInitial : ¬ (initialAtom (remaining + count)).Holds (interpretation F G) {}
      ((reductionRootInput proverValues proverDimension claim count handle).boundary (.stopped .incomplete))
      (store (owner := reductionRoot) (invocation := rootInvocation) table)) (s : S) :
    mass (do
      let execution ← ((reductionRootInput proverValues proverDimension claim count handle).process.interpret
        forgetSites).runM
        (withUniformQueries network [queryKey (ProtocolContext.enter {} "s3" [0, 1]) handle] before after) s
      pure (retainedRequest remaining count table
        (reductionRootInput proverValues proverDimension claim count handle) execution.outcome)) ≤
      (count : ENNReal) / Fintype.card F := by
  have falseClaim := (false_initial_iff remaining count table proverValues proverDimension claim handle).mp
    falseInitial
  have bound := SourceVerifier.reduction_residual_bound network before after proverValues proverDimension
    remaining count table claim falseClaim handle s
  change mass (do
    let execution ← (SumcheckReduceViews.imported.program.participant F G 1
      (SumcheckReduceVerifier.reduceRootInputs proverValues proverDimension (some claim) (some count)
        (some handle))).runM
      (withUniformQueries network [queryKey (ProtocolContext.enter {} "s3" [0, 1]) handle] before after) s
    pure (retainedRequest remaining count table
      (reductionRootInput proverValues proverDimension claim count handle) execution.outcome)) ≤ _
  refine Eq.trans_le ?_ bound
  apply congrArg mass
  apply bind_congr
  intro execution
  exact congrArg pure (propext (retained_request_iff remaining count table proverValues proverDimension
    claim handle execution))

/-- The existing Lean-authored request, which decodes a raw vector parameter, is
the logical request whenever that vector represents the binder's table. -/
theorem existing_request_iff {environment : RelationEnvironment SumcheckReduceViews.imported F G}
    (raw : List F) (remaining count : Nat) (table : Table F (remaining + count))
    (represented : ofList? (remaining + count) raw = some table)
    (proverValues : Option (List F)) (proverDimension : Option Nat) (claim : F) (handle : Nat)
    (outcome : PIR.Outcome (Values (Component (assignment F G)) reductionRoot.protocol.outputs)) :
    SourceContracts.residualRequest (reductionEnvironment := environment) raw remaining count
        (reductionRootInput proverValues proverDimension claim count handle) outcome ↔
      retainedRequest remaining count table
        (reductionRootInput proverValues proverDimension claim count handle) outcome := by
  cases outcome with
  | stopped reason => rfl
  | returned outputs =>
    exact wrapper_terminal_iff_atom raw remaining count table represented proverValues proverDimension
      claim handle outputs

/-- The existing source-contract bound is a corollary of the logical one: its
refuted retained clause gives the refuted logical atom, and its request is the
logical request, under the representation law it already assumes. -/
theorem existing_bound_from_logical [Fintype F] [SampleableType F]
    {environment : RelationEnvironment SumcheckReduceViews.imported F G}
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (before : Key → Phase S E Unit) (after : Key → F → Phase S E Unit)
    (proverValues : Option (List F)) (proverDimension : Option Nat)
    (remaining count : Nat) (raw : List F) (table : Table F (remaining + count))
    (decoded : ofList? (remaining + count) raw = some table) (claim : F) (handle : Nat)
    (falseTarget : (reductionRefutation (G := G) (reductionEnvironment := environment)
      raw (remaining + count) claim count handle).Meaning) (bounded : raw.length < indexLimit) (state : S) :
    mass (do
      let execution ← ((reductionRootInput proverValues proverDimension claim count handle).process.interpret
        forgetSites).runM
        (withUniformQueries network [queryKey (ProtocolContext.enter {} "s3" [0,1]) handle] before after) state
      pure (SourceContracts.residualRequest (reductionEnvironment := environment) raw remaining count
        (reductionRootInput proverValues proverDimension claim count handle) execution.outcome)) ≤
      (count : ENNReal) / Fintype.card F := by
  have falseInitial := (false_initial_iff (G := G) remaining count table proverValues proverDimension
    claim handle).mpr (by
      rw [booleanSum_ofList? raw table decoded]
      exact reduction_false_sum raw (remaining + count) claim count handle falseTarget
        ⟨SumcheckContractBindings.reduction_formula_law, bounded⟩)
  refine Eq.trans_le ?_ (retained_bound network before after proverValues proverDimension remaining count
    table claim handle falseInitial state)
  apply congrArg mass
  apply bind_congr
  intro execution
  exact congrArg pure (propext (existing_request_iff raw remaining count table decoded proverValues
    proverDimension claim handle execution.outcome))

/-- The same logical request transported to the repacked root's boundary. -/
def repackedRequest (remaining count : Nat) (table : Table F (remaining + count))
    (input : ComponentInput repackedRoot F G) :
    PIR.Outcome (Values (Component (assignment F G)) repackedRoot.protocol.outputs) → Prop :=
  input.returnedEvent (fun boundary =>
    (rootMap.atom (residualAtom remaining count)).Holds (interpretation F G) {} boundary
      (store (owner := repackedRoot) (invocation := rootInvocation) table))

/-- The observation on the repacked root's own return order. -/
def repackedObservation (remaining count : Nat) (table : Table F (remaining + count))
    (outputs : Values (Component (assignment F G)) SumcheckRepackedBodies.runSignature.outputs) : Prop :=
  match outputs.get .here, outputs.get (.there .here) with
  | some point, some claim => Causal.residualTerminal remaining count table point claim
  | _, _ => False

/-- Exact observation of the complete repacked root through the same child
round process as the retained root. -/
theorem repacked_observation
    (handler : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (claim : F) (count : Nat) (admitted : count ≤ 4) (proverDimension : Option Nat)
    (proverValues : Option (List F)) (handle remaining : Nat) (table : Table F (remaining + count)) (s : S) :
    (do
      let e ← (SumcheckRepackedViews.imported.program.participant F G 1
        (SumcheckRepackedVerifier.rootInputs (some claim) (some count) proverDimension proverValues
          (some handle))).runM handler s
      pure (returnedSatisfies (repackedObservation remaining count table) e)) = (do
      let e ← (PIR.repeatN count (SumcheckVerifierLaws.roundPresent
        (ProtocolContext.enter {} "s3" [0, 1]) handle) ([], claim)).runM handler s
      pure (Causal.accepts (Causal.residualTerminal remaining count table) e)) := by
  have present : SumcheckRepackedViews.imported.program.participant F G 1
      (SumcheckRepackedVerifier.rootInputs (some claim) (some count) proverDimension proverValues
        (some handle)) =
      (PIR.repeatN count (SumcheckVerifierLaws.roundPresent
        (ProtocolContext.enter {} "s3" [0, 1]) handle) ([], claim)).bind
          (fun pc => .done (SumcheckRepackedVerifier.rootResults (some pc.1, some pc.2))) := by
    change SumcheckRepackedViews.program.participant F G 1 _ = _
    rw [SumcheckRepackedVerifier.verifier_optional]
    simp only [SumcheckVerifierPrelude.admittedRounds, admitted, ↓reduceIte]
    rw [SumcheckVerifierLaws.repeat_present _ handle count ([], claim), PIR.Proc.bind_assoc]
    rfl
  change (do
    let e ← PIR.Proc.runM
      (A := Values (Component (assignment F G)) SumcheckRepackedBodies.runSignature.outputs) handler
      (SumcheckRepackedViews.imported.program.participant F G 1
        (SumcheckRepackedVerifier.rootInputs (some claim) (some count) proverDimension proverValues
          (some handle))) s
    pure (returnedSatisfies (repackedObservation remaining count table) e)) = _
  rw [present, observation_bind_done]
  apply bind_congr
  intro e
  cases e with
  | mk outcome state events =>
    cases outcome <;> rfl

/-- The repacked root, under the same premise over the same binder. The bound
is the unchanged `repeat_uniform_residual_soundness`. -/
theorem repacked_bound [Fintype F] [SampleableType F]
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (before : Key → Phase S E Unit) (after : Key → F → Phase S E Unit)
    (proverDimension : Option Nat) (proverValues : Option (List F))
    (remaining count : Nat) (table : Table F (remaining + count)) (claim : F) (handle : Nat)
    (falseInitial : ¬ (rootMap.atom (initialAtom (remaining + count))).Holds (interpretation F G) {}
      ((repackedInput claim count proverDimension proverValues handle).boundary (.stopped .incomplete))
      (store (owner := repackedRoot) (invocation := rootInvocation) table)) (s : S) :
    mass (do
      let execution ← ((repackedInput claim count proverDimension proverValues handle).process.interpret
        forgetSites).runM
        (withUniformQueries network [queryKey (ProtocolContext.enter {} "s3" [0, 1]) handle] before after) s
      pure (repackedRequest remaining count table
        (repackedInput claim count proverDimension proverValues handle) execution.outcome)) ≤
      (count : ENNReal) / Fintype.card F := by
  have falseClaim : claim ≠ booleanSum table := by
    intro equality
    apply falseInitial
    rw [rootMap.atom_holds]
    exact ⟨.cons table (.cons claim .nil), rfl, equality⟩
  change mass (do
    let execution ← PIR.Proc.runM
      (A := Values (Component (assignment F G)) SumcheckRepackedBodies.runSignature.outputs)
      (withUniformQueries network [queryKey (ProtocolContext.enter {} "s3" [0, 1]) handle] before after)
      (SumcheckRepackedViews.imported.program.participant F G 1
        (SumcheckRepackedVerifier.rootInputs (some claim) (some count) proverDimension proverValues
          (some handle))) s
    pure (repackedRequest remaining count table
      (repackedInput claim count proverDimension proverValues handle) execution.outcome)) ≤ _
  by_cases admitted : count ≤ 4
  · have observed : (fun execution : PIR.Execution S E
        (Values (Component (assignment F G)) SumcheckRepackedBodies.runSignature.outputs) =>
        repackedRequest remaining count table
          (repackedInput claim count proverDimension proverValues handle) execution.outcome) =
        (fun execution => returnedSatisfies (repackedObservation remaining count table) execution) := by
      funext execution
      cases execution with | mk outcome state events => ?_
      cases outcome with
      | stopped reason => rfl
      | returned outputs =>
        exact propext ((repacked_residual_iff remaining count table claim proverDimension proverValues
          handle outputs).trans (residual_iff remaining count table proverValues proverDimension
            claim handle _))
    refine Eq.trans_le ?_ (repeat_uniform_residual_soundness network before after
      (ProtocolContext.enter {} "s3" [0, 1]) handle remaining count table claim falseClaim s)
    apply congrArg mass
    refine Eq.trans ?_ (repacked_observation _ claim count admitted proverDimension proverValues
      handle remaining table s)
    apply bind_congr
    intro execution
    exact congrArg pure (congrFun observed execution)
  · erw [SumcheckRepackedVerifier.verifier_excess (some claim) count (Nat.lt_of_not_ge admitted)
      proverDimension proverValues (some handle)]
    simp [PIR.Proc.runM, repackedRequest, ComponentInput.returnedEvent]

section ConcreteField

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
noncomputable local instance : SampleableType (ZMod 5) := SampleableType.ofFintype _

/-- The refuted initial atom of `retained_bound` and of `repacked_bound` holds
over `ZMod 5` for the zero table of arity one and claim one. -/
theorem zero_table_refuted (handle : Nat) :
    ¬ (initialAtom (0 + 1)).Holds (interpretation (ZMod 5) (ZMod 5)) {}
        ((reductionRootInput (G := ZMod 5) none none 1 1 handle).boundary (.stopped .incomplete))
        (store (owner := reductionRoot) (invocation := rootInvocation) (fun _ => (0 : ZMod 5))) ∧
    ¬ (rootMap.atom (initialAtom (0 + 1))).Holds (interpretation (ZMod 5) (ZMod 5)) {}
        ((repackedInput (G := ZMod 5) 1 1 none none handle).boundary (.stopped .incomplete))
        (store (owner := repackedRoot) (invocation := rootInvocation) (fun _ => (0 : ZMod 5))) := by
  have sum : booleanSum (fun _ => (0 : ZMod 5) : Table (ZMod 5) (0 + 1)) = 0 := by
    rw [booleanSum_eq_sum]
    exact Finset.sum_const_zero
  have different : (1 : ZMod 5) ≠ booleanSum (fun _ => (0 : ZMod 5) : Table (ZMod 5) (0 + 1)) := by
    rw [sum]
    decide
  constructor
  · exact (false_initial_iff (G := ZMod 5) 0 1 _ none none 1 handle).mpr different
  · rw [rootMap.atom_holds]
    rintro ⟨arguments, read, holds⟩
    cases read
    exact different holds

/-- Both bounds apply to that concrete instance: probability at most `1 / 5`. -/
theorem zero_table_bounds {S E : Type}
    (network : PIR.MonadHandler ProbComp (participantInterface (ZMod 5) (ZMod 5)) S E)
    (before : Key → Phase S E Unit) (after : Key → ZMod 5 → Phase S E Unit) (handle : Nat) (s : S) :
    mass (do
      let execution ← ((reductionRootInput (G := ZMod 5) none none 1 1 handle).process.interpret
        forgetSites).runM
        (withUniformQueries network [queryKey (ProtocolContext.enter {} "s3" [0, 1]) handle] before after) s
      pure (retainedRequest 0 1 (fun _ => (0 : ZMod 5))
        (reductionRootInput none none 1 1 handle) execution.outcome)) ≤
        ((1 : Nat) : ENNReal) / Fintype.card (ZMod 5) ∧
    mass (do
      let execution ← ((repackedInput (G := ZMod 5) 1 1 none none handle).process.interpret
        forgetSites).runM
        (withUniformQueries network [queryKey (ProtocolContext.enter {} "s3" [0, 1]) handle] before after) s
      pure (repackedRequest 0 1 (fun _ => (0 : ZMod 5))
        (repackedInput 1 1 none none handle) execution.outcome)) ≤
        ((1 : Nat) : ENNReal) / Fintype.card (ZMod 5) :=
  ⟨retained_bound network before after none none 0 1 _ 1 handle (zero_table_refuted handle).1 s,
    repacked_bound network before after none none 0 1 _ 1 handle (zero_table_refuted handle).2 s⟩

/-- The bound needs the residual's binder to be the refuted one. Over `ZMod 5`
with zero rounds, the initial atom over `first` is refuted, yet the request
over the other table `second` holds with mass one on the actual retained and
repacked roots under every handler, exceeding the would-be bound `0 / 5`. -/
theorem other_binder_unbounded {S E : Type}
    (handler : PIR.MonadHandler ProbComp (participantInterface (ZMod 5) (ZMod 5)) S E)
    (handle : Nat) (s : S) :
    let first : Table (ZMod 5) (0 + 0) := fun _ => 0
    let second : Table (ZMod 5) (0 + 0) := fun _ => 1
    ¬ (initialAtom (0 + 0)).Holds (interpretation (ZMod 5) (ZMod 5)) {}
        ((reductionRootInput (G := ZMod 5) none none 1 0 handle).boundary (.stopped .incomplete))
        (store (owner := reductionRoot) (invocation := rootInvocation) first) ∧
    ¬ mass (do
      let execution ← ((reductionRootInput (G := ZMod 5) none none 1 0 handle).process.interpret
        forgetSites).runM handler s
      pure (retainedRequest 0 0 second (reductionRootInput none none 1 0 handle) execution.outcome)) ≤
        ((0 : Nat) : ENNReal) / Fintype.card (ZMod 5) ∧
    ¬ mass (do
      let execution ← ((repackedInput (G := ZMod 5) 1 0 none none handle).process.interpret
        forgetSites).runM handler s
      pure (repackedRequest 0 0 second (repackedInput 1 0 none none handle) execution.outcome)) ≤
        ((0 : Nat) : ENNReal) / Fintype.card (ZMod 5) := by
  intro first second
  have holds : Residual 0 0 second [] 1 := by
    refine ⟨Fin.elim0, rfl, ?_⟩
    rw [Zkc.Protocols.Sumcheck.Multilinear.residualClaim_zero]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [false_initial_iff]
    change (1 : ZMod 5) ≠ 0
    decide
  · change ¬ mass (do
      let execution ← PIR.Proc.runM
        (A := Values (Component (assignment (ZMod 5) (ZMod 5))) SumcheckReduceBodies.runSignature.outputs)
        handler (SumcheckReduceViews.program.participant (ZMod 5) (ZMod 5) 1
          (SumcheckReduceVerifier.reduceRootInputs none none (some 1) (some 0) (some handle))) s
      pure (retainedRequest 0 0 second (reductionRootInput none none 1 0 handle) execution.outcome)) ≤ _
    rw [SumcheckReduceVerifier.verifier_zero]
    simp only [PIR.Proc.runM, pure_bind]
    have request : retainedRequest 0 0 second (reductionRootInput (G := ZMod 5) none none 1 0 handle)
        (.returned (SumcheckReduceVerifier.reduceRootResults (some [], some 1))) :=
      (residual_iff 0 0 second none none 1 handle _).mpr holds
    simp only [request]
    simp [mass]
  · change ¬ mass (do
      let execution ← PIR.Proc.runM
        (A := Values (Component (assignment (ZMod 5) (ZMod 5))) SumcheckRepackedBodies.runSignature.outputs)
        handler (SumcheckRepackedViews.program.participant (ZMod 5) (ZMod 5) 1
          (SumcheckRepackedVerifier.rootInputs (some 1) (some 0) none none (some handle))) s
      pure (repackedRequest 0 0 second (repackedInput 1 0 none none handle) execution.outcome)) ≤ _
    rw [SumcheckRepackedVerifier.verifier_optional, SumcheckVerifierPrelude.admittedRounds_zero]
    simp only [PIR.Proc.bind, PIR.Proc.runM, pure_bind]
    have request : repackedRequest 0 0 second (repackedInput (G := ZMod 5) 1 0 none none handle)
        (.returned (SumcheckRepackedVerifier.rootResults (some [], some 1))) :=
      (repacked_residual_iff 0 0 second 1 none none handle _).mpr
        ((residual_iff 0 0 second none none 1 handle _).mpr holds)
    simp only [request]
    simp [mass]

end ConcreteField

end ZkcSecurity.Examples.CausalSumcheck.LogicalResidual
