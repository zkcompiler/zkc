module

public import ZkcSecurity.ArkLib.Sumcheck.FiatShamir.Knowledge
public import Zkc.Protocols.Sumcheck.Common

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Two logical rounds, their native oracle-message replay, and the acceptance
projection of the common imported PIR contract. Completion is deliberately not
an equality of early-stopping traces or mutable provider states. -/

namespace ZkcSecurity.ArkLib.Sumcheck.FiatShamir

open Interaction.Oracle Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.TypeTree
open OracleComp OracleSpec
open Zkc.Polynomial Zkc.Protocols.AlgebraicRounds
open Zkc.Protocols.Sumcheck.Common

variable {F : Type} [Field F] [DecidableEq F] [Fintype F] [SampleableType F]

deriving instance DecidableEq for Coefficients

/-- The complete public statement is bound in every restoration key. -/
structure Statement (F : Type) where
  coefficients : Coefficients F
  claim : F
  deriving DecidableEq

abbrev tree := (protocol (rounds (F := F) 2)).tree
abbrev roles := (protocol (rounds (F := F) 2)).roles
abbrev oracles := (protocol (rounds (F := F) 2)).oracles
abbrev initial := emptySpec.toPFunctor

def inputImpl : Statement F → QueryImpl (ofPFunctor initial) Id := fun _ q => nomatch q

def inputState (z : Statement F) : KnowledgeState :=
  residualState True (polynomial z.coefficients) z.claim

def statementExtractor (z : Statement F) : RoundExtractor (tree (F := F)) (inputState z) :=
  extractor 2 True (polynomial z.coefficients) z.claim

/-- Group three ordered scalar coefficients into each existing mathematical message. -/
def path (firstMessage : Message F) (first : F) (secondMessage : Message F) (second : F) :
    (tree (F := F)).ExecutionPath := ⟨firstMessage, first, secondMessage, second, PUnit.unit⟩

/-- Complete verification checks, with both boundary guards retained. -/
def accepted (z : Statement F) (firstMessage : Message F) (first : F)
    (secondMessage : Message F) (second : F) : Prop :=
  wireBoundary firstMessage = z.claim ∧
  wireBoundary secondMessage = wireEvaluate firstMessage first ∧
  wireEvaluate secondMessage second = evaluate z.coefficients first second

instance acceptedDecidable (z : Statement F) (firstMessage : Message F) (first : F)
    (secondMessage : Message F) (second : F) :
    Decidable (accepted z firstMessage first secondMessage second) := by
  unfold accepted
  infer_instance

def Out (_ : Statement F) (_ : (tree (F := F)).BranchPath) : Type := Bool

/-- ArkLib's actual terminal verifier queries both accumulated prover messages.
It receives challenges from the public branch path, never a hidden oracle table. -/
def terminal (z : Statement F) (p : (tree (F := F)).BranchPath) :
    OracleComp (ofPFunctor (accessAfter (tree (F := F)) (oracles (F := F)) initial p)) (Out z p) := by
  rcases p with ⟨_, first, _, second, _⟩
  change OracleComp ((emptySpec + @OracleInterface.spec (Message F) messageInterface) +
    @OracleInterface.spec (Message F) messageInterface) Bool
  exact do
    let firstMessage : Message F ← liftM (((emptySpec + @OracleInterface.spec (Message F) messageInterface) +
      @OracleInterface.spec (Message F) messageInterface).query (Sum.inl (Sum.inr ())))
    let secondMessage : Message F ← liftM (((emptySpec + @OracleInterface.spec (Message F) messageInterface) +
      @OracleInterface.spec (Message F) messageInterface).query (Sum.inr ()))
    pure (decide (accepted z firstMessage first secondMessage second))

/-- The actual native replay observes precisely the grouped coefficient checks. -/
theorem terminalObservation_eq (z : Statement F) (firstMessage : Message F) (first : F)
    (secondMessage : Message F) (second : F) :
    terminalObservation initial inputImpl Out terminal z
      (path firstMessage first secondMessage second) =
        decide (accepted z firstMessage first secondMessage second) := by
  rfl

def terminalWitness (z : Statement F) (p : (tree (F := F)).ExecutionPath) :
    Unit ≃ ((statementExtractor z).terminalState p).Witness := by
  rcases p with ⟨firstMessage, first, secondMessage, second, _⟩
  exact Equiv.refl Unit

omit [DecidableEq F] [Fintype F] [SampleableType F] in
/-- The terminal residual is the actual public bivariate polynomial evaluation. -/
theorem finalResidual_eq (coefficients : Coefficients F) (first second : F) :
    (((polynomial coefficients).restrict first).restrict second).booleanSum =
      evaluate coefficients first second := by
  change (((polynomial coefficients).restrict first).restrict second).eval Fin.elim0 = _
  rw [Quadratic.eval_restrict, Quadratic.eval_restrict]
  rfl

/-- Endpoint identification is proved from the recursive extractor and native queries. -/
theorem terminal_iff (z : Statement F) (firstMessage : Message F) (first : F)
    (secondMessage : Message F) (second : F) (witness : Unit) :
    ((statementExtractor z).terminalState (path firstMessage first secondMessage second)).holds
      (terminalWitness z _ witness) ↔ accepted z firstMessage first secondMessage second := by
  change (((True ∧ firstMessage.boundary = z.claim) ∧
    secondMessage.boundary = firstMessage.evaluate first) ∧
    secondMessage.evaluate second =
      (((polynomial z.coefficients).restrict first).restrict second).booleanSum) ↔ _
  simp only [finalResidual_eq, accepted, wireBoundary_eq, wireEvaluate_eq, true_and, and_assoc]

/-- Existing contracted PIR may stop after three or eight effects; only its
accepting outcome is identified with completed replay. -/
theorem actualVerifier_accepts_iff {wiring : Wiring} {program : Verifier F}
    (certificate : VerifierContract wiring program) (z : Statement F) (service : Nat)
    (firstMessage : Message F) (first : F) (secondMessage : Message F) (second : F) :
    (run program z.coefficients z.claim service ⟨firstMessage, fun _ => secondMessage⟩
      first second).outcome = .returned (some true) ↔
        terminalObservation initial inputImpl Out terminal z
          (path firstMessage first secondMessage second) = true := by
  rw [certificate.run_outcome, terminalObservation_eq]
  by_cases hfirst : wireBoundary firstMessage = z.claim
  all_goals by_cases hsecond : wireBoundary secondMessage = wireEvaluate firstMessage first
  all_goals simp [accepted, hfirst, hsecond]
  exact ⟨fun h => decide_eq_true h, of_decide_eq_true⟩

/-- Full mathematical field evaluation requires no PCS, private witness, or
assumed terminal oracle correctness. -/
theorem outputLaw (z : Statement F) (p : (tree (F := F)).ExecutionPath) (witness : Unit) :
    ((statementExtractor z).terminalState p).holds (terminalWitness z p witness) ↔
      terminalObservation initial inputImpl Out terminal z p = true := by
  rcases p with ⟨firstMessage, first, secondMessage, second, finish⟩
  cases finish
  exact (terminal_iff z firstMessage first secondMessage second witness).trans
    ⟨fun h => decide_eq_true h, of_decide_eq_true⟩

end ZkcSecurity.ArkLib.Sumcheck.FiatShamir
