import ZkcSecurity.Stage.Joint
import ZkcSecurity.Examples.CommittedOpeningBridge
import ZkcTools.DeclarationAudit

/-! Composition of stage relations: a control where the transported budget matters, and the
joint-stage contract applied to a committed verifier.

**Control.** A guessing game charges `a` guesses `a / 8`, the probability that `a` distinct
guesses at a uniform secret among eight hit, and is bounded by `b / 8` at budget `b`
(`guessing_bounded`). A split game counts its budget per family over two families, so a
budget `b` admits `2 · b` guesses; it is a zero-loss stage over the guessing game with the budget
map `b ↦ 2 · b` (`provider`). The composed relation from the trivial game has the loss
`2 · b / 8` (`composed_loss`): the guessing bound evaluated at the transported budget. Two
guesses at budget one attain it (`composed_attained`), and the bound at the untransported budget,
`b / 8`, is false (`untransported_fails`): composition must transport budgets before evaluating
the earlier stage's loss.

**Consumer.** The committed verifier that reads one row of a committed table at one drawn index
(`ZkcSecurity.Examples.CommittedOpeningBridge`) gives the commitment stage of its joint game
(`bridgeRelation`), with the loss `q · ((1 - δ) + h q) + ((1 - δ) + (depth + 1) · h q)` at `q`
prover queries, `h` the hash charge (`bridgeRelation_loss`). A provider simulated in the joint
oracle, with the frame's pass-through and separation obligations recorded in `Frame`, gives the
provider stage; with namespace separation, the bridge's checkpoint extraction and an intended
event implying the concrete failure, the contract composes (`frame_composes`): the intended event
of a concrete adversary within a per-family budget `b` has probability at most the simulation's
loss at `b` and the verifier expansion, plus the commitment stage's loss at the simulation's
transported query budget `cost b`. No compiled claim is made. -/

namespace TestsSecurity.StageComposition
open OracleComp OracleSpec
open ZkcSecurity.FiatShamir ZkcSecurity.Commitment ZkcSecurity.Stage
open scoped ENNReal

/-! ### Control: budgets are transported before losses are evaluated -/

/-- `a` guesses at a uniform secret among eight hit with probability `a / 8` for `a ≤ 8`. -/
noncomputable def guessing : Game where
  Adversary := ℕ
  Budget := ℕ
  Admissible budget guesses := guesses ≤ budget
  bad guesses := (guesses : ENNReal) / 8

theorem guessing_bounded : guessing.Bounded fun (budget : ℕ) => (budget : ENNReal) / 8 :=
  fun _ _ within => ENNReal.div_le_div_right (Nat.cast_le.mpr within) 8

/-- The guessing game with its budget counted per family over two families. -/
noncomputable def split : Game where
  Adversary := ℕ
  Budget := ℕ
  Admissible budget guesses := guesses ≤ 2 * budget
  bad guesses := (guesses : ENNReal) / 8

/-- The split game over the guessing game: no translation and no loss, the budget map
`b ↦ 2 · b`. -/
noncomputable def provider : Relation guessing split :=
  Relation.ofLe (S := guessing) (T := split) (fun (guesses : ℕ) => guesses)
    (fun (budget : ℕ) => 2 * budget)
    (fun _ _ within => within) fun _ _ _ => le_rfl

noncomputable def composed : Relation Game.trivial split :=
  (Relation.ofBound guessing _ guessing_bounded).comp provider

/-- The composed loss is the guessing bound at the transported budget. -/
theorem composed_loss (budget : ℕ) : composed.loss budget = ((2 * budget : ℕ) : ENNReal) / 8 :=
  zero_add _

theorem composed_bounded : split.Bounded fun (budget : ℕ) => ((2 * budget : ℕ) : ENNReal) / 8 := by
  intro budget adversary within
  exact (composed.bounded budget adversary within).trans (le_of_eq (composed_loss budget))

/-- Two guesses at budget one are admissible in the split game and attain the composed loss. -/
theorem composed_attained :
    split.Admissible (1 : ℕ) (2 : ℕ) ∧ split.bad (2 : ℕ) = composed.loss (1 : ℕ) := by
  refine ⟨le_refl 2, ?_⟩
  rw [composed_loss]
  rfl

/-- The guessing bound at the untransported budget does not bound the split game. -/
theorem untransported_fails : ¬ split.Bounded fun (budget : ℕ) => (budget : ENNReal) / 8 := by
  intro bounded
  have twice : ((2 : ℕ) : ENNReal) / 8 ≤ ((1 : ℕ) : ENNReal) / 8 :=
    bounded (1 : ℕ) (2 : ℕ) (le_refl 2)
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)] at twice
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_ofNat] at twice
  norm_num at twice

/-! ### Consumer: one committed table and one challenge through the joint stage -/

open ZkcSecurity.Examples.CommittedOpeningBridge

section Bridge
variable {Row Query Digest : Type} [DecidableEq Row] [DecidableEq Query] [DecidableEq Digest]
  [SampleableType Digest] [Fintype Digest] (model : LeafHashing Row Query Digest)

/-- The bridge's joint game. -/
noncomputable abbrev bridgeGame (accepts : Row → Bool) (depth : ℕ) (fraction : ENNReal)
    (default : Row) : Game :=
  jointGame (absorb depth) (words depth default) (scheme model depth)
    (fun _ : Digest => validator accepts depth) initial (fun root => [((), root)])
    (FalseTable accepts depth fraction default) (· = true)

/-- The bridge's hash charge at `q` prover queries: one root, two inputs per hash call and
`depth + 2` verifier queries. -/
noncomputable abbrev bridgeHash (depth queries : ℕ) : ENNReal :=
  hashCharge Digest 1 2 (depth + 2) queries

/-- The commitment stage of the bridge, from the trivial game. -/
noncomputable def bridgeRelation (accepts : Row → Bool) (depth : ℕ) (fraction : ENNReal)
    (default : Row) : Relation Game.trivial (bridgeGame model accepts depth fraction default) :=
  commitmentRelation (absorb depth) (words depth default) (scheme model depth)
    (fun _ : Digest => validator accepts depth) initial (fun root => [((), root)])
    (certificate accepts depth fraction default) (siteBound := 1 - fraction)
    (fun event => by cases event <;> simp [error]) (fun _ => ⟨_, _, rfl⟩)
    (carries model depth default) initial_determined (fun _ => rfl) 1 (fun _ => le_rfl)
    (fun _ => validator_commitBound accepts depth) (FalseTable accepts depth fraction default)
    (fun _ tables falseTable => by
      obtain ⟨rows, rfl, far⟩ := falseTable
      exact Or.inr (Or.inr ⟨rows, far, rfl⟩))
    2 (fun query => LeafHashing.inputs_length model query) (depth + 2)
    (fun root proof => validator_queryBound model accepts depth root proof.messages proof.openings)
    (fun queries => (1 - fraction) + ((depth + 1 : ℕ) : ENNReal) * bridgeHash (Digest := Digest)
      depth queries)
    fun queries root proof => validator_costBound model accepts depth fraction _ root
      proof.messages proof.openings

theorem bridgeRelation_loss (accepts : Row → Bool) (depth : ℕ) (fraction : ENNReal) (default : Row)
    (queries : ℕ) :
    (bridgeRelation model accepts depth fraction default).loss queries =
      queries * ((1 - fraction) + bridgeHash (Digest := Digest) depth queries) +
        ((1 - fraction) + ((depth + 1 : ℕ) : ENNReal) * bridgeHash (Digest := Digest) depth queries) :=
  rfl

/-- The joint-stage contract composes for the bridge: a provider simulated in the joint oracle,
with the frame's obligations, gives a provider stage; with namespace separation of the shared
primitive's inputs and an intended event implying the concrete failure, the intended event of an
adversary within a per-family budget has probability at most the simulation's loss, the verifier
expansion included, plus the commitment stage's loss at the transported query budget. -/
theorem frame_composes {ι Family ExecBound ChainCall Input : Type} [DecidableEq Family]
    [Fintype Family] {primitive : OracleSpec ι} {family : ι → Family}
    {concreteFailure : OracleComp primitive (Digest × Proof (List Row) Row Digest) → ExecBound →
      ENNReal}
    (accepts : Row → Bool) (depth : ℕ) (fraction : ENNReal) (default : Row)
    (frame : Joint.Frame primitive family
      (JointRange (fun _ : Event Row => Fin (2 ^ depth)) Unit Digest Query) concreteFailure
      (fun provers _ => Joint.oracleMixture
        (experiment (absorb depth) (scheme model depth) (fun _ : Digest => validator accepts depth)
          initial (fun root => [((), root)]))
        (FalseAcceptance (words depth default) (scheme model depth) (fun root => [((), root)])
          (FalseTable accepts depth fraction default) (· = true)) provers))
    (executions : ExecBound) (namespaces : Joint.Namespaces Query ChainCall Input)
    (intended : OracleComp primitive (Digest × Proof (List Row) Row Digest) → ENNReal)
    (implies : ∀ adversary, intended adversary ≤ concreteFailure adversary executions)
    (adversary : OracleComp primitive (Digest × Proof (List Row) Row Digest))
    (budget : Provider.Budget Family) (within : Provider.FamilyQueryBound family adversary budget) :
    intended adversary ≤
      frame.simulation.queryCost.loss budget (frame.simulation.queryCost.expansion executions) +
        (bridgeRelation model accepts depth fraction default).loss
          (frame.simulation.queryCost.cost budget) := by
  let contract : Joint.Contract (bridgeGame model accepts depth fraction default)
      (Provider.concreteGame primitive family concreteFailure executions) Query ChainCall Input
      (TranscriptKey (Event Row) Unit Digest)
      ((key : JointKey (Event Row) Unit Digest Query) ×
        JointRange (fun _ : Event Row => Fin (2 ^ depth)) Unit Digest Query key)
      (Digest → List (Table Row)) :=
    { namespaces := namespaces
      checkpoint := Joint.bridgeCheckpoint (words depth default) (scheme model depth)
        (fun root => [((), root)])
      provider := frame.oracleRelation _ _ executions
      intended := intended
      implies := implies }
  refine (contract.bounded (bridgeRelation model accepts depth fraction default) budget adversary
    within).trans (le_of_eq ?_)
  show (frame.simulation.queryCost.loss budget (frame.simulation.queryCost.expansion executions) +
      0) + _ = _
  rw [add_zero]
  rfl

end Bridge

end TestsSecurity.StageComposition

run_cmd ZkcTools.DeclarationAudit.checkCurrent "STAGE-COMPOSITION-AXIOM-PASS"
