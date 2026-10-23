module

public import ZkcSecurity.Examples.Components.TwoSumsReadbackRounds
public import ZkcSecurity.Families.Sumcheck.TableComponentExecution

@[expose] public section

/-! Honest read-back of both actual sequential TwoSums calls. The first call's
complete carries and history enter the second; both terminal results and the
actual final conjunction are retained. No independence assertion is used. -/
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 2400000
namespace ZkcSecurity.Examples.Components.TwoSums
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured Generated.Constructed
open ZkcSecurity.Families.Sumcheck.TableComponent
open ZkcSecurity.FiatShamir
open ReadbackRound
open ZkcSecurity.Examples.Generated.Components.TwoSumsRounds

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

set_option linter.unusedSimpArgs false in
theorem root_readback (context : Context)
    (suite : context.suite = "merlin3.bls12-381.fr64be/0")
    (sites : ∀ second index, Sites (roundPlan second) context index)
    (leftRaw rightRaw : List F) (count : Nat) (admitted : count ≤ round0.maximum)
    (leftShape : leftRaw.length = 2 ^ count) (rightShape : rightRaw.length = 2 ^ count)
    (leftBound : leftRaw.length < indexLimit) (rightBound : rightRaw.length < indexLimit)
    (history : Domain.History (ringModel F G).toCarriers) :
    Readback (fun _ result => HonestCompiled.acceptanceAt 0 result.values = some true)
      (Domain.participant (ringModel F G) Generated.Bindings.TwoSumsInputs.imported.program context TwoSumsProducer.artifact
        [.data (.vector "bls12-381.fr" leftRaw), .data (.vector "bls12-381.fr" rightRaw),
          .data (.index count), .transcript "merlin3.bls12-381.fr64be/0" history])
      (Domain.participant (ringModel F G) Generated.Bindings.TwoSumsInputs.imported.program context TwoSumsValidator.artifact
        [.data (.vector "bls12-381.fr" leftRaw), .data (.vector "bls12-381.fr" rightRaw),
          .data (.field "bls12-381.fr" leftRaw.sum), .data (.field "bls12-381.fr" rightRaw.sum),
          .data (.index count), .transcript "merlin3.bls12-381.fr64be/0" history]) := by
  dsimp only [round0.maximum, round0.descriptor] at admitted
  have countSmall : count < 64 := lt_of_le_of_lt admitted (by decide +kernel)
  have countBound : count < indexLimit := countSmall.trans (by decide +kernel)
  have leftTable := SumcheckDomainHelpers.table (G := G) Generated.Bindings.TwoSumsInputs.imported.program
    domain_bodies.sumcheck leftRaw count 1
    (PrimitiveLibrary.hasShape_of_length _ _ _ (by decide) countSmall (by simpa using leftShape))
    leftBound countBound (by decide +kernel)
  have rightTable := SumcheckDomainHelpers.table (G := G) Generated.Bindings.TwoSumsInputs.imported.program
    domain_bodies.sumcheck rightRaw count 1
    (PrimitiveLibrary.hasShape_of_length _ _ _ (by decide) countSmall (by simpa using rightShape))
    rightBound countBound (by decide +kernel)
  have emptyLaw := SumcheckDomainHelpers.empty (F := F) (G := G) Generated.Bindings.TwoSumsInputs.imported.program domain_bodies.sumcheck
  have lessLaw := SumcheckDomainHelpers.less (F := F) (G := G) Generated.Bindings.TwoSumsInputs.imported.program domain_bodies.sumcheck count count countBound countBound
  rw [TwoSumsProducer.participant_eq, TwoSumsValidator.participant_eq]
  unfold_component_bodies [TwoSumsProducer.view, TwoSumsValidator.view]
  normalize_table_readback [leftTable, rightTable, emptyLaw, lessLaw] unfolding [admitted]
  readback_table_loop round0
    [Generated.Bindings.TwoSumsInputs.imported.program, round_helpers false, context, suite,
      sites false, leftRaw, count, countSmall, leftShape, leftBound, history]
    as leftCaptured, rightCaptured, firstState, sameLeft, firstHonest
  have terminalTrue := SumcheckDomainHelpers.terminal_condition leftRaw firstState sameLeft leftBound firstHonest
  have leftTerminal := SumcheckDomainHelpers.check (G := G) Generated.Bindings.TwoSumsInputs.imported.program
    domain_bodies.prefixBodies domain_bodies.sumcheck.first domain_bodies.check domain_bodies.checkTable
    leftRaw firstState.point firstState.scalar leftBound (terminalTrue.1.2.1.trans (by decide +kernel))
  simp only [terminalTrue, decide_true] at leftTerminal
  normalize_table_readback [leftTable, rightTable, emptyLaw, lessLaw, leftTerminal]
    unfolding [producerCarried, validatorCarried, leftCaptured, rightCaptured, admitted]
  readback_table_loop round1
    [Generated.Bindings.TwoSumsInputs.imported.program, round_helpers true, context, suite,
      sites true, rightRaw, count, countSmall, rightShape, rightBound, firstState.frame]
    as secondLeftCaptured, secondRightCaptured, secondState, sameRight, secondHonest
  have terminalTrue := SumcheckDomainHelpers.terminal_condition rightRaw secondState sameRight rightBound secondHonest
  have rightTerminal := SumcheckDomainHelpers.check (G := G) Generated.Bindings.TwoSumsInputs.imported.program
    domain_bodies.prefixBodies domain_bodies.sumcheck.first domain_bodies.check domain_bodies.checkTable
    rightRaw secondState.point secondState.scalar rightBound (terminalTrue.1.2.1.trans (by decide +kernel))
  simp only [terminalTrue, decide_true] at rightTerminal
  normalize_table_readback [rightTerminal] unfolding
    [producerCarried, validatorCarried, leftCaptured, rightCaptured,
      secondLeftCaptured, secondRightCaptured, suite]
  apply Readback.done
  rfl

end ZkcSecurity.Examples.Components.TwoSums
