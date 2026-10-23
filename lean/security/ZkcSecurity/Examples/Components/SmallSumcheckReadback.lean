module

public import ZkcSecurity.Examples.Components.SmallSumcheckReadbackRound
public import Zkc.Construction.DomainCalculations
public import ZkcSecurity.FiatShamir.HonestReadbackLoops
public import ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer
public import ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator
public import ZkcSecurity.Families.Sumcheck.TableComponentExecution

@[expose] public section

/-! Honest read-back of the actual exported complete SmallSumcheck pair.
The constructed prefix, loop, terminal checker and full result projection are
all retained. This is consumed by the fixed Subject's compiled experiment. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
namespace ZkcSecurity.Examples.Components.SmallSumcheck
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured
open ZkcSecurity.Families.Sumcheck.TableComponent
open ZkcSecurity.FiatShamir
open ReadbackRound
open ZkcSecurity.Examples.Generated.Components.SmallSumcheckRounds
open ZkcExamples.Structured.Generated.Constructed

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

set_option linter.unusedSimpArgs false in
theorem root_readback (context : Context)
    (suite : context.suite = "merlin3.bls12-381.fr64be/0")
    (sites : ∀ index, Sites round0.plan context index)
    (raw : List F) (count : Nat) (admitted : count ≤ round0.maximum)
    (length : raw.length = 2 ^ count) (bounded : raw.length < indexLimit)
    (history : Domain.History (ringModel F G).toCarriers) :
    Readback (fun _ result => HonestCompiled.acceptanceAt 0 result.values = some true)
      (Domain.participant (ringModel F G) Generated.Bindings.SmallSumcheckInputs.imported.program context SmallSumcheckProducer.artifact
        [.data (.vector "bls12-381.fr" raw), .data (.index count),
          .transcript "merlin3.bls12-381.fr64be/0" history])
      (Domain.participant (ringModel F G) Generated.Bindings.SmallSumcheckInputs.imported.program context SmallSumcheckValidator.artifact
        [.data (.vector "bls12-381.fr" raw), .data (.field "bls12-381.fr" raw.sum),
          .data (.index count), .transcript "merlin3.bls12-381.fr64be/0" history]) := by
  dsimp only [round0.maximum, round0.descriptor] at admitted
  have countSmall : count < 64 := lt_of_le_of_lt admitted (by decide +kernel)
  have countBound : count < indexLimit := lt_trans countSmall (by decide +kernel)
  have shape : PrimitiveLibrary.HasShape raw count 1 :=
    PrimitiveLibrary.hasShape_of_length raw count 1 (by decide) countSmall (by simpa using length)
  have tableLaw := SumcheckDomainHelpers.table (G := G) Generated.Bindings.SmallSumcheckInputs.imported.program
    helper_bodies.sumcheck raw count 1 shape bounded countBound (by decide +kernel)
  have emptyLaw := SumcheckDomainHelpers.empty (F := F) (G := G) Generated.Bindings.SmallSumcheckInputs.imported.program
    helper_bodies.sumcheck
  have lessLaw := SumcheckDomainHelpers.less (F := F) (G := G) Generated.Bindings.SmallSumcheckInputs.imported.program
    helper_bodies.sumcheck count count countBound countBound
  rw [SmallSumcheckProducer.participant_eq, SmallSumcheckValidator.participant_eq]
  unfold_component_bodies [SmallSumcheckProducer.view, SmallSumcheckValidator.view]
  normalize_table_readback [tableLaw, emptyLaw, lessLaw] unfolding [admitted]
  readback_table_loop round0
    [Generated.Bindings.SmallSumcheckInputs.imported.program, round_helpers, context, suite,
      sites, raw, count, countSmall, length, bounded, history]
    as leftCaptured, rightCaptured, state, sameOriginal, honest
  have terminalTrue := SumcheckDomainHelpers.terminal_condition raw state sameOriginal bounded honest
  have pointBound : state.point.length < indexLimit :=
    terminalTrue.1.2.1.trans (by decide +kernel)
  have terminalLaw := call_check (G := G) raw state.point state.scalar bounded pointBound
  simp only [terminalTrue, decide_true] at terminalLaw
  normalize_table_readback [terminalLaw] unfolding
    [producerCarried, validatorCarried, leftCaptured, rightCaptured]
  exact .done rfl

end ZkcSecurity.Examples.Components.SmallSumcheck
