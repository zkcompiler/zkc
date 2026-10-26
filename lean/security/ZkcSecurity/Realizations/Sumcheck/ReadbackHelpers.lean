module

public import ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers
public import ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers
public import ZkcSecurity.Families.Sumcheck.TableComponentReadbackTactics

@[expose] public section

/-! The source terminal checker follows from the installed honest table
invariant. Its index bounds are consequences of that invariant and the input
capacity law, rather than extra caller-specific transport obligations. -/
set_option autoImplicit false
namespace ZkcSecurity.Realizations.Sumcheck.ReadbackHelpers
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Families.Sumcheck.TableComponent
open ZkcExamples.Structured.SumcheckHelperBodies

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem terminal (program : Structured.Program) (bodies : ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers.Bodies program)
    (raw : List F) (state : PrefixState F (Domain.History (ringModel F G).toCarriers) 0)
    (original : state.original = raw) (bounded : raw.length < indexLimit)
    (honest : state.scalar = state.entries.sum) :
    Domain.callHelper (ringModel F G) program checkHelper.name [.data .boolean]
      [.data (.vector "bls12-381.fr" raw), .data (.vector "bls12-381.fr" state.point),
        .data (.field "bls12-381.fr" state.scalar)] = .returned [.data (.boolean true)] := by
  have truth := DomainHelpers.terminal_condition raw state original bounded honest
  have law := DomainHelpers.check (G := G) program bodies.terminal raw state.point state.scalar bounded
    (truth.1.2.1.trans (by decide +kernel))
  simpa only [truth, and_self, decide_true] using law

/-- Normalize the installed source helpers and pure/checkpoint structure.
Only proved arithmetic guards are reduced; the returned-state equations stay
available to the component contract instead of rewriting its representation. -/
macro "normalize_sumcheck_readback " "[" F:term ", " G:term ", " program:term ", " bodies:term "]"
    " unfolding " "[" definitions:term,* "]" : tactic =>
  `(tactic| repeat first
    | fail_if_no_progress (simp (disch := first | assumption | omega) only
        [terminal $program $bodies])
    | fail_if_no_progress (simp (disch := first | assumption | omega |
          (apply ZkcExamples.Structured.PrimitiveLibrary.hasShape_of_length <;> omega)) only
        [ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers.table (G := $G) $program ($bodies).sumcheck,
          ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers.empty (F := $F) (G := $G) $program ($bodies).sumcheck,
          ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers.less (F := $F) (G := $G) $program ($bodies).sumcheck])
    | fail_if_no_progress (
        normalize_table_readback [] unfolding
          [ReadbackRound.producerCarried, ReadbackRound.validatorCarried, $definitions,*]
        try simp (disch := omega) only [ite_eq_left, ite_eq_right])
    | fail_if_no_progress (simp only [PIR.Process.bind_assoc]))

end ZkcSecurity.Realizations.Sumcheck.ReadbackHelpers
