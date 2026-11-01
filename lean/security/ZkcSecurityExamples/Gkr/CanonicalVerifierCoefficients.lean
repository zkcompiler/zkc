module

public import ZkcSecurityExamples.Gkr.HonestProducerSource
public import Zkc.Protocols.Sumcheck.Source.VerifierHelpers
public import Zkc.Protocols.Gkr.Source.VerifierProcess
public import ZkcExamples.Structured.GkrLayerReading

@[expose] public section

/-! The actual verifier coefficient repeat, retaining its inner source index
and every supplied coefficient, without a polynomial or transcript premise. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.CanonicalVerifier
open Zkc Source Structured
open ZkcExamples.Structured Generated.Presentations.Gkr.Root SumcheckVerifierHelpers
open HonestProducerSource HonestProducerObservedLayers
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

theorem coefficient_reads (ctx : ProtocolContext) (coefficients : List F) :
    (verifierCoefficientProcess (F := F) (G := G) ctx (some coefficients)).interpret Occurrence.actions =
      (((GkrVerifier.lineCoefficient ctx coefficients).interpret CommonAdapter.embed).interpret
        Occurrence.actions).bind (fun next => .done (some next)) := by
  simp only [verifierCoefficientProcess, Evaluation.ComponentTables.toOn, Generated.Presentations.Gkr.payload,
    Generated.Presentations.Gkr.program, GkrSourceViews.program, GkrVerifier.lineCoefficient,
    PIR.Process.interpret, CommonAdapter.embed, Occurrence.actions, PIR.Process.bind,
    GkrRoundsReading.append_plain]
  rfl

theorem coefficients_repeat (ctx : ProtocolContext) (separate : ctx.roles 0 ≠ ctx.roles 1)
    (site : String) (count : Nat) (bounded : count ≤ 4) (coefficients : List F) :
    denoteRepeatOn (carriers := uniformCarriers F G) coefficientSpec ctx (ctx.roles 1) (some count)
      (verifierCoefficientState (some coefficients)) ((SourceRows.CoefficientCaptures.pack { line := none }))
      (fun args => coefficientBody.denote (participantMeaningWithOn (ringModel F G) (.silent _)
        Occurrence.actions observedHelpers (ctx.roles 1) [] ctx Occurrence.iterations) args.get)
      Occurrence.iterations site =
      (validatorCoefficients ctx (qualifyProtocolSite ctx.applicationPrefix site) 0 count coefficients).bind
        (fun next => .done (verifierCoefficientState (some next))) := by
  have repeated := Zkc.Source.Structured.LoopPresentation.present (carriers := uniformCarriers F G) coefficientSpec ctx (ctx.roles 1) (by simp)
    ((SourceRows.CoefficientCaptures.pack { line := none }))
    (fun args => coefficientBody.denote (participantMeaningWithOn (ringModel F G) (.silent _)
      Occurrence.actions observedHelpers (ctx.roles 1) [] ctx Occurrence.iterations) args.get)
    Occurrence.iterations site
    (fun coefficients : List F => verifierCoefficientState (some coefficients))
    (fun coefficients => verifierCoefficientState_masked ctx _ rfl _)
    (fun coefficients _ => (((GkrVerifier.lineCoefficient ctx coefficients).interpret CommonAdapter.embed).interpret
      Occurrence.actions)) (by
      intro coefficients index
      erw [coefficient_occurrence (F := F) (G := G) ctx (ctx.roles 1) []
        ((SourceRows.CoefficientArguments.pack {
            index := some index,
            coefficients := some coefficients,
            line := none
          })), verifierCoefficient_process ctx _ rfl (.ofSeparate separate (by decide)) index (some coefficients) none,
        PIR.Process.interpret_bind, coefficient_reads, PIR.Process.bind_assoc]) count bounded _ coefficients (verifierCoefficientState_masked ctx _ rfl _)
  rw [repeated]
  rfl

end ZkcSecurity.Realizations.Gkr.CanonicalVerifier
