module

public import ZkcSecurity.Realizations.Gkr.HonestHelpersSource
public import ZkcExamples.Structured.GkrVerifierProcess
public import ZkcExamples.Structured.SumcheckVerifierHelpers
public import ZkcExamples.Structured.Generated.Presentations.Gkr

@[expose] public section

/-! Exact packet equations at the source normal form's output-point and line
coefficient callbacks. Line coefficient extraction is proved here; computing
the line polynomial in helper69 is a separate obligation. -/

namespace ZkcSecurity.Realizations.Gkr.HonestPackets
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceLaws SumcheckVerifierHelpers Generated.Presentations.Gkr.Root

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

set_option backward.isDefEq.respectTransparency false

/-- Every delivered output challenge is appended to the entire existing point. -/
theorem output_point (ctx : ProtocolContext) (point : List F) :
    proverOutputProcess (G := G) ctx (some point) =
      .call (.receive (.field scalarDomain) (GkrVerifier.outputDeliverySite ctx) (ctx.roles 1)) fun challenge =>
      .done (some (point ++ [challenge])) := by
  simp only [proverOutputProcess, Evaluation.ComponentTables.toOn, Generated.Presentations.Gkr.payload,
    Generated.Presentations.Gkr.program, GkrSourceViews.program]
  apply congrArg (PIR.Process.call (I := participantInterface F G)
    (.receive (.field scalarDomain) (GkrVerifier.outputDeliverySite ctx) (ctx.roles 1)))
  funext challenge
  rw [closed_invoke_plain]
  change ((invoke (helpers (G := G)) GkrSourceBodies.appendHelper _).interpret _).bind _ = _
  rw [append_equation]
  rfl

/-- The source reads the coefficient at index + 1, retaining its checked
index bound even when the requested position is beyond the vector. -/
theorem line_coefficient (ctx : ProtocolContext) (line : List F) (index : Nat)
    (lineBound : line.length < indexLimit) (indexBound : index + 1 < indexLimit) :
    proverCoefficientProcess (G := G) ctx index (some line) =
      .call (.send (ty := .field scalarDomain) (GkrVerifier.lineCoefficientSite ctx) (ctx.roles 1)
        (line[index + 1]?.getD 0)) fun _ => .done () := by
  simp only [proverCoefficientProcess, Evaluation.ComponentTables.toOn, Generated.Presentations.Gkr.payload,
    Generated.Presentations.Gkr.program, GkrSourceViews.program]
  rw [HonestHelpers.element_after_plain line index lineBound indexBound]
  rfl

end ZkcSecurity.Realizations.Gkr.HonestPackets
