module

public import ZkcSecurityExamples.Gkr.HonestProducerRounds
public import Zkc.Protocols.Gkr.Source.VerifierProcess
public import Zkc.Protocols.Sumcheck.Source.VerifierHelpers
public import ZkcSecurityExamples.Gkr.HonestProducerPacketAlgorithm
public import ZkcSecurityExamples.Gkr.HonestHelpersSource
public import ZkcSecurityExamples.Gkr.HonestLineSource

@[expose] public section

/-! Complete coefficient packet stream computed by the actual producer. -/



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZkcSecurity.Realizations.Gkr.HonestProducerPackets
open Zkc Source Structured
open Zkc.Polynomial Zkc.Polynomial.Multilinear CoefficientRows
open ZkcExamples.Structured GkrSourceLaws SumcheckVerifierHelpers Generated.Presentations.Gkr.Root

variable {F G : Type}

variable [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

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
        ((line)[index + 1]?.getD 0)) fun _ => .done () := by
  simp only [proverCoefficientProcess, Evaluation.ComponentTables.toOn, Generated.Presentations.Gkr.payload,
    Generated.Presentations.Gkr.program, GkrSourceViews.program]
  rw [HonestHelpers.element_after_plain line index lineBound indexBound]
  rfl


/-- All indexed sends are extracted by the actual checked readback helper. -/
theorem coefficient_fold (ctx : ProtocolContext) (line : List F) (start count : Nat)
    (lineBound : line.length < indexLimit) (indexBound : start + count < indexLimit) :
    Finite.fold (fun (_ : Unit) index => proverCoefficientProcess (G := G) ctx index (some line))
      (List.range' start count) () = sendTail ctx (tail line start count) := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [List.range'_succ, Finite.fold, line_coefficient ctx line start
      lineBound (by omega), tail_succ]
    simp only [PIR.Process.bind, sendTail]
    congr 1
    funext _
    exact ih (start + 1) (by omega)

/-- The admitted actual repeat emits the entire coefficient suffix. -/
theorem coefficients (ctx : ProtocolContext) (separate : ctx.roles 1 ≠ ctx.roles 0)
    (line : List F) (count : Nat) (bounded : count ≤ 4)
    (lineBound : line.length < indexLimit) :
    denoteRepeat coefficientSpec ctx (ctx.roles 0) (some count) (.cons none .nil)
      (.cons (some line) .nil) (coefficientFn (F := F) (G := G) ctx (ctx.roles 0)) =
      (sendTail ctx (tail line 0 count)).bind fun _ => .done (proverCoefficientState) := by
  change denoteRepeat coefficientSpec ctx (ctx.roles 0) (some count) proverCoefficientState
    (.cons (some line) .nil) (coefficientFn (F := F) (G := G) ctx (ctx.roles 0)) = _
  rw [proverCoefficient_fold ctx (.ofSeparate separate (by decide)) (some line) count bounded _ ()
    (proverCoefficientState_masked ctx _ rfl)]
  rw [coefficient_fold ctx line 0 count lineBound (by
    simp only [indexLimit]; omega)]

end ZkcSecurity.Realizations.Gkr.HonestProducerPackets
