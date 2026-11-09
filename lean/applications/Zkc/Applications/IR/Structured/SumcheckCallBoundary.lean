module

public import Zkc.Applications.IR.Structured.SumcheckContractRequests
public import Zkc.Program.Polynomial.Coordinates

@[expose] public section

/-! The complete caller is its actual checked child invocation followed by its
owned terminal. Terminal laws quantify arbitrary returned child tuples and use
only the fixed public table's shape, never the child's iteration invariant. -/
namespace ZkcExamples.Structured.SumcheckCallBoundary
open Zkc.Source Zkc.Source.Structured
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open SumcheckContractBindings SumcheckContractInstantiation SumcheckContractRequests

set_option smartUnfolding false

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def terminal (raw : List F)
    (outputs : Values (Component (assignment F G)) SumcheckVerifierBodies.reduceOutputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) [.boolean]) :=
  SumcheckVerifierTerminal.ownedCheck (G := G) SumcheckSourceViews.unit 1 (some raw)
    (outputs.get (.there (.there (.there (.there .here)))))
    (outputs.get (.there (.there (.there (.there (.there .here))))))
    (outputs.get (.there (.there (.there (.there (.there (.there .here)))))))

set_option smartUnfolding true in
set_option backward.isDefEq.respectTransparency false in
/-- The terminal is the actual source suffix for every returned tuple, including
absent custody. This equation does not inspect or execute the child body. -/
theorem terminal_continuation (raw : List F) (claim : F) (count handle : Nat)
    (outputs : Values (Component (assignment F G)) SumcheckVerifierBodies.reduceOutputs) :
    SumcheckSourceVerifier.reduceCall.continuation.2.denote
      (participantMeaningWith (.silent _) (participantActions F G)
        (plainHelpers (F := F) (G := G) SumcheckSourceViews.unit) 1
        (SumcheckSourceViews.unit.plainProtocolTable F G) {})
      (Environment.prepend
        (SumcheckSourceVerifier.callEnvironment (some raw) (some claim)
          (some count) (some handle)) outputs) = terminal raw outputs := by
  have body : SumcheckSourceVerifier.reduceCall.continuation.2 =
      (.letOp (.mark "s9") .nil .nil <|
       .letOp (.localCall SumcheckHelperBodies.checkHelper rfl 1 "s9")
         (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))) .nil <|
       .ret (.cons .here .nil)) := by kernel_rfl
  have exposed : SumcheckSourceVerifier.reduceCall.continuation.2.denote
      (participantMeaningWith (.silent _) (participantActions F G)
        (plainHelpers (F := F) (G := G) SumcheckSourceViews.unit) 1
        (SumcheckSourceViews.unit.plainProtocolTable F G) {})
      (Environment.prepend
        (SumcheckSourceVerifier.callEnvironment (some raw) (some claim)
          (some count) (some handle)) outputs) =
      (terminal raw outputs).bind (fun result => .done (.cons (result.get .here) .nil)) := by
    rw [body]
    cases outputs with
    | cons x0 tail => cases tail with
      | cons x1 tail => cases tail with
        | cons x2 tail => cases tail with
          | cons x3 tail => cases tail with
            | cons token tail => cases tail with
              | cons point tail => cases tail with
                | cons value tail =>
                  cases tail
                  simp only [Region.denote.eq_1, Region.denote.eq_3, Regions.denote.eq_1,
                    participantMeaningWith, protocolOperationWith, SiteObservations.silent,
                    PIR.Process.bind.eq_1, Operands.eval.eq_1, Operands.eval.eq_2,
                    Environment.prepend.eq_1, Environment.prepend.eq_2,
                    Environment.push.eq_1, Environment.push.eq_2,
                    Values.get.eq_1, Values.get.eq_2,
                    SumcheckSourceVerifier.callEnvironment,
                    SumcheckSourceVerifier.sourceRootInputs,
                    Values.absent.eq_1, Values.absent.eq_2,
                    terminal, SumcheckVerifierTerminal.ownedCheck]
                  apply congrArg (PIR.Process.bind _)
                  funext result
                  cases result with | cons decision rest => cases rest; rfl
  rw [exposed]
  conv_rhs => rw [← PIR.Process.bind_done (terminal raw outputs)]
  apply congrArg (PIR.Process.bind _)
  funext result
  cases result with | cons value rest => cases rest; rfl

/-- No callee-body equation is used: this is the actual linked root boundary. -/
theorem source_linked (raw : List F) (claim : F) (count handle : Nat) :
    SumcheckSourceViews.imported.program.participant F G 1
      (SumcheckSourceVerifier.sourceRootInputs (some raw) (some claim) (some count) (some handle)) =
    (childProcess raw claim count handle).bind (terminal raw) := by
  change SumcheckSourceViews.program.participant F G 1 _ = _
  rw [SumcheckSourceVerifier.verifier_linked]
  have child : childProcess (G := G) raw claim count handle =
      invokeProtocol (SumcheckSourceViews.unit.plainProtocolTable F G) SumcheckSourceBodies.reduceSignature
        SumcheckSourceVerifier.childContext 1
        (SumcheckSourceVerifier.childInputs (some claim) (some count) (some handle)) := by
    change (invokeProtocol (SumcheckSourceViews.unit.protocolTable F G) SumcheckSourceBodies.reduceSignature
      SumcheckSourceVerifier.childContext 1
      (SumcheckSourceVerifier.childInputs (some claim) (some count) (some handle))).interpret forgetSites = _
    exact SumcheckSourceViews.unit.protocolTable_forgetSites _ _ _ _
  rw [child]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Count refusal belongs to the child interface, including before its terminal. -/
theorem child_excess (raw : List F) (claim : F) (count handle : Nat) (large : SumcheckSourceNormalForms.reduceMaximum < count) :
    childProcess (G := G) raw claim count handle = .halt .refused := by
  change (invokeProtocol (SumcheckSourceViews.unit.protocolTable F G) SumcheckSourceBodies.reduceSignature
    SumcheckSourceVerifier.childContext 1
    (SumcheckSourceVerifier.childInputs (some claim) (some count) (some handle))).interpret forgetSites = _
  rw [SumcheckSourceViews.unit.protocolTable_forgetSites, SumcheckSourceVerifier.reduce_invoke_plain (F := F) (G := G)]
  exact SumcheckVerifierPrelude.reduce_excess (G := G) SumcheckSourceViews.unit SumcheckSourceVerifier.helperBodies SumcheckSourceVerifier.claimBodies
    SumcheckSourceVerifier.childContext 1 rfl (by decide) SumcheckSourceNormalForms.reduceMaximum count large none none none 0 [] claim (some handle)

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The actual shape guard and fixed-table decoding determine the point length. -/
theorem shape_dimension (n : Nat) (raw point : List F) (table : Table F n)
    (decoded : ofList? n raw = some table) (shape : PrimitiveLibrary.HasShape raw point.length 1) :
    point.length = n := by
  have equal := shape.length
  rw [ofList?_length raw table decoded, Nat.mul_one] at equal
  exact (Nat.pow_right_injective (by decide : 2 ≤ (2 : Nat)) equal).symm

/-- Exact caller terminal on arbitrary present point/value operands. Malformed
lengths return false; unrepresentable points stop before any acceptance. -/
theorem terminal_present (n : Nat) (raw : List F) (table : Table F n)
    (decoded : ofList? n raw = some table) (bounded : raw.length < indexLimit)
    (point : List F) (value : F) :
    SumcheckVerifierTerminal.actualOwnedCheck (G := G) SumcheckSourceViews.unit 1
      (some raw) (some point) (some value) =
    if point.length < indexLimit then
      .done (.cons (some (decide (point.length = n ∧
        extension n table (coordinates n point) = value))) .nil)
    else .halt .exhausted := by
  by_cases pointBound : point.length < indexLimit
  · rw [ite_eq_left pointBound]
    by_cases length : point.length = n
    · rw [SumcheckVerifierTerminal.terminal_decoded_length 1 n raw point value table decoded bounded length]
      simp only [length, true_and]
    · have malformed : ¬ PrimitiveLibrary.HasShape raw point.length 1 :=
        fun shape => length (shape_dimension n raw point table decoded shape)
      rw [SumcheckVerifierTerminal.terminal_malformed 1 raw point value bounded pointBound malformed]
      simp only [length, false_and, decide_false]
  · rw [ite_eq_right pointBound, SumcheckVerifierTerminal.terminal_decision, ite_eq_right pointBound]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
set_option backward.isDefEq.respectTransparency false in
/-- All seven slots are arbitrary. Only the actual selected V point/value outputs
can discharge the inherited fixed-table request. -/
theorem child_request_iff (raw : List F) (claim : F) (count handle : Nat)
    (table : Table F (0 + count)) (decoded : ofList? (0 + count) raw = some table)
    (outputs : Values (Component (assignment F G)) SumcheckVerifierBodies.reduceOutputs) :
    (childTerminal (G := G) 0 count).Holds SumcheckSourceVerifier.childContext
      (childBoundary raw claim count handle (.returned outputs))
      (childAssignments raw claim count handle) ↔
    match outputs.get (.there (.there (.there (.there (.there .here))))),
        outputs.get (.there (.there (.there (.there (.there (.there .here)))))) with
    | some point, some value => Residual 0 count table point value
    | _, _ => False := by
  refine (residual_terminal_iff (.parameter childTable) 0 count childPoint childValue rfl rfl
    _ _ _ raw rfl table decoded).trans ?_
  have pointRead := publicReductionCall.boundaryOfOutcome_returned_output {} 1
    (publicCallEnvironment (G := G) raw claim count handle) outputs childPoint
    (.there (.there (.there (.there (.there .here))))) rfl rfl
  have valueRead := publicReductionCall.boundaryOfOutcome_returned_output {} 1
    (publicCallEnvironment (G := G) raw claim count handle) outputs childValue
    (.there (.there (.there (.there (.there (.there .here)))))) rfl rfl
  change (∃ p v, _ = some p ∧ _ = some v ∧ Residual 0 count table p v) ↔ _
  erw [pointRead, valueRead]
  generalize outputs.get (.there (.there (.there (.there (.there .here))))) = point
  generalize outputs.get (.there (.there (.there (.there (.there (.there .here)))))) = value
  cases point <;> cases value <;> simp

end ZkcExamples.Structured.SumcheckCallBoundary
