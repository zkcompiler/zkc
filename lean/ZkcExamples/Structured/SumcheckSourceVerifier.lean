module

public import ZkcExamples.Structured.SumcheckSourceAssociations
public import ZkcExamples.Structured.SumcheckSourceNormalForms
public import ZkcExamples.Structured.SumcheckVerifierBodies
public import ZkcExamples.Structured.SumcheckVerifierHelpers
public import ZkcExamples.Structured.SumcheckVerifierPrelude
public import ZkcExamples.Structured.SumcheckVerifierProcess
public import ZkcExamples.Structured.SumcheckVerifierTerminal
public import Zkc.Semantics.Boundary
public import Zkc.Source.Structured.ContractComposition

@[expose] public section

/-! The complete original Source verifier. The root's participant normal form,
with the generated normal form of the applied `Reduce` body substituted at its
application, is `SumcheckSourceNormalForms`; the equations below restate it
with the repeat admission (`admittedRounds`) and the terminal check. -/
namespace ZkcExamples.Structured.SumcheckSourceVerifier
open Zkc.Source Zkc.Source.Structured SumcheckSourceViews

/-- Exact helper associations supplied by the complete-source helper package. -/
theorem helperBodies : SumcheckVerifierHelpers.Bodies unit.definitions :=
  ⟨SumcheckSourceAssociations.empty_association,
   SumcheckSourceAssociations.append_association,
   SumcheckSourceAssociations.width_association,
   SumcheckSourceAssociations.variables_association,
   SumcheckSourceAssociations.values_association⟩

/-- The original full Source Reduce tree has maximum 2 independently of Reduction. -/
theorem reduce_raw : reduceDefinition.raw = (SumcheckVerifierBodies.reduceBody 2).erase := by
  refine SumcheckSourceViews.reduce_raw.trans ?_
  unfold SumcheckVerifierBodies.reduceBody SumcheckVerifierBodies.roundBody
    SumcheckVerifierBodies.reduceReturn
  rfl

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The actual complete Source protocol table selects the maximum-two child body. -/
theorem reduce_invoke_plain (ctx : ProtocolContext) (self : Nat)
    (arguments : Values (Component (assignment F G)) SumcheckVerifierBodies.reduceInputs) :
    invokeProtocol (unit.plainProtocolTable F G) SumcheckSourceBodies.reduceSignature
      ctx self arguments = SumcheckVerifierPrelude.reduceDenote 2 unit ctx self arguments :=
  SumcheckSourceNormalForms.reduce_view ctx self arguments _ rfl

def sourceRootInputs (rawV : Option (List F)) (claim : Option F)
    (count service : Option Nat) :
    Values (Component (assignment F G)) SumcheckSourceBodies.runSignature.inputs :=
  .cons rawV (.cons claim (.cons count (.cons service .nil)))

/-- The actual root application qualifies every child action at this site. -/
def childContext : ProtocolContext :=
  ProtocolContext.enter {} "label_726564756365" [0, 1]

/-- Foreign inputs to the child are absent at V; no prover prerequisite is imposed. -/
def childInputs (claim : Option F) (count service : Option Nat) :
    Values (Component (assignment F G)) SumcheckSourceBodies.reduceSignature.inputs :=
  .cons none (.cons none (.cons none (.cons claim (.cons count (.cons service .nil)))))

/-- The call and terminal suffix are recovered from the actual source tree. -/
abbrev reduceCall : CallOccurrence SumcheckSourceBodies.runBody :=
  (callInventory SumcheckSourceBodies.runBody).get ⟨0, by decide⟩

/-- Evaluated verifier environment after the actual root prefix. The foreign
Table construction contributes absent outputs; the caller's V inputs survive. -/
def callEnvironment (rawV : Option (List F)) (claim : Option F) (count service : Option Nat) :
    Environment (Component (assignment F G)) reduceCall.callSite.context :=
    Environment.prepend (Environment.prepend (Environment.prepend
      (Environment.prepend (Environment.prepend
        (sourceRootInputs (G := G) rawV claim count service).get .nil)
        (.cons (some 1) .nil)) .nil)
      (Values.absent (assignment F G) SumcheckSourceBodies.tableHelper.outputs)) .nil

/-- Complete Source invocation in an arbitrary caller context, including its
actual child label, retained rawV and terminal owned by the original self. -/
theorem verifier_context_optional (ctx : ProtocolContext) (self : Nat)
    (verifier : self = ctx.roles 1) (separate : ctx.roles 0 ≠ self)
    (rawV : Option (List F)) (claim : Option F) (count service : Option Nat) :
    invokeProtocol (unit.plainProtocolTable F G) SumcheckSourceBodies.runSignature
      ctx self (sourceRootInputs rawV claim count service) =
      (SumcheckVerifierPrelude.admittedRounds 2
        (ctx.enter "label_726564756365" [0, 1]) count service claim).bind
        (fun pc => SumcheckVerifierTerminal.actualOwnedCheck unit self rawV pc.1 pc.2) := by
  refine (SumcheckSourceNormalForms.verifier_invoke helperBodies ctx self verifier separate
    rawV claim count service).trans ?_
  subst self
  unfold SumcheckSourceNormalForms.verifierProcess
  rw [SumcheckVerifierPrelude.verifierReduce_rounds unit helperBodies (SumcheckSourceNormalForms.reduceContext ctx) separate]
  simp only [PIR.Proc.bind_assoc, PIR.Proc.bind]
  refine congrArg (PIR.Proc.bind _) (funext fun pc => ?_)
  conv_rhs => rw [← PIR.Proc.bind_done (SumcheckVerifierTerminal.actualOwnedCheck unit _ rawV pc.1 pc.2)]
  refine congrArg (PIR.Proc.bind _) (funext fun checked => ?_)
  cases checked with
  | cons value rest => cases rest; rfl

/-- The complete root retains rawV and invokes its actual terminal under the
caller's immutable participant identity and mapped child context. -/
theorem root_context_expansion (ctx : ProtocolContext) (self : Nat)
    (verifier : self = ctx.roles 1) (separate : ctx.roles 0 ≠ self)
    (rawV : Option (List F)) (claim : Option F) (count service : Option Nat) :
    invokeProtocol (unit.plainProtocolTable F G) SumcheckSourceBodies.runSignature
      ctx self (sourceRootInputs rawV claim count service) =
      (invokeProtocol (unit.plainProtocolTable F G) SumcheckSourceBodies.reduceSignature
        (ctx.enter "label_726564756365" [0, 1]) self (childInputs claim count service)).bind
        fun result => SumcheckVerifierTerminal.actualOwnedCheck unit self rawV
          (result.get (.there (.there (.there (.there .here)))))
          (result.get (.there (.there (.there (.there (.there .here)))))) := by
  rw [verifier_context_optional ctx self verifier separate,
    reduce_invoke_plain (ctx.enter "label_726564756365" [0, 1]) self (childInputs claim count service)]
  erw [SumcheckVerifierPrelude.reduce_optional unit helperBodies (ctx.enter "label_726564756365" [0, 1])
    self verifier separate 2 none none none claim count service]
  refine Eq.trans ?_ (PIR.Proc.bind_assoc _ _ _).symm
  rfl

/-- Root construction skips P work and passes the unchanged raw V vector to check. -/
theorem verifier_linked (rawV : Option (List F)) (claim : Option F)
    (count service : Option Nat) :
    program.participant F G 1 (sourceRootInputs rawV claim count service) =
      (invokeProtocol (unit.plainProtocolTable F G) SumcheckSourceBodies.reduceSignature
        childContext 1 (childInputs claim count service)).bind fun result =>
          SumcheckVerifierTerminal.actualOwnedCheck unit 1 rawV
            (result.get (.there (.there (.there (.there .here)))))
            (result.get (.there (.there (.there (.there (.there .here)))))) :=
  (unit.protocolTable_forgetSites (F := F) (G := G)
    SumcheckSourceBodies.runSignature {} 1 (sourceRootInputs rawV claim count service)).trans
    (root_context_expansion {} 1 rfl (by decide) rawV claim count service)

/-- Complete original Source verifier: maximum-two admission, actual rounds,
then the actual terminal on the unchanged raw verifier vector. -/
theorem verifier_optional (rawV : Option (List F)) (claim : Option F)
    (count service : Option Nat) :
    program.participant F G 1 (sourceRootInputs rawV claim count service) =
      (SumcheckVerifierPrelude.admittedRounds 2 childContext count service claim).bind
        (fun pc => SumcheckVerifierTerminal.actualOwnedCheck unit 1 rawV pc.1 pc.2) :=
  (unit.protocolTable_forgetSites (F := F) (G := G)
    SumcheckSourceBodies.runSignature {} 1 (sourceRootInputs rawV claim count service)).trans
    (verifier_context_optional {} 1 rfl (by decide) rawV claim count service)

/-- Missing count stops before rounds or terminal work. -/
theorem verifier_missing (rawV : Option (List F)) (claim : Option F)
    (service : Option Nat) :
    program.participant F G 1 (sourceRootInputs rawV claim none service) =
      .halt .incomplete := by
  rw [verifier_optional]
  rfl

/-- Source's own maximum is two, independently of the separate Reduction unit. -/
theorem verifier_excess (rawV : Option (List F)) (claim : Option F)
    (count : Nat) (service : Option Nat) (large : 2 < count) :
    program.participant F G 1 (sourceRootInputs rawV claim (some count) service) =
      .halt .refused := by
  rw [verifier_optional, SumcheckVerifierPrelude.admittedRounds_excess 2 count _ large]
  rfl

/-- Zero rounds still perform the actual source terminal and need no service. -/
theorem verifier_zero (rawV : Option (List F)) (claim : Option F)
    (service : Option Nat) :
    program.participant F G 1 (sourceRootInputs rawV claim (some 0) service) =
      SumcheckVerifierTerminal.actualOwnedCheck unit 1 rawV (some []) claim := by
  rw [verifier_optional, SumcheckVerifierPrelude.admittedRounds_zero]
  rfl

/-- The actual terminal consumes the point length established by successful rounds. -/
private theorem repeat_checked (count : Nat) (raw : List F) (claim : Option F)
    (service : Option Nat) (table : Zkc.Polynomial.Multilinear.Table F count)
    (decoded : Zkc.Polynomial.Multilinear.ofList? count raw = some table)
    (vectorBound : raw.length < indexLimit) :
    (PIR.repeatN count (SumcheckVerifierLaws.roundPlain (G := G) childContext service)
      (some [], claim)).bind
      (fun pc => SumcheckVerifierTerminal.actualOwnedCheck unit 1 (some raw) pc.1 pc.2) =
    (PIR.repeatN count (SumcheckVerifierLaws.roundPlain childContext service)
      (some [], claim)).bind (fun pc => match pc.1, pc.2 with
        | some point, some value => .done (.cons (some (decide
            (point.length = count ∧ Zkc.Polynomial.Multilinear.extension count table
              (Zkc.Polynomial.coordinates count point) = value))) .nil)
        | _, _ => .halt .incomplete) := by
  let interaction : PIR.Interaction (participantInterface F G) :=
    ⟨Unit, Unit, fun _ => (), fun _ _ => True, fun _ _ _ => ()⟩
  apply PIR.Boundary.bind_congr_returns interaction _ _ ()
    (SumcheckVerifierLaws.repeat_returns interaction childContext service count [] claim ())
  intro result phase returned
  obtain ⟨point, present, length, _, _⟩ := returned
  rcases result with ⟨maybePoint, maybeClaim⟩
  dsimp only at present ⊢
  subst maybePoint
  cases maybeClaim with
  | none => rw [SumcheckVerifierTerminal.terminal_optional]
  | some value =>
    have pointLength : point.length = count := by simpa using length
    simpa [pointLength] using
      SumcheckVerifierTerminal.terminal_decoded_length 1 count
        raw point value table decoded vectorBound pointLength

/-- The complete Source equation with a nonempty prefix and mapped roles [2,0]
keeps root self0 as the terminal owner for every optional input and reply. -/
theorem verifier_permuted_optional (rawV : Option (List F)) (claim : Option F)
    (count service : Option Nat) :
    invokeProtocol (unit.plainProtocolTable F G) SumcheckSourceBodies.runSignature
      ⟨some "outer", roleSubstitution [2, 0]⟩ 0
      (sourceRootInputs rawV claim count service) =
      (SumcheckVerifierPrelude.admittedRounds 2
        (ProtocolContext.enter ⟨some "outer", roleSubstitution [2, 0]⟩
          "label_726564756365" [0, 1]) count service claim).bind
        (fun pc => SumcheckVerifierTerminal.actualOwnedCheck unit 0 rawV pc.1 pc.2) :=
  verifier_context_optional _ 0 rfl (by decide) rawV claim count service

/-- A decoded raw V table supplies the terminal mathematical checker. Point
length follows from successful rounds; initial claim and service remain optional. -/
theorem verifier_checked (count : Nat) (admitted : count ≤ 2)
    (raw : List F) (claim : Option F) (service : Option Nat)
    (table : Zkc.Polynomial.Multilinear.Table F count)
    (decoded : Zkc.Polynomial.Multilinear.ofList? count raw = some table)
    (vectorBound : raw.length < indexLimit) :
    program.participant F G 1 (sourceRootInputs (some raw) claim (some count) service) =
      (PIR.repeatN count (SumcheckVerifierLaws.roundPlain childContext service)
        (some [], claim)).bind (fun pc => match pc.1, pc.2 with
          | some point, some value => .done (.cons (some (decide
              (point.length = count ∧ Zkc.Polynomial.Multilinear.extension count table
                (Zkc.Polynomial.coordinates count point) = value))) .nil)
          | _, _ => .halt .incomplete) := by
  rw [verifier_optional]
  simp only [SumcheckVerifierPrelude.admittedRounds, admitted, ↓reduceIte]
  exact repeat_checked count raw claim service table decoded vectorBound

end ZkcExamples.Structured.SumcheckSourceVerifier
