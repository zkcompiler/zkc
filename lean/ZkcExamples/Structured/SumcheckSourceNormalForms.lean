module

public import ZkcExamples.Structured.Generated.Scalar.SumcheckSourceLibrary

public import ZkcExamples.Structured.SumcheckSourceViews
public import ZkcExamples.Structured.SumcheckPreludeNormalForms
public import ZkcExamples.Structured.NormalFormSteps
public import Zkc.Source.Structured.NormalForm.Presentation

@[expose] public section

/-! Mathematical presentations under explicit checked helper-body laws.
The participant normalizer constructs each form directly from the typed body.
These library laws retain their optional-input and complete-return statements;
source-facing role/invocation views are generated separately by RoleViews.
No family traversal or printer template supplies the source interpretation. -/
namespace ZkcExamples.Structured.SumcheckSourceNormalForms
open Zkc.Source Zkc.Source.Structured SumcheckVerifierHelpers PrimitiveLibrary

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

private abbrev one {ty : Ty} (value : Option (assignment F G ty)) :
    Values (Component (assignment F G)) [ty] := .cons value .nil

/-! Protocol applications: the child context (application prefix and role mapping)
and the callee's invocation in this unit. -/
/-- The child context of the `reduce` application: its sites are qualified by the
application site and its roles map to the caller's roles [0, 1]. -/
abbrev reduceContext (ctx : ProtocolContext) : ProtocolContext :=
  ctx.enter "label_726564756365" [0, 1]

/-- The repeat maximum of the applied `reduce` body in this unit. -/
abbrev reduceMaximum : Nat := 2

/-- The checked body of `reduce` at any context, between its input and output
masks, with this unit's plain tables. -/
theorem reduce_view (ctx : ProtocolContext) (self : Nat) (args masked : Values (Component (assignment F G)) [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"])
    (mask : maskValues self (ctx.mapScopes [[0], [0], [0], [1], [1], [0, 1], [1]]) args = masked) :
    invokeProtocol (SumcheckSourceViews.unit.plainProtocolTable F G) SumcheckSourceBodies.reduceSignature ctx self args =
      ((SumcheckVerifierBodies.reduceBody reduceMaximum).denote
        (participantMeaningWith (.silent _) (participantActions F G) (plainHelpers (F := F) (G := G) SumcheckSourceViews.unit) self (SumcheckSourceViews.unit.plainProtocolTable F G) ctx) masked.get).bind
        (fun out => .done (maskValues self (ctx.mapScopes [[0], [0], [0], [0], [1], [1]]) out)) := by
  rw [← mask]
  exact protocol_invoke_body_view (.silent _) (participantActions F G) (plainHelpers (F := F) (G := G) SumcheckSourceViews.unit)
    SumcheckSourceViews.unit.protocols SumcheckSourceViews.unit.protocolsLinked SumcheckSourceViews.reduceDefinition
    SumcheckSourceViews.reduce_member (SumcheckVerifierBodies.reduceBody reduceMaximum)
      (SumcheckSourceViews.reduceDefinition.exactBody.symm.trans
        (congrArg Region.erase Generated.Scalar.SumcheckSourceLibrary.reduce_body)) ctx self args

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The returned components kept at role 1; the others are masked away. -/
theorem reduce_verifier_outputs (ctx : ProtocolContext) (separate : ctx.roles 0 ≠ ctx.roles 1)
    (values : Values (Component (assignment F G)) [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .field "bls12-381.fr"]) :
    maskValues (ctx.roles 1) ((reduceContext ctx).mapScopes [[0], [0], [0], [0], [1], [1]]) values =
      .cons none (.cons none (.cons none (.cons none (.cons (values.get (.there (.there (.there (.there .here))))) (.cons (values.get (.there (.there (.there (.there (.there .here)))))) .nil))))) := by
  cases values with | cons value0 values =>
    cases values with | cons value1 values =>
      cases values with | cons value2 values =>
        cases values with | cons value3 values =>
          cases values with | cons value4 values =>
            cases values with | cons value5 values =>
              cases values
              simp [maskValues, ProtocolContext.mapScopes, ProtocolContext.enter, roleSubstitution,
                Participant.restrict, Ne.symm separate, Values.get]

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The returned components kept at role 0; the others are masked away. -/
theorem reduce_prover_outputs (ctx : ProtocolContext) (separate : ctx.roles 1 ≠ ctx.roles 0)
    (values : Values (Component (assignment F G)) [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .field "bls12-381.fr"]) :
    maskValues (ctx.roles 0) ((reduceContext ctx).mapScopes [[0], [0], [0], [0], [1], [1]]) values =
      .cons (values.get .here) (.cons (values.get (.there .here)) (.cons (values.get (.there (.there .here))) (.cons (values.get (.there (.there (.there .here)))) (.cons none (.cons none .nil))))) := by
  cases values with | cons value0 values =>
    cases values with | cons value1 values =>
      cases values with | cons value2 values =>
        cases values with | cons value3 values =>
          cases values with | cons value4 values =>
            cases values with | cons value5 values =>
              cases values
              simp [maskValues, ProtocolContext.mapScopes, ProtocolContext.enter, roleSubstitution,
                Participant.restrict, Ne.symm separate, Values.get]

/-- The typed body's process at one participant, with this unit's tables. -/
def runFn (ctx : ProtocolContext) (self : Nat) :
    RegionFunction (Component (assignment F G)) (participantInterface F G)
      ([.vector "bls12-381.fr", .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"], [.boolean]) :=
  fun args => SumcheckSourceBodies.runBody.denote
    (participantMeaningWith (.silent _) (participantActions F G) (plainHelpers (F := F) (G := G) SumcheckSourceViews.unit) self (SumcheckSourceViews.unit.plainProtocolTable F G) ctx) args.get

/-- The checked body of `run` at any context, between its input and output
masks, with this unit's plain tables. -/
theorem run_view (ctx : ProtocolContext) (self : Nat) (args masked : Values (Component (assignment F G)) [.vector "bls12-381.fr", .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"])
    (mask : maskValues self (ctx.mapScopes [[0, 1], [1], [0, 1], [1]]) args = masked) :
    invokeProtocol (SumcheckSourceViews.unit.plainProtocolTable F G) SumcheckSourceBodies.runSignature ctx self args =
      (SumcheckSourceBodies.runBody.denote
        (participantMeaningWith (.silent _) (participantActions F G) (plainHelpers (F := F) (G := G) SumcheckSourceViews.unit) self (SumcheckSourceViews.unit.plainProtocolTable F G) ctx) masked.get).bind
        (fun out => .done (maskValues self (ctx.mapScopes [[1]]) out)) := by
  rw [← mask]
  exact protocol_invoke_body_view (.silent _) (participantActions F G) (plainHelpers (F := F) (G := G) SumcheckSourceViews.unit)
    SumcheckSourceViews.unit.protocols SumcheckSourceViews.unit.protocolsLinked SumcheckSourceViews.runDefinition
    SumcheckSourceViews.run_member (SumcheckSourceBodies.runBody) SumcheckSourceViews.run_raw ctx self args

/-- The verifier's normal form of the whole body. -/
def verifierProcess (ctx : ProtocolContext) (raw : Option (List F)) (claim : Option F) (count service : Option Nat) :
    PIR.Process (participantInterface F G)
      (Values (Component (assignment F G)) [.boolean]) :=
  (Participant.owned (ctx.roles 1) (ctx.roles 1) (invoke (plainHelpers (F := F) (G := G) SumcheckSourceViews.unit).closed SumcheckSourceBodies.pendingHelper) (.cons claim .nil)).bind fun (pendingReturned : Values (Component (assignment F G)) [.vector "bls12-381.fr", .field "bls12-381.fr"]) =>
  (SumcheckPreludeNormalForms.verifierReduceProcess SumcheckSourceViews.unit reduceMaximum (reduceContext ctx) (pendingReturned.get .here) (pendingReturned.get (.there .here)) count service).bind fun (reduceReturned : Values (Component (assignment F G)) [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .field "bls12-381.fr"]) =>
  (Participant.owned (ctx.roles 1) (ctx.roles 1) (invoke (plainHelpers (F := F) (G := G) SumcheckSourceViews.unit).closed SumcheckSourceBodies.checkHelper) (.cons raw (.cons (reduceReturned.get (.there (.there (.there (.there .here))))) (.cons (reduceReturned.get (.there (.there (.there (.there (.there .here)))))) .nil)))).bind fun (checkReturned : Values (Component (assignment F G)) [.boolean]) =>
  .done (.cons (checkReturned.get .here) .nil : Values (Component (assignment F G)) [.boolean])

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The returned components kept at role 1; the others are masked away. -/
theorem reduce_verifierReduce_returned (ctx : ProtocolContext) (separate : ctx.roles 0 ≠ ctx.roles 1)
    (values : Values (Component (assignment F G)) [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .field "bls12-381.fr"]) :
    maskValues (ctx.roles 1) (ctx.mapScopes [[0], [0], [0], [0], [1], [1]]) values =
      .cons none (.cons none (.cons none (.cons none (.cons (values.get (.there (.there (.there (.there .here))))) (.cons (values.get (.there (.there (.there (.there (.there .here)))))) .nil))))) := by
  cases values with | cons value0 values =>
    cases values with | cons value1 values =>
      cases values with | cons value2 values =>
        cases values with | cons value3 values =>
          cases values with | cons value4 values =>
            cases values with | cons value5 values =>
              cases values
              simp [maskValues, ProtocolContext.mapScopes,
                Participant.restrict, Ne.symm separate, Values.get]

/-- The `reduce` callee at role 1: its invocation in this unit at any child context. -/
theorem reduce_verifierReduce_invoke (bodies : SumcheckVerifierHelpers.Bodies SumcheckSourceViews.unit.definitions) (claims : SumcheckPendingLaws.Bodies SumcheckSourceViews.unit.definitions) (ctx : ProtocolContext) (separate : ctx.roles 0 ≠ ctx.roles 1)
    (point : Option (List F)) (claim : Option F) (count service : Option Nat) (input0 : Option (List F)) (input1 input2 : Option Nat) :
    invokeProtocol (SumcheckSourceViews.unit.plainProtocolTable F G) SumcheckSourceBodies.reduceSignature ctx (ctx.roles 1)
      (.cons input0 (.cons input1 (.cons input2 (.cons point (.cons claim (.cons count (.cons service .nil)))))) : Values (Component (assignment F G)) [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"]) =
      (SumcheckPreludeNormalForms.verifierReduceProcess SumcheckSourceViews.unit reduceMaximum ctx point claim count service).bind (fun out => .done (.cons none (.cons none (.cons none (.cons none (.cons (out.get (.there (.there (.there (.there .here))))) (.cons (out.get (.there (.there (.there (.there (.there .here)))))) .nil))))))) := by
  refine (reduce_view ctx (ctx.roles 1) _ (.cons none (.cons none (.cons none (.cons point (.cons claim (.cons count (.cons service .nil)))))) : Values (Component (assignment F G)) [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"]) ?_).trans ?_
  · iterate 8 unfold maskValues
    simp [ProtocolContext.mapScopes, Participant.restrict, Ne.symm separate]
  refine (congrArg (fun process => PIR.Process.bind process _)
    (SumcheckPreludeNormalForms.verifierReduce_process (U := SumcheckSourceViews.unit) (maximum := reduceMaximum) (bodies := bodies) (claims := claims) (ctx := ctx) (self := ctx.roles 1) (role := rfl) (separate := separate) (point := point) (claim := claim) (count := count) (service := service))).trans ?_
  apply congrArg (PIR.Process.bind _)
  funext out
  exact congrArg PIR.Process.done (reduce_verifierReduce_returned ctx separate out)

/-- The verifier's laws as the normalizer reads them, keyed by helper. -/
def verifierSignature : NormalForm.Signature :=
  ⟨[], false, false, [SumcheckSourceBodies.checkHelper, SumcheckSourceBodies.pendingHelper], [⟨SumcheckSourceBodies.reduceSignature, 1, (.cons .absent (.cons .absent (.cons .absent (.cons .optional (.cons .optional (.cons .optional (.cons .optional .nil))))))), [none, none, none, none]⟩]⟩

/-- The results the verifier's laws present, of the mathematical helper laws. -/
def verifierResults : NormalForm.LawResults (ringModel F G) verifierSignature.laws :=
  ⟨fun entry => entry.elim0⟩

/-- The verifier's callees' processes, by callee. -/
def verifierCallees : NormalForm.CalleeProcesses (ringModel F G) verifierSignature.callees :=
  fun callee => match callee with
  | ⟨0, _⟩ => fun ctx binders => SumcheckPreludeNormalForms.verifierReduceProcess SumcheckSourceViews.unit reduceMaximum ctx (NormalForm.entryAt binders .here) (NormalForm.entryAt binders (.there .here)) (NormalForm.entryAt binders (.there (.there .here))) (NormalForm.entryAt binders (.there (.there (.there .here))))
  | ⟨_ + 1, outside⟩ => absurd outside (by simp [verifierSignature])

/-- The verifier's inputs as the normalizer reads them. -/
def verifierPattern : NormalForm.InputPattern [.vector "bls12-381.fr", .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"] :=
  .cons .optional (.cons .optional (.cons .optional (.cons .optional .nil)))

/-- The existing typed normalizer supplies the complete form. -/
noncomputable def verifierForm : NormalForm.Form verifierSignature.laws verifierSignature.callees verifierPattern.scope [.boolean] :=
  (NormalForm.normalize verifierSignature SumcheckSourceBodies.runBody 1 2 verifierPattern).toOption.get (by kernel_rfl)

theorem verifier_normalized :
    NormalForm.normalize verifierSignature SumcheckSourceBodies.runBody 1 2 verifierPattern = .ok verifierForm := by
  kernel_rfl

theorem verifier_lawsMatch : verifierForm.CallsMatch := by
  kernel_rfl

theorem verifier_environment (raw : Option (List F)) (claim : Option F) (count service : Option Nat) :
    verifierPattern.environment (ringModel F G) (.cons raw (.cons claim (.cons count (.cons service .nil)))) =
      (.cons raw (.cons claim (.cons count (.cons service .nil))) : Values (Component (assignment F G)) [.vector "bls12-381.fr", .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"]) := by
  kernel_rfl

/-- The form's process is the readable process. -/
theorem verifier_presentation (ctx : ProtocolContext)
    (raw : Option (List F)) (claim : Option F) (count service : Option Nat) :
    verifierForm.denote (ringModel F G) (plainHelpers (F := F) (G := G) SumcheckSourceViews.unit).toOn verifierResults ctx
        (NormalForm.Runs.uniform (plainHelpers (F := F) (G := G) SumcheckSourceViews.unit) (SumcheckSourceViews.unit.plainProtocolTable F G) ctx (ctx.roles 1)) verifierCallees
        (.cons raw (.cons claim (.cons count (.cons service .nil)))) =
      verifierProcess ctx raw claim count service := by
  kernel_rfl

/-- The verifier's laws hold at its inputs, by the admitted helpers' laws. -/
theorem verifier_laws (raw : Option (List F)) (claim : Option F) (count service : Option Nat) :
    NormalForm.LawsHold (plainHelpers (F := F) (G := G) SumcheckSourceViews.unit).toOn verifierResults
      (.cons raw (.cons claim (.cons count (.cons service .nil))) : Values (Component (assignment F G)) [.vector "bls12-381.fr", .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"]) :=
  fun entry => entry.elim0

/-- The verifier's callees present their applications: each callee's invocation in this unit. -/
theorem verifier_callees (bodies : SumcheckVerifierHelpers.Bodies SumcheckSourceViews.unit.definitions) (claims : SumcheckPendingLaws.Bodies SumcheckSourceViews.unit.definitions) (raw : Option (List F)) (claim : Option F) (count service : Option Nat) :
    NormalForm.CalleesHold (SumcheckSourceViews.unit.plainProtocolTable F G) verifierCallees
      (.cons raw (.cons claim (.cons count (.cons service .nil))) : Values (Component (assignment F G)) [.vector "bls12-381.fr", .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"]) :=
  fun callee => match callee with
  | ⟨0, _⟩ => fun ctx binders others pinned distinct =>
    match binders, others, pinned with
    | .cons calleePoint (.cons calleeClaim (.cons calleeCount (.cons calleeService .nil))), .cons input0 (.cons input1 (.cons input2 .nil)), _ => by
      exact reduce_verifierReduce_invoke bodies claims ctx (distinct 0 (show 0 < 2 by decide) (show (0 : Nat) ≠ 1 by decide)) calleePoint calleeClaim calleeCount calleeService input0 input1 input2
  | ⟨_ + 1, outside⟩ => absurd outside (by simp [verifierSignature])

/-- The process equation of `verifierProcess`, an instance of the normalizer's soundness. -/
theorem verifier_process (bodies : SumcheckVerifierHelpers.Bodies SumcheckSourceViews.unit.definitions) (claims : SumcheckPendingLaws.Bodies SumcheckSourceViews.unit.definitions)
    (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 1)
    (separate : ctx.roles 0 ≠ self)
    (raw : Option (List F)) (claim : Option F) (count service : Option Nat) :
    runFn (F := F) (G := G) ctx self
      (.cons raw (.cons claim (.cons count (.cons service .nil)))) =
      verifierProcess ctx raw claim count service := by
  subst self
  exact (NormalForm.sound_uniform verifierSignature SumcheckSourceBodies.runBody 1 2 verifierPattern
    verifierForm (verifier_normalized ) (verifier_lawsMatch ) ctx (.ofSeparate separate (by decide))
    (plainHelpers (F := F) (G := G) SumcheckSourceViews.unit) (SumcheckSourceViews.unit.plainProtocolTable F G) verifierResults verifierCallees (.cons raw (.cons claim (.cons count (.cons service .nil)))) _
    (verifier_environment raw claim count service) (verifier_laws raw claim count service) (verifier_callees bodies claims raw claim count service)).trans
    (verifier_presentation ctx raw claim count service)

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The returned components kept at role 1; the others are masked away. -/
theorem verifier_outputs (ctx : ProtocolContext)
    (values : Values (Component (assignment F G)) [.boolean]) :
    maskValues (ctx.roles 1) (ctx.mapScopes [[1]]) values =
      .cons (values.get .here) .nil := by
  cases values with | cons value0 values =>
    cases values
    simp [maskValues, ProtocolContext.mapScopes,
      Participant.restrict, Values.get]

/-- The verifier's invocation at any caller context: the input masks, the normal form of
the body and the output masks, with this unit's protocol table. -/
theorem verifier_invoke (bodies : SumcheckVerifierHelpers.Bodies SumcheckSourceViews.unit.definitions) (claims : SumcheckPendingLaws.Bodies SumcheckSourceViews.unit.definitions)
    (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 1)
    (separate : ctx.roles 0 ≠ self)
    (raw : Option (List F)) (claim : Option F) (count service : Option Nat) :
    invokeProtocol (SumcheckSourceViews.unit.plainProtocolTable F G) SumcheckSourceBodies.runSignature ctx self
      (.cons raw (.cons claim (.cons count (.cons service .nil)))) =
      (verifierProcess ctx raw claim count service).bind (fun out => .done (.cons (out.get .here) .nil)) := by
  refine (run_view ctx self _ (.cons raw (.cons claim (.cons count (.cons service .nil)))) ?_).trans ?_
  · subst self
    iterate 5 unfold maskValues
    simp [ProtocolContext.mapScopes, Participant.restrict, Ne.symm separate]
  subst self
  refine (congrArg (fun process => PIR.Process.bind process _)
    (verifier_process (bodies := bodies) (claims := claims) (raw := raw) (claim := claim) (count := count) (service := service) (ctx := ctx) (self := ctx.roles 1) (role := rfl)
      (separate := separate) )).trans ?_
  apply congrArg (PIR.Process.bind _)
  funext out
  exact congrArg PIR.Process.done (verifier_outputs ctx out)

/-- The verifier's participant of the admitted unit. -/
theorem verifier_participant (bodies : SumcheckVerifierHelpers.Bodies SumcheckSourceViews.unit.definitions) (claims : SumcheckPendingLaws.Bodies SumcheckSourceViews.unit.definitions)
    (raw : Option (List F)) (claim : Option F) (count service : Option Nat) :
    SumcheckSourceViews.program.participant F G 1 (.cons raw (.cons claim (.cons count (.cons service .nil)))) =
      (verifierProcess ({} : ProtocolContext) raw claim count service).bind (fun out => .done (.cons (out.get .here) .nil)) :=
  (SumcheckSourceViews.unit.protocolTable_forgetSites (F := F) (G := G) SumcheckSourceBodies.runSignature {} 1
    (.cons raw (.cons claim (.cons count (.cons service .nil))))).trans
    (verifier_invoke (bodies := bodies) (claims := claims) (raw := raw) (claim := claim) (count := count) (service := service) (ctx := {}) (self := 1) (role := rfl)
      (separate := by decide))

/-- The prover's normal form of the whole body. -/
def proverProcess (ctx : ProtocolContext) (raw : List F) (rounds : Nat) :
    PIR.Process (participantInterface F G)
      (Values (Component (assignment F G)) [.boolean]) :=
  (SumcheckPreludeNormalForms.proverReduceProcess SumcheckSourceViews.unit reduceMaximum (reduceContext ctx) raw rounds rounds).bind fun (_ : Values (Component (assignment F G)) [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .field "bls12-381.fr"]) =>
  .done (.cons none .nil : Values (Component (assignment F G)) [.boolean])

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The returned components kept at role 0; the others are masked away. -/
theorem reduce_proverReduce_returned (ctx : ProtocolContext) (separate : ctx.roles 1 ≠ ctx.roles 0)
    (values : Values (Component (assignment F G)) [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .field "bls12-381.fr"]) :
    maskValues (ctx.roles 0) (ctx.mapScopes [[0], [0], [0], [0], [1], [1]]) values =
      .cons (values.get .here) (.cons (values.get (.there .here)) (.cons (values.get (.there (.there .here))) (.cons (values.get (.there (.there (.there .here)))) (.cons none (.cons none .nil))))) := by
  cases values with | cons value0 values =>
    cases values with | cons value1 values =>
      cases values with | cons value2 values =>
        cases values with | cons value3 values =>
          cases values with | cons value4 values =>
            cases values with | cons value5 values =>
              cases values
              simp [maskValues, ProtocolContext.mapScopes,
                Participant.restrict, Ne.symm separate, Values.get]

/-- The `reduce` callee at role 0: its invocation in this unit at any child context. -/
theorem reduce_proverReduce_invoke (bodies : SumcheckUnitContracts.Bodies SumcheckSourceViews.unit.definitions) (ctx : ProtocolContext) (separate : ctx.roles 1 ≠ ctx.roles 0)
    (raw : List F) (rounds : Nat) (input3 : Option (List F)) (input4 : Option F) (input6 : Option Nat) (shape : HasShape raw rounds 1) :
    invokeProtocol (SumcheckSourceViews.unit.plainProtocolTable F G) SumcheckSourceBodies.reduceSignature ctx (ctx.roles 0)
      (.cons (some raw) (.cons (some rounds) (.cons (some 1) (.cons input3 (.cons input4 (.cons (some rounds) (.cons input6 .nil)))))) : Values (Component (assignment F G)) [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"]) =
      (SumcheckPreludeNormalForms.proverReduceProcess SumcheckSourceViews.unit reduceMaximum ctx raw rounds rounds).bind (fun out => .done (.cons (out.get .here) (.cons (out.get (.there .here)) (.cons (out.get (.there (.there .here))) (.cons (out.get (.there (.there (.there .here)))) (.cons none (.cons none .nil))))))) := by
  refine (reduce_view ctx (ctx.roles 0) _ (.cons (some raw) (.cons (some rounds) (.cons (some 1) (.cons none (.cons none (.cons (some rounds) (.cons none .nil)))))) : Values (Component (assignment F G)) [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"]) ?_).trans ?_
  · iterate 8 unfold maskValues
    simp [ProtocolContext.mapScopes, Participant.restrict, Ne.symm separate]
  refine (congrArg (fun process => PIR.Process.bind process _)
    (SumcheckPreludeNormalForms.proverReduce_process (U := SumcheckSourceViews.unit) (maximum := reduceMaximum) (bodies := bodies) (ctx := ctx) (self := ctx.roles 0) (role := rfl) (separate := separate) (entries := raw) (count := rounds) (rounds := rounds) (countBound := Nat.lt_trans shape.2.1 (by decide +kernel)) (roundsBound := Nat.lt_trans shape.2.1 (by decide +kernel)) (enough := Nat.le_refl _))).trans ?_
  apply congrArg (PIR.Process.bind _)
  funext out
  exact congrArg PIR.Process.done (reduce_proverReduce_returned ctx separate out)

/-- The prover's laws as the normalizer reads them, keyed by helper. -/
def proverSignature : NormalForm.Signature :=
  ⟨[⟨SumcheckSourceBodies.tableHelper, .returns [.argument 0, .argument 1, .argument 2], [.input 0, .input 2, .literal 1]⟩], false, false, [], [⟨SumcheckSourceBodies.reduceSignature, 0, (.cons .present (.cons .present (.cons (.index 1) (.cons .absent (.cons .absent (.cons .present (.cons .absent .nil))))))), [some 0, some 2, some 2]⟩]⟩

/-- The results the prover's laws present, of the mathematical helper laws. -/
def proverResults : NormalForm.LawResults (ringModel F G) proverSignature.laws :=
  ⟨fun entry => match entry with
    | ⟨0, _⟩ => fun (args : Values (assignment F G) [.vector "bls12-381.fr", .index, .index]) =>
      (.cons (args.get .here) (.cons (args.get (.there .here)) (.cons (args.get (.there (.there .here))) .nil)) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index])
    | ⟨_ + 1, outside⟩ => absurd outside (by simp [proverSignature])⟩

/-- The prover's callees' processes, by callee. -/
def proverCallees : NormalForm.CalleeProcesses (ringModel F G) proverSignature.callees :=
  fun callee => match callee with
  | ⟨0, _⟩ => fun ctx binders => SumcheckPreludeNormalForms.proverReduceProcess SumcheckSourceViews.unit reduceMaximum ctx (NormalForm.entryAt binders .here) (NormalForm.entryAt binders (.there .here)) (NormalForm.entryAt binders (.there (.there .here)))
  | ⟨_ + 1, outside⟩ => absurd outside (by simp [proverSignature])

/-- The prover's inputs as the normalizer reads them. -/
def proverPattern : NormalForm.InputPattern [.vector "bls12-381.fr", .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"] :=
  .cons .present (.cons .absent (.cons .present (.cons .absent .nil)))

/-- The existing typed normalizer supplies the complete form. -/
noncomputable def proverForm : NormalForm.Form proverSignature.laws proverSignature.callees proverPattern.scope [.boolean] :=
  (NormalForm.normalize proverSignature SumcheckSourceBodies.runBody 0 2 proverPattern).toOption.get (by kernel_rfl)

theorem prover_normalized :
    NormalForm.normalize proverSignature SumcheckSourceBodies.runBody 0 2 proverPattern = .ok proverForm := by
  kernel_rfl

theorem prover_lawsMatch : proverForm.CallsMatch := by
  kernel_rfl

theorem prover_environment (raw : List F) (rounds : Nat) :
    proverPattern.environment (ringModel F G) (.cons raw (.cons rounds .nil)) =
      (.cons (some raw) (.cons none (.cons (some rounds) (.cons none .nil))) : Values (Component (assignment F G)) [.vector "bls12-381.fr", .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"]) := by
  kernel_rfl

/-- The form's process is the readable process. -/
theorem prover_presentation (ctx : ProtocolContext)
    (raw : List F) (rounds : Nat) :
    proverForm.denote (ringModel F G) (plainHelpers (F := F) (G := G) SumcheckSourceViews.unit).toOn proverResults ctx
        (NormalForm.Runs.uniform (plainHelpers (F := F) (G := G) SumcheckSourceViews.unit) (SumcheckSourceViews.unit.plainProtocolTable F G) ctx (ctx.roles 0)) proverCallees
        (.cons raw (.cons rounds .nil)) =
      proverProcess ctx raw rounds := by
  kernel_rfl

/-- The prover's laws hold at its inputs, by the admitted helpers' laws. -/
theorem prover_laws (bodies : SumcheckUnitContracts.Bodies SumcheckSourceViews.unit.definitions) (raw : List F) (rounds : Nat) (shape : HasShape raw rounds 1) (bound : raw.length < indexLimit):
    NormalForm.LawsHold (plainHelpers (F := F) (G := G) SumcheckSourceViews.unit).toOn proverResults
      (.cons (some raw) (.cons none (.cons (some rounds) (.cons none .nil))) : Values (Component (assignment F G)) [.vector "bls12-381.fr", .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"]) :=
  fun entry => match entry with
  | ⟨0, _⟩ => fun args pinned => match args, pinned with
    | .cons a0 (.cons a1 (.cons a2 .nil)), ⟨p0, p1, p2, _⟩ => fun values found => by
      obtain rfl : values = (.cons a0 (.cons a1 (.cons a2 .nil)) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index]) :=
        Option.some.inj (found.symm.trans (by kernel_rfl))
      rw [← (Option.some.inj p0 : raw = a0), ← (Option.some.inj p1 : rounds = a1), ← (Option.some.inj (p2 : some 1 = some a2) : 1 = a2)]
      show invoke (plainHelpers (F := F) (G := G) SumcheckSourceViews.unit).closed SumcheckSourceBodies.tableHelper _ = .done (.cons raw (.cons rounds (.cons 1 .nil)) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index])
      exact SumcheckProverLaws.table_present SumcheckSourceViews.unit bodies raw rounds shape bound
  | ⟨_ + 1, outside⟩ => absurd outside (by simp [proverSignature])

/-- The prover's callees present their applications: each callee's invocation in this unit. -/
theorem prover_callees (bodies : SumcheckUnitContracts.Bodies SumcheckSourceViews.unit.definitions) (raw : List F) (rounds : Nat) (shape : HasShape raw rounds 1):
    NormalForm.CalleesHold (SumcheckSourceViews.unit.plainProtocolTable F G) proverCallees
      (.cons (some raw) (.cons none (.cons (some rounds) (.cons none .nil))) : Values (Component (assignment F G)) [.vector "bls12-381.fr", .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"]) :=
  fun callee => match callee with
  | ⟨0, _⟩ => fun ctx binders others pinned distinct =>
    match binders, others, pinned with
    | .cons calleeEntries (.cons calleeCount (.cons calleeRounds .nil)), .cons input3 (.cons input4 (.cons input6 .nil)), ⟨p0, p1, p2, _⟩ => by
      rw [← (Option.some.inj (p0 : some raw = some calleeEntries) : raw = calleeEntries), ← (Option.some.inj (p1 : some rounds = some calleeCount) : rounds = calleeCount), ← (Option.some.inj (p2 : some rounds = some calleeRounds) : rounds = calleeRounds)]
      exact reduce_proverReduce_invoke bodies ctx (distinct 1 (show 1 < 2 by decide) (show (1 : Nat) ≠ 0 by decide)) raw rounds input3 input4 input6 shape
  | ⟨_ + 1, outside⟩ => absurd outside (by simp [proverSignature])

/-- The process equation of `proverProcess`, an instance of the normalizer's soundness. -/
theorem prover_process (bodies : SumcheckUnitContracts.Bodies SumcheckSourceViews.unit.definitions)
    (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 0)
    (separate : ctx.roles 1 ≠ self)
    (raw : List F) (rounds : Nat) (shape : HasShape raw rounds 1) (bound : raw.length < indexLimit) :
    runFn (F := F) (G := G) ctx self
      (.cons (some raw) (.cons none (.cons (some rounds) (.cons none .nil)))) =
      proverProcess ctx raw rounds := by
  subst self
  exact (NormalForm.sound_uniform proverSignature SumcheckSourceBodies.runBody 0 2 proverPattern
    proverForm (prover_normalized ) (prover_lawsMatch ) ctx (.ofSeparate separate (by decide))
    (plainHelpers (F := F) (G := G) SumcheckSourceViews.unit) (SumcheckSourceViews.unit.plainProtocolTable F G) proverResults proverCallees (.cons raw (.cons rounds .nil)) _
    (prover_environment raw rounds) (prover_laws bodies raw rounds shape bound) (prover_callees bodies raw rounds shape)).trans
    (prover_presentation ctx raw rounds)

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The returned components kept at role 0; the others are masked away. -/
theorem prover_outputs (ctx : ProtocolContext) (separate : ctx.roles 1 ≠ ctx.roles 0)
    (values : Values (Component (assignment F G)) [.boolean]) :
    maskValues (ctx.roles 0) (ctx.mapScopes [[1]]) values =
      .cons none .nil := by
  cases values with | cons value0 values =>
    cases values
    simp [maskValues, ProtocolContext.mapScopes,
      Participant.restrict, Ne.symm separate]

/-- The prover's invocation at any caller context: the input masks, the normal form of
the body and the output masks, with this unit's protocol table. -/
theorem prover_invoke (bodies : SumcheckUnitContracts.Bodies SumcheckSourceViews.unit.definitions)
    (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 0)
    (separate : ctx.roles 1 ≠ self)
    (raw : List F) (rounds : Nat) (claim : Option F) (service : Option Nat) (shape : HasShape raw rounds 1) (bound : raw.length < indexLimit) :
    invokeProtocol (SumcheckSourceViews.unit.plainProtocolTable F G) SumcheckSourceBodies.runSignature ctx self
      (.cons (some raw) (.cons claim (.cons (some rounds) (.cons service .nil)))) =
      (proverProcess ctx raw rounds).bind (fun _ => .done (.cons none .nil)) := by
  refine (run_view ctx self _ (.cons (some raw) (.cons none (.cons (some rounds) (.cons none .nil)))) ?_).trans ?_
  · subst self
    iterate 5 unfold maskValues
    simp [ProtocolContext.mapScopes, Participant.restrict, Ne.symm separate]
  subst self
  refine (congrArg (fun process => PIR.Process.bind process _)
    (prover_process (bodies := bodies) (raw := raw) (rounds := rounds) (shape := shape) (bound := bound) (ctx := ctx) (self := ctx.roles 0) (role := rfl)
      (separate := separate) )).trans ?_
  apply congrArg (PIR.Process.bind _)
  funext out
  exact congrArg PIR.Process.done (prover_outputs ctx separate out)

/-- The prover's participant of the admitted unit. -/
theorem prover_participant (bodies : SumcheckUnitContracts.Bodies SumcheckSourceViews.unit.definitions)
    (raw : List F) (rounds : Nat) (claim : Option F) (service : Option Nat) (shape : HasShape raw rounds 1) (bound : raw.length < indexLimit) :
    SumcheckSourceViews.program.participant F G 0 (.cons (some raw) (.cons claim (.cons (some rounds) (.cons service .nil)))) =
      (proverProcess ({} : ProtocolContext) raw rounds).bind (fun _ => .done (.cons none .nil)) :=
  (SumcheckSourceViews.unit.protocolTable_forgetSites (F := F) (G := G) SumcheckSourceBodies.runSignature {} 0
    (.cons (some raw) (.cons claim (.cons (some rounds) (.cons service .nil))))).trans
    (prover_invoke (bodies := bodies) (raw := raw) (rounds := rounds) (shape := shape) (bound := bound) (claim := claim) (service := service) (ctx := {}) (self := 0) (role := rfl)
      (separate := by decide))

end ZkcExamples.Structured.SumcheckSourceNormalForms
