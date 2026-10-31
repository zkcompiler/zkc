module

public import ZkcSecurity.Bindings.Gkr.RoundsBoundaryInstallation
public import ZkcSecurity.Bindings.Gkr.RoundsRealization
public import ZkcSecurity.Families.Sumcheck.Composition
public import Zkc.Source.Structured.RepeatLaws

@[expose] public section
noncomputable section

/-! Reusable degree-two round execution and its complete verifier ABI. The
reference, raw factors and runtime masks are distinct. Source clients supply
exact helper associations and the selected callback presentation. -/
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Examples.Components.GkrRoundsBinding
open Zkc.Source Zkc.Source.Structured
open ZkcSecurity.Families.Sumcheck
open GkrRoundsRealization
open ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev field := "bls12-381.fr"
abbrev vector := Ty.vector field
abbrev scalar := Ty.field field

abbrev repeatSpec (maximum : Nat) : RepeatSpec :=
  ⟨[vector, vector, vector, vector, vector, vector, scalar],
    [.service "random.bls12-381.fr/0"], [0, 1], [[0], [0], [0], [0], [0], [1], [1]], maximum⟩

abbrev spec : RepeatSpec := repeatSpec 4

structure State (F : Type) (n : Nat) where
  reference : GkrRoundsReference.State F n
  raw : RawState F
  point : List F
  claim : F

/-- All five prover-private results are absent in the verifier's carried ABI. -/
def runtime (point : List F) (claim : F) :
    Values (Component (assignment F G)) spec.state :=
  .cons none (.cons none (.cons none (.cons none (.cons none
    (.cons (some point) (.cons (some claim) .nil))))))

def carried {n : Nat} (s : State F n) : Values (Component (assignment F G)) spec.state :=
  runtime s.point s.claim

def advance {n : Nat} (s : State F (n + 1)) (m : F × F × F) (r : F) : State F n :=
  ⟨GkrRoundsReference.restrict s.reference r, s.raw.restrict r,
    s.point ++ [r], (Message.coefficientTriples F).evaluate m r⟩

def receive (ctx : ProtocolContext) : PIR.Process (participantInterface F G) (Option (F × F × F)) :=
  .call (.receive scalar (qualifyProtocolSite ctx.applicationPrefix "label_726f756e64_0") (ctx.roles 0)) fun a =>
  .call (.receive scalar (qualifyProtocolSite ctx.applicationPrefix "label_726f756e64_1") (ctx.roles 0)) fun b =>
  .call (.receive scalar (qualifyProtocolSite ctx.applicationPrefix "label_726f756e64_2") (ctx.roles 0)) fun c =>
  .done (some (a, b, c))

abbrev query (ctx : ProtocolContext) (service : Nat) : (participantInterface F G).Op :=
  .query (qualifyProtocolSite ctx.applicationPrefix "label_6368616c6c656e6765") field (.cons service .nil)

def delivery (ctx : ProtocolContext) (r : F) : PIR.Process (participantInterface F G) PUnit :=
  .call (.send (ty := scalar) (qualifyProtocolSite ctx.applicationPrefix "label_64656c6976657279_0")
    (ctx.roles 0) r) fun _ => .done ()

def program (service : Nat) :
    Program (participantInterface F G) ProtocolContext (State F) (Message.coefficientTriples F) where
  claim := State.claim
  receive ctx _ := receive ctx
  query ctx _ _ := query ctx service
  challenge _ _ _ r := r
  deliver ctx _ _ r := delivery ctx r
  advance _ s m r := advance s m r

def representation (service : Nat) :
    Representation (program (F := F) (G := G) service) (GkrRoundsReference.data F) where
  state := State.reference
  advance _ _ _ _ := rfl
  claim _ _ _ _ := rfl

omit [DecidableEq F] in
theorem boundary (a b c : F) :
    (Message.coefficientTriples F).boundary (a, b, c) = a + a + b + c := by
  change (Message.ofTriple (a, b, c)).boundary = _
  simp only [Message.ofTriple,
    Zkc.Protocols.AlgebraicRounds.Message.boundary, Zkc.Protocols.AlgebraicRounds.Message.evaluate]
  ring

omit [DecidableEq F] in
theorem evaluation (a b c r : F) :
    (Message.coefficientTriples F).evaluate (a, b, c) r = a + r * (b + r * c) := by
  change (Message.ofTriple (a, b, c)).evaluate r = _
  simp only [Message.ofTriple, Zkc.Protocols.AlgebraicRounds.Message.evaluate]
  ring


omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The actual masked state ABI is fixed by role substitution, including zero
iterations. -/
theorem mask_carried (ctx : ProtocolContext)
    {n : Nat} (s : State F n) :
    maskValues (ctx.roles 1) (ctx.mapScopes spec.stateScopes) (carried (G := G) s) =
      carried (G := G) s := by
  simp [carried, runtime, spec, maskValues, ProtocolContext.mapScopes, Participant.restrict]


end ZkcSecurity.Examples.Components.GkrRoundsBinding

namespace ZkcSecurity.Bindings.Gkr.RoundsVerifierInstallation
open Zkc.Source Zkc.Source.Structured
open ZkcSecurity.Families.Sumcheck
open ZkcSecurity.Examples.Components.GkrRoundsBinding
open ZkcSecurity.Examples.Components.GkrRoundsHelpers

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]
variable {definitions : List CheckedDefinition}

/-- A small dependent-type presentation of the actual generated callback. -/
def callback (definitions : List CheckedDefinition) (ctx : ProtocolContext) (point : Option (List F))
    (claim : Option F) (service : Option Nat) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) spec.state) :=
  (receive ctx).bind fun decoded =>
    match decoded with
    | none => .halt .refused
    | some (c0, c1, c2) =>
      match claim with
      | none => .halt .incomplete
      | some claim =>
        if claim = c0 + c0 + c1 + c2 then
          match service with
          | none => .halt .incomplete
          | some service =>
            .call (query ctx service) fun (r : F) =>
              (delivery ctx r).bind fun _ =>
                (Participant.owned (ctx.roles 1) (ctx.roles 1)
                  (invoke (RoundsBoundaryInstallation.helpers (F := F) (G := G) definitions)
                    ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.appendHelper)
                  (.cons point (.cons (some r) .nil))).bind fun appended =>
                  .done (.cons none (.cons none (.cons none (.cons none (.cons none
                    (.cons (appended.get .here) (.cons (some (c0 + r * (c1 + r * c2))) .nil)))))))
        else .halt .reject

/-- The arbitrary coefficient replies precede the actual scalar boundary.
The append law is from the admitted full body, not an opaque helper assertion. -/
theorem callback_equation (linked : DeclarationsLinked [] definitions)
    (bodies : RoundsBoundaryInstallation.Bodies definitions) (ctx : ProtocolContext) (point : List F) (claim : F) (service : Nat) :
    callback (F := F) (G := G) definitions ctx (some point) (some claim) (some service) =
    (receive (G := G) ctx).bind (fun decoded =>
      match decoded with
      | none => .halt .refused
      | some message =>
        if (Message.coefficientTriples F).boundary message = claim then
          .call (query (F := F) (G := G) ctx service) fun (challenge : F) =>
            (delivery (G := G) ctx challenge).bind fun _ =>
              .done (runtime (G := G) (point ++ [challenge])
                ((Message.coefficientTriples F).evaluate message challenge))
        else .halt .reject) := by
  unfold callback
  simp_rw [RoundsBoundaryInstallation.owned_append (F := F) (G := G) linked bodies]
  unfold receive
  dsimp only [ZkcSecurity.Examples.Components.GkrRoundsBinding.query, delivery, participantInterface, Participant.interface, services, assignment, scalar, field]
  simp only [PIR.Process.bind]
  congr 1
  funext c0
  congr 1
  funext c1
  congr 1
  funext c2
  have b : (Message.ofTriple (c0, c1, c2)).boundary = c0 + c0 + c1 + c2 :=
    boundary (F := F) c0 c1 c2
  rw [b]
  by_cases checked : claim = c0 + c0 + c1 + c2
  · rw [ite_eq_left checked, ite_eq_left checked.symm]
    congr 1
    funext challenge
    congr 1
    funext reply
    have e : (Message.ofTriple (c0, c1, c2)).evaluate challenge = c0 + challenge * (c1 + challenge * c2) :=
      evaluation (F := F) c0 c1 c2 challenge
    rw [e]
    rfl
  · rw [ite_eq_right checked, ite_eq_right (Ne.symm checked)]


omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- Dependent-state adapter for an existing repeat and Sumcheck Program. The
only operational premise is one masked callback equation, universally over the
residual dimension, shifted source index and complete mathematical state. -/
theorem counted_loop {H : Type} [Field H] [DecidableEq H]
    {I : PIR.Signature} {Context : Type} {S : Nat → Type} {message : Message H}
    (reference : Program I Context S message) (context : Context)
    (loopSpec : RepeatSpec) (ctx : ProtocolContext) (self : Nat)
    (captures : Values (Component (assignment F G)) loopSpec.captures)
    (body : RegionFunction (Component (assignment F G)) I
      (.index :: (loopSpec.state ++ loopSpec.captures), loopSpec.state))
    (embed : {n : Nat} → S n → Values (Component (assignment F G)) loopSpec.state)
    (step : ∀ {n} (state : S (n + 1)) index,
      Repeat.step loopSpec ctx self captures body (embed state) index =
        (reference.receive context state).bind (fun decoded =>
          match decoded with
          | none => .halt .refused
          | some m =>
            if message.boundary m = reference.claim state then
              .call (reference.query context state m) fun reply =>
                (reference.deliver context state m (reference.challenge context state m reply)).bind fun _ =>
                  .done (embed (reference.advance context state m
                    (reference.challenge context state m reply)))
            else .halt .reject))
    {n : Nat} (count start : Nat) (state : S (n + count)) :
    Repeat.loop loopSpec ctx self captures body start count (embed state) =
      (reference.remaining count context state).bind (fun result => .done (embed result)) := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [Repeat.loop_succ, step]
    simp only [Program.remaining, PIR.Process.bind_assoc]
    apply congrArg (PIR.Process.bind _)
    funext decoded
    cases decoded with
    | none => rfl
    | some m =>
      dsimp only
      split
      · simp only [PIR.Process.bind, PIR.Process.bind_assoc]
        apply congrArg (PIR.Process.call _)
        funext reply
        apply congrArg (PIR.Process.bind _)
        funext _
        exact ih (start + 1) _
      · rfl

/-- The exact callback argument ABI, including the immutable optional capture. -/
def callbackBody (definitions : List CheckedDefinition) (ctx : ProtocolContext) :
    RegionFunction (Component (assignment F G)) (participantInterface F G)
      (.index :: (spec.state ++ spec.captures), spec.state) :=
  fun args => callback definitions ctx
    (args.get (.there (.there (.there (.there (.there (.there .here)))))))
    (args.get (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (args.get (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))

theorem remaining_binding_for (linked : DeclarationsLinked [] definitions)
    (bodies : RoundsBoundaryInstallation.Bodies definitions)
    (maximum service : Nat) (ctx : ProtocolContext)
    {n : Nat} (count start : Nat) (state : State F (n + count)) :
    Repeat.loop (repeatSpec maximum) ctx (ctx.roles 1) (.cons (some service) .nil)
      (callbackBody (G := G) definitions ctx) start count (carried state) =
      ((program service).remaining count ctx state).bind (fun final => .done (carried (G := G) final)) := by
  apply counted_loop (program service) ctx (repeatSpec maximum) ctx (ctx.roles 1) _ _
    (fun state => carried state)
  intro n state index
  rw [Repeat.step_equation, mask_carried ctx]
  simp only [callbackBody, carried, runtime, spec, Values.append, Values.get]
  rw [callback_equation linked bodies]
  simp only [program, PIR.Process.bind_assoc]
  apply congrArg (PIR.Process.bind _)
  funext decoded
  cases decoded with
  | none => rfl
  | some m =>
    dsimp only
    split
    · simp only [PIR.Process.bind, PIR.Process.bind_assoc]
      apply congrArg (PIR.Process.call _)
      funext challenge
      apply congrArg (PIR.Process.bind _)
      funext _
      change PIR.Process.done (maskValues (ctx.roles 1) (ctx.mapScopes spec.stateScopes)
        (carried (G := G) (advance state m challenge))) = _
      rw [mask_carried ctx]
      rfl
    · rfl

theorem remaining_binding (linked : DeclarationsLinked [] definitions)
    (bodies : RoundsBoundaryInstallation.Bodies definitions)
    (service : Nat) (ctx : ProtocolContext)
    {n : Nat} (count start : Nat) (state : State F (n + count)) :
    Repeat.loop spec ctx (ctx.roles 1) (.cons (some service) .nil)
      (callbackBody (G := G) definitions ctx) start count (carried state) =
      ((program service).remaining count ctx state).bind (fun final => .done (carried (G := G) final)) := by
  exact remaining_binding_for linked bodies 4 service ctx count start state

end ZkcSecurity.Bindings.Gkr.RoundsVerifierInstallation
