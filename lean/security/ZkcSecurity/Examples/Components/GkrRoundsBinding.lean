module

public import ZkcSecurity.Examples.Components.GkrRoundsBindingHelpers
public import ZkcSecurity.Families.Sumcheck.Composition

@[expose] public section
noncomputable section

/-! The actual imported Rounds verifier as one shared Sumcheck component.
Ghost factors retain off-cube observations; runtime private slots retain their
actual absent masks. The equation is over the complete open Process. -/
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Examples.Components.GkrRoundsBinding
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Bindings Zkc.Source.Structured.NormalForm
open ZkcExamples.Structured.Generated.Bindings.GkrRounds (payload)
open ZkcExamples.Structured.Generated.Bindings.GkrRoundsCallbacks
open ZkcSecurity.Families.Sumcheck
open GkrRoundsRealization GkrRoundsGateRealization

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev field := "bls12-381.fr"
abbrev vector := Ty.vector field
abbrev scalar := Ty.field field

abbrev spec : RepeatSpec :=
  ⟨[vector, vector, vector, vector, vector, vector, scalar],
    [.service "random.bls12-381.fr/0"], [0, 1], [[0], [0], [0], [0], [0], [1], [1]], 4⟩

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
    (Message.coefficientTriples F).boundary (a, b, c) = a + a + b + c :=
  (wire_boundary a b c).symm

omit [DecidableEq F] in
theorem evaluation (a b c r : F) :
    (Message.coefficientTriples F).evaluate (a, b, c) r = a + r * (b + r * c) :=
  (wire_evaluation a b c r).symm

/-- A small dependent-type presentation of the actual generated callback. -/
def callback (ctx : ProtocolContext) (point : Option (List F))
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
                  (invoke (helpers (F := F) (G := G) payload).toOn.closed
                    ZkcExamples.Structured.Generated.Bindings.GkrRoundsInputs.helper1Helper)
                  (.cons point (.cons (some r) .nil))).bind fun appended =>
                  .done (.cons none (.cons none (.cons none (.cons none (.cons none
                    (.cons (appended.get .here) (.cons (some (c0 + r * (c1 + r * c2))) .nil)))))))
        else .halt .reject

theorem callback_source (ctx : ProtocolContext) (index : Option Nat)
    (a m l r pp point : Option (List F)) (claim : Option F) (service : Option Nat) :
    protocol0Role1Callback0Process (F := F) (G := G) ctx index a m l r pp point claim service =
      callback ctx point claim service := by
  rfl

/-- The arbitrary coefficient replies precede the actual scalar boundary.
The append law is from the admitted full body, not an opaque helper assertion. -/
theorem callback_equation (ctx : ProtocolContext) (index : Option Nat)
    (a m l r pp : Option (List F)) (point : List F) (claim : F) (service : Nat) :
    protocol0Role1Callback0Process (F := F) (G := G) ctx index a m l r pp
      (some point) (some claim) (some service) =
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
  rw [callback_source]
  unfold callback
  simp_rw [GkrRoundsBindingHelpers.owned_append (F := F) (G := G)]
  unfold receive
  dsimp only [query, delivery, participantInterface, Participant.interface, services, assignment, scalar, field]
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
/-- The actual masked state ABI is fixed by role substitution, including zero
iterations. -/
theorem mask_carried (ctx : ProtocolContext)
    {n : Nat} (s : State F n) :
    maskValues (ctx.roles 1) (ctx.mapScopes spec.stateScopes) (carried (G := G) s) =
      carried (G := G) s := by
  simp [carried, runtime, spec, maskValues, ProtocolContext.mapScopes, Participant.restrict]

/-- Residual source loop after its original maximum check. Its shifted index
and optional immutable service capture are the actual source arguments. -/
def actualRemaining (service : Nat) (ctx : ProtocolContext) {n : Nat}
    (count start : Nat) (s : State F (n + count)) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) spec.state) :=
  Repeat.loop spec ctx (ctx.roles 1) (.cons (some service) .nil)
    (fun args => protocol0Role1Callback0Process ctx
      (args.get .here) (args.get (.there .here)) (args.get (.there (.there .here)))
      (args.get (.there (.there (.there .here))))
      (args.get (.there (.there (.there (.there .here)))))
      (args.get (.there (.there (.there (.there (.there .here))))))
      (args.get (.there (.there (.there (.there (.there (.there .here)))))))
      (args.get (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (args.get (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
    start count (carried s)

/-- One whole binding for both consumers, over arbitrary replies and halts. -/
theorem remaining_binding (service : Nat) (ctx : ProtocolContext) (_distinct : RosterDistinct ctx 1 2)
    {n : Nat} (count start : Nat) (s : State F (n + count)) :
    actualRemaining (G := G) service ctx count start s =
      ((program service).remaining count ctx s).bind (fun final => .done (carried (G := G) final)) := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    unfold actualRemaining
    rw [Repeat.loop_succ, Repeat.step_equation, mask_carried ctx]
    simp only [carried, runtime, spec, Values.append, Values.get]
    rw [callback_equation]
    simp only [receive, program, Program.remaining, PIR.Process.bind_assoc, PIR.Process.bind]
    congr 1
    funext c0
    congr 1
    funext c1
    congr 1
    funext c2
    split
    · simp only [query, delivery, PIR.Process.bind]
      congr 1
      funext challenge
      congr 1
      funext reply
      change Repeat.loop spec ctx (ctx.roles 1) _ _ (start + 1) count
        (maskValues (ctx.roles 1) (ctx.mapScopes spec.stateScopes)
          (carried (G := G) (advance s (c0, c1, c2) challenge))) = _
      rw [mask_carried ctx]
      exact ih (start + 1) (advance s (c0, c1, c2) challenge)
    · rfl

end ZkcSecurity.Examples.Components.GkrRoundsBinding
