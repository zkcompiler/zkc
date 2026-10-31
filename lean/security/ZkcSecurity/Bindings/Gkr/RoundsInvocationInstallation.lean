module

public import ZkcSecurity.Bindings.Gkr.RoundsVerifierInstallation
public import Zkc.Source.Structured.NormalForm.Presentation

@[expose] public section
noncomputable section

/-! Full optional bounded execution for any linked helper installation and
source maximum. Exact source-entry installation is supplied separately. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Examples.Components.GkrRoundsBinding
open Zkc.Source Zkc.Source.Structured NormalForm
open ZkcSecurity.Families.Sumcheck
open GkrRoundsRealization
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def initial {n : Nat} (raw : RawState F) (reference : GkrRoundsReference.State F n) (claim : F) : State F n :=
  ⟨reference, raw, [], claim⟩

theorem inside (ctx : ProtocolContext) : (spec.roles.map ctx.roles).contains (ctx.roles 1) = true := by
  simp

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem mask_entry (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (a m l r point : Option (List F)) (claim : Option F) :
    maskValues (ctx.roles 1) (ctx.mapScopes spec.stateScopes)
      (.cons a (.cons m (.cons l (.cons r (.cons none (.cons point (.cons claim .nil)))))) :
        Values (Component (assignment F G)) spec.state) =
      .cons none (.cons none (.cons none (.cons none (.cons none (.cons point (.cons claim .nil)))))) := by
  change (Values.cons (Participant.restrict ([ctx.roles 0].contains (ctx.roles 1)) a)
    (.cons (Participant.restrict ([ctx.roles 0].contains (ctx.roles 1)) m)
      (.cons (Participant.restrict ([ctx.roles 0].contains (ctx.roles 1)) l)
        (.cons (Participant.restrict ([ctx.roles 0].contains (ctx.roles 1)) r)
          (.cons (Participant.restrict ([ctx.roles 0].contains (ctx.roles 1)) none)
            (.cons (Participant.restrict ([ctx.roles 1].contains (ctx.roles 1)) point)
              (.cons (Participant.restrict ([ctx.roles 1].contains (ctx.roles 1)) claim) .nil)))))) :
      Values (Component (assignment F G)) spec.state) = _
  simp [Participant.restrict, Ne.symm (distinct 0 (by decide) (by decide))]

end ZkcSecurity.Examples.Components.GkrRoundsBinding

namespace ZkcSecurity.Bindings.Gkr.RoundsInvocationInstallation
open Zkc.Source Zkc.Source.Structured NormalForm
open ZkcSecurity.Families.Sumcheck
open ZkcSecurity.Examples.Components
open ZkcSecurity.Examples.Components.GkrRoundsBinding
open ZkcSecurity.Examples.Components.GkrRoundsRealization
open ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]
variable {definitions : List CheckedDefinition}

/-- Full operational body presentation, before the selected declaration's
input/output masks. No optional input or private result is discarded. -/
def process (definitions : List CheckedDefinition) (maximum : Nat) (ctx : ProtocolContext)
    (a m l r point : Option (List F)) (claim : Option F) (count service : Option Nat) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) spec.state) :=
  (Participant.owned (ctx.roles 1) (ctx.roles 1)
    (invoke (RoundsBoundaryInstallation.helpers definitions) roundsOpenHelper)
    (.cons point (.cons claim .nil))).bind fun opened =>
  (denoteRepeat (repeatSpec maximum) ctx (ctx.roles 1) count
    (.cons a (.cons m (.cons l (.cons r (.cons none
      (.cons (opened.get .here) (.cons (opened.get (.there .here)) .nil)))))))
    (.cons service .nil) (RoundsVerifierInstallation.callbackBody definitions ctx)).bind fun repeated =>
  (Participant.owned (ctx.roles 1) (ctx.roles 1)
    (invoke (RoundsBoundaryInstallation.helpers definitions) roundsCloseHelper)
    (.cons (repeated.get (.there (.there (.there (.there (.there .here))))))
      (.cons (repeated.get (.there (.there (.there (.there (.there (.there .here))))))) .nil))).bind fun closed =>
  .done (.cons (repeated.get (.there (.there (.there (.there .here)))))
    (.cons (repeated.get .here) (.cons (repeated.get (.there .here))
      (.cons (repeated.get (.there (.there .here)))
        (.cons (repeated.get (.there (.there (.there .here))))
          (.cons (closed.get .here) (.cons (closed.get (.there .here)) .nil)))))))

/-- Direct imported whole-Process equation. Mathematical representation facts
are intentionally absent: this binding is shared by both property consumers. -/
theorem verifier_binding (linked : DeclarationsLinked [] definitions)
    (bodies : RoundsBoundaryInstallation.Bodies definitions) (maximum : Nat)
    (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (a m l r : Option (List F)) (claim : F) (service count : Nat) (bounded : count ≤ maximum)
    {n : Nat} (raw : RawState F) (reference : GkrRoundsReference.State F (n + count)) :
    process (F := F) (G := G) definitions maximum ctx a m l r (some []) (some claim) (some count) (some service) =
      ((program service).remaining count ctx (initial raw reference claim)).bind
        (fun final => .done (carried (G := G) final)) := by
  unfold process
  rw [RoundsBoundaryInstallation.owned_rounds_open linked bodies]
  simp only [PIR.Process.bind, Values.get]
  rw [repeat_admitted (repeatSpec maximum) ctx (ctx.roles 1) _ _ _ count (inside ctx) bounded]
  rw [mask_entry ctx distinct]
  change (Repeat.loop (repeatSpec maximum) ctx (ctx.roles 1) (.cons (some service) .nil)
    (RoundsVerifierInstallation.callbackBody (G := G) definitions ctx) 0 count
    (carried (initial raw reference claim))).bind _ = _
  rw [RoundsVerifierInstallation.remaining_binding_for linked bodies]
  simp only [PIR.Process.bind_assoc, GkrRoundsBinding.carried, runtime, PIR.Process.bind, Values.get,
    RoundsBoundaryInstallation.owned_rounds_close linked bodies]

/-- Missing or excessive source counts stop before any receive or query. -/
theorem missing_count (linked : DeclarationsLinked [] definitions)
    (bodies : RoundsBoundaryInstallation.Bodies definitions) (maximum : Nat)
    (ctx : ProtocolContext) (_distinct : RosterDistinct ctx 1 2)
    (a m l r point : Option (List F)) (claim : Option F) (service : Option Nat) :
    process (F := F) (G := G) definitions maximum ctx a m l r point claim none service = .halt .incomplete := by
  unfold process
  rw [RoundsBoundaryInstallation.owned_rounds_open linked bodies]
  cases point <;> cases claim <;> simp only [PIR.Process.bind, Values.get]
  rw [repeat_missing_count (repeatSpec maximum) ctx (ctx.roles 1) _ _ _ (inside ctx)]
  rfl

theorem above_maximum (linked : DeclarationsLinked [] definitions)
    (bodies : RoundsBoundaryInstallation.Bodies definitions) (maximum : Nat)
    (ctx : ProtocolContext) (_distinct : RosterDistinct ctx 1 2)
    (a m l r point : Option (List F)) (claim : Option F) (service : Option Nat)
    (count : Nat) (large : maximum < count) :
    process (F := F) (G := G) definitions maximum ctx a m l r point claim (some count) service =
      match point, claim with
      | some _, some _ => .halt .refused
      | _, _ => .halt .incomplete := by
  unfold process
  rw [RoundsBoundaryInstallation.owned_rounds_open linked bodies]
  cases point <;> cases claim <;> simp only [PIR.Process.bind, Values.get]
  rw [repeat_above_maximum (repeatSpec maximum) ctx (ctx.roles 1) _ _ _ count (inside ctx) large]
  rfl

/-- Zero rounds retains the complete Pending input and does not demand a
service handle. Missing Pending components still stop at the linear boundary.
All private output slots are masked even for present local private inputs. -/
theorem zero (linked : DeclarationsLinked [] definitions)
    (bodies : RoundsBoundaryInstallation.Bodies definitions) (maximum : Nat)
    (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (a m l r point : Option (List F)) (claim : Option F) (service : Option Nat) :
    process (F := F) (G := G) definitions maximum ctx a m l r point claim (some 0) service =
      match point, claim with
      | some point, some claim =>
        .done (.cons none (.cons none (.cons none (.cons none (.cons none
          (.cons (some point) (.cons (some claim) .nil)))))))
      | _, _ => .halt .incomplete := by
  unfold process
  rw [RoundsBoundaryInstallation.owned_rounds_open linked bodies]
  cases point <;> cases claim <;> simp only [PIR.Process.bind, Values.get]
  rw [repeat_zero (repeatSpec maximum) ctx (ctx.roles 1) _ _ _ (inside ctx), mask_entry ctx distinct]
  simp only [Values.get, RoundsBoundaryInstallation.owned_rounds_close linked bodies, PIR.Process.bind]

end ZkcSecurity.Bindings.Gkr.RoundsInvocationInstallation
