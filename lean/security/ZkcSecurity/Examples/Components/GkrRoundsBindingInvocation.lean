module

public import ZkcSecurity.Examples.Components.GkrRoundsBinding

@[expose] public section
noncomputable section

/-! Exact bounded invocation of the imported Rounds role 1. The source's maximum,
optional count, runtime scopes and output permutation remain operational. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Examples.Components.GkrRoundsBinding
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Bindings Zkc.Source.Structured.NormalForm
open ZkcExamples.Structured.Generated.Bindings.GkrRounds
open ZkcExamples.Structured.Generated.Bindings.GkrRoundsCallbacks
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
    (a m l r : Option (List F)) (claim : Option F) :
    maskValues (ctx.roles 1) (ctx.mapScopes spec.stateScopes)
      (.cons a (.cons m (.cons l (.cons r (.cons none (.cons (some []) (.cons claim .nil)))))) :
        Values (Component (assignment F G)) spec.state) =
      .cons none (.cons none (.cons none (.cons none (.cons none (.cons (some []) (.cons claim .nil)))))) := by
  change (Values.cons (Participant.restrict ([ctx.roles 0].contains (ctx.roles 1)) a)
    (.cons (Participant.restrict ([ctx.roles 0].contains (ctx.roles 1)) m)
      (.cons (Participant.restrict ([ctx.roles 0].contains (ctx.roles 1)) l)
        (.cons (Participant.restrict ([ctx.roles 0].contains (ctx.roles 1)) r)
          (.cons (Participant.restrict ([ctx.roles 0].contains (ctx.roles 1)) none)
            (.cons (Participant.restrict ([ctx.roles 1].contains (ctx.roles 1)) (some []))
              (.cons (Participant.restrict ([ctx.roles 1].contains (ctx.roles 1)) claim) .nil)))))) :
      Values (Component (assignment F G)) spec.state) = _
  simp [Participant.restrict, Ne.symm (distinct 0 (by decide) (by decide))]

/-- Direct imported whole-Process equation. Mathematical representation facts
are intentionally absent: this binding is shared by both property consumers. -/
theorem verifier_binding (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (a m l r : Option (List F)) (claim : F) (service count : Nat) (bounded : count ≤ 4)
    {n : Nat} (raw : RawState F) (reference : GkrRoundsReference.State F (n + count)) :
    protocol0Role1Process (F := F) (G := G) ctx a m l r (some claim) (some count) (some service) =
      ((program service).remaining count ctx (initial raw reference claim)).bind
        (fun final => .done (carried (G := G) final)) := by
  rw [protocol0Role1_readable ctx distinct]
  unfold protocol0Role1ReadableProcess
  rw [GkrRoundsBindingHelpers.owned_empty]
  simp only [PIR.Process.bind, Values.get, Runs.uniform]
  rw [repeat_admitted spec ctx (ctx.roles 1) _ _ _ count (inside ctx) bounded]
  rw [mask_entry ctx distinct]
  change (actualRemaining (G := G) service ctx count 0 (initial raw reference claim)).bind _ = _
  rw [remaining_binding service ctx distinct]
  simp only [PIR.Process.bind_assoc, carried, runtime, PIR.Process.bind, Values.get]

/-- Missing or excessive source counts stop before any receive or query. -/
theorem missing_count (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (a m l r : Option (List F)) (claim : Option F) (service : Option Nat) :
    protocol0Role1Process (F := F) (G := G) ctx a m l r claim none service = .halt .incomplete := by
  rw [protocol0Role1_readable ctx distinct]
  unfold protocol0Role1ReadableProcess
  rw [GkrRoundsBindingHelpers.owned_empty]
  simp only [PIR.Process.bind, Runs.uniform]
  rw [repeat_missing_count spec ctx (ctx.roles 1) _ _ _ (inside ctx)]
  rfl

theorem above_maximum (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (a m l r : Option (List F)) (claim : Option F) (service : Option Nat)
    (count : Nat) (large : 4 < count) :
    protocol0Role1Process (F := F) (G := G) ctx a m l r claim (some count) service = .halt .refused := by
  rw [protocol0Role1_readable ctx distinct]
  unfold protocol0Role1ReadableProcess
  rw [GkrRoundsBindingHelpers.owned_empty]
  simp only [PIR.Process.bind, Runs.uniform]
  rw [repeat_above_maximum spec ctx (ctx.roles 1) _ _ _ count (inside ctx) large]
  rfl

/-- Zero rounds does not demand a claim or service handle. All private output
slots are masked even if adversarial local input options contain values. -/
theorem zero (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (a m l r : Option (List F)) (claim : Option F) (service : Option Nat) :
    protocol0Role1Process (F := F) (G := G) ctx a m l r claim (some 0) service =
      .done (.cons none (.cons none (.cons none (.cons none (.cons none
        (.cons (some []) (.cons claim .nil))))))) := by
  rw [protocol0Role1_readable ctx distinct]
  unfold protocol0Role1ReadableProcess
  rw [GkrRoundsBindingHelpers.owned_empty]
  simp only [PIR.Process.bind, Runs.uniform]
  rw [repeat_zero spec ctx (ctx.roles 1) _ _ _ (inside ctx)]
  simp only [Values.get]
  rw [mask_entry ctx distinct]
  rfl

end ZkcSecurity.Examples.Components.GkrRoundsBinding
