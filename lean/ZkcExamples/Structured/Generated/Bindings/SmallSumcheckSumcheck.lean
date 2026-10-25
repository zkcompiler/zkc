module

public import ZkcExamples.Structured.Generated.Bindings.SmallSumcheckCallbacks
public import ZkcExamples.Structured.SumcheckVerifierLaws

@[expose] public section

/-! Generated actual-source endpoint template bindings. -/
namespace ZkcExamples.Structured.Generated.Bindings.SmallSumcheckSumcheck
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm Zkc.Source.Structured.Bindings
open ZkcExamples.Structured ZkcExamples.Structured.Generated.Bindings.SmallSumcheck ZkcExamples.Structured.Generated.Bindings.SmallSumcheckCallbacks
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option smartUnfolding false
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

theorem helper_bodies : SumcheckVerifierHelpers.Bodies payload.definitions where
  empty := ⟨payload.definitions.get ⟨13, by decide +kernel⟩, List.get_mem _ _, rfl, by kernel_rfl⟩
  append := ⟨payload.definitions.get ⟨19, by decide +kernel⟩, List.get_mem _ _, rfl, by kernel_rfl⟩
  width := ⟨payload.definitions.get ⟨11, by decide +kernel⟩, List.get_mem _ _, rfl, by kernel_rfl⟩
  «variables» := ⟨payload.definitions.get ⟨12, by decide +kernel⟩, List.get_mem _ _, rfl, by kernel_rfl⟩
  values := ⟨payload.definitions.get ⟨8, by decide +kernel⟩, List.get_mem _ _, rfl, by kernel_rfl⟩

theorem protocol0Role1Callback0_body_template : protocol0Role1Callback0Body = SumcheckVerifierBodies.roundBody := by
  kernel_rfl

theorem protocol0Role1Callback0_template (ctx : ProtocolContext) (index : Option Nat)
    (table : Option (List F)) (dimension width : Option Nat) (privatePoint point : Option (List F))
    (claim : Option F) (service : Option Nat) :
    protocol0Role1Callback0Process (G := G) ctx index table dimension width privatePoint point claim service =
      (SumcheckVerifierLaws.roundPlain ctx service (point, claim)).bind
        (fun result => .done (SumcheckVerifierLaws.embedV result)) := by
  unfold protocol0Role1Callback0Process SumcheckVerifierLaws.roundPlain
  simp only [PIR.Process.bind.eq_3]
  congr 1
  funext low
  congr 1
  funext high
  cases claim with
  | none => rfl
  | some current =>
    dsimp only
    by_cases passed : current = low + high
    · simp only [ite_eq_left passed]
      cases service with
      | none => rfl
      | some handle =>
        dsimp only
        congr 1
        funext challenge
        congr 1
        funext acknowledgement
        cases point <;> rfl
    · simp only [ite_eq_right passed, PIR.Process.bind.eq_2]

theorem protocol0Role1Callback0_family_source (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (index : Option Nat) (table : Option (List F)) (dimension width : Option Nat)
    (privatePoint point : Option (List F)) (claim : Option F) (service : Option Nat) :
    protocol0Role1Callback0Body.denote (participantMeaningWith (.silent _) (participantActions F G)
      (helpers payload) (ctx.roles 1) (payload.plainProtocolTable F G) ctx)
      (Values.cons index (.cons table (.cons dimension (.cons width (.cons privatePoint
        (.cons point (.cons claim (.cons service .nil)))))))).get =
      (SumcheckVerifierLaws.roundPlain ctx service (point, claim)).bind
        (fun result => .done (SumcheckVerifierLaws.embedV result)) :=
  (protocol0Role1Callback0_source ctx distinct _).trans (protocol0Role1Callback0_template ctx index table dimension width privatePoint point claim service)

theorem protocol0Role1Callback0_loop_family (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (start count : Nat) (service : Option Nat) (state : Option (List F) × Option F) :
    Repeat.loop (⟨[(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.service "random.bls12-381.fr/0")], [0, 1], [[0], [0], [0], [0], [1], [1]], 2⟩ : RepeatSpec) ctx (ctx.roles 1) (SumcheckVerifierLaws.cap service)
      ((Runs.uniform (helpers (F := F) (G := G) payload) (payload.plainProtocolTable F G) ctx
        (ctx.roles 1)).callback (⟨[(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.service "random.bls12-381.fr/0")], [0, 1], [[0], [0], [0], [0], [1], [1]], 2⟩ : RepeatSpec) protocol0Role1Callback0Body)
      start count (SumcheckVerifierLaws.embedV state) =
      (PIR.repeatN count (SumcheckVerifierLaws.roundPlain ctx service) state).bind
        (fun result => .done (SumcheckVerifierLaws.embedV result)) := by
  rw [protocol0Role1Callback0_body_template]
  exact SumcheckVerifierLaws.loop_optional payload helper_bodies ctx (ctx.roles 1) rfl
    (fun same => distinct 0 (by decide) (by decide) same) start count 2 service state

end ZkcExamples.Structured.Generated.Bindings.SmallSumcheckSumcheck
