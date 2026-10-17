module

public import ZkcExamples.Structured.ApplicationViews
public import Zkc.Source.Structured.OpenLaws

public section

/-! Algebraic equations for the complete unchanged application source. Each
participant has its own optional inputs. These equations concern the admitted
Lean process; native correspondence is an independent comparison boundary. -/
namespace ZkcExamples.Structured.Application
open Zkc.Source Zkc.Source.Structured ApplicationBodies ApplicationViews

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

@[expose] def inputs (x y : Option F) : Values (Component (assignment F G)) pairTypes :=
  .cons x (.cons y .nil)

@[expose] def optionalBinary (operation : F → F → F) (x y : Option F) : Option F := do
  return operation (← x) (← y)

/-- Exact full-signature transport from the retained checked Step declaration. -/
theorem step_body_view (context : ProtocolContext) (self : Nat) (x y : Option F) :
    invokeProtocol (unit.protocolTable F G) stepSignature context self (inputs x y) =
      (stepBody.denote
        (participantMeaning (unit.tables F G) self (unit.protocolTable F G) context)
        (maskValues self (context.mapScopes stepSignature.inputScopes) (inputs x y)).get).bind
        (fun results => .done (maskValues self
          (context.mapScopes stepSignature.outputScopes) results)) :=
  unit.protocol_body_view_as stepDefinition step_member stepSignature step_signature
    stepBody step_raw context self (inputs x y)

/-- The zero-result Observe declaration is a retained closure with an exact body. -/
theorem observe_body_view (context : ProtocolContext) (self : Nat) :
    invokeProtocol (unit.protocolTable F G) observeSignature context self .nil =
      (observeBody.denote
        (participantMeaning (unit.tables F G) self (unit.protocolTable F G) context)
        Values.nil.get).bind (fun results => .done results) :=
  unit.protocol_body_view_as observeDefinition observe_member observeSignature observe_signature
    observeBody observe_raw context self .nil

theorem segment_body_view (context : ProtocolContext) (self : Nat) (x y : Option F) :
    invokeProtocol (unit.protocolTable F G) segmentSignature context self (inputs x y) =
      (segmentBody.denote
        (participantMeaning (unit.tables F G) self (unit.protocolTable F G) context)
        (maskValues self (context.mapScopes segmentSignature.inputScopes) (inputs x y)).get).bind
        (fun results => .done (maskValues self
          (context.mapScopes segmentSignature.outputScopes) results)) :=
  unit.protocol_body_view_as segmentDefinition segment_member segmentSignature segment_signature
    segmentBody segment_raw context self (inputs x y)

/-- Run uses its literal full ABI when transporting the selected source body. -/
theorem run_body_view (context : ProtocolContext) (self : Nat) (x y : Option F) :
    invokeProtocol (unit.protocolTable F G) runSignature context self (inputs x y) =
      (runBody.denote
        (participantMeaning (unit.tables F G) self (unit.protocolTable F G) context)
        (maskValues self (context.mapScopes runSignature.inputScopes) (inputs x y)).get).bind
        (fun results => .done (maskValues self
          (context.mapScopes runSignature.outputScopes) results)) :=
  unit.protocol_body_view_as runDefinition run_member runSignature run_signature
    runBody run_raw context self (inputs x y)

/-- Step calculates both positions before masking the root participant's results. -/
theorem step_body (tables : OpenTables F G)
    (protocols : ProtocolTable (assignment F G) (observedInterface F G))
    (context : ProtocolContext) (self : Nat) (x y : Option F) :
    stepBody.denote (participantMeaning tables self protocols context) (inputs x y).get =
      .call (.mark "") (fun _ => .call (.mark "") (fun _ =>
        .done (.cons (optionalBinary (· + ·) x y)
          (.cons (optionalBinary (· * ·) x y) .nil)))) := by
  rcases context with ⟨parentSite, roleMap⟩
  cases parentSite <;> cases x <;> cases y <;> rfl

theorem observe_returns (context : ProtocolContext) (self : Nat) :
    invokeProtocol (unit.protocolTable F G) observeSignature context self .nil =
      .done .nil := by
  rw [observe_body_view]
  rfl

/-- Local role zero of Step exposes the addition result. -/
theorem step_first (x y : Option F) :
    (invokeProtocol (unit.protocolTable F G) stepSignature {} 0 (inputs x y)).interpret
      forgetSites = .done (.cons (optionalBinary (· + ·) x y) (.cons none .nil)) := by
  rw [step_body_view]
  cases x <;> cases y <;> rfl

/-- Local role one of Step exposes the multiplication result. -/
theorem step_second (x y : Option F) :
    (invokeProtocol (unit.protocolTable F G) stepSignature {} 1 (inputs x y)).interpret
      forgetSites = .done (.cons none (.cons (optionalBinary (· * ·) x y) .nil)) := by
  rw [step_body_view]
  cases x <;> cases y <;> rfl

/-- Segment applies Step with the actual positional permutation [1,0]. -/
theorem segment_first (x y : Option F) :
    (invokeProtocol (unit.protocolTable F G) segmentSignature {} 0 (inputs x y)).interpret
      forgetSites = .done (.cons (optionalBinary (· * ·) x y) (.cons none .nil)) := by
  rw [segment_body_view]
  have stepView := unit.protocol_body_view_as (F := F) (G := G)
    stepDefinition step_member stepSignature step_signature stepBody step_raw
  have observeView := unit.protocol_body_view_as (F := F) (G := G)
    observeDefinition observe_member observeSignature observe_signature observeBody observe_raw
  -- Expose nested calls while keeping the checked protocol table folded.
  simp only [segmentBody, Region.denote, Regions.denote, participantMeaning,
    participantMeaningWith, protocolOperationWith, Operands.eval]
  -- Normalize dependent ABI types before rewriting below SSA continuations.
  dsimp +instances only [ProtocolOp.arguments, ProtocolOp.results, ProtocolOp.regions,
    stepSignature, observeSignature, segmentSignature, runSignature] at *
  simp only [stepView, observeView]
  cases x <;> cases y <;> rfl

theorem segment_second (x y : Option F) :
    (invokeProtocol (unit.protocolTable F G) segmentSignature {} 1 (inputs x y)).interpret
      forgetSites = .done (.cons none (.cons (optionalBinary (· + ·) x y) .nil)) := by
  rw [segment_body_view]
  have stepView := unit.protocol_body_view_as (F := F) (G := G)
    stepDefinition step_member stepSignature step_signature stepBody step_raw
  have observeView := unit.protocol_body_view_as (F := F) (G := G)
    observeDefinition observe_member observeSignature observe_signature observeBody observe_raw
  simp only [segmentBody, Region.denote, Regions.denote, participantMeaning,
    participantMeaningWith, protocolOperationWith, Operands.eval]
  dsimp +instances only [ProtocolOp.arguments, ProtocolOp.results, ProtocolOp.regions,
    stepSignature, observeSignature, segmentSignature, runSignature] at *
  simp only [stepView, observeView]
  cases x <;> cases y <;> rfl

/-- Exact observed marks include the retained zero-result call's header. -/
theorem observed_first (x y : Option F) :
    program.observed F G 0 (inputs x y) =
      .call (.mark "s0") (fun _ =>
        .call (.mark "apply_2_s0_s0") (fun _ =>
          .call (.mark "") (fun _ => .call (.mark "") (fun _ =>
            .call (.mark "apply_2_s0_s3") (fun _ =>
              .done (.cons (optionalBinary (· * ·) x y) (.cons none .nil))))))) := by
  change invokeProtocol (unit.protocolTable F G) runSignature {} 0 (inputs x y) = _
  rw [run_body_view]
  have stepView := unit.protocol_body_view_as (F := F) (G := G)
    stepDefinition step_member stepSignature step_signature stepBody step_raw
  have observeView := unit.protocol_body_view_as (F := F) (G := G)
    observeDefinition observe_member observeSignature observe_signature observeBody observe_raw
  have segmentView := unit.protocol_body_view_as (F := F) (G := G)
    segmentDefinition segment_member segmentSignature segment_signature segmentBody segment_raw
  simp only [runBody, Region.denote, Regions.denote, participantMeaning,
    participantMeaningWith, protocolOperationWith, Operands.eval]
  dsimp +instances only [ProtocolOp.arguments, ProtocolOp.results, ProtocolOp.regions,
    stepSignature, observeSignature, segmentSignature, runSignature] at *
  simp only [segmentView]
  simp only [segmentBody, Region.denote, Regions.denote, participantMeaning,
    participantMeaningWith, protocolOperationWith, Operands.eval]
  dsimp +instances only [ProtocolOp.arguments, ProtocolOp.results, ProtocolOp.regions,
    stepSignature, observeSignature, segmentSignature, runSignature] at *
  simp only [stepView, observeView]
  cases x <;> cases y <;> rfl

theorem observed_second (x y : Option F) :
    program.observed F G 1 (inputs x y) =
      .call (.mark "s0") (fun _ =>
        .call (.mark "apply_2_s0_s0") (fun _ =>
          .call (.mark "") (fun _ => .call (.mark "") (fun _ =>
            .call (.mark "apply_2_s0_s3") (fun _ =>
              .done (.cons none (.cons (optionalBinary (· + ·) x y) .nil))))))) := by
  change invokeProtocol (unit.protocolTable F G) runSignature {} 1 (inputs x y) = _
  rw [run_body_view]
  have stepView := unit.protocol_body_view_as (F := F) (G := G)
    stepDefinition step_member stepSignature step_signature stepBody step_raw
  have observeView := unit.protocol_body_view_as (F := F) (G := G)
    observeDefinition observe_member observeSignature observe_signature observeBody observe_raw
  have segmentView := unit.protocol_body_view_as (F := F) (G := G)
    segmentDefinition segment_member segmentSignature segment_signature segmentBody segment_raw
  simp only [runBody, Region.denote, Regions.denote, participantMeaning,
    participantMeaningWith, protocolOperationWith, Operands.eval]
  dsimp +instances only [ProtocolOp.arguments, ProtocolOp.results, ProtocolOp.regions,
    stepSignature, observeSignature, segmentSignature, runSignature] at *
  simp only [segmentView]
  simp only [segmentBody, Region.denote, Regions.denote, participantMeaning,
    participantMeaningWith, protocolOperationWith, Operands.eval]
  dsimp +instances only [ProtocolOp.arguments, ProtocolOp.results, ProtocolOp.regions,
    stepSignature, observeSignature, segmentSignature, runSignature] at *
  simp only [stepView, observeView]
  cases x <;> cases y <;> rfl

theorem first_participant (x y : Option F) :
    program.participant F G 0 (inputs x y) =
      .done (.cons (optionalBinary (· * ·) x y) (.cons none .nil)) := by
  unfold Program.participant
  rw [observed_first]
  rfl

theorem second_participant (x y : Option F) :
    program.participant F G 1 (inputs x y) =
      .done (.cons none (.cons (optionalBinary (· + ·) x y) .nil)) := by
  unfold Program.participant
  rw [observed_second]
  rfl

/-- Each participant's source inputs remain independent of the other's copy. -/
theorem independent_inputs (px py vx vy : F) :
    program.participant F G 0 (inputs (some px) (some py)) =
        .done (.cons (some (px * py)) (.cons none .nil)) ∧
      program.participant F G 1 (inputs (some vx) (some vy)) =
        .done (.cons none (.cons (some (vx + vy)) .nil)) :=
  ⟨first_participant _ _, second_participant _ _⟩

end ZkcExamples.Structured.Application
