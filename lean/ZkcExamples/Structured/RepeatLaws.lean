module

public import ZkcExamples.Structured.RepeatViews
public import Zkc.Source.Structured.OpenLaws
public import Zkc.Source.Structured.RepeatLaws

@[expose] public section

/-! Complete process equations of the unchanged repeat client. Participant
counts, received values and service replies are independent parameters. -/
namespace ZkcExamples.Structured.RepeatLaws
open Zkc.Source Zkc.Source.Structured RepeatBodies RepeatViews

set_option smartUnfolding true

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def inputs (count : Option Nat) (a b : Option F) (go : Option Bool) (coins : Option Nat) :
    Values (Component (assignment F G)) runSignature.inputs :=
  .cons count (.cons a (.cons b (.cons go (.cons coins .nil))))

theorem round_body_view (context : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G)) roundSignature.inputs) :
    invokeProtocol (unit.protocolTable F G) roundSignature context self args =
      (roundBody.denote
        (participantMeaning (unit.tables F G) self (unit.protocolTable F G) context)
        (maskValues self (context.mapScopes roundSignature.inputScopes) args).get).bind
        (fun results => .done (maskValues self
          (context.mapScopes roundSignature.outputScopes) results)) :=
  unit.protocol_body_view_as roundDefinition round_member roundSignature round_signature
    roundBody round_raw context self args

theorem run_body_view (context : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G)) runSignature.inputs) :
    invokeProtocol (unit.protocolTable F G) runSignature context self args =
      (runBody.denote
        (participantMeaning (unit.tables F G) self (unit.protocolTable F G) context)
        (maskValues self (context.mapScopes runSignature.inputScopes) args).get).bind
        (fun results => .done (maskValues self
          (context.mapScopes runSignature.outputScopes) results)) :=
  unit.protocol_body_view_as runDefinition run_member runSignature run_signature
    runBody run_raw context self args

def receiverStep (parent : Option String) (a : F) : PIR.Proc (observedInterface F G) F :=
  let site := qualifyProtocolSite parent
  let child := qualifyProtocolSite (some (site "s5"))
  .call (.mark (site "s4")) <| fun _ =>
  .call (.mark (site "s5")) <| fun _ =>
  .call (.mark (child "s0")) <| fun _ =>
  .call (.mark (child "s2_0")) <| fun _ =>
  .call (.action (.receive (.field "bls12-381.fr") (child "s2_0") 1)) <| fun received =>
  .call (.mark "") <| fun _ =>
  .call (.mark "") <| fun _ =>
  .call (.mark "") <| fun _ =>
  .done (a + received)

def verifierStep (parent : Option String) (go : Bool) (coins : Nat) (b : F) :
    PIR.Proc (observedInterface F G) F :=
  let site := qualifyProtocolSite parent
  let child := qualifyProtocolSite (some (site "s5"))
  .call (.mark (site "s4")) <| fun _ =>
  if go then
    .call (.mark (site "s5")) <| fun _ =>
    .call (.mark (child "s0")) <| fun _ =>
    .call (.action (.query (child "s0") "bls12-381.fr" (.cons coins .nil))) <| fun (drawn : F) =>
    .call (.mark (child "s2_0")) <| fun _ =>
    .call (.action (.send (ty := .field "bls12-381.fr") (child "s2_0") 0 drawn)) <| fun _ =>
    .call (.mark "") <| fun _ =>
    .call (.mark "") <| fun _ =>
    .call (.mark "") <| fun _ =>
    .done (b + drawn)
  else .halt .reject

def receiverObserved (parent : Option String) (count : Nat) (a : F) :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs) :=
  .call (.mark (qualifyProtocolSite parent "s3")) <| fun _ =>
  (PIR.repeatN count (receiverStep parent) a).bind <| fun result =>
  .done (.cons (some result) (.cons none .nil))

def verifierObserved (parent : Option String) (count : Nat) (b : F) (go : Bool) (coins : Nat) :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs) :=
  .call (.mark (qualifyProtocolSite parent "s3")) <| fun _ =>
  (PIR.repeatN count (verifierStep parent go coins) b).bind <| fun result =>
  .done (.cons none (.cons (some result) .nil))

def receiverState (a : F) : Values (Component (assignment F G)) repeatSpec.state :=
  .cons (some a) (.cons none .nil)

def verifierState (b : F) : Values (Component (assignment F G)) repeatSpec.state :=
  .cons none (.cons (some b) .nil)

def callback (parent : Option String) (self : Nat) :
    RegionFunction (Component (assignment F G)) (observedInterface F G)
      (.index :: (repeatSpec.state ++ repeatSpec.captures), repeatSpec.state) :=
  fun args => repeatBody.denote
    (participantMeaning (unit.tables F G) self (unit.protocolTable F G) ⟨parent, id⟩) args.get

set_option smartUnfolding false in
theorem receiver_step (parent : Option String) (a : F) (index : Nat) :
    Repeat.step repeatSpec ⟨parent, id⟩ 0 (.cons none (.cons none .nil))
      (callback (F := F) (G := G) parent 0) (receiverState a) index =
      (receiverStep parent a).bind (fun result => .done (receiverState result)) := by
  cases parent <;> rfl

set_option smartUnfolding false in
theorem verifier_step (parent : Option String) (go : Bool) (coins : Nat) (b : F) (index : Nat) :
    Repeat.step repeatSpec ⟨parent, id⟩ 1 (.cons (some go) (.cons (some coins) .nil))
      (callback (F := F) (G := G) parent 1) (verifierState b) index =
      (verifierStep parent go coins b).bind (fun result => .done (verifierState result)) := by
  cases parent <;> cases go <;> rfl

theorem receiver_repeat (parent : Option String) (count : Nat) (bound : count ≤ 4) (a : F) :
    denoteRepeat repeatSpec ⟨parent, id⟩ 0 (some count) (receiverState a)
      (.cons none (.cons none .nil)) (callback (F := F) (G := G) parent 0) =
      (PIR.repeatN count (receiverStep parent) a).bind
        (fun result => .done (receiverState result)) := by
  rw [repeat_admitted _ _ _ _ _ _ count rfl bound]
  change Repeat.loop _ _ _ _ _ 0 count (receiverState a) = _
  rw [Repeat.loop_embed _ _ _ _ _ receiverState
    (fun value _ => receiverStep parent value) 0 count a (receiver_step parent)]
  rw [Finite.fold_range_repeatN]

theorem verifier_repeat (parent : Option String) (count : Nat) (bound : count ≤ 4)
    (go : Bool) (coins : Nat) (b : F) :
    denoteRepeat repeatSpec ⟨parent, id⟩ 1 (some count) (verifierState b)
      (.cons (some go) (.cons (some coins) .nil)) (callback (F := F) (G := G) parent 1) =
      (PIR.repeatN count (verifierStep parent go coins) b).bind
        (fun result => .done (verifierState result)) := by
  rw [repeat_admitted _ _ _ _ _ _ count rfl bound]
  change Repeat.loop _ _ _ _ _ 0 count (verifierState b) = _
  rw [Repeat.loop_embed _ _ _ _ _ verifierState
    (fun value _ => verifierStep parent go coins value) 0 count b (verifier_step parent go coins)]
  rw [Finite.fold_range_repeatN]

theorem contextual_receiver (parent : Option String) (count : Nat) (bound : count ≤ 4)
    (a : F) (b : Option F) (go : Option Bool) (coins : Option Nat) :
    invokeProtocol (unit.protocolTable F G) runSignature ⟨parent, id⟩ 0
      (inputs (some count) (some a) b go coins) = receiverObserved parent count a := by
  rw [run_body_view]
  change ((PIR.Proc.call (I := observedInterface F G)
    (.mark (qualifyProtocolSite parent "s3")) (fun _ =>
      (denoteRepeat repeatSpec ⟨parent, id⟩ 0 (some count) (receiverState a)
        (.cons none (.cons none .nil)) (callback (F := F) (G := G) parent 0)).bind _)).bind _ :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs)) = _
  simp only [PIR.Proc.bind]
  rw [receiver_repeat parent count bound a]
  erw [PIR.Proc.bind_assoc, PIR.Proc.bind_assoc]
  rfl

theorem contextual_verifier (parent : Option String) (count : Nat) (bound : count ≤ 4)
    (a : Option F) (b : F) (go : Bool) (coins : Nat) :
    invokeProtocol (unit.protocolTable F G) runSignature ⟨parent, id⟩ 1
      (inputs (some count) a (some b) (some go) (some coins)) =
        verifierObserved parent count b go coins := by
  rw [run_body_view]
  change ((PIR.Proc.call (I := observedInterface F G)
    (.mark (qualifyProtocolSite parent "s3")) (fun _ =>
      (denoteRepeat repeatSpec ⟨parent, id⟩ 1 (some count) (verifierState b)
        (.cons (some go) (.cons (some coins) .nil)) (callback (F := F) (G := G) parent 1)).bind _)).bind _ :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs)) = _
  simp only [PIR.Proc.bind]
  rw [verifier_repeat parent count bound go coins b]
  erw [PIR.Proc.bind_assoc, PIR.Proc.bind_assoc]
  rfl

theorem observed_receiver (count : Nat) (bound : count ≤ 4)
    (a : F) (b : Option F) (go : Option Bool) (coins : Option Nat) :
    program.observed F G 0 (inputs (some count) (some a) b go coins) =
      receiverObserved none count a := contextual_receiver none count bound a b go coins

theorem observed_verifier (count : Nat) (bound : count ≤ 4)
    (a : Option F) (b : F) (go : Bool) (coins : Nat) :
    program.observed F G 1 (inputs (some count) a (some b) (some go) (some coins)) =
      verifierObserved none count b go coins := contextual_verifier none count bound a b go coins

/-- Internal marks disappear; actual qualified receive sites remain. -/
theorem receiver_participant (count : Nat) (bound : count ≤ 4)
    (a : F) (b : Option F) (go : Option Bool) (coins : Option Nat) :
    program.participant F G 0 (inputs (some count) (some a) b go coins) =
      (receiverObserved (G := G) none count a).interpret forgetSites :=
  congrArg (fun p => p.interpret forgetSites) (observed_receiver (F := F) (G := G) count bound a b go coins)

theorem verifier_participant (count : Nat) (bound : count ≤ 4)
    (a : Option F) (b : F) (go : Bool) (coins : Nat) :
    program.participant F G 1 (inputs (some count) a (some b) (some go) (some coins)) =
      (verifierObserved (G := G) none count b go coins).interpret forgetSites :=
  congrArg (fun p => p.interpret forgetSites) (observed_verifier (F := F) (G := G) count bound a b go coins)

/-- Independent local counts require no equality or honest-delivery premise. -/
theorem independent_counts (nP nV : Nat) (pBound : nP ≤ 4) (vBound : nV ≤ 4)
    (aP bV : F) (go : Bool) (coins : Nat) :
    program.observed F G 0 (inputs (some nP) (some aP) none none none) =
        receiverObserved none nP aP ∧
      program.observed F G 1 (inputs (some nV) none (some bV) (some go) (some coins)) =
        verifierObserved none nV bV go coins :=
  ⟨observed_receiver nP pBound aP none none none,
    observed_verifier nV vBound none bV go coins⟩

theorem zero_verifier (a b : Option F) (go : Option Bool) (coins : Option Nat) :
    program.participant F G 1 (inputs (some 0) a b go coins) =
      .done (.cons none (.cons b .nil)) := by
  change (invokeProtocol (unit.protocolTable F G) runSignature {} 1
    (inputs (some 0) a b go coins)).interpret forgetSites = _
  rw [run_body_view]
  rfl

/-- Missing count retains the source header and demands no state or captures. -/
theorem missing_count_receiver (a b : Option F) (go : Option Bool) (coins : Option Nat) :
    program.observed F G 0 (inputs none a b go coins) =
      .call (.mark "s3") (fun _ => .halt .incomplete) := by
  change invokeProtocol (unit.protocolTable F G) runSignature {} 0 (inputs none a b go coins) = _
  rw [run_body_view]
  rfl

/-- Every excessive natural refuses at the original header, before callbacks. -/
theorem excess_count_receiver (count : Nat) (large : 4 < count)
    (a b : Option F) (go : Option Bool) (coins : Option Nat) :
    program.observed F G 0 (inputs (some count) a b go coins) =
      .call (.mark "s3") (fun _ => .halt .refused) := by
  change invokeProtocol (unit.protocolTable F G) runSignature {} 0
    (inputs (some count) a b go coins) = _
  rw [run_body_view]
  change ((PIR.Proc.call (I := observedInterface F G)
    (.mark (qualifyProtocolSite none "s3")) (fun _ =>
      (denoteRepeat repeatSpec ⟨none, id⟩ 0 (some count) (.cons a (.cons none .nil))
        (.cons none (.cons none .nil)) (callback (F := F) (G := G) none 0)).bind _)).bind _ :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs)) = _
  simp only [PIR.Proc.bind]
  rw [repeat_above_maximum repeatSpec ⟨none, id⟩ 0 _ _ _ count rfl large]
  rfl

/-- Missing count retains the source header and demands no state or captures. -/
theorem missing_count_verifier (a b : Option F) (go : Option Bool) (coins : Option Nat) :
    program.observed F G 1 (inputs none a b go coins) =
      .call (.mark "s3") (fun _ => .halt .incomplete) := by
  change invokeProtocol (unit.protocolTable F G) runSignature {} 1 (inputs none a b go coins) = _
  rw [run_body_view]
  rfl

/-- Every excessive natural refuses at the original header, before callbacks. -/
theorem excess_count_verifier (count : Nat) (large : 4 < count)
    (a b : Option F) (go : Option Bool) (coins : Option Nat) :
    program.observed F G 1 (inputs (some count) a b go coins) =
      .call (.mark "s3") (fun _ => .halt .refused) := by
  change invokeProtocol (unit.protocolTable F G) runSignature {} 1
    (inputs (some count) a b go coins) = _
  rw [run_body_view]
  change ((PIR.Proc.call (I := observedInterface F G)
    (.mark (qualifyProtocolSite none "s3")) (fun _ =>
      (denoteRepeat repeatSpec ⟨none, id⟩ 1 (some count) (.cons none (.cons b .nil))
        (.cons go (.cons coins .nil)) (callback (F := F) (G := G) none 1)).bind _)).bind _ :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs)) = _
  simp only [PIR.Proc.bind]
  rw [repeat_above_maximum repeatSpec ⟨none, id⟩ 1 _ _ _ count rfl large]
  rfl

/-- For every positive admitted count, absent go stops at the first reached guard.
Neither optional field state nor the service handle is demanded first. -/
theorem positive_missing_go (count : Nat) (positive : 0 < count) (bound : count ≤ 4)
    (a b : Option F) (coins : Option Nat) :
    program.observed F G 1 (inputs (some count) a b none coins) =
      .call (.mark "s3") (fun _ => .call (.mark "s4") (fun _ => .halt .incomplete)) := by
  cases count with
  | zero => cases positive
  | succ count =>
    change invokeProtocol (unit.protocolTable F G) runSignature {} 1
      (inputs (some (count + 1)) a b none coins) = _
    rw [run_body_view]
    change ((PIR.Proc.call (I := observedInterface F G) (.mark "s3") (fun _ =>
      (denoteRepeat repeatSpec {} 1 (some (count + 1)) (.cons none (.cons b .nil))
        (.cons none (.cons coins .nil)) (callback (F := F) (G := G) none 1)).bind _)).bind _ :
      PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs)) = _
    simp only [PIR.Proc.bind]
    rw [repeat_admitted repeatSpec {} 1 _ _ _ (count + 1) rfl bound, Repeat.loop_succ]
    rfl

end ZkcExamples.Structured.RepeatLaws
