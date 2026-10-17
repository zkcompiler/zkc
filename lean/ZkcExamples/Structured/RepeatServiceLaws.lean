module

public import ZkcExamples.Structured.RepeatServiceViews
public import Zkc.Source.Structured.OpenLaws
public import Zkc.Source.Structured.RepeatLaws

@[expose] public section

/-! Complete source processes retain the same two actual service operands in
prelude, each ordered Draw application, and suffix. No distribution is assumed. -/
namespace ZkcExamples.Structured.RepeatServiceLaws
open Zkc.Source Zkc.Source.Structured RepeatServiceBodies RepeatServiceViews

set_option smartUnfolding true

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def inputs (count first second : Option Nat) :
    Values (Component (assignment F G)) runSignature.inputs :=
  .cons count (.cons first (.cons second .nil))

theorem draw_body_view (context : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G)) drawSignature.inputs) :
    invokeProtocol (unit.protocolTable F G) drawSignature context self args =
      (drawBody.denote
        (participantMeaning (unit.tables F G) self (unit.protocolTable F G) context)
        (maskValues self (context.mapScopes drawSignature.inputScopes) args).get).bind
        (fun results => .done (maskValues self
          (context.mapScopes drawSignature.outputScopes) results)) :=
  unit.protocol_body_view_as drawDefinition draw_member drawSignature draw_signature
    drawBody draw_raw context self args

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

def verifierStep (parent : Option String) (peer first second : Nat) (state : F) :
    PIR.Proc (observedInterface F G) F :=
  let site := qualifyProtocolSite parent
  let child := qualifyProtocolSite (some (site "s7"))
  .call (.mark (site "s7")) <| fun _ =>
  .call (.mark (child "s0")) <| fun _ =>
  .call (.action (.query (child "s0") "bls12-381.fr" (.cons first .nil))) <| fun (a : F) =>
  .call (.mark (child "s2")) <| fun _ =>
  .call (.action (.query (child "s2") "bls12-381.fr" (.cons second .nil))) <| fun (b : F) =>
  .call (.mark "") <| fun _ =>
  .call (.mark (child "s5_0")) <| fun _ =>
  .call (.action (.send (ty := .field "bls12-381.fr") (child "s5_0") peer (a + b))) <| fun _ =>
  .call (.mark "") <| fun _ =>
  .call (.mark "") <| fun _ =>
  .call (.mark "") <| fun _ =>
  .call (.mark "") <| fun _ =>
  .done (state + (a + b))

def receiverStep (parent : Option String) (peer : Nat) (state : F) :
    PIR.Proc (observedInterface F G) F :=
  let site := qualifyProtocolSite parent
  let child := qualifyProtocolSite (some (site "s7"))
  .call (.mark (site "s7")) <| fun _ =>
  .call (.mark (child "s0")) <| fun _ =>
  .call (.mark (child "s2")) <| fun _ =>
  .call (.mark "") <| fun _ =>
  .call (.mark (child "s5_0")) <| fun _ =>
  .call (.action (.receive (.field "bls12-381.fr") (child "s5_0") peer)) <| fun received =>
  .call (.mark "") <| fun _ =>
  .call (.mark "") <| fun _ =>
  .call (.mark "") <| fun _ =>
  .call (.mark "") <| fun _ =>
  .done (state + received)

def verifierObserved (parent : Option String) (peer count first second : Nat) :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs) :=
  let site := qualifyProtocolSite parent
  .call (.mark (site "s0")) <| fun _ =>
  .call (.action (.query (site "s0") "bls12-381.fr" (.cons first .nil))) <| fun (before : F) =>
  .call (.mark "") <| fun _ =>
  .call (.mark "") <| fun _ =>
  .call (.mark (site "s6")) <| fun _ =>
  (PIR.repeatN count (verifierStep parent peer first second) before).bind <| fun result =>
  .call (.mark (site "s16")) <| fun _ =>
  .call (.action (.query (site "s16") "bls12-381.fr" (.cons first .nil))) <| fun (after : F) =>
  .call (.mark "") <| fun _ =>
  .done (.cons none (.cons (some (result + after)) .nil))

def receiverObserved (parent : Option String) (peer count : Nat) :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs) :=
  let site := qualifyProtocolSite parent
  .call (.mark (site "s0")) <| fun _ =>
  .call (.mark "") <| fun _ =>
  .call (.mark "") <| fun _ =>
  .call (.mark (site "s6")) <| fun _ =>
  (PIR.repeatN count (receiverStep parent peer) ((0 : Nat) : F)).bind <| fun result =>
  .call (.mark (site "s16")) <| fun _ =>
  .call (.mark "") <| fun _ =>
  .done (.cons (some result) (.cons none .nil))

def receiverState (a : F) : Values (Component (assignment F G)) repeatSpec.state :=
  .cons (some a) (.cons none .nil)

def verifierState (b : F) : Values (Component (assignment F G)) repeatSpec.state :=
  .cons none (.cons (some b) .nil)

def mappedContext (parent : Option String) (swapped : Bool) : ProtocolContext :=
  ⟨parent, if swapped then roleSubstitution [2, 0] else id⟩

def receiverRole (swapped : Bool) : Nat := if swapped then 2 else 0

def verifierRole (swapped : Bool) : Nat := if swapped then 0 else 1

def callback (parent : Option String) (swapped : Bool) (self : Nat) :
    RegionFunction (Component (assignment F G)) (observedInterface F G)
      (.index :: (repeatSpec.state ++ repeatSpec.captures), repeatSpec.state) :=
  fun args => repeatBody.denote
    (participantMeaning (unit.tables F G) self (unit.protocolTable F G)
      (mappedContext parent swapped)) args.get

set_option smartUnfolding false in
theorem receiver_step (parent : Option String) (swapped : Bool) (a : F) (index : Nat) :
    Repeat.step repeatSpec (mappedContext parent swapped) (receiverRole swapped)
      (.cons none (.cons none .nil)) (callback (F := F) (G := G) parent swapped (receiverRole swapped))
      (receiverState a) index =
      (receiverStep parent (verifierRole swapped) a).bind
        (fun result => .done (receiverState result)) := by
  cases swapped <;> cases parent <;> rfl

set_option smartUnfolding false in
theorem verifier_step (parent : Option String) (swapped : Bool)
    (first second : Nat) (b : F) (index : Nat) :
    Repeat.step repeatSpec (mappedContext parent swapped) (verifierRole swapped)
      (.cons (some first) (.cons (some second) .nil))
      (callback (F := F) (G := G) parent swapped (verifierRole swapped)) (verifierState b) index =
      (verifierStep parent (receiverRole swapped) first second b).bind
        (fun result => .done (verifierState result)) := by
  cases swapped <;> cases parent <;> rfl

theorem receiver_repeat (parent : Option String) (swapped : Bool)
    (count : Nat) (bound : count ≤ 3) (a : F) :
    denoteRepeat repeatSpec (mappedContext parent swapped) (receiverRole swapped) (some count)
      (receiverState a) (.cons none (.cons none .nil))
      (callback (F := F) (G := G) parent swapped (receiverRole swapped)) =
      (PIR.repeatN count (receiverStep parent (verifierRole swapped)) a).bind
        (fun result => .done (receiverState result)) := by
  have inside : (repeatSpec.roles.map (mappedContext parent swapped).roles).contains
      (receiverRole swapped) = true := by cases swapped <;> rfl
  rw [repeat_admitted _ _ _ _ _ _ count inside bound]
  have masked : maskValues (receiverRole swapped)
      ((mappedContext parent swapped).mapScopes repeatSpec.stateScopes) (receiverState (G := G) a) =
        receiverState a := by cases swapped <;> rfl
  rw [masked, Repeat.loop_embed _ _ _ _ _ receiverState
    (fun value _ => receiverStep parent (verifierRole swapped) value) 0 count a
    (receiver_step parent swapped), Finite.fold_range_repeatN]

theorem verifier_repeat (parent : Option String) (swapped : Bool)
    (count : Nat) (bound : count ≤ 3) (first second : Nat) (b : F) :
    denoteRepeat repeatSpec (mappedContext parent swapped) (verifierRole swapped) (some count)
      (verifierState b) (.cons (some first) (.cons (some second) .nil))
      (callback (F := F) (G := G) parent swapped (verifierRole swapped)) =
      (PIR.repeatN count (verifierStep parent (receiverRole swapped) first second) b).bind
        (fun result => .done (verifierState result)) := by
  have inside : (repeatSpec.roles.map (mappedContext parent swapped).roles).contains
      (verifierRole swapped) = true := by cases swapped <;> rfl
  rw [repeat_admitted _ _ _ _ _ _ count inside bound]
  have masked : maskValues (verifierRole swapped)
      ((mappedContext parent swapped).mapScopes repeatSpec.stateScopes) (verifierState (G := G) b) =
        verifierState b := by cases swapped <;> rfl
  rw [masked, Repeat.loop_embed _ _ _ _ _ verifierState
    (fun value _ => verifierStep parent (receiverRole swapped) first second value) 0 count b
    (verifier_step parent swapped first second), Finite.fold_range_repeatN]

theorem contextual_verifier (parent : Option String) (count : Nat) (bound : count ≤ 3)
    (first second : Nat) :
    invokeProtocol (unit.protocolTable F G) runSignature ⟨parent, id⟩ 1
      (inputs (some count) (some first) (some second)) =
        verifierObserved parent 0 count first second := by
  rw [run_body_view]
  change ((PIR.Proc.call (I := observedInterface F G)
    (.mark (qualifyProtocolSite parent "s0")) (fun _ =>
    .call (.action (.query (qualifyProtocolSite parent "s0") "bls12-381.fr" (.cons first .nil)))
      (fun (before : F) =>
    .call (.mark (qualifyProtocolSite parent "")) (fun _ =>
    .call (.mark (qualifyProtocolSite parent "")) (fun _ =>
    .call (.mark (qualifyProtocolSite parent "s6")) (fun _ =>
      (denoteRepeat repeatSpec (mappedContext parent false) 1 (some count)
        (verifierState before) (.cons (some first) (.cons (some second) .nil))
        (callback (F := F) (G := G) parent false 1)).bind _)))))).bind _ :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs)) = _
  simp only [PIR.Proc.bind]
  change (PIR.Proc.call (I := observedInterface F G)
    (.mark (qualifyProtocolSite parent "s0")) _ :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs)) =
      PIR.Proc.call (I := observedInterface F G) (.mark (qualifyProtocolSite parent "s0")) _
  congr 1
  funext ignored
  change (PIR.Proc.call (I := observedInterface F G)
    (.action (.query (qualifyProtocolSite parent "s0") "bls12-381.fr" (.cons first .nil))) _ :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs)) =
      PIR.Proc.call (I := observedInterface F G)
        (.action (.query (qualifyProtocolSite parent "s0") "bls12-381.fr" (.cons first .nil))) _
  congr 1
  funext (before : F)
  erw [verifier_repeat parent false count bound first second before]
  erw [PIR.Proc.bind_assoc, PIR.Proc.bind_assoc]
  cases parent <;> rfl

theorem contextual_receiver (parent : Option String) (count : Nat) (bound : count ≤ 3)
    (first second : Option Nat) :
    invokeProtocol (unit.protocolTable F G) runSignature ⟨parent, id⟩ 0
      (inputs (some count) first second) = receiverObserved parent 1 count := by
  rw [run_body_view]
  change ((PIR.Proc.call (I := observedInterface F G)
    (.mark (qualifyProtocolSite parent "s0")) (fun _ =>
    .call (.mark (qualifyProtocolSite parent "")) (fun _ =>
    .call (.mark (qualifyProtocolSite parent "")) (fun _ =>
    .call (.mark (qualifyProtocolSite parent "s6")) (fun _ =>
      (denoteRepeat repeatSpec (mappedContext parent false) 0 (some count)
        (receiverState ((0 : Nat) : F)) (.cons none (.cons none .nil))
        (callback (F := F) (G := G) parent false 0)).bind _))))).bind _ :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs)) = _
  simp only [PIR.Proc.bind]
  erw [receiver_repeat parent false count bound]
  erw [PIR.Proc.bind_assoc, PIR.Proc.bind_assoc]
  cases parent <;> rfl

theorem permuted_verifier (parent : Option String) (count : Nat) (bound : count ≤ 3)
    (first second : Nat) :
    invokeProtocol (unit.protocolTable F G) runSignature ⟨parent, roleSubstitution [2, 0]⟩ 0
      (inputs (some count) (some first) (some second)) =
        verifierObserved parent 2 count first second := by
  rw [run_body_view]
  change ((PIR.Proc.call (I := observedInterface F G)
    (.mark (qualifyProtocolSite parent "s0")) (fun _ =>
    .call (.action (.query (qualifyProtocolSite parent "s0") "bls12-381.fr" (.cons first .nil)))
      (fun (before : F) =>
    .call (.mark (qualifyProtocolSite parent "")) (fun _ =>
    .call (.mark (qualifyProtocolSite parent "")) (fun _ =>
    .call (.mark (qualifyProtocolSite parent "s6")) (fun _ =>
      (denoteRepeat repeatSpec (mappedContext parent true) 0 (some count)
        (verifierState before) (.cons (some first) (.cons (some second) .nil))
        (callback (F := F) (G := G) parent true 0)).bind _)))))).bind _ :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs)) = _
  simp only [PIR.Proc.bind]
  change (PIR.Proc.call (I := observedInterface F G)
    (.mark (qualifyProtocolSite parent "s0")) _ :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs)) =
      PIR.Proc.call (I := observedInterface F G) (.mark (qualifyProtocolSite parent "s0")) _
  congr 1
  funext ignored
  change (PIR.Proc.call (I := observedInterface F G)
    (.action (.query (qualifyProtocolSite parent "s0") "bls12-381.fr" (.cons first .nil))) _ :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs)) =
      PIR.Proc.call (I := observedInterface F G)
        (.action (.query (qualifyProtocolSite parent "s0") "bls12-381.fr" (.cons first .nil))) _
  congr 1
  funext (before : F)
  erw [verifier_repeat parent true count bound first second before]
  erw [PIR.Proc.bind_assoc, PIR.Proc.bind_assoc]
  cases parent <;> rfl

theorem permuted_receiver (parent : Option String) (count : Nat) (bound : count ≤ 3)
    (first second : Option Nat) :
    invokeProtocol (unit.protocolTable F G) runSignature ⟨parent, roleSubstitution [2, 0]⟩ 2
      (inputs (some count) first second) = receiverObserved parent 0 count := by
  rw [run_body_view]
  change ((PIR.Proc.call (I := observedInterface F G)
    (.mark (qualifyProtocolSite parent "s0")) (fun _ =>
    .call (.mark (qualifyProtocolSite parent "")) (fun _ =>
    .call (.mark (qualifyProtocolSite parent "")) (fun _ =>
    .call (.mark (qualifyProtocolSite parent "s6")) (fun _ =>
      (denoteRepeat repeatSpec (mappedContext parent true) 2 (some count)
        (receiverState ((0 : Nat) : F)) (.cons none (.cons none .nil))
        (callback (F := F) (G := G) parent true 2)).bind _))))).bind _ :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs)) = _
  simp only [PIR.Proc.bind]
  erw [receiver_repeat parent true count bound]
  erw [PIR.Proc.bind_assoc, PIR.Proc.bind_assoc]
  cases parent <;> rfl

theorem observed_verifier (count : Nat) (bound : count ≤ 3) (first second : Nat) :
    program.observed F G 1 (inputs (some count) (some first) (some second)) =
      verifierObserved none 0 count first second := contextual_verifier none count bound first second

theorem observed_receiver (count : Nat) (bound : count ≤ 3) (first second : Option Nat) :
    program.observed F G 0 (inputs (some count) first second) =
      receiverObserved none 1 count := contextual_receiver none count bound first second

theorem verifier_participant (count : Nat) (bound : count ≤ 3) (first second : Nat) :
    program.participant F G 1 (inputs (some count) (some first) (some second)) =
      (verifierObserved (F := F) (G := G) none 0 count first second).interpret forgetSites :=
  congrArg (fun p => p.interpret forgetSites) (observed_verifier (F := F) (G := G) count bound first second)

theorem receiver_participant (count : Nat) (bound : count ≤ 3) (first second : Option Nat) :
    program.participant F G 0 (inputs (some count) first second) =
      (receiverObserved (F := F) (G := G) none 1 count).interpret forgetSites :=
  congrArg (fun p => p.interpret forgetSites) (observed_receiver (F := F) (G := G) count bound first second)

def zeroVerifierObserved (first : Nat) :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs) :=
  .call (.mark "s0") <| fun _ =>
  .call (.action (.query "s0" "bls12-381.fr" (.cons first .nil))) <| fun (before : F) =>
  .call (.mark "") <| fun _ =>
  .call (.mark "") <| fun _ =>
  .call (.mark "s6") <| fun _ =>
  .call (.mark "s16") <| fun _ =>
  .call (.action (.query "s16" "bls12-381.fr" (.cons first .nil))) <| fun (after : F) =>
  .call (.mark "") <| fun _ =>
  .done (.cons none (.cons (some (before + after)) .nil))

/-- Zero skips Draw and its second handle, while the original prelude/suffix still run. -/
theorem zero_verifier (first : Nat) (second : Option Nat) :
    program.observed F G 1 (inputs (some 0) (some first) second) =
      zeroVerifierObserved first := by
  change invokeProtocol (unit.protocolTable F G) runSignature {} 1
    (inputs (some 0) (some first) second) = _
  rw [run_body_view]
  rfl

/-- The prelude's optional first service is demanded before count admission.
If present, its query precedes the actual repeat header and count failure. -/
def verifierFailure (first : Option Nat) (reason : PIR.Stop) :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs) :=
  .call (.mark "s0") <| fun _ =>
  match first with
  | none => .halt .incomplete
  | some first =>
    .call (.action (.query "s0" "bls12-381.fr" (.cons first .nil))) <| fun (_ : F) =>
    .call (.mark "") <| fun _ =>
    .call (.mark "") <| fun _ =>
    .call (.mark "s6") <| fun _ =>
    .halt reason

def receiverFailure (reason : PIR.Stop) :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs) :=
  .call (.mark "s0") <| fun _ =>
  .call (.mark "") <| fun _ =>
  .call (.mark "") <| fun _ =>
  .call (.mark "s6") <| fun _ =>
  .halt reason

theorem missing_count_receiver (first second : Option Nat) :
    program.observed F G 0 (inputs none first second) = receiverFailure .incomplete := by
  change invokeProtocol (unit.protocolTable F G) runSignature {} 0 (inputs none first second) = _
  rw [run_body_view]
  rfl

theorem missing_count_verifier (first second : Option Nat) :
    program.observed F G 1 (inputs none first second) = verifierFailure first .incomplete := by
  change invokeProtocol (unit.protocolTable F G) runSignature {} 1 (inputs none first second) = _
  rw [run_body_view]
  cases first <;> rfl

theorem excess_count_receiver (count : Nat) (large : 3 < count) (first second : Option Nat) :
    program.observed F G 0 (inputs (some count) first second) = receiverFailure .refused := by
  change invokeProtocol (unit.protocolTable F G) runSignature {} 0
    (inputs (some count) first second) = _
  rw [run_body_view]
  change ((PIR.Proc.call (I := observedInterface F G) (.mark "s0") (fun _ =>
    .call (.mark "") (fun _ =>
    .call (.mark "") (fun _ =>
    .call (.mark "s6") (fun _ =>
      (denoteRepeat repeatSpec {} 0 (some count)
        (receiverState ((0 : Nat) : F)) (.cons none (.cons none .nil))
        (callback (F := F) (G := G) none false 0)).bind _))))).bind _ :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs)) = _
  simp only [PIR.Proc.bind]
  rw [repeat_above_maximum repeatSpec {} 0 _ _ _ count rfl large]
  rfl

theorem excess_count_verifier (count : Nat) (large : 3 < count) (first second : Option Nat) :
    program.observed F G 1 (inputs (some count) first second) = verifierFailure first .refused := by
  change invokeProtocol (unit.protocolTable F G) runSignature {} 1
    (inputs (some count) first second) = _
  rw [run_body_view]
  cases first with
  | none => rfl
  | some first =>
    change ((PIR.Proc.call (I := observedInterface F G) (.mark "s0") (fun _ =>
      .call (.action (.query "s0" "bls12-381.fr" (.cons first .nil))) (fun (before : F) =>
      .call (.mark "") (fun _ =>
      .call (.mark "") (fun _ =>
      .call (.mark "s6") (fun _ =>
        (denoteRepeat repeatSpec {} 1 (some count) (verifierState before)
          (.cons (some first) (.cons second .nil))
          (callback (F := F) (G := G) none false 1)).bind _)))))).bind _ :
      PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs)) = _
    simp only [PIR.Proc.bind]
    change (PIR.Proc.call (I := observedInterface F G) (.mark "s0") _ :
      PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs)) =
        PIR.Proc.call (I := observedInterface F G) (.mark "s0") _
    congr 1
    funext ignored
    change (PIR.Proc.call (I := observedInterface F G)
      (.action (.query "s0" "bls12-381.fr" (.cons first .nil))) _ :
      PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs)) =
        PIR.Proc.call (I := observedInterface F G)
          (.action (.query "s0" "bls12-381.fr" (.cons first .nil))) _
    congr 1
    funext (before : F)
    erw [repeat_above_maximum repeatSpec {} 1 _ _ _ count rfl large]
    rfl

end ZkcExamples.Structured.RepeatServiceLaws
