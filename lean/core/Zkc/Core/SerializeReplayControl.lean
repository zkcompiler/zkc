module

public import Zkc.Core.SerializeReplay

public section

/-! The replay relation over the control operations of a protocol.

The operations that run nested regions (`repeat`, `choose`), an application and the
sequencing of an operation with the rest of its region, for the relation `PartsReplay`
between a grouped process and its two parts under their handlers. The relation is closed
under sequencing and iteration, so each statement is the one of the restriction law
(`Zkc.Core.EndpointsMeaning`) with the relation `Together` replaced, and its proof is the
same: a grouped process that returns has agreed on the count or tag, so each part that has a
participant holds the same count or tag and runs the same iterations or the same arm, and a
part without a participant does nothing.

- `agreed_replays`, `agreed_replays_keyed`: a count or tag shared by the participants.
- `RegionsReplay`: region functions of a union and of its two parts, related one by one.
- `repeat_replays`, `choose_replays`: the two operations, from the relation for their
  regions and from the fact that a region does nothing for a part without a participant.
- `apply_replays`: an application, from the relation for the callee at the preimages of the
  two parts.
- `letOp_replays`: one operation followed by the rest of its region.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Zkc.Core

open Zkc.Source

section AgreedReplays

variable {model : Model} {Writer Reader : Type} {channel : Channel model Writer Reader}
  {proverHandler : PIR.StatefulInterpretation (Effects model) (Effects model) Writer}
  {verifierHandler : PIR.StatefulInterpretation (Effects model) (Effects model) Reader} {X : Type} {same : X → X → Bool}
  {first second : Side} {grouped firstType secondType : Type} {left : grouped → firstType}
  {right : grouped → secondType}

/-- A count or tag shared by the participants. A grouped process that returns has agreed
on it, so every part with a participant holds it and continues with it; a part without a
participant does what the operation does for a side outside it. -/
theorem agreed_replays (decides : ∀ left right, same left right = true ↔ left = right)
    {onWhole : X → PIR.Process (Effects model) grouped}
    {onFirst : X → PIR.Process (Effects model) firstType}
    {onSecond : X → PIR.Process (Effects model) secondType} (participants : List Nat)
    (copies : Values (fun role => Held X (first.union second role)) participants)
    (firstCopies : Values (fun role => Held X (first role)) participants)
    (secondCopies : Values (fun role => Held X (second role)) participants)
    (sameFirst : firstCopies =
      copies.map (fun {role} value => Held.left (first role) (second role) value))
    (sameSecond : secondCopies =
      copies.map (fun {role} value => Held.right (first role) (second role) value))
    {noneWhole : participants.any (first.union second) = false → grouped}
    {noneFirst : participants.any first = false → firstType}
    {noneSecond : participants.any second = false → secondType}
    (none : ∀ whole inFirst inSecond,
      noneFirst inFirst = left (noneWhole whole) ∧ noneSecond inSecond = right (noneWhole whole))
    (both : participants.any first = true → participants.any second = true → ∀ value,
      PartsReplay channel proverHandler verifierHandler left right (onWhole value) (onFirst value) (onSecond value))
    (onlyFirst : participants.any first = true → ∀ (outside : participants.any second = false)
      (value : X), PartsReplay channel proverHandler verifierHandler left right (onWhole value) (onFirst value)
        (.done (noneSecond outside)))
    (onlySecond : ∀ (outside : participants.any first = false), participants.any second = true →
      ∀ value, PartsReplay channel proverHandler verifierHandler left right (onWhole value) (.done (noneFirst outside))
        (onSecond value)) :
    PartsReplay channel proverHandler verifierHandler left right
      (agreed same (first.union second) onWhole (.halt .incomplete) participants copies
        fun outside => .done (noneWhole outside))
      (agreed same first onFirst (.halt .incomplete) participants firstCopies
        fun outside => .done (noneFirst outside))
      (agreed same second onSecond (.halt .incomplete) participants secondCopies
        fun outside => .done (noneSecond outside)) := by
  subst sameFirst sameSecond
  have split := any_union (first := first) (second := second) participants
  rcases Bool.eq_false_or_eq_true (participants.any (first.union second)) with inWhole | outWhole
  · rcases agreed_cases (onValue := onWhole) (onDisagree := .halt .incomplete) decides participants
        copies (fun outside => .done (noneWhole outside)) inWhole with
      ⟨value, agrees, equal⟩ | differs
    · rw [agrees]
      have reflexive : ∀ value, same value value = true := fun value => (decides value value).mpr rfl
      have firstAgrees : participants.any first = true →
          agreed same first onFirst (.halt .incomplete) participants
              (copies.map (fun {role} value => Held.left (first role) (second role) value))
              (fun outside => .done (noneFirst outside)) = onFirst value := fun inFirst =>
        agreed_equal same _ _ _ reflexive value participants _ _
          (fun {role} position member =>
            (congrArg (Held.value (first role) member)
              (Values.map_get (fun {role} value => Held.left (first role) (second role) value) copies
                position)).trans
              ((Held.value_left (first role) (second role) member (union_first member) _).trans
                (equal position (union_first member))))
          inFirst
      have secondAgrees : participants.any second = true →
          agreed same second onSecond (.halt .incomplete) participants
              (copies.map (fun {role} value => Held.right (first role) (second role) value))
              (fun outside => .done (noneSecond outside)) = onSecond value := fun inSecond =>
        agreed_equal same _ _ _ reflexive value participants _ _
          (fun {role} position member =>
            (congrArg (Held.value (second role) member)
              (Values.map_get (fun {role} value => Held.right (first role) (second role) value)
                copies position)).trans
              ((Held.value_right (first role) (second role) member (union_second member) _).trans
                (equal position (union_second member))))
          inSecond
      rcases Bool.eq_false_or_eq_true (participants.any first) with inFirst | outFirst
      · rcases Bool.eq_false_or_eq_true (participants.any second) with inSecond | outSecond
        · rw [firstAgrees inFirst, secondAgrees inSecond]
          exact both inFirst inSecond value
        · rw [firstAgrees inFirst,
            agreed_none same second onSecond (.halt .incomplete) participants _ _
              (absent_of_any outSecond)]
          exact onlyFirst inFirst _ value
      · rcases Bool.eq_false_or_eq_true (participants.any second) with inSecond | outSecond
        · rw [secondAgrees inSecond,
            agreed_none same first onFirst (.halt .incomplete) participants _ _
              (absent_of_any outFirst)]
          exact onlySecond _ inSecond value
        · rw [inWhole, outFirst, outSecond] at split
          cases split
    · rw [differs]
      exact PartsReplay.halt
  · have outFirst : participants.any first = false := by
      rcases Bool.eq_false_or_eq_true (participants.any first) with inFirst | outFirst
      · rw [outWhole, inFirst] at split
        cases split
      · exact outFirst
    have outSecond : participants.any second = false := by
      rcases Bool.eq_false_or_eq_true (participants.any second) with inSecond | outSecond
      · rw [outWhole, outFirst, inSecond] at split
        cases split
      · exact outSecond
    rw [agreed_none same (first.union second) onWhole (.halt .incomplete) participants _ _
        (absent_of_any outWhole),
      agreed_none same first onFirst (.halt .incomplete) participants _ _ (absent_of_any outFirst),
      agreed_none same second onSecond (.halt .incomplete) participants _ _
        (absent_of_any outSecond)]
    exact PartsReplay.done (none outWhole outFirst outSecond).1 (none outWhole outFirst outSecond).2


/-- A tag whose copies agree when their keys are equal, with continuations that read the
key only: as `agreed_replays`, on the key that the participants agree on. -/
theorem agreed_replays_keyed {K : Type} (key : X → K) {sameKey : K → K → Bool}
    (decides : ∀ left right, sameKey left right = true ↔ left = right)
    {onWhole : K → PIR.Process (Effects model) grouped}
    {onFirst : K → PIR.Process (Effects model) firstType}
    {onSecond : K → PIR.Process (Effects model) secondType} (participants : List Nat)
    (copies : Values (fun role => Held X (first.union second role)) participants)
    (firstCopies : Values (fun role => Held X (first role)) participants)
    (secondCopies : Values (fun role => Held X (second role)) participants)
    (sameFirst : firstCopies =
      copies.map (fun {role} value => Held.left (first role) (second role) value))
    (sameSecond : secondCopies =
      copies.map (fun {role} value => Held.right (first role) (second role) value))
    {noneWhole : participants.any (first.union second) = false → grouped}
    {noneFirst : participants.any first = false → firstType}
    {noneSecond : participants.any second = false → secondType}
    (none : ∀ whole inFirst inSecond,
      noneFirst inFirst = left (noneWhole whole) ∧ noneSecond inSecond = right (noneWhole whole))
    (both : participants.any first = true → participants.any second = true → ∀ value,
      PartsReplay channel proverHandler verifierHandler left right (onWhole value) (onFirst value) (onSecond value))
    (onlyFirst : participants.any first = true → ∀ (outside : participants.any second = false)
      (value : K), PartsReplay channel proverHandler verifierHandler left right (onWhole value) (onFirst value)
        (.done (noneSecond outside)))
    (onlySecond : ∀ (outside : participants.any first = false), participants.any second = true →
      ∀ value, PartsReplay channel proverHandler verifierHandler left right (onWhole value) (.done (noneFirst outside))
        (onSecond value)) :
    PartsReplay channel proverHandler verifierHandler left right
      (agreed (fun left right => sameKey (key left) (key right)) (first.union second)
        (fun copy => onWhole (key copy)) (.halt .incomplete) participants copies
        fun outside => .done (noneWhole outside))
      (agreed (fun left right => sameKey (key left) (key right)) first
        (fun copy => onFirst (key copy)) (.halt .incomplete) participants firstCopies
        fun outside => .done (noneFirst outside))
      (agreed (fun left right => sameKey (key left) (key right)) second
        (fun copy => onSecond (key copy)) (.halt .incomplete) participants secondCopies
        fun outside => .done (noneSecond outside)) := by
  subst sameFirst sameSecond
  rw [agreed_key (first.union second) _ key sameKey onWhole,
    agreed_key first _ key sameKey onFirst, agreed_key second _ key sameKey onSecond]
  exact agreed_replays decides participants _ _ _ (keys_left key participants copies)
    (keys_right key participants copies) none both onlyFirst onlySecond

end AgreedReplays

section Related

variable {model : Model} {Writer Reader : Type} (channel : Channel model Writer Reader)
  (proverHandler : PIR.StatefulInterpretation (Effects model) (Effects model) Writer)
  (verifierHandler : PIR.StatefulInterpretation (Effects model) (Effects model) Reader)

/-- Region functions of a union and of its two parts, related one by one. -/
@[expose] def RegionsReplay (first second : Side) :
    (signatures : List (List Located × List Located)) →
      Values (RegionFunction (SideValue model (first.union second)) (Effects model)) signatures →
      Values (RegionFunction (SideValue model first) (Effects model)) signatures →
      Values (RegionFunction (SideValue model second) (Effects model)) signatures → Prop
  | [], _, _, _ => True
  | _ :: rest, whole, firstPart, secondPart =>
      (∀ values, PartsReplay channel proverHandler verifierHandler (leftValues model first second)
        (rightValues model first second) ((whole.get .here) values)
        ((firstPart.get .here) (leftValues model first second values))
        ((secondPart.get .here) (rightValues model first second values))) ∧
      RegionsReplay first second rest whole.tail firstPart.tail secondPart.tail

end Related


section Arms

variable {model : Model} {Writer Reader : Type} {channel : Channel model Writer Reader}
  {proverHandler : PIR.StatefulInterpretation (Effects model) (Effects model) Writer}
  {verifierHandler : PIR.StatefulInterpretation (Effects model) (Effects model) Reader} {first second : Side}

/-- The selected arm of a `choose` of which both parts have a participant. -/
theorem selectArm_replays (signature : List Located × List Located) :
    ∀ (count : Nat)
      (whole : Values (RegionFunction (SideValue model (first.union second)) (Effects model))
        (List.replicate count signature))
      (firstPart : Values (RegionFunction (SideValue model first) (Effects model))
        (List.replicate count signature))
      (secondPart : Values (RegionFunction (SideValue model second) (Effects model))
        (List.replicate count signature)),
      RegionsReplay channel proverHandler verifierHandler first second (List.replicate count signature) whole firstPart
        secondPart →
      ∀ (number : Fin count) (captured : Values (SideValue model (first.union second)) signature.1),
        PartsReplay channel proverHandler verifierHandler (leftValues model first second) (rightValues model first second)
          (selectArm signature count whole number captured)
          (selectArm signature count firstPart number (leftValues model first second captured))
          (selectArm signature count secondPart number (rightValues model first second captured))
  | 0, _, _, _, _, number, _ => number.elim0
  | _ + 1, _, _, _, related, ⟨0, _⟩, captured => related.1 captured
  | count + 1, whole, firstPart, secondPart, related, ⟨number + 1, below⟩, captured =>
      selectArm_replays signature count whole.tail firstPart.tail secondPart.tail related.2
        ⟨number, Nat.lt_of_succ_lt_succ below⟩ captured

/-- The selected arm of a `choose` of which the second part has no participant. -/
theorem selectArm_replaysFirst (signature : List Located × List Located)
    (unique : ∀ one other : Values (SideValue model second) signature.2, one = other) :
    ∀ (count : Nat)
      (whole : Values (RegionFunction (SideValue model (first.union second)) (Effects model))
        (List.replicate count signature))
      (firstPart : Values (RegionFunction (SideValue model first) (Effects model))
        (List.replicate count signature))
      (secondPart : Values (RegionFunction (SideValue model second) (Effects model))
        (List.replicate count signature)),
      RegionsReplay channel proverHandler verifierHandler first second (List.replicate count signature) whole firstPart
        secondPart →
      RegionsIdle second (List.replicate count signature) secondPart →
      ∀ (number : Fin count) (captured : Values (SideValue model (first.union second)) signature.1)
        (idle : Values (SideValue model second) signature.2),
        PartsReplay channel proverHandler verifierHandler (leftValues model first second) (rightValues model first second)
          (selectArm signature count whole number captured)
          (selectArm signature count firstPart number (leftValues model first second captured))
          (.done idle)
  | 0, _, _, _, _, _, number, _, _ => number.elim0
  | _ + 1, _, _, _, related, idles, ⟨0, _⟩, captured, idle => by
      obtain ⟨result, returns⟩ := idles.1 (rightValues model first second captured)
      exact PartsReplay.congr rfl
        ((congrArg PIR.Process.done (unique idle result)).trans returns.symm) (related.1 captured)
  | count + 1, whole, firstPart, secondPart, related, idles, ⟨number + 1, below⟩, captured, idle =>
      selectArm_replaysFirst signature unique count whole.tail firstPart.tail secondPart.tail related.2
        idles.2 ⟨number, Nat.lt_of_succ_lt_succ below⟩ captured idle

/-- The selected arm of a `choose` of which the first part has no participant. -/
theorem selectArm_replaysSecond (signature : List Located × List Located)
    (unique : ∀ one other : Values (SideValue model first) signature.2, one = other) :
    ∀ (count : Nat)
      (whole : Values (RegionFunction (SideValue model (first.union second)) (Effects model))
        (List.replicate count signature))
      (firstPart : Values (RegionFunction (SideValue model first) (Effects model))
        (List.replicate count signature))
      (secondPart : Values (RegionFunction (SideValue model second) (Effects model))
        (List.replicate count signature)),
      RegionsReplay channel proverHandler verifierHandler first second (List.replicate count signature) whole firstPart
        secondPart →
      RegionsIdle first (List.replicate count signature) firstPart →
      ∀ (number : Fin count) (captured : Values (SideValue model (first.union second)) signature.1)
        (idle : Values (SideValue model first) signature.2),
        PartsReplay channel proverHandler verifierHandler (leftValues model first second) (rightValues model first second)
          (selectArm signature count whole number captured) (.done idle)
          (selectArm signature count secondPart number (rightValues model first second captured))
  | 0, _, _, _, _, _, number, _, _ => number.elim0
  | _ + 1, _, _, _, related, idles, ⟨0, _⟩, captured, idle => by
      obtain ⟨result, returns⟩ := idles.1 (leftValues model first second captured)
      exact PartsReplay.congr
        ((congrArg PIR.Process.done (unique idle result)).trans returns.symm) rfl (related.1 captured)
  | count + 1, whole, firstPart, secondPart, related, idles, ⟨number + 1, below⟩, captured, idle =>
      selectArm_replaysSecond signature unique count whole.tail firstPart.tail secondPart.tail related.2
        idles.2 ⟨number, Nat.lt_of_succ_lt_succ below⟩ captured idle


/-- The region of an alternative of a `choose` of which both parts have a participant. -/
theorem alternativeProcess_replays {participants : List Nat} {captures outputs : List Located} :
    ∀ (alternatives : List Ty)
      (whole : Values (RegionFunction (SideValue model (first.union second)) (Effects model))
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs)))
      (firstPart : Values (RegionFunction (SideValue model first) (Effects model))
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs)))
      (secondPart : Values (RegionFunction (SideValue model second) (Effects model))
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs))),
      RegionsReplay channel proverHandler verifierHandler first second _ whole firstPart secondPart →
      ∀ (number : Nat)
        (copies : Values
          (fun role => Held (Ty.Variant model.Carrier alternatives) (first.union second role))
          participants)
        (captured : Values (SideValue model (first.union second)) captures),
        PartsReplay channel proverHandler verifierHandler (leftValues model first second) (rightValues model first second)
          (alternativeProcess model (first.union second) participants captures outputs alternatives
            whole number copies captured)
          (alternativeProcess model first participants captures outputs alternatives firstPart
            number (copies.map fun {role} copy => Held.left (first role) (second role) copy)
            (leftValues model first second captured))
          (alternativeProcess model second participants captures outputs alternatives secondPart
            number (copies.map fun {role} copy => Held.right (first role) (second role) copy)
            (rightValues model first second captured))
  | [], _, _, _, _, _, _, _ => PartsReplay.halt
  | payload :: rest, whole, firstPart, secondPart, related, 0, copies, captured => by
      cases found : firstPayloads model (first.union second) payload rest participants copies with
      | none =>
          rw [alternativeProcess_first_other found]
          exact PartsReplay.halt
      | some payloads =>
          rw [alternativeProcess_first found,
            alternativeProcess_first (firstPayloads_left payload rest participants copies _ found),
            alternativeProcess_first (firstPayloads_right payload rest participants copies _ found)]
          exact PartsReplay.congr
            (congrArg (firstPart.get .here) (payloads_left payload payloads captured).symm)
            (congrArg (secondPart.get .here) (payloads_right payload payloads captured).symm)
            (related.1 _)
  | payload :: rest, whole, firstPart, secondPart, related, number + 1, copies, captured => by
      cases found : laterCopies model (first.union second) payload rest participants copies with
      | none =>
          rw [alternativeProcess_later_other number found]
          exact PartsReplay.halt
      | some later =>
          rw [alternativeProcess_later number found,
            alternativeProcess_later number
              (laterCopies_left payload rest participants copies _ found),
            alternativeProcess_later number
              (laterCopies_right payload rest participants copies _ found)]
          exact alternativeProcess_replays rest whole.tail firstPart.tail secondPart.tail
            related.2 number later captured

/-- The region of an alternative of a `choose` of which the second part has no
participant. -/
theorem alternativeProcess_replaysFirst {participants : List Nat} {captures outputs : List Located}
    (unique : ∀ one other : Values (SideValue model second) outputs, one = other) :
    ∀ (alternatives : List Ty)
      (whole : Values (RegionFunction (SideValue model (first.union second)) (Effects model))
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs)))
      (firstPart : Values (RegionFunction (SideValue model first) (Effects model))
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs)))
      (secondPart : Values (RegionFunction (SideValue model second) (Effects model))
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs))),
      RegionsReplay channel proverHandler verifierHandler first second _ whole firstPart secondPart →
      RegionsIdle second _ secondPart →
      ∀ (number : Nat)
        (copies : Values
          (fun role => Held (Ty.Variant model.Carrier alternatives) (first.union second role))
          participants)
        (captured : Values (SideValue model (first.union second)) captures)
        (idle : Values (SideValue model second) outputs),
        PartsReplay channel proverHandler verifierHandler (leftValues model first second) (rightValues model first second)
          (alternativeProcess model (first.union second) participants captures outputs alternatives
            whole number copies captured)
          (alternativeProcess model first participants captures outputs alternatives firstPart
            number (copies.map fun {role} copy => Held.left (first role) (second role) copy)
            (leftValues model first second captured))
          (.done idle)
  | [], _, _, _, _, _, _, _, _, _ => PartsReplay.halt
  | payload :: rest, whole, firstPart, secondPart, related, idles, 0, copies, captured, idle => by
      cases found : firstPayloads model (first.union second) payload rest participants copies with
      | none =>
          rw [alternativeProcess_first_other found]
          exact PartsReplay.halt
      | some payloads =>
          rw [alternativeProcess_first found,
            alternativeProcess_first (firstPayloads_left payload rest participants copies _ found)]
          obtain ⟨result, returns⟩ := idles.1 (rightValues model first second
            ((remapValues (F := SideValue model (first.union second)) (fun role => ⟨payload, role⟩)
              participants payloads).append captured))
          exact PartsReplay.congr
            (congrArg (firstPart.get .here) (payloads_left payload payloads captured).symm)
            ((congrArg PIR.Process.done (unique idle result)).trans returns.symm) (related.1 _)
  | payload :: rest, whole, firstPart, secondPart, related, idles, number + 1, copies, captured,
      idle => by
      cases found : laterCopies model (first.union second) payload rest participants copies with
      | none =>
          rw [alternativeProcess_later_other number found]
          exact PartsReplay.halt
      | some later =>
          rw [alternativeProcess_later number found,
            alternativeProcess_later number
              (laterCopies_left payload rest participants copies _ found)]
          exact alternativeProcess_replaysFirst unique rest whole.tail firstPart.tail secondPart.tail
            related.2 idles.2 number later captured idle

/-- The region of an alternative of a `choose` of which the first part has no
participant. -/
theorem alternativeProcess_replaysSecond {participants : List Nat} {captures outputs : List Located}
    (unique : ∀ one other : Values (SideValue model first) outputs, one = other) :
    ∀ (alternatives : List Ty)
      (whole : Values (RegionFunction (SideValue model (first.union second)) (Effects model))
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs)))
      (firstPart : Values (RegionFunction (SideValue model first) (Effects model))
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs)))
      (secondPart : Values (RegionFunction (SideValue model second) (Effects model))
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs))),
      RegionsReplay channel proverHandler verifierHandler first second _ whole firstPart secondPart →
      RegionsIdle first _ firstPart →
      ∀ (number : Nat)
        (copies : Values
          (fun role => Held (Ty.Variant model.Carrier alternatives) (first.union second role))
          participants)
        (captured : Values (SideValue model (first.union second)) captures)
        (idle : Values (SideValue model first) outputs),
        PartsReplay channel proverHandler verifierHandler (leftValues model first second) (rightValues model first second)
          (alternativeProcess model (first.union second) participants captures outputs alternatives
            whole number copies captured)
          (.done idle)
          (alternativeProcess model second participants captures outputs alternatives secondPart
            number (copies.map fun {role} copy => Held.right (first role) (second role) copy)
            (rightValues model first second captured))
  | [], _, _, _, _, _, _, _, _, _ => PartsReplay.halt
  | payload :: rest, whole, firstPart, secondPart, related, idles, 0, copies, captured, idle => by
      cases found : firstPayloads model (first.union second) payload rest participants copies with
      | none =>
          rw [alternativeProcess_first_other found]
          exact PartsReplay.halt
      | some payloads =>
          rw [alternativeProcess_first found,
            alternativeProcess_first (firstPayloads_right payload rest participants copies _ found)]
          obtain ⟨result, returns⟩ := idles.1 (leftValues model first second
            ((remapValues (F := SideValue model (first.union second)) (fun role => ⟨payload, role⟩)
              participants payloads).append captured))
          exact PartsReplay.congr
            ((congrArg PIR.Process.done (unique idle result)).trans returns.symm)
            (congrArg (secondPart.get .here) (payloads_right payload payloads captured).symm)
            (related.1 _)
  | payload :: rest, whole, firstPart, secondPart, related, idles, number + 1, copies, captured,
      idle => by
      cases found : laterCopies model (first.union second) payload rest participants copies with
      | none =>
          rw [alternativeProcess_later_other number found]
          exact PartsReplay.halt
      | some later =>
          rw [alternativeProcess_later number found,
            alternativeProcess_later number
              (laterCopies_right payload rest participants copies _ found)]
          exact alternativeProcess_replaysSecond unique rest whole.tail firstPart.tail
            secondPart.tail related.2 idles.2 number later captured idle

end Arms

/-! ## Operations with nested regions, and applications -/

section Nested

variable {model : Model} {Writer Reader : Type} {channel : Channel model Writer Reader}
  {proverHandler : PIR.StatefulInterpretation (Effects model) (Effects model) Writer}
  {verifierHandler : PIR.StatefulInterpretation (Effects model) (Effects model) Reader} {operations : List OperationSignature}
  {functions : List FunctionHeader} {protocols : List ProtocolHeader} {deployed : Bool}
  {functionTable : FunctionTable model functions} {table : ProtocolTable model protocols}
  {label : Nat → Site} {first second : Side}


/-- The loop of a `repeat`: the parts run the same number of iterations and collect their
shares of what the grouped process collects. -/
theorem repeatProcess_replays (count : RepeatCount) (carried collected : List Located)
    {wholeStep : Nat → Values (SideValue model (first.union second)) carried →
      PIR.Process (Effects model)
        (Values (SideValue model (first.union second)) (collected ++ carried))}
    {firstStep : Nat → Values (SideValue model first) carried →
      PIR.Process (Effects model) (Values (SideValue model first) (collected ++ carried))}
    {secondStep : Nat → Values (SideValue model second) carried →
      PIR.Process (Effects model) (Values (SideValue model second) (collected ++ carried))}
    (step : ∀ iteration value,
      PartsReplay channel proverHandler verifierHandler (leftValues model first second) (rightValues model first second)
        (wholeStep iteration value) (firstStep iteration (leftValues model first second value))
        (secondStep iteration (rightValues model first second value)))
    (agreed : Nat) (value : Values (SideValue model (first.union second)) carried) :
    PartsReplay channel proverHandler verifierHandler (leftValues model first second) (rightValues model first second)
      (repeatProcess model (first.union second) count carried collected wholeStep agreed value)
      (repeatProcess model first count carried collected firstStep agreed
        (leftValues model first second value))
      (repeatProcess model second count carried collected secondStep agreed
        (rightValues model first second value)) := by
  have iterated : ∀ number : Nat,
      PartsReplay channel proverHandler verifierHandler
        (fun final : Values (SideValue model (first.union second)) carried ×
            Values (SideValue model (first.union second))
              (collectedSequencesAt (some (iterationsAfter number 0)) collected) =>
          (leftValues model first second final.1, leftValues model first second final.2))
        (fun final : Values (SideValue model (first.union second)) carried ×
            Values (SideValue model (first.union second))
              (collectedSequencesAt (some (iterationsAfter number 0)) collected) =>
          (rightValues model first second final.1, rightValues model first second final.2))
        (repeatIterations model (first.union second) carried collected wholeStep number 0 value
          (sideCollectedNone model (first.union second) collected))
        (repeatIterations model first carried collected firstStep number 0
          (leftValues model first second value) (sideCollectedNone model first collected))
        (repeatIterations model second carried collected secondStep number 0
          (rightValues model first second value) (sideCollectedNone model second collected)) :=
    fun number => by
      rw [sideCollectedNone_left (first := first) (second := second),
        sideCollectedNone_right (first := first) (second := second)]
      exact PartsReplay.iterations
        (fun produced => leftValues model first second produced)
        (fun produced => rightValues model first second produced)
        (fun _ earlier => leftValues model first second earlier)
        (fun _ earlier => rightValues model first second earlier)
        (collected := fun done => Values (SideValue model (first.union second))
          (collectedSequencesAt (some done) collected))
        (firstCollected := fun done => Values (SideValue model first)
          (collectedSequencesAt (some done) collected))
        (secondCollected := fun done => Values (SideValue model second)
          (collectedSequencesAt (some done) collected))
        (carry := fun produced => (produced.split collected).2)
        (carryFirst := fun produced => (produced.split collected).2)
        (carrySecond := fun produced => (produced.split collected).2)
        (push := fun _ produced earlier =>
          sideCollectedPush model (first.union second) collected (produced.split collected).1
            earlier)
        (pushFirst := fun _ produced earlier =>
          sideCollectedPush model first collected (produced.split collected).1 earlier)
        (pushSecond := fun _ produced earlier =>
          sideCollectedPush model second collected (produced.split collected).1 earlier)
        step
        (fun made => congrArg Prod.snd (Values.map_split _ collected made))
        (fun made => congrArg Prod.snd (Values.map_split _ collected made))
        (fun done made earlier =>
          (congrArg
            (fun values => sideCollectedPush model first collected values
              (leftValues model first second earlier))
            (congrArg Prod.fst (Values.map_split _ collected made))).trans
            (sideCollectedPush_left collected (made.split collected).1 earlier))
        (fun done made earlier =>
          (congrArg
            (fun values => sideCollectedPush model second collected values
              (rightValues model first second earlier))
            (congrArg Prod.fst (Values.map_split _ collected made))).trans
            (sideCollectedPush_right collected (made.split collected).1 earlier))
        number 0 value _
  cases count with
  | static number =>
      refine PartsReplay.bind (iterated number) fun final => PartsReplay.done ?_ ?_
      · exact (congrArg (fun sequences => Values.append sequences _)
          (sideCollectedSized_left _ collected final.2)).trans (Values.map_append _ _ _).symm
      · exact (congrArg (fun sequences => Values.append sequences _)
          (sideCollectedSized_right _ collected final.2)).trans (Values.map_append _ _ _).symm
  | runtime maximum =>
      show PartsReplay channel proverHandler verifierHandler _ _
        (if agreed ≤ maximum then PIR.Process.bind _ _ else .halt .undefined)
        (if agreed ≤ maximum then PIR.Process.bind _ _ else .halt .undefined)
        (if agreed ≤ maximum then PIR.Process.bind _ _ else .halt .undefined)
      split
      · refine PartsReplay.bind (iterated agreed) fun final => PartsReplay.done ?_ ?_
        · exact (congrArg (fun sequences => Values.append sequences _)
            (sideCollectedLists_left collected final.2)).trans (Values.map_append _ _ _).symm
        · exact (congrArg (fun sequences => Values.append sequences _)
            (sideCollectedLists_right collected final.2)).trans (Values.map_append _ _ _).symm
      · exact PartsReplay.halt


/-- `repeat`: the parts that have a participant run the iterations that the grouped
process runs; a part without one does nothing. -/
theorem repeat_replays (participants : List Nat) (count : RepeatCount)
    (carried collected captures : List Located)
    (covered : Located.heldBy participants collected = true)
    (held : Located.heldBy participants carried = true)
    (arguments : Values (SideValue model (first.union second))
      (count.operands participants ++ (carried ++ captures)))
    (whole : Values (RegionFunction (SideValue model (first.union second)) (Effects model))
      [(Located.ofRoles .nat participants ++ (carried ++ captures), collected ++ carried)])
    (firstPart : Values (RegionFunction (SideValue model first) (Effects model))
      [(Located.ofRoles .nat participants ++ (carried ++ captures), collected ++ carried)])
    (secondPart : Values (RegionFunction (SideValue model second) (Effects model))
      [(Located.ofRoles .nat participants ++ (carried ++ captures), collected ++ carried)])
    (related : RegionsReplay channel proverHandler verifierHandler first second
      [(Located.ofRoles .nat participants ++ (carried ++ captures), collected ++ carried)] whole
      firstPart secondPart)
    (idleFirst : participants.any first = false →
      RegionsIdle first
        [(Located.ofRoles .nat participants ++ (carried ++ captures), collected ++ carried)]
        firstPart)
    (idleSecond : participants.any second = false →
      RegionsIdle second
        [(Located.ofRoles .nat participants ++ (carried ++ captures), collected ++ carried)]
        secondPart) :
    PartsReplay channel proverHandler verifierHandler (leftValues model first second) (rightValues model first second)
      (labelledOperation model label functionTable table (first.union second)
        (operations := operations) (deployed := deployed)
        (.repeat participants count carried collected captures covered) arguments whole)
      (labelledOperation model label functionTable table first
        (operations := operations) (deployed := deployed)
        (.repeat participants count carried collected captures covered)
        (leftValues model first second arguments) firstPart)
      (labelledOperation model label functionTable table second
        (operations := operations) (deployed := deployed)
        (.repeat participants count carried collected captures covered)
        (rightValues model first second arguments) secondPart) := by
  obtain ⟨counts, state, rfl⟩ : ∃ (counts : Values (SideValue model (first.union second))
      (count.operands participants))
      (state : Values (SideValue model (first.union second)) (carried ++ captures)),
      arguments = counts.append state :=
    ⟨_, _, (Values.append_split _ arguments).symm⟩
  obtain ⟨initial, captured, rfl⟩ : ∃ (initial : Values (SideValue model (first.union second))
      carried) (captured : Values (SideValue model (first.union second)) captures),
      state = initial.append captured :=
    ⟨_, _, (Values.append_split _ state).symm⟩
  simp only [Values.map_append]
  simp only [labelledOperation, repeatOperation, Values.split_append]
  have step : ∀ (iteration : Nat) values,
      PartsReplay channel proverHandler verifierHandler (leftValues model first second) (rightValues model first second)
        ((whole.get .here)
          ((heldCopies model (first.union second) .nat iteration participants).append
            (values.append captured)))
        ((firstPart.get .here)
          ((heldCopies model first .nat iteration participants).append
            ((leftValues model first second values).append
              (leftValues model first second captured))))
        ((secondPart.get .here)
          ((heldCopies model second .nat iteration participants).append
            ((rightValues model first second values).append
              (rightValues model first second captured)))) := fun iteration values =>
    PartsReplay.congr
      (congrArg (firstPart.get .here)
        ((Values.map_append _ _ (values.append captured)).trans
          (congr (congrArg Values.append (heldCopies_left .nat iteration participants))
            (Values.map_append _ values captured))).symm)
      (congrArg (secondPart.get .here)
        ((Values.map_append _ _ (values.append captured)).trans
          (congr (congrArg Values.append (heldCopies_right .nat iteration participants))
            (Values.map_append _ values captured))).symm)
      (related.1 ((heldCopies model (first.union second) .nat iteration participants).append
        (values.append captured)))
  -- The results are held by participants, so a part without one holds none of them.
  have outside : ∀ {side : Side}, participants.any side = false →
      ∀ located ∈ collectedSequencesAt count.size collected ++ carried,
        side located.holder = false := by
    intro side none located member
    rcases List.mem_append.mp member with sequence | value
    · obtain ⟨source, inside, rfl⟩ := List.mem_map.mp sequence
      exact not_held_of_heldBy (located := source) covered none inside
    · exact not_held_of_heldBy held none value
  have together := fun agreed : Nat =>
    repeatProcess_replays (channel := channel) (proverHandler := proverHandler) (verifierHandler := verifierHandler) count carried collected
      (wholeStep := fun iteration values => (whole.get .here)
        ((heldCopies model (first.union second) .nat iteration participants).append
          (values.append captured)))
      (firstStep := fun iteration values => (firstPart.get .here)
        ((heldCopies model first .nat iteration participants).append
          (values.append (leftValues model first second captured))))
      (secondStep := fun iteration values => (secondPart.get .here)
        ((heldCopies model second .nat iteration participants).append
          (values.append (rightValues model first second captured))))
      step agreed initial
  refine agreed_replays nat_beq_decides participants _ _ _
    (repeatCopies_left participants count counts) (repeatCopies_right participants count counts)
    (noneWhole := fun none => (absentSequences model (first.union second) count.size collected
      fun _ member => not_held_of_heldBy covered none member).append initial)
    (fun _ outFirst outSecond =>
      ⟨outside_values_unique (outside outFirst) _ _, outside_values_unique (outside outSecond) _ _⟩)
    (fun _ _ agreed => together agreed)
    (fun _ outSecond agreed => ?_) (fun outFirst _ agreed => ?_)
  · have both := together agreed
    rcases repeatProcess_idle second count carried collected
      (step := fun iteration values => (secondPart.get .here)
        ((heldCopies model second .nat iteration participants).append
          (values.append (rightValues model first second captured))))
      (fun iteration value => (idleSecond outSecond).1 _) agreed
      (rightValues model first second initial) with ⟨result, returns⟩ | ⟨maximum, rfl, beyond⟩
    · exact PartsReplay.congr rfl
        (returns.trans (congrArg PIR.Process.done
          (outside_values_unique (outside outSecond) _ _))).symm
        both
    · rw [repeatProcess_beyond model _ beyond]
      exact PartsReplay.halt
  · have both := together agreed
    rcases repeatProcess_idle first count carried collected
      (step := fun iteration values => (firstPart.get .here)
        ((heldCopies model first .nat iteration participants).append
          (values.append (leftValues model first second captured))))
      (fun iteration value => (idleFirst outFirst).1 _) agreed
      (leftValues model first second initial) with ⟨result, returns⟩ | ⟨maximum, rfl, beyond⟩
    · exact PartsReplay.congr
        (returns.trans (congrArg PIR.Process.done
          (outside_values_unique (outside outFirst) _ _))).symm
        rfl both
    · rw [repeatProcess_beyond model _ beyond]
      exact PartsReplay.halt

/-- `choose`: the parts that have a participant run the arm that the grouped process
runs; a part without one holds none of the outputs. -/
theorem choose_replays (participants : List Nat) (tag : ChoiceTag) (captures outputs : List Located)
    (covered : Located.heldBy participants outputs = true)
    (arguments : Values (SideValue model (first.union second))
      (Located.ofRoles tag.type participants ++ captures))
    (whole : Values (RegionFunction (SideValue model (first.union second)) (Effects model))
      (tag.regions participants captures outputs))
    (firstPart : Values (RegionFunction (SideValue model first) (Effects model))
      (tag.regions participants captures outputs))
    (secondPart : Values (RegionFunction (SideValue model second) (Effects model))
      (tag.regions participants captures outputs))
    (related : RegionsReplay channel proverHandler verifierHandler first second (tag.regions participants captures outputs)
      whole firstPart secondPart)
    (idleFirst : participants.any first = false →
      RegionsIdle first (tag.regions participants captures outputs) firstPart)
    (idleSecond : participants.any second = false →
      RegionsIdle second (tag.regions participants captures outputs) secondPart) :
    PartsReplay channel proverHandler verifierHandler (leftValues model first second) (rightValues model first second)
      (labelledOperation model label functionTable table (first.union second)
        (operations := operations) (deployed := deployed)
        (.choose participants tag captures outputs covered) arguments whole)
      (labelledOperation model label functionTable table first
        (operations := operations) (deployed := deployed)
        (.choose participants tag captures outputs covered)
        (leftValues model first second arguments) firstPart)
      (labelledOperation model label functionTable table second
        (operations := operations) (deployed := deployed)
        (.choose participants tag captures outputs covered)
        (rightValues model first second arguments) secondPart) := by
  obtain ⟨tags, captured, rfl⟩ : ∃ (tags : Values (SideValue model (first.union second))
      (Located.ofRoles tag.type participants))
      (captured : Values (SideValue model (first.union second)) captures),
      arguments = tags.append captured :=
    ⟨_, _, (Values.append_split _ arguments).symm⟩
  simp only [Values.map_append]
  simp only [labelledOperation, Values.split_append]
  -- The copies of the tag that a part holds are its shares of the copies of the union.
  have copiesFirst := unmapValues_map (F := SideValue model (first.union second))
    (fun role => ⟨tag.type, role⟩)
    (fun {located} value => restrictLeft model first second (located := located) value) _ tags
  have copiesSecond := unmapValues_map (F := SideValue model (first.union second))
    (fun role => ⟨tag.type, role⟩)
    (fun {located} value => restrictRight model first second (located := located) value) _ tags
  have none : ∀ (_ : participants.any (first.union second) = false)
      (outFirst : participants.any first = false) (outSecond : participants.any second = false),
      (absentOutputs model first outputs fun _ member =>
          not_held_of_heldBy covered outFirst member) =
        leftValues model first second
          (absentOutputs model (first.union second) outputs fun _ member =>
            not_held_of_heldBy covered (by assumption) member) ∧
      (absentOutputs model second outputs fun _ member =>
          not_held_of_heldBy covered outSecond member) =
        rightValues model first second
          (absentOutputs model (first.union second) outputs fun _ member =>
            not_held_of_heldBy covered (by assumption) member) :=
    fun _ outFirst outSecond =>
      ⟨outside_values_unique (fun _ member => not_held_of_heldBy covered outFirst member) _ _,
        outside_values_unique (fun _ member => not_held_of_heldBy covered outSecond member) _ _⟩
  cases tag with
  | condition =>
    rw [copiesFirst, copiesSecond]
    exact agreed_replays agreeBool_decides participants _ _ _ rfl rfl none
      (fun _ _ value => selectArm_replays (captures, outputs) 2 whole firstPart secondPart
        related (ChoiceTag.select model.Carrier .condition value) captured)
      (fun _ outSecond value => selectArm_replaysFirst (captures, outputs)
        (fun one other => outside_values_unique
          (fun _ member => not_held_of_heldBy covered outSecond member) one other)
        2 whole firstPart secondPart related (idleSecond outSecond)
        (ChoiceTag.select model.Carrier .condition value) captured _)
      (fun outFirst _ value => selectArm_replaysSecond (captures, outputs)
        (fun one other => outside_values_unique
          (fun _ member => not_held_of_heldBy covered outFirst member) one other)
        2 whole firstPart secondPart related (idleFirst outFirst)
        (ChoiceTag.select model.Carrier .condition value) captured _)
  | arm count =>
    rw [copiesFirst, copiesSecond]
    exact agreed_replays (ChoiceTag.same_decides model.Carrier (.arm count)) participants _ _ _
      rfl rfl none
      (fun _ _ value => selectArm_replays (captures, outputs) count whole firstPart secondPart
        related (ChoiceTag.select model.Carrier (.arm count) value) captured)
      (fun _ outSecond value => selectArm_replaysFirst (captures, outputs)
        (fun one other => outside_values_unique
          (fun _ member => not_held_of_heldBy covered outSecond member) one other)
        count whole firstPart secondPart related (idleSecond outSecond)
        (ChoiceTag.select model.Carrier (.arm count) value) captured _)
      (fun outFirst _ value => selectArm_replaysSecond (captures, outputs)
        (fun one other => outside_values_unique
          (fun _ member => not_held_of_heldBy covered outFirst member) one other)
        count whole firstPart secondPart related (idleFirst outFirst)
        (ChoiceTag.select model.Carrier (.arm count) value) captured _)
  | alternative declaration alternatives =>
    -- The participants agree on the number of the alternative; the region of that
    -- alternative takes the payloads that each part holds.
    rw [copiesFirst, copiesSecond]
    exact agreed_replays_keyed (alternativeNumber alternatives) nat_beq_decides participants _ _ _
      rfl rfl none
      (fun _ _ number => alternativeProcess_replays alternatives whole firstPart secondPart
        related number _ captured)
      (fun _ outSecond number => alternativeProcess_replaysFirst
        (fun one other => outside_values_unique
          (fun _ member => not_held_of_heldBy covered outSecond member) one other)
        alternatives whole firstPart secondPart related (idleSecond outSecond) number _ captured _)
      (fun outFirst _ number => alternativeProcess_replaysSecond
        (fun one other => outside_values_unique
          (fun _ member => not_held_of_heldBy covered outFirst member) one other)
        alternatives whole firstPart secondPart related (idleFirst outFirst) number _ captured _)


/-- `apply`: the relation for the callee, at the preimages of the two parts. -/
theorem apply_replays {header : ProtocolHeader} (callee : Var protocols header) (roleMap : RoleMap)
    (site : Nat) (permitted : (deployed && header.specificationOnly) = false)
    (calleeReplays : ∀ arguments : Values
        (SideValue model ((Side.preimage roleMap first).union (Side.preimage roleMap second)))
        header.inputs,
      PartsReplay channel proverHandler verifierHandler
        (leftValues model (Side.preimage roleMap first) (Side.preimage roleMap second))
        (rightValues model (Side.preimage roleMap first) (Side.preimage roleMap second))
        ((table.get callee) (label site).below
          ((Side.preimage roleMap first).union (Side.preimage roleMap second)) arguments)
        ((table.get callee) (label site).below (Side.preimage roleMap first)
          (leftValues model (Side.preimage roleMap first) (Side.preimage roleMap second) arguments))
        ((table.get callee) (label site).below (Side.preimage roleMap second)
          (rightValues model (Side.preimage roleMap first) (Side.preimage roleMap second)
            arguments)))
    (arguments : Values (SideValue model (first.union second))
      (header.inputs.map (Located.rename roleMap)))
    (whole : Values (RegionFunction (SideValue model (first.union second)) (Effects model)) [])
    (firstPart : Values (RegionFunction (SideValue model first) (Effects model)) [])
    (secondPart : Values (RegionFunction (SideValue model second) (Effects model)) []) :
    PartsReplay channel proverHandler verifierHandler (leftValues model first second)
      (rightValues model first second)
      (labelledOperation model label functionTable table (first.union second)
        (operations := operations) (.apply callee roleMap site permitted) arguments whole)
      (labelledOperation model label functionTable table first
        (operations := operations) (.apply callee roleMap site permitted)
        (leftValues model first second arguments) firstPart)
      (labelledOperation model label functionTable table second
        (operations := operations) (.apply callee roleMap site permitted)
        (rightValues model first second arguments) secondPart) := by
  have calleeRelated := calleeReplays
    (unmapValues (F := SideValue model (first.union second)) (Located.rename roleMap) header.inputs
      arguments)
  refine PartsReplay.congr ?_ ?_ (PartsReplay.bind
    (proverNext := fun values => .done
      (remapValues (F := SideValue model first) (Located.rename roleMap) _ values))
    (verifierNext := fun values => .done
      (remapValues (F := SideValue model second) (Located.rename roleMap) _ values))
    calleeRelated fun values =>
    PartsReplay.done
      (remapValues_map (F := SideValue model (first.union second)) (Located.rename roleMap)
        (fun {located} value => restrictLeft model first second (located := located) value) _
        values).symm
      (remapValues_map (F := SideValue model (first.union second)) (Located.rename roleMap)
        (fun {located} value => restrictRight model first second (located := located) value) _
        values).symm)
  · exact congrArg
      (fun values => ((table.get callee) (label site).below (Side.preimage roleMap first)
        values).bind fun values => .done
          (remapValues (F := SideValue model first) (Located.rename roleMap) _ values))
      (unmapValues_map (F := SideValue model (first.union second)) (Located.rename roleMap)
        (fun {located} value => restrictLeft model first second (located := located) value) _
        arguments)
  · exact congrArg
      (fun values => ((table.get callee) (label site).below (Side.preimage roleMap second)
        values).bind fun values => .done
          (remapValues (F := SideValue model second) (Located.rename roleMap) _ values))
      (unmapValues_map (F := SideValue model (first.union second)) (Located.rename roleMap)
        (fun {located} value => restrictRight model first second (located := located) value) _
        arguments)


end Nested

/-! ## Regions, definitions and programs -/

section Regions

variable {model : Model} {Writer Reader : Type} {channel : Channel model Writer Reader}
  {proverHandler : PIR.StatefulInterpretation (Effects model) (Effects model) Writer}
  {verifierHandler : PIR.StatefulInterpretation (Effects model) (Effects model) Reader} {operations : List OperationSignature}
  {functions : List FunctionHeader} {protocols : List ProtocolHeader} {deployed : Bool}
  {functionTable : FunctionTable model functions} {table : ProtocolTable model protocols}
  {label : Nat → Site} {first second : Side}

/-- One operation followed by the rest of its region. -/
theorem letOp_replays {Γ out : List Located}
    (op : ProtocolOp operations functions protocols deployed)
    (arguments : Operands Γ (ProtocolOp.arguments op))
    (bodies : Regions (ProtocolDialect operations functions protocols deployed)
      (ProtocolOp.regions op))
    (rest : Region (ProtocolDialect operations functions protocols deployed)
      (bindAll Γ (ProtocolOp.results op)) out)
    (env : Environment (SideValue model (first.union second)) Γ)
    (envFirst : Environment (SideValue model first) Γ)
    (envSecond : Environment (SideValue model second) Γ)
    (isLeft : Restricts (fun {located} value => restrictLeft model first second (located := located)
      value) env envFirst)
    (isRight : Restricts (fun {located} value => restrictRight model first second
      (located := located) value) env envSecond)
    (operation : PartsReplay channel proverHandler verifierHandler (leftValues model first second) (rightValues model first second)
      (labelledOperation model label functionTable table (first.union second) op
        (Operands.eval env arguments)
        (bodies.denote (labelledMeaning model label functionTable table (first.union second))))
      (labelledOperation model label functionTable table first op
        (leftValues model first second (Operands.eval env arguments))
        (bodies.denote (labelledMeaning model label functionTable table first)))
      (labelledOperation model label functionTable table second op
        (rightValues model first second (Operands.eval env arguments))
        (bodies.denote (labelledMeaning model label functionTable table second))))
    (continues : ∀ values,
      PartsReplay channel proverHandler verifierHandler (leftValues model first second) (rightValues model first second)
        (rest.denote (labelledMeaning model label functionTable table (first.union second))
          (Environment.bindAll env values))
        (rest.denote (labelledMeaning model label functionTable table first)
          (Environment.bindAll envFirst (leftValues model first second values)))
        (rest.denote (labelledMeaning model label functionTable table second)
          (Environment.bindAll envSecond (rightValues model first second values)))) :
    PartsReplay channel proverHandler verifierHandler (leftValues model first second) (rightValues model first second)
      ((Region.letOp (dialect := ProtocolDialect operations functions protocols deployed) op
        arguments bodies rest).denote
        (labelledMeaning model label functionTable table (first.union second)) env)
      ((Region.letOp (dialect := ProtocolDialect operations functions protocols deployed) op
        arguments bodies rest).denote (labelledMeaning model label functionTable table first)
        envFirst)
      ((Region.letOp (dialect := ProtocolDialect operations functions protocols deployed) op
        arguments bodies rest).denote (labelledMeaning model label functionTable table second)
        envSecond) :=
  PartsReplay.bind
    (PartsReplay.congr
      (congrArg
        (fun values => labelledOperation model label functionTable table first op values
          (bodies.denote (labelledMeaning model label functionTable table first)))
        (isLeft.eval arguments))
      (congrArg
        (fun values => labelledOperation model label functionTable table second op values
          (bodies.denote (labelledMeaning model label functionTable table second)))
        (isRight.eval arguments))
      operation)
    continues

end Regions

end Zkc.Core
