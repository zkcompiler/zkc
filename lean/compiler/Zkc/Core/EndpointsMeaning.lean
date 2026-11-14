module

public import Zkc.Core.EndpointsValues
public import Zkc.Core.ThreadPlain

public section

/-! The restriction law: the meaning of a protocol for a side that is the union of two
disjoint sides, and the meanings for the two sides run against each other.

For every operation form the grouped process and the two parts are `Together`: when the
grouped process returns, the parts return together, on the same coins, the restrictions
of the grouped values. The law is proved for the presence steps of the model by cases on
the memberships of the roles involved, then for every operation, for a region, for a
definition and for the protocols of a program.

- Local work, `sample`: the part that has the role does what the grouped process does.
  Local work performs no effect when the functions of the program perform none
  (`QuietTable`), which is a hypothesis of the law: a function that drew would announce a
  coin where no receiver hears it.
- `exchange`: within one part it is no effect; across the parts it is a `send` and a
  `receive`; to or from a role outside both the grouped process does not return alone.
- `draw`: the owner's part announces the coin and the other part's receiver hears it. The
  law is stated for listeners that are those of the region (`regionListens`): at the site of
  every `draw` they say that the owner's part does not hear and that the other part hears
  exactly when it has a receiver, and each part holds at most one receiver, so that it hears
  each coin once. `Zkc.Core.EndpointsListeners` shows that every protocol of a program has
  such listeners for two sides that each hold at most one of its roles.
- `repeat`, `choose`: a grouped process that returns has agreed on the count or tag, so
  each part that has a participant holds the same count or tag and runs the same
  iterations or the same arm. A part without a participant does nothing; the grouped
  process does the same only if the operations inside name participants alone and the
  values that leave are held by participants. These are residual conditions of a
  well-formed definition; here they are the hypothesis `Region.Enclosed`.
- `apply`: the law for the callee, at the preimages of the two sides, for which the
  listeners are those of the callee below the site of the application.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- The relation holds of processes equal to related ones. -/
theorem Together.congr {model : Model} {sampler : Sampler model} {listeners : Listeners}
    {grouped first second : Type}
    {left : grouped → first} {right : grouped → second}
    {whole : PIR.Process (Effects model) grouped}
    {firstPart firstPart' : PIR.Process (Effects model) first}
    {secondPart secondPart' : PIR.Process (Effects model) second}
    (sameFirst : firstPart' = firstPart) (sameSecond : secondPart' = secondPart)
    (together : Together sampler listeners left right whole firstPart secondPart) :
    Together sampler listeners left right whole firstPart' secondPart' := by
  subst sameFirst sameSecond
  exact together

/-! ## Presence steps -/

section Steps

variable {model : Model} {sampler : Sampler model} {listeners : Listeners}

/-- The first part returns or stops as the grouped process does, without an effect, and the
second part does nothing. -/
theorem Together.quietFirst {grouped second : Type} {idle : second} {left : grouped → grouped}
    {right : grouped → second} (sameValue : ∀ value, left value = value)
    (absent : ∀ value, right value = idle) (whole firstPart : PIR.Process (Effects model) grouped)
    (same : firstPart = whole) (quiet : whole.Quiet) :
    Together sampler listeners left right whole firstPart (.done idle) := by
  subst same
  refine ⟨?_⟩
  intro γ α β afterWhole afterFirst afterSecond board heardFirst heardSecond asked result
    firstResult secondResult heardAll continues returns
  cases firstPart with
  | done value =>
      have continued := continues value board heardFirst heardSecond asked heardAll returns
      rw [sameValue, absent] at continued
      exact continued
  | halt reason =>
      have stopped : ReturnsAlone sampler (.halt reason : PIR.Process (Effects model) γ) asked
          result := returns
      cases stopped
  | call effect next => cases quiet

/-- The second part returns or stops as the grouped process does, without an effect, and the
first part does nothing. -/
theorem Together.quietSecond {grouped first : Type} {idle : first} {left : grouped → first}
    {right : grouped → grouped} (absent : ∀ value, left value = idle)
    (sameValue : ∀ value, right value = value)
    (whole secondPart : PIR.Process (Effects model) grouped) (same : secondPart = whole)
    (quiet : whole.Quiet) : Together sampler listeners left right whole (.done idle) secondPart :=
  Together.swap (listeners := listeners.swap)
    (Together.quietFirst sameValue absent whole secondPart same quiet)

/-- `at`: the part that has the role performs the operation, which has no effect. -/
theorem performStep_together {inputs outputs : List Ty}
    (run : Values model.Value inputs → PIR.Process (Effects model) (Values model.Value outputs))
    (quiet : ∀ arguments, (run arguments).Quiet) :
    ∀ (first second : Bool), (first && second) = false →
    ∀ (arguments : Values (fun type => Held (model.Value type) (first || second)) inputs),
      Together sampler listeners
        (Values.map (fun {type} value => Held.left (X := model.Value type) first second value))
        (Values.map (fun {type} value => Held.right (X := model.Value type) first second value))
        (performStep model run (first || second) arguments)
        (performStep model run first
          (arguments.map (fun {type} value => Held.left (X := model.Value type) first second value)))
        (performStep model run second
          (arguments.map (fun {type} value => Held.right (X := model.Value type) first second value)))
  | true, true, both, _ => Bool.noConfusion both
  | true, false, _, arguments =>
      Together.quietFirst (map_left_present false) (fun _ => absent_values_unique _ _)
        (run arguments) _ (congrArg run (map_left_present false arguments)) (quiet arguments)
  | false, true, _, arguments =>
      Together.quietSecond (fun _ => absent_values_unique _ _) map_right_present
        (run arguments) _ (congrArg run (map_right_present arguments)) (quiet arguments)
  | false, false, _, _ => Together.done (absent_values_unique _ _) (absent_values_unique _ _)

/-- `exchange`: no effect within one part, a `send` and a `receive` across the parts. -/
theorem exchangeStep_together (site : Site) (type : Ty) :
    ∀ (senderFirst senderSecond receiverFirst receiverSecond : Bool),
      (senderFirst && senderSecond) = false → (receiverFirst && receiverSecond) = false →
      ∀ (value : Held (model.Value type) (senderFirst || senderSecond)),
        Together sampler listeners (Held.left receiverFirst receiverSecond)
          (Held.right receiverFirst receiverSecond)
          (exchangeStep model site type (senderFirst || senderSecond)
            (receiverFirst || receiverSecond) value)
          (exchangeStep model site type senderFirst receiverFirst
            (Held.left senderFirst senderSecond value))
          (exchangeStep model site type senderSecond receiverSecond
            (Held.right senderFirst senderSecond value))
  | true, true, _, _, both, _, _ => Bool.noConfusion both
  | _, _, true, true, _, both, _ => Bool.noConfusion both
  | true, false, true, false, _, _, _ => Together.done rfl rfl
  | false, true, false, true, _, _, _ => Together.done rfl rfl
  | false, false, false, false, _, _, _ => Together.done rfl rfl
  | true, false, false, true, _, _, value => Together.message (value := value) rfl rfl
  | false, true, true, false, _, _, value =>
      Together.swap (listeners := listeners.swap) (Together.message (value := value) rfl rfl)
  | true, false, false, false, _, _, _ => Together.send
  | false, true, false, false, _, _, _ => Together.send
  | false, false, true, false, _, _, _ => Together.receive
  | false, false, false, true, _, _, _ => Together.receive

/-- `sample`: the owner's part samples. -/
theorem sampleStep_together (site : Site) (law : SamplingRow) :
    ∀ (first second : Bool), (first && second) = false →
    ∀ (inputs : Values (fun type => Held (model.Value type) (first || second)) law.inputs),
      Together sampler listeners (Held.left first second) (Held.right first second)
        (sampleStep model site law (first || second) inputs)
        (sampleStep model site law first
          (inputs.map (fun {type} value => Held.left (X := model.Value type) first second value)))
        (sampleStep model site law second
          (inputs.map (fun {type} value => Held.right (X := model.Value type) first second value)))
  | true, true, both, _ => Bool.noConfusion both
  | true, false, _, _ => Together.sample (fun _ => rfl) (fun _ => rfl)
  | false, true, _, _ =>
      Together.swap (listeners := listeners.swap) (Together.sample (fun _ => rfl) (fun _ => rfl))
  | false, false, _, _ => Together.done rfl rfl

end Steps

/-! ## Operations without nested regions -/

section Leaves

variable {model : Model} {sampler : Sampler model} {listeners : Listeners} {operations : List OperationSignature}
  {functions : List FunctionHeader} {protocols : List ProtocolHeader} {deployed : Bool}
  {functionTable : FunctionTable model functions} {table : ProtocolTable model protocols}
  {label : Nat → Site} {first second : Side}

/-- Local work of one role. The functions of the program perform no effect, so local work
announces no coin. -/
theorem at_together (quiet : QuietTable functionTable) (disjoint : first.Disjoint second)
    (role : Nat)
    (op : LocalOp operations functions deployed)
    (bodies : Regions (LocalDialect operations functions deployed) op.regions)
    (arguments : Values (SideValue model (first.union second)) (Located.atRole role op.arguments))
    (whole : Values (RegionFunction (SideValue model (first.union second)) (Effects model)) [])
    (firstPart : Values (RegionFunction (SideValue model first) (Effects model)) [])
    (secondPart : Values (RegionFunction (SideValue model second) (Effects model)) []) :
    Together sampler listeners (leftValues model first second) (rightValues model first second)
      (labelledOperation model label functionTable table (first.union second) (.at role op bodies)
        arguments whole)
      (labelledOperation model label functionTable table first (.at role op bodies)
        (leftValues model first second arguments) firstPart)
      (labelledOperation model label functionTable table second (.at role op bodies)
        (rightValues model first second arguments) secondPart) := by
  have step := performStep_together (sampler := sampler) (listeners := listeners)
    (fun values => localOperation model functionTable op values
      (bodies.denote (localMeaning model functionTable)))
    (fun values => localOperation_quiet quiet op values _ (localRegions_quiet quiet bodies))
    (first role) (second role) (disjoint role)
    (unmapValues (F := SideValue model (first.union second)) (fun type => ⟨type, role⟩) _ arguments)
  refine Together.congr ?_ ?_ (Together.bind
    (firstNext := fun values => .done
      (remapValues (F := SideValue model first) (fun type => ⟨type, role⟩) _ values))
    (secondNext := fun values => .done
      (remapValues (F := SideValue model second) (fun type => ⟨type, role⟩) _ values))
    step fun values =>
    Together.done
      (remapValues_map (F := SideValue model (first.union second)) (fun type => ⟨type, role⟩)
        (fun {located} value => restrictLeft model first second (located := located) value) _
        values).symm
      (remapValues_map (F := SideValue model (first.union second)) (fun type => ⟨type, role⟩)
        (fun {located} value => restrictRight model first second (located := located) value) _
        values).symm)
  · exact congrArg
      (fun values => (performStep model
        (fun values => localOperation model functionTable op values
          (bodies.denote (localMeaning model functionTable))) (first role) values).bind
        fun values => .done
          (remapValues (F := SideValue model first) (fun type => ⟨type, role⟩) _ values))
      (unmapValues_map (F := SideValue model (first.union second)) (fun type => ⟨type, role⟩)
        (fun {located} value => restrictLeft model first second (located := located) value) _
        arguments)
  · exact congrArg
      (fun values => (performStep model
        (fun values => localOperation model functionTable op values
          (bodies.denote (localMeaning model functionTable))) (second role) values).bind
        fun values => .done
          (remapValues (F := SideValue model second) (fun type => ⟨type, role⟩) _ values))
      (unmapValues_map (F := SideValue model (first.union second)) (fun type => ⟨type, role⟩)
        (fun {located} value => restrictRight model first second (located := located) value) _
        arguments)

/-- A message from one role to another. -/
theorem exchange_together (disjoint : first.Disjoint second) (sender receiver site : Nat)
    (type : Ty) (arguments : Values (SideValue model (first.union second)) [⟨type, sender⟩])
    (whole : Values (RegionFunction (SideValue model (first.union second)) (Effects model)) [])
    (firstPart : Values (RegionFunction (SideValue model first) (Effects model)) [])
    (secondPart : Values (RegionFunction (SideValue model second) (Effects model)) []) :
    Together sampler listeners (leftValues model first second) (rightValues model first second)
      (labelledOperation model label functionTable table (first.union second)
        (operations := operations) (deployed := deployed) (.exchange sender receiver site type)
        arguments whole)
      (labelledOperation model label functionTable table first
        (operations := operations) (deployed := deployed) (.exchange sender receiver site type)
        (leftValues model first second arguments) firstPart)
      (labelledOperation model label functionTable table second
        (operations := operations) (deployed := deployed) (.exchange sender receiver site type)
        (rightValues model first second arguments) secondPart) := by
  have step := exchangeStep_together (sampler := sampler) (listeners := listeners) (label site) type (first sender)
    (second sender) (first receiver) (second receiver) (disjoint sender) (disjoint receiver)
    (arguments.get .here)
  refine Together.congr ?_ ?_ (Together.bind
    (firstNext := fun result => .done
      (Values.cons (Value := SideValue model first) (ty := ⟨type, receiver⟩) result .nil))
    (secondNext := fun result => .done
      (Values.cons (Value := SideValue model second) (ty := ⟨type, receiver⟩) result .nil))
    step fun result => Together.done rfl rfl)
  · exact congrArg
      (fun value => (exchangeStep model (label site) type (first sender) (first receiver)
        value).bind fun result => .done
          (Values.cons (Value := SideValue model first) (ty := ⟨type, receiver⟩) result .nil))
      (Values.map_get (fun {located} value => restrictLeft model first second (located := located)
        value) arguments .here)
  · exact congrArg
      (fun value => (exchangeStep model (label site) type (second sender) (second receiver)
        value).bind fun result => .done
          (Values.cons (Value := SideValue model second) (ty := ⟨type, receiver⟩) result .nil))
      (Values.map_get (fun {located} value => restrictRight model first second (located := located)
        value) arguments .here)

/-- A secret sample of one role. -/
theorem sample_together (disjoint : first.Disjoint second) (owner site : Nat) {inputs : List Ty}
    {output : Ty} (law : Var operations ⟨inputs, [output], .sampling⟩)
    (populated : output.populated = true)
    (arguments : Values (SideValue model (first.union second)) (Located.atRole owner inputs))
    (whole : Values (RegionFunction (SideValue model (first.union second)) (Effects model)) [])
    (firstPart : Values (RegionFunction (SideValue model first) (Effects model)) [])
    (secondPart : Values (RegionFunction (SideValue model second) (Effects model)) []) :
    Together sampler listeners (leftValues model first second) (rightValues model first second)
      (labelledOperation model label functionTable table (first.union second) (deployed := deployed)
        (.sample owner site law populated) arguments whole)
      (labelledOperation model label functionTable table first (deployed := deployed)
        (.sample owner site law populated) (leftValues model first second arguments) firstPart)
      (labelledOperation model label functionTable table second (deployed := deployed)
        (.sample owner site law populated) (rightValues model first second arguments) secondPart) := by
  have step := sampleStep_together (sampler := sampler) (listeners := listeners) (label site) (.of law populated) (first owner)
    (second owner) (disjoint owner)
    (unmapValues (F := SideValue model (first.union second)) (fun type => ⟨type, owner⟩) _ arguments)
  refine Together.congr ?_ ?_ (Together.bind
    (firstNext := fun reply => .done
      (Values.cons (Value := SideValue model first) (ty := ⟨output, owner⟩) reply .nil))
    (secondNext := fun reply => .done
      (Values.cons (Value := SideValue model second) (ty := ⟨output, owner⟩) reply .nil))
    step fun reply => Together.done rfl rfl)
  · exact congrArg
      (fun values => (sampleStep model (label site) (.of law populated) (first owner) values).bind
        fun reply => .done
          (Values.cons (Value := SideValue model first) (ty := ⟨output, owner⟩) reply .nil))
      (unmapValues_map (F := SideValue model (first.union second)) (fun type => ⟨type, owner⟩)
        (fun {located} value => restrictLeft model first second (located := located) value) _
        arguments)
  · exact congrArg
      (fun values => (sampleStep model (label site) (.of law populated) (second owner) values).bind
        fun reply => .done
          (Values.cons (Value := SideValue model second) (ty := ⟨output, owner⟩) reply .nil))
      (unmapValues_map (F := SideValue model (first.union second)) (fun type => ⟨type, owner⟩)
        (fun {located} value => restrictRight model first second (located := located) value) _
        arguments)

/-- A value known to be the value that a process hears and returns, and a known answer to
whether it listens. -/
theorem Hears.of_eq {site : Site} {type : Ty} {coin : model.Value type} {X : Type}
    {process : PIR.Process (Effects model) X} {value other : X} {listening known : Bool}
    (sameListening : known = listening) (same : value = other)
    (hears : Hears sampler site type coin listening process value) :
    Hears sampler site type coin known process other := by
  subst sameListening same
  exact hears

/-- A side holds at most one of the receivers of a draw: after a receiver in the side, no
later one is in it. The process of such a side performs at most one `receive` for the draw,
so it hears the coin once. -/
@[expose] def hearsOnce (side : Side) : List Nat → Prop
  | [] => True
  | role :: rest => (side role = true → rest.any side = false) ∧ hearsOnce side rest

/-- The receivers of a side that holds at most one of them hear the coin announced at the
draw's site once, when one of them is in the side: each copy held in the side is the coin. -/
theorem receiverReplies_hears (side : Side) (site : Site) (type : Ty) (coin : model.Value type) :
    ∀ (receivers : List Nat), hearsOnce side receivers →
      Hears sampler site type coin (receivers.any side)
        (receiverReplies model side site type receivers) (heldCopies model side type coin receivers)
  | [], _ => Hears.done _
  | role :: rest, once => by
      rcases Bool.eq_false_or_eq_true (side role) with present | absent
      · have later : rest.any side = false := once.1 present
        rw [receiverReplies_present model side site type role rest present]
        refine Hears.of_eq (listening := true || (rest.any side || false))
          (by rw [List.any_cons, present, later]; rfl) rfl ?_
        exact Hears.bind (process := .call (.receive site type) fun reply => .done reply)
          (value := coin)
          (next := fun reply => (receiverReplies model side site type rest).bind fun replies =>
            .done (Values.cons (Value := SideValue model side) (ty := ⟨type, role⟩)
              (Held.of (side role) reply) replies))
          (Hears.receive fun reply => reply)
          (Hears.bind
            (next := fun replies => .done
              (Values.cons (Value := SideValue model side) (ty := ⟨type, role⟩)
                (Held.of (side role) coin) replies))
            (receiverReplies_hears side site type coin rest once.2) (Hears.done _)
            (Bool.and_false _))
          (by rw [later]; rfl)
      · rw [receiverReplies_absent model side site type role rest absent]
        refine Hears.of_eq (listening := rest.any side || false)
          (by rw [List.any_cons, absent, Bool.false_or, Bool.or_false]) ?_
          (Hears.bind
            (next := fun replies => .done
              (Values.cons (Value := SideValue model side) (ty := ⟨type, role⟩)
                (Held.absent (side role) absent) replies))
            (receiverReplies_hears side site type coin rest once.2) (Hears.done _)
            (Bool.and_false _))
        exact congrArg
          (fun head => Values.cons (Value := SideValue model side) (ty := ⟨type, role⟩) head
            (heldCopies model side type coin rest))
          (Held.absent_unique (side role) absent _ _)

/-- A side without any of the receivers hears nothing. -/
theorem receiverReplies_idle (side : Side) (site : Site) (type : Ty) :
    ∀ (receivers : List Nat), (∀ role ∈ receivers, side role = false) →
      ∃ replies, receiverReplies model side site type receivers = .done replies
  | [], _ => ⟨_, rfl⟩
  | role :: rest, absent => by
      obtain ⟨replies, returns⟩ := receiverReplies_idle side site type rest
        fun other member => absent other (List.mem_cons_of_mem _ member)
      rw [receiverReplies_absent model side site type role rest (absent role (List.mem_cons_self ..)),
        returns]
      exact ⟨_, rfl⟩

theorem union_first {role : Nat} (member : first role = true) : (first.union second) role = true := by
  show (first role || second role) = true
  rw [member]
  rfl

theorem union_second {role : Nat} (member : second role = true) :
    (first.union second) role = true := by
  show (first role || second role) = true
  rw [member]
  exact Bool.or_true _

theorem union_neither {role : Nat} (outFirst : first role = false) (outSecond : second role = false) :
    (first.union second) role = false := by
  show (first role || second role) = false
  rw [outFirst, outSecond]
  rfl

theorem Side.Disjoint.second_absent (disjoint : first.Disjoint second) {role : Nat}
    (member : first role = true) : second role = false := by
  have none := disjoint role
  rw [member] at none
  exact none

/-- An announcement from outside both parts: the grouped process waits for it and does
not return alone, unless no receiver is in either part. -/
theorem receiverReplies_together (site : Site) (type : Ty) :
    ∀ (receivers : List Nat),
      Together sampler listeners (leftValues model first second) (rightValues model first second)
        (receiverReplies model (first.union second) site type receivers)
        (receiverReplies model first site type receivers)
        (receiverReplies model second site type receivers)
  | [] => Together.done rfl rfl
  | role :: rest => by
      rcases Bool.eq_false_or_eq_true (first role) with inFirst | outFirst
      · rw [receiverReplies_present model (first.union second) site type role rest
          (union_first inFirst)]
        exact Together.receive
      · rcases Bool.eq_false_or_eq_true (second role) with inSecond | outSecond
        · rw [receiverReplies_present model (first.union second) site type role rest
            (union_second inSecond)]
          exact Together.receive
        · rw [receiverReplies_absent model (first.union second) site type role rest
              (union_neither outFirst outSecond),
            receiverReplies_absent model first site type role rest outFirst,
            receiverReplies_absent model second site type role rest outSecond]
          exact Together.bind (receiverReplies_together site type rest) fun replies =>
            Together.done
              (congrArg
                (fun head => Values.cons (Value := SideValue model first) (ty := ⟨type, role⟩) head
                  (leftValues model first second replies))
                (Held.absent_unique (first role) outFirst _ _))
              (congrArg
                (fun head => Values.cons (Value := SideValue model second) (ty := ⟨type, role⟩) head
                  (rightValues model first second replies))
                (Held.absent_unique (second role) outSecond _ _))

theorem broadcast_left (owner : Nat) (receivers : List Nat) (type : Ty) (reply : model.Value type) :
    leftValues model first second (broadcast model (first.union second) owner receivers type reply) =
      broadcast model first owner receivers type reply :=
  congr
    (congrArg (Values.cons (Value := SideValue model first) (ty := ⟨type, owner⟩))
      (Held.left_of (X := model.Value type) (first owner) (second owner) reply))
    (heldCopies_left type reply receivers)

theorem broadcast_right (owner : Nat) (receivers : List Nat) (type : Ty) (reply : model.Value type) :
    rightValues model first second (broadcast model (first.union second) owner receivers type reply) =
      broadcast model second owner receivers type reply :=
  congr
    (congrArg (Values.cons (Value := SideValue model second) (ty := ⟨type, owner⟩))
      (Held.right_of (X := model.Value type) (first owner) (second owner) reply))
    (heldCopies_right type reply receivers)

/-- The results of a draw for a side without the owner, once every receiver in the side
has heard the coin. -/
theorem heard_eq_broadcast {side : Side} (owner : Nat) (absent : side owner = false)
    (receivers : List Nat) (type : Ty) (reply : model.Value type) :
    Values.cons (Value := SideValue model side) (ty := ⟨type, owner⟩)
        (Held.absent (side owner) absent) (heldCopies model side type reply receivers) =
      broadcast model side owner receivers type reply :=
  congrArg
    (fun head => Values.cons (Value := SideValue model side) (ty := ⟨type, owner⟩) head
      (heldCopies model side type reply receivers))
    (Held.absent_unique (side owner) absent _ _)

/-- A public coin: the owner's part draws and announces it, and the receiver of the other
part hears it. The listeners say so of the draw's site: the owner's part does not hear there,
the other part hears there exactly when it has a receiver, and each part holds at most one
of the receivers. -/
theorem draw_together (disjoint : first.Disjoint second) (owner : Nat) (receivers : List Nat)
    (site : Nat) {inputs : List Ty} {output : Ty}
    (law : Var operations ⟨inputs, [output], .sampling⟩) (populated : output.populated = true)
    (hearsFirst : listeners.first (label site) = (second owner && receivers.any first))
    (hearsSecond : listeners.second (label site) = (first owner && receivers.any second))
    (onceFirst : hearsOnce first receivers) (onceSecond : hearsOnce second receivers)
    (arguments : Values (SideValue model (first.union second)) (Located.atRole owner inputs))
    (whole : Values (RegionFunction (SideValue model (first.union second)) (Effects model)) [])
    (firstPart : Values (RegionFunction (SideValue model first) (Effects model)) [])
    (secondPart : Values (RegionFunction (SideValue model second) (Effects model)) []) :
    Together sampler listeners (leftValues model first second) (rightValues model first second)
      (labelledOperation model label functionTable table (first.union second) (deployed := deployed)
        (.draw owner receivers site law populated) arguments whole)
      (labelledOperation model label functionTable table first (deployed := deployed)
        (.draw owner receivers site law populated) (leftValues model first second arguments) firstPart)
      (labelledOperation model label functionTable table second (deployed := deployed)
        (.draw owner receivers site law populated) (rightValues model first second arguments) secondPart) := by
  rcases Bool.eq_false_or_eq_true (first owner) with inFirst | outFirst
  · have outSecond := disjoint.second_absent inFirst
    rw [outSecond, Bool.false_and] at hearsFirst
    rw [inFirst, Bool.true_and] at hearsSecond
    rw [labelled_draw_owner (side := first.union second) (union_first inFirst),
      labelled_draw_owner (side := first) inFirst, labelled_draw_outside (side := second) outSecond]
    exact Together.draw (site := label site) (law := .of law populated)
      (left := leftValues model first second) (right := rightValues model first second)
      (wholeValue := fun reply => broadcast model (first.union second) owner receivers output reply)
      (firstValue := fun reply => broadcast model first owner receivers output reply)
      (heard := fun reply => Values.cons (Value := SideValue model second) (ty := ⟨output, owner⟩)
        (Held.absent (second owner) outSecond) (heldCopies model second output reply receivers))
      hearsFirst hearsSecond
      (fun reply => (broadcast_left owner receivers output reply).symm)
      (fun reply => Hears.of_eq (Bool.or_false _).symm rfl (Hears.bind
        (next := fun replies => .done
          (Values.cons (Value := SideValue model second) (ty := ⟨output, owner⟩)
            (Held.absent (second owner) outSecond) replies))
        (receiverReplies_hears second (label site) output reply receivers onceSecond)
        (Hears.done _) (Bool.and_false _)))
      (fun reply => (heard_eq_broadcast owner outSecond receivers output reply).trans
        (broadcast_right owner receivers output reply).symm)
  · rcases Bool.eq_false_or_eq_true (second owner) with inSecond | outSecond
    · rw [inSecond, Bool.true_and] at hearsFirst
      rw [outFirst, Bool.false_and] at hearsSecond
      rw [labelled_draw_owner (side := first.union second) (union_second inSecond),
        labelled_draw_owner (side := second) inSecond, labelled_draw_outside (side := first) outFirst]
      exact Together.swap (listeners := listeners.swap)
        (Together.draw (site := label site) (law := .of law populated)
        (left := rightValues model first second) (right := leftValues model first second)
        (wholeValue := fun reply => broadcast model (first.union second) owner receivers output reply)
        (firstValue := fun reply => broadcast model second owner receivers output reply)
        (heard := fun reply => Values.cons (Value := SideValue model first) (ty := ⟨output, owner⟩)
          (Held.absent (first owner) outFirst) (heldCopies model first output reply receivers))
        hearsSecond hearsFirst
        (fun reply => (broadcast_right owner receivers output reply).symm)
        (fun reply => Hears.of_eq (Bool.or_false _).symm rfl (Hears.bind
          (next := fun replies => .done
            (Values.cons (Value := SideValue model first) (ty := ⟨output, owner⟩)
              (Held.absent (first owner) outFirst) replies))
          (receiverReplies_hears first (label site) output reply receivers onceFirst)
          (Hears.done _) (Bool.and_false _)))
        (fun reply => (heard_eq_broadcast owner outFirst receivers output reply).trans
          (broadcast_left owner receivers output reply).symm))
    · rw [labelled_draw_outside (side := first.union second) (union_neither outFirst outSecond),
        labelled_draw_outside (side := first) outFirst,
        labelled_draw_outside (side := second) outSecond]
      exact Together.bind (receiverReplies_together (label site) output receivers) fun replies =>
        Together.done
          (congrArg
            (fun head => Values.cons (Value := SideValue model first) (ty := ⟨output, owner⟩) head
              (leftValues model first second replies))
            (Held.absent_unique (first owner) outFirst _ _))
          (congrArg
            (fun head => Values.cons (Value := SideValue model second) (ty := ⟨output, owner⟩) head
              (rightValues model first second replies))
            (Held.absent_unique (second owner) outSecond _ _))

end Leaves

/-! ## Agreement on a count or a tag -/

section Agreement

variable {X α : Type} {same : X → X → Bool} {side : Side} {onValue : X → α} {onDisagree : α}

/-- The later copies held in the side equal the first one, or the side disagrees. -/
theorem agreeWith_cases (decides : ∀ left right, same left right = true ↔ left = right)
    (value : X) :
    ∀ (roles : List Nat) (values : Values (fun role => Held X (side role)) roles),
      (agreeWith same side onValue onDisagree value roles values = onValue value ∧
        ∀ {role : Nat} (position : Var roles role) (member : side role = true),
          Held.value (side role) member (values.get position) = value) ∨
      agreeWith same side onValue onDisagree value roles values = onDisagree
  | [], _ => .inl ⟨rfl, fun position => position.elimNil⟩
  | role :: rest, values => by
      rcases Bool.eq_false_or_eq_true (side role) with present | absent
      · rw [agreeWith_present present]
        rcases Bool.eq_false_or_eq_true
            (same value (Held.value (side role) present (values.get .here))) with equal | unequal
        · rw [equal]
          rcases agreeWith_cases decides value rest values.tail with ⟨agrees, others⟩ | differs
          · refine .inl ⟨agrees, ?_⟩
            intro other position member
            cases position with
            | here => exact ((decides _ _).mp equal).symm
            | there position => rw [← tail_get]; exact others position member
          · exact .inr differs
        · rw [unequal]
          exact .inr rfl
      · rw [agreeWith_absent absent]
        rcases agreeWith_cases decides value rest values.tail with ⟨agrees, others⟩ | differs
        · refine .inl ⟨agrees, ?_⟩
          intro other position member
          cases position with
          | here => rw [absent] at member; cases member
          | there position => rw [← tail_get]; exact others position member
        · exact .inr differs

/-- With a participant in the side: the copies held in the side are one value and the side
continues with it, or the side disagrees. -/
theorem agreed_cases (decides : ∀ left right, same left right = true ↔ left = right) :
    ∀ (roles : List Nat) (values : Values (fun role => Held X (side role)) roles)
      (onNone : roles.any side = false → α), roles.any side = true →
      (∃ value, agreed same side onValue onDisagree roles values onNone = onValue value ∧
        ∀ {role : Nat} (position : Var roles role) (member : side role = true),
          Held.value (side role) member (values.get position) = value) ∨
      agreed same side onValue onDisagree roles values onNone = onDisagree
  | [], _, _, inside => Bool.noConfusion inside
  | role :: rest, values, onNone, inside => by
      rcases Bool.eq_false_or_eq_true (side role) with present | absent
      · rw [agreed_present present]
        rcases agreeWith_cases (onValue := onValue) (onDisagree := onDisagree) decides
            (Held.value (side role) present (values.get .here)) rest values.tail with
          ⟨agrees, others⟩ | differs
        · refine .inl ⟨_, agrees, ?_⟩
          intro other position member
          cases position with
          | here => rfl
          | there position => rw [← tail_get]; exact others position member
        · exact .inr differs
      · rw [agreed_absent absent]
        have restInside : rest.any side = true := by
          simpa only [List.any_cons, absent, Bool.false_or] using inside
        rcases agreed_cases decides rest values.tail _ restInside with
          ⟨value, agrees, others⟩ | differs
        · refine .inl ⟨value, agrees, ?_⟩
          intro other position member
          cases position with
          | here => rw [absent] at member; cases member
          | there position => rw [← tail_get]; exact others position member
        · exact .inr differs

end Agreement

section AgreedTogether

variable {model : Model} {sampler : Sampler model} {listeners : Listeners} {X : Type} {same : X → X → Bool}
  {first second : Side} {grouped firstType secondType : Type} {left : grouped → firstType}
  {right : grouped → secondType}

/-- A count or tag shared by the participants. A grouped process that returns has agreed
on it, so every part with a participant holds it and continues with it; a part without a
participant does what the operation does for a side outside it. -/
theorem agreed_together (decides : ∀ left right, same left right = true ↔ left = right)
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
      Together sampler listeners left right (onWhole value) (onFirst value) (onSecond value))
    (onlyFirst : participants.any first = true → ∀ (outside : participants.any second = false)
      (value : X), Together sampler listeners left right (onWhole value) (onFirst value)
        (.done (noneSecond outside)))
    (onlySecond : ∀ (outside : participants.any first = false), participants.any second = true →
      ∀ value, Together sampler listeners left right (onWhole value) (.done (noneFirst outside))
        (onSecond value)) :
    Together sampler listeners left right
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
      exact Together.halt
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
    exact Together.done (none outWhole outFirst outSecond).1 (none outWhole outFirst outSecond).2

/-- The keys of the copies that a part holds are the part's shares of the keys of the
copies that the union holds. -/
theorem keys_left {K : Type} (key : X → K) :
    ∀ (roles : List Nat) (copies : Values (fun role => Held X (first.union second role)) roles),
      (copies.map fun {role} copy => Held.left (first role) (second role) copy).map
          (fun {role} copy => Held.map key (first role) copy) =
        (copies.map fun {role} copy => Held.map key (first.union second role) copy).map
          fun {role} copy => Held.left (first role) (second role) copy
  | [], .nil => rfl
  | role :: rest, .cons copy copies =>
      cons_congr (Held.left_map key (first role) (second role) copy) (keys_left key rest copies)

theorem keys_right {K : Type} (key : X → K) :
    ∀ (roles : List Nat) (copies : Values (fun role => Held X (first.union second role)) roles),
      (copies.map fun {role} copy => Held.right (first role) (second role) copy).map
          (fun {role} copy => Held.map key (second role) copy) =
        (copies.map fun {role} copy => Held.map key (first.union second role) copy).map
          fun {role} copy => Held.right (first role) (second role) copy
  | [], .nil => rfl
  | role :: rest, .cons copy copies =>
      cons_congr (Held.right_map key (first role) (second role) copy) (keys_right key rest copies)

/-- A tag whose copies agree when their keys are equal, with continuations that read the
key only: as `agreed_together`, on the key that the participants agree on. -/
theorem agreed_together_keyed {K : Type} (key : X → K) {sameKey : K → K → Bool}
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
      Together sampler listeners left right (onWhole value) (onFirst value) (onSecond value))
    (onlyFirst : participants.any first = true → ∀ (outside : participants.any second = false)
      (value : K), Together sampler listeners left right (onWhole value) (onFirst value)
        (.done (noneSecond outside)))
    (onlySecond : ∀ (outside : participants.any first = false), participants.any second = true →
      ∀ value, Together sampler listeners left right (onWhole value) (.done (noneFirst outside))
        (onSecond value)) :
    Together sampler listeners left right
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
  exact agreed_together decides participants _ _ _ (keys_left key participants copies)
    (keys_right key participants copies) none both onlyFirst onlySecond

end AgreedTogether

/-! ## The shape that the law needs of a region

These are residual conditions of a well-formed definition, stated here as propositions
over the region so that the law does not depend on the checker's pass. -/

section Shape

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}

/-- The role map of an application has an entry for every role of the callee. -/
@[expose] def opCovers : ProtocolOp operations functions protocols deployed → Prop
  | .apply (header := header) _ roleMap _ _ => header.roles ≤ roleMap.length
  | .at .. | .exchange .. | .draw .. | .sample .. | .repeat .. | .choose .. => True

/-- Every operation of the region, outside its nested regions, names roles of the list
only and applies protocols whose roles the role map covers; the region has no `stop`. -/
@[expose] def regionWithin (roles : List Nat) {Γ out : List Located} :
    Region (ProtocolDialect operations functions protocols deployed) Γ out → Prop
  | .ret _ => True
  | .stop _ => False
  | .bind body rest => regionWithin roles body ∧ regionWithin roles rest
  | .letOp op _ _ rest =>
      (∀ role ∈ ProtocolOp.roles op, role ∈ roles) ∧ opCovers op ∧ regionWithin roles rest

@[expose] def regionsWithin (roles : List Nat) :
    {signatures : List (List Located × List Located)} →
      Regions (ProtocolDialect operations functions protocols deployed) signatures → Prop
  | _, .nil => True
  | _, .cons body tail => regionWithin roles body ∧ regionsWithin roles tail

/-- The regions of a `repeat` or `choose` name its participants only, and the values that
leave a `repeat` are held by participants. (Those that leave a `choose` are, by typing.) -/
@[expose] def opEncloses :
    (op : ProtocolOp operations functions protocols deployed) →
      Regions (ProtocolDialect operations functions protocols deployed) (ProtocolOp.regions op) →
        Prop
  | .repeat participants _ carried _ _ _, bodies =>
      Located.heldBy participants carried = true ∧ regionsWithin participants bodies
  | .choose participants _ _ _ _, bodies => regionsWithin participants bodies
  | .at .., _ | .exchange .., _ | .draw .., _ | .sample .., _ | .apply .., _ => True

mutual
  /-- Every `repeat` and `choose` of the region, nested ones included, encloses its
  regions. -/
  @[expose] def regionEnclosed {Γ out : List Located} :
      Region (ProtocolDialect operations functions protocols deployed) Γ out → Prop
    | .ret _ => True
    | .stop _ => True
    | .bind body rest => regionEnclosed body ∧ regionEnclosed rest
    | .letOp op _ bodies rest => opEncloses op bodies ∧ regionsEnclosed bodies ∧ regionEnclosed rest

  @[expose] def regionsEnclosed {signatures : List (List Located × List Located)} :
      Regions (ProtocolDialect operations functions protocols deployed) signatures → Prop
    | .nil => True
    | .cons body tail => regionEnclosed body ∧ regionsEnclosed tail
end

/-- For every protocol of a program: whether given listeners are those of the protocol
reached under a path, for two sides. -/
abbrev ListenTable (protocols : List ProtocolHeader) : Type :=
  Values (fun _ : ProtocolHeader => List Nat → Side → Side → Prop) protocols

section Listens

variable (listeners : Listeners) (label : Nat → Site) (callees : ListenTable protocols)
  (first second : Side)

/-- The listeners are those of one operation, for two sides. At the site of a `draw` a side
hears exactly when the other side has the owner and it has a receiver, and each side holds
at most one of the receivers. The listeners are those of the protocol that an application
applies, below the site of the application, for the preimages of the two sides. -/
@[expose] def opListens : ProtocolOp operations functions protocols deployed → Prop
  | .draw owner receivers site _ _ =>
      listeners.first (label site) = (second owner && receivers.any first) ∧
        listeners.second (label site) = (first owner && receivers.any second) ∧
        hearsOnce first receivers ∧ hearsOnce second receivers
  | .apply callee roleMap site _ =>
      (callees.get callee) (label site).below (Side.preimage roleMap first)
        (Side.preimage roleMap second)
  | .at .. | .exchange .. | .sample .. | .repeat .. | .choose .. => True

mutual
  /-- The listeners are those of every operation of the region, nested ones included. -/
  @[expose] def regionListens {Γ out : List Located} :
      Region (ProtocolDialect operations functions protocols deployed) Γ out → Prop
    | .ret _ => True
    | .stop _ => True
    | .bind body rest => regionListens body ∧ regionListens rest
    | .letOp op _ bodies rest =>
        opListens listeners label callees first second op ∧ regionsListens bodies ∧
          regionListens rest

  @[expose] def regionsListens {signatures : List (List Located × List Located)} :
      Regions (ProtocolDialect operations functions protocols deployed) signatures → Prop
    | .nil => True
    | .cons body tail => regionListens body ∧ regionsListens tail
end

end Listens

end Shape

/-! ## Nested regions, and the protocols a region applies -/

section Related

variable {model : Model} (sampler : Sampler model) (listeners : Listeners)

/-- Region functions of a union and of its two parts, related one by one. -/
def RegionsTogether (first second : Side) :
    (signatures : List (List Located × List Located)) →
      Values (RegionFunction (SideValue model (first.union second)) (Effects model)) signatures →
      Values (RegionFunction (SideValue model first) (Effects model)) signatures →
      Values (RegionFunction (SideValue model second) (Effects model)) signatures → Prop
  | [], _, _, _ => True
  | _ :: rest, whole, firstPart, secondPart =>
      (∀ values, Together sampler listeners (leftValues model first second) (rightValues model first second)
        ((whole.get .here) values) ((firstPart.get .here) (leftValues model first second values))
        ((secondPart.get .here) (rightValues model first second values))) ∧
      RegionsTogether first second rest whole.tail firstPart.tail secondPart.tail

/-- Region functions that return without an effect. -/
@[expose] def RegionsIdle (side : Side) :
    (signatures : List (List Located × List Located)) →
      Values (RegionFunction (SideValue model side) (Effects model)) signatures → Prop
  | [], _ => True
  | _ :: rest, regions =>
      (∀ values, ∃ result, (regions.get .here) values = .done result) ∧
        RegionsIdle side rest regions.tail

/-- What the law needs of the protocols that a region applies: the law itself for every
callee, under every path and for every two sides at which the listeners are those of the
callee, and that a callee does nothing for a side without any of its roles. -/
structure TableTogether {protocols : List ProtocolHeader} (listens : ListenTable protocols)
    (table : ProtocolTable model protocols) : Prop where
  together : ∀ {header : ProtocolHeader} (callee : Var protocols header) (path : List Nat)
    (first second : Side), first.Disjoint second → (listens.get callee) path first second →
    ∀ (arguments : Values (SideValue model (first.union second)) header.inputs),
      Together sampler listeners (leftValues model first second) (rightValues model first second)
        ((table.get callee) path (first.union second) arguments)
        ((table.get callee) path first (leftValues model first second arguments))
        ((table.get callee) path second (rightValues model first second arguments))
  idle : ∀ {header : ProtocolHeader} (callee : Var protocols header) (path : List Nat) (side : Side),
    (∀ role, role < header.roles → side role = false) →
    ∀ (arguments : Values (SideValue model side) header.inputs),
      ∃ values, (table.get callee) path side arguments = .done values

end Related

section Arms

variable {model : Model} {sampler : Sampler model} {listeners : Listeners} {first second : Side}

/-- The selected arm of a `choose` of which both parts have a participant. -/
theorem selectArm_together (signature : List Located × List Located) :
    ∀ (count : Nat)
      (whole : Values (RegionFunction (SideValue model (first.union second)) (Effects model))
        (List.replicate count signature))
      (firstPart : Values (RegionFunction (SideValue model first) (Effects model))
        (List.replicate count signature))
      (secondPart : Values (RegionFunction (SideValue model second) (Effects model))
        (List.replicate count signature)),
      RegionsTogether sampler listeners first second (List.replicate count signature) whole firstPart
        secondPart →
      ∀ (number : Fin count) (captured : Values (SideValue model (first.union second)) signature.1),
        Together sampler listeners (leftValues model first second) (rightValues model first second)
          (selectArm signature count whole number captured)
          (selectArm signature count firstPart number (leftValues model first second captured))
          (selectArm signature count secondPart number (rightValues model first second captured))
  | 0, _, _, _, _, number, _ => number.elim0
  | _ + 1, _, _, _, related, ⟨0, _⟩, captured => related.1 captured
  | count + 1, whole, firstPart, secondPart, related, ⟨number + 1, below⟩, captured =>
      selectArm_together signature count whole.tail firstPart.tail secondPart.tail related.2
        ⟨number, Nat.lt_of_succ_lt_succ below⟩ captured

/-- The selected arm of a `choose` of which the second part has no participant. -/
theorem selectArm_first (signature : List Located × List Located)
    (unique : ∀ one other : Values (SideValue model second) signature.2, one = other) :
    ∀ (count : Nat)
      (whole : Values (RegionFunction (SideValue model (first.union second)) (Effects model))
        (List.replicate count signature))
      (firstPart : Values (RegionFunction (SideValue model first) (Effects model))
        (List.replicate count signature))
      (secondPart : Values (RegionFunction (SideValue model second) (Effects model))
        (List.replicate count signature)),
      RegionsTogether sampler listeners first second (List.replicate count signature) whole firstPart
        secondPart →
      RegionsIdle second (List.replicate count signature) secondPart →
      ∀ (number : Fin count) (captured : Values (SideValue model (first.union second)) signature.1)
        (idle : Values (SideValue model second) signature.2),
        Together sampler listeners (leftValues model first second) (rightValues model first second)
          (selectArm signature count whole number captured)
          (selectArm signature count firstPart number (leftValues model first second captured))
          (.done idle)
  | 0, _, _, _, _, _, number, _, _ => number.elim0
  | _ + 1, _, _, _, related, idles, ⟨0, _⟩, captured, idle => by
      obtain ⟨result, returns⟩ := idles.1 (rightValues model first second captured)
      exact Together.congr rfl
        ((congrArg PIR.Process.done (unique idle result)).trans returns.symm) (related.1 captured)
  | count + 1, whole, firstPart, secondPart, related, idles, ⟨number + 1, below⟩, captured, idle =>
      selectArm_first signature unique count whole.tail firstPart.tail secondPart.tail related.2
        idles.2 ⟨number, Nat.lt_of_succ_lt_succ below⟩ captured idle

/-- The selected arm of a `choose` of which the first part has no participant. -/
theorem selectArm_second (signature : List Located × List Located)
    (unique : ∀ one other : Values (SideValue model first) signature.2, one = other) :
    ∀ (count : Nat)
      (whole : Values (RegionFunction (SideValue model (first.union second)) (Effects model))
        (List.replicate count signature))
      (firstPart : Values (RegionFunction (SideValue model first) (Effects model))
        (List.replicate count signature))
      (secondPart : Values (RegionFunction (SideValue model second) (Effects model))
        (List.replicate count signature)),
      RegionsTogether sampler listeners first second (List.replicate count signature) whole firstPart
        secondPart →
      RegionsIdle first (List.replicate count signature) firstPart →
      ∀ (number : Fin count) (captured : Values (SideValue model (first.union second)) signature.1)
        (idle : Values (SideValue model first) signature.2),
        Together sampler listeners (leftValues model first second) (rightValues model first second)
          (selectArm signature count whole number captured) (.done idle)
          (selectArm signature count secondPart number (rightValues model first second captured))
  | 0, _, _, _, _, _, number, _, _ => number.elim0
  | _ + 1, _, _, _, related, idles, ⟨0, _⟩, captured, idle => by
      obtain ⟨result, returns⟩ := idles.1 (leftValues model first second captured)
      exact Together.congr
        ((congrArg PIR.Process.done (unique idle result)).trans returns.symm) rfl (related.1 captured)
  | count + 1, whole, firstPart, secondPart, related, idles, ⟨number + 1, below⟩, captured, idle =>
      selectArm_second signature unique count whole.tail firstPart.tail secondPart.tail related.2
        idles.2 ⟨number, Nat.lt_of_succ_lt_succ below⟩ captured idle

/-- A copy that is the first alternative for the union is the first alternative for a
part, with the part's share of the payload. -/
theorem firstPayload_left {First Later : Type} :
    ∀ (first second : Bool) (copy : Held (First ⊕ Later) (first || second))
      (payload : Held First (first || second)),
      firstPayload (first || second) copy = some payload →
        firstPayload first (Held.left first second copy) = some (Held.left first second payload)
  | true, _, _, _, found => found
  | false, _, _, _, _ => rfl

theorem firstPayload_right {First Later : Type} :
    ∀ (first second : Bool) (copy : Held (First ⊕ Later) (first || second))
      (payload : Held First (first || second)),
      firstPayload (first || second) copy = some payload →
        firstPayload second (Held.right first second copy) =
          some (Held.right first second payload)
  | true, true, _, _, found => found
  | false, true, _, _, found => found
  | true, false, _, _, _ => rfl
  | false, false, _, _, _ => rfl

theorem laterCopy_left {First Later : Type} :
    ∀ (first second : Bool) (copy : Held (First ⊕ Later) (first || second))
      (later : Held Later (first || second)),
      laterCopy (first || second) copy = some later →
        laterCopy first (Held.left first second copy) = some (Held.left first second later)
  | true, _, _, _, found => found
  | false, _, _, _, _ => rfl

theorem laterCopy_right {First Later : Type} :
    ∀ (first second : Bool) (copy : Held (First ⊕ Later) (first || second))
      (later : Held Later (first || second)),
      laterCopy (first || second) copy = some later →
        laterCopy second (Held.right first second copy) = some (Held.right first second later)
  | true, true, _, _, found => found
  | false, true, _, _, found => found
  | true, false, _, _, _ => rfl
  | false, false, _, _, _ => rfl

/-- The payloads of the first alternative that a part holds are the part's shares of
those that the union holds. -/
theorem firstPayloads_left (payload : Ty) (rest : List Ty) :
    ∀ (roles : List Nat)
      (copies : Values
        (fun role => Held (Ty.Variant model.Carrier (payload :: rest)) (first.union second role))
        roles)
      (payloads : Values (fun role => Held (model.Value payload) (first.union second role)) roles),
      firstPayloads model (first.union second) payload rest roles copies = some payloads →
        firstPayloads model first payload rest roles
            (copies.map fun {role} copy => Held.left (first role) (second role) copy) =
          some (payloads.map fun {role} value => Held.left (first role) (second role) value)
  | [], .nil, _, found => by cases found; rfl
  | role :: roles, .cons copy copies, _, found => by
      obtain ⟨head, tail, headFound, tailFound, rfl⟩ := consFound_some _ _ _ found
      exact congr
        (congrArg consFound (firstPayload_left (first role) (second role) copy head headFound))
        (firstPayloads_left payload rest roles copies tail tailFound)

theorem firstPayloads_right (payload : Ty) (rest : List Ty) :
    ∀ (roles : List Nat)
      (copies : Values
        (fun role => Held (Ty.Variant model.Carrier (payload :: rest)) (first.union second role))
        roles)
      (payloads : Values (fun role => Held (model.Value payload) (first.union second role)) roles),
      firstPayloads model (first.union second) payload rest roles copies = some payloads →
        firstPayloads model second payload rest roles
            (copies.map fun {role} copy => Held.right (first role) (second role) copy) =
          some (payloads.map fun {role} value => Held.right (first role) (second role) value)
  | [], .nil, _, found => by cases found; rfl
  | role :: roles, .cons copy copies, _, found => by
      obtain ⟨head, tail, headFound, tailFound, rfl⟩ := consFound_some _ _ _ found
      exact congr
        (congrArg consFound (firstPayload_right (first role) (second role) copy head headFound))
        (firstPayloads_right payload rest roles copies tail tailFound)

theorem laterCopies_left (payload : Ty) (rest : List Ty) :
    ∀ (roles : List Nat)
      (copies : Values
        (fun role => Held (Ty.Variant model.Carrier (payload :: rest)) (first.union second role))
        roles)
      (later : Values (fun role => Held (Ty.Variant model.Carrier rest) (first.union second role))
        roles),
      laterCopies model (first.union second) payload rest roles copies = some later →
        laterCopies model first payload rest roles
            (copies.map fun {role} copy => Held.left (first role) (second role) copy) =
          some (later.map fun {role} value => Held.left (first role) (second role) value)
  | [], .nil, _, found => by cases found; rfl
  | role :: roles, .cons copy copies, _, found => by
      obtain ⟨head, tail, headFound, tailFound, rfl⟩ := consFound_some _ _ _ found
      exact congr
        (congrArg consFound (laterCopy_left (first role) (second role) copy head headFound))
        (laterCopies_left payload rest roles copies tail tailFound)

theorem laterCopies_right (payload : Ty) (rest : List Ty) :
    ∀ (roles : List Nat)
      (copies : Values
        (fun role => Held (Ty.Variant model.Carrier (payload :: rest)) (first.union second role))
        roles)
      (later : Values (fun role => Held (Ty.Variant model.Carrier rest) (first.union second role))
        roles),
      laterCopies model (first.union second) payload rest roles copies = some later →
        laterCopies model second payload rest roles
            (copies.map fun {role} copy => Held.right (first role) (second role) copy) =
          some (later.map fun {role} value => Held.right (first role) (second role) value)
  | [], .nil, _, found => by cases found; rfl
  | role :: roles, .cons copy copies, _, found => by
      obtain ⟨head, tail, headFound, tailFound, rfl⟩ := consFound_some _ _ _ found
      exact congr
        (congrArg consFound (laterCopy_right (first role) (second role) copy head headFound))
        (laterCopies_right payload rest roles copies tail tailFound)

/-- A part's shares of the payloads of the participants and the captures are the payloads
that the part holds and its shares of the captures. -/
theorem payloads_left {participants : List Nat} {captures : List Located} (payload : Ty)
    (payloads : Values (fun role => Held (model.Value payload) (first.union second role))
      participants)
    (captured : Values (SideValue model (first.union second)) captures) :
    leftValues model first second
        ((remapValues (F := SideValue model (first.union second)) (fun role => ⟨payload, role⟩)
          participants payloads).append captured) =
      (remapValues (F := SideValue model first) (fun role => ⟨payload, role⟩) participants
        (payloads.map fun {role} value => Held.left (first role) (second role) value)).append
        (leftValues model first second captured) :=
  (Values.map_append _ _ captured).trans
    (congrArg (fun values => Values.append values (leftValues model first second captured))
      (remapValues_map (F := SideValue model (first.union second)) (fun role => ⟨payload, role⟩)
        (fun {located} value => restrictLeft model first second (located := located) value)
        participants payloads))

theorem payloads_right {participants : List Nat} {captures : List Located} (payload : Ty)
    (payloads : Values (fun role => Held (model.Value payload) (first.union second role))
      participants)
    (captured : Values (SideValue model (first.union second)) captures) :
    rightValues model first second
        ((remapValues (F := SideValue model (first.union second)) (fun role => ⟨payload, role⟩)
          participants payloads).append captured) =
      (remapValues (F := SideValue model second) (fun role => ⟨payload, role⟩) participants
        (payloads.map fun {role} value => Held.right (first role) (second role) value)).append
        (rightValues model first second captured) :=
  (Values.map_append _ _ captured).trans
    (congrArg (fun values => Values.append values (rightValues model first second captured))
      (remapValues_map (F := SideValue model (first.union second)) (fun role => ⟨payload, role⟩)
        (fun {located} value => restrictRight model first second (located := located) value)
        participants payloads))

/-- The region of an alternative of a `choose` of which both parts have a participant. -/
theorem alternativeProcess_together {participants : List Nat} {captures outputs : List Located} :
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
      RegionsTogether sampler listeners first second _ whole firstPart secondPart →
      ∀ (number : Nat)
        (copies : Values
          (fun role => Held (Ty.Variant model.Carrier alternatives) (first.union second role))
          participants)
        (captured : Values (SideValue model (first.union second)) captures),
        Together sampler listeners (leftValues model first second) (rightValues model first second)
          (alternativeProcess model (first.union second) participants captures outputs alternatives
            whole number copies captured)
          (alternativeProcess model first participants captures outputs alternatives firstPart
            number (copies.map fun {role} copy => Held.left (first role) (second role) copy)
            (leftValues model first second captured))
          (alternativeProcess model second participants captures outputs alternatives secondPart
            number (copies.map fun {role} copy => Held.right (first role) (second role) copy)
            (rightValues model first second captured))
  | [], _, _, _, _, _, _, _ => Together.halt
  | payload :: rest, whole, firstPart, secondPart, related, 0, copies, captured => by
      cases found : firstPayloads model (first.union second) payload rest participants copies with
      | none =>
          rw [alternativeProcess_first_other found]
          exact Together.halt
      | some payloads =>
          rw [alternativeProcess_first found,
            alternativeProcess_first (firstPayloads_left payload rest participants copies _ found),
            alternativeProcess_first (firstPayloads_right payload rest participants copies _ found)]
          exact Together.congr
            (congrArg (firstPart.get .here) (payloads_left payload payloads captured).symm)
            (congrArg (secondPart.get .here) (payloads_right payload payloads captured).symm)
            (related.1 _)
  | payload :: rest, whole, firstPart, secondPart, related, number + 1, copies, captured => by
      cases found : laterCopies model (first.union second) payload rest participants copies with
      | none =>
          rw [alternativeProcess_later_other number found]
          exact Together.halt
      | some later =>
          rw [alternativeProcess_later number found,
            alternativeProcess_later number
              (laterCopies_left payload rest participants copies _ found),
            alternativeProcess_later number
              (laterCopies_right payload rest participants copies _ found)]
          exact alternativeProcess_together rest whole.tail firstPart.tail secondPart.tail
            related.2 number later captured

/-- The region of an alternative of a `choose` of which the second part has no
participant. -/
theorem alternativeProcess_onlyFirst {participants : List Nat} {captures outputs : List Located}
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
      RegionsTogether sampler listeners first second _ whole firstPart secondPart →
      RegionsIdle second _ secondPart →
      ∀ (number : Nat)
        (copies : Values
          (fun role => Held (Ty.Variant model.Carrier alternatives) (first.union second role))
          participants)
        (captured : Values (SideValue model (first.union second)) captures)
        (idle : Values (SideValue model second) outputs),
        Together sampler listeners (leftValues model first second) (rightValues model first second)
          (alternativeProcess model (first.union second) participants captures outputs alternatives
            whole number copies captured)
          (alternativeProcess model first participants captures outputs alternatives firstPart
            number (copies.map fun {role} copy => Held.left (first role) (second role) copy)
            (leftValues model first second captured))
          (.done idle)
  | [], _, _, _, _, _, _, _, _, _ => Together.halt
  | payload :: rest, whole, firstPart, secondPart, related, idles, 0, copies, captured, idle => by
      cases found : firstPayloads model (first.union second) payload rest participants copies with
      | none =>
          rw [alternativeProcess_first_other found]
          exact Together.halt
      | some payloads =>
          rw [alternativeProcess_first found,
            alternativeProcess_first (firstPayloads_left payload rest participants copies _ found)]
          obtain ⟨result, returns⟩ := idles.1 (rightValues model first second
            ((remapValues (F := SideValue model (first.union second)) (fun role => ⟨payload, role⟩)
              participants payloads).append captured))
          exact Together.congr
            (congrArg (firstPart.get .here) (payloads_left payload payloads captured).symm)
            ((congrArg PIR.Process.done (unique idle result)).trans returns.symm) (related.1 _)
  | payload :: rest, whole, firstPart, secondPart, related, idles, number + 1, copies, captured,
      idle => by
      cases found : laterCopies model (first.union second) payload rest participants copies with
      | none =>
          rw [alternativeProcess_later_other number found]
          exact Together.halt
      | some later =>
          rw [alternativeProcess_later number found,
            alternativeProcess_later number
              (laterCopies_left payload rest participants copies _ found)]
          exact alternativeProcess_onlyFirst unique rest whole.tail firstPart.tail secondPart.tail
            related.2 idles.2 number later captured idle

/-- The region of an alternative of a `choose` of which the first part has no
participant. -/
theorem alternativeProcess_onlySecond {participants : List Nat} {captures outputs : List Located}
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
      RegionsTogether sampler listeners first second _ whole firstPart secondPart →
      RegionsIdle first _ firstPart →
      ∀ (number : Nat)
        (copies : Values
          (fun role => Held (Ty.Variant model.Carrier alternatives) (first.union second role))
          participants)
        (captured : Values (SideValue model (first.union second)) captures)
        (idle : Values (SideValue model first) outputs),
        Together sampler listeners (leftValues model first second) (rightValues model first second)
          (alternativeProcess model (first.union second) participants captures outputs alternatives
            whole number copies captured)
          (.done idle)
          (alternativeProcess model second participants captures outputs alternatives secondPart
            number (copies.map fun {role} copy => Held.right (first role) (second role) copy)
            (rightValues model first second captured))
  | [], _, _, _, _, _, _, _, _, _ => Together.halt
  | payload :: rest, whole, firstPart, secondPart, related, idles, 0, copies, captured, idle => by
      cases found : firstPayloads model (first.union second) payload rest participants copies with
      | none =>
          rw [alternativeProcess_first_other found]
          exact Together.halt
      | some payloads =>
          rw [alternativeProcess_first found,
            alternativeProcess_first (firstPayloads_right payload rest participants copies _ found)]
          obtain ⟨result, returns⟩ := idles.1 (leftValues model first second
            ((remapValues (F := SideValue model (first.union second)) (fun role => ⟨payload, role⟩)
              participants payloads).append captured))
          exact Together.congr
            ((congrArg PIR.Process.done (unique idle result)).trans returns.symm)
            (congrArg (secondPart.get .here) (payloads_right payload payloads captured).symm)
            (related.1 _)
  | payload :: rest, whole, firstPart, secondPart, related, idles, number + 1, copies, captured,
      idle => by
      cases found : laterCopies model (first.union second) payload rest participants copies with
      | none =>
          rw [alternativeProcess_later_other number found]
          exact Together.halt
      | some later =>
          rw [alternativeProcess_later number found,
            alternativeProcess_later number
              (laterCopies_right payload rest participants copies _ found)]
          exact alternativeProcess_onlySecond unique rest whole.tail firstPart.tail
            secondPart.tail related.2 idles.2 number later captured idle

end Arms

/-! ## Operations with nested regions, and applications -/

section Nested

variable {model : Model} {sampler : Sampler model} {listeners : Listeners} {operations : List OperationSignature}
  {functions : List FunctionHeader} {protocols : List ProtocolHeader} {deployed : Bool}
  {functionTable : FunctionTable model functions} {table : ProtocolTable model protocols}
  {label : Nat → Site} {first second : Side}

/-- The copies of the count of a `repeat` held in a part are the part's shares of the
copies held in the union. -/
theorem repeatCopies_left (participants : List Nat) :
    ∀ (count : RepeatCount)
      (counts : Values (SideValue model (first.union second)) (count.operands participants)),
      repeatCopies model first participants count (leftValues model first second counts) =
        (repeatCopies model (first.union second) participants count counts).map
          (fun {role} value => Held.left (first role) (second role) value)
  | .static number, _ => by
      show unmapValues (F := SideValue model first) (fun role => ⟨.nat, role⟩) participants
        (heldCopies model first .nat number participants) = _
      rw [← heldCopies_left .nat number participants]
      exact unmapValues_map (F := SideValue model (first.union second)) (fun role => ⟨.nat, role⟩)
        (fun {located} value => restrictLeft model first second (located := located) value) _ _
  | .runtime _, counts =>
      unmapValues_map (F := SideValue model (first.union second)) (fun role => ⟨.nat, role⟩)
        (fun {located} value => restrictLeft model first second (located := located) value) _ counts

theorem repeatCopies_right (participants : List Nat) :
    ∀ (count : RepeatCount)
      (counts : Values (SideValue model (first.union second)) (count.operands participants)),
      repeatCopies model second participants count (rightValues model first second counts) =
        (repeatCopies model (first.union second) participants count counts).map
          (fun {role} value => Held.right (first role) (second role) value)
  | .static number, _ => by
      show unmapValues (F := SideValue model second) (fun role => ⟨.nat, role⟩) participants
        (heldCopies model second .nat number participants) = _
      rw [← heldCopies_right .nat number participants]
      exact unmapValues_map (F := SideValue model (first.union second)) (fun role => ⟨.nat, role⟩)
        (fun {located} value => restrictRight model first second (located := located) value) _ _
  | .runtime _, counts =>
      unmapValues_map (F := SideValue model (first.union second)) (fun role => ⟨.nat, role⟩)
        (fun {located} value => restrictRight model first second (located := located) value) _
        counts

/-! ### What a `repeat` collects, in the parts -/

theorem sideCollectedNone_left :
    ∀ (collected : List Located),
      sideCollectedNone model first collected =
        leftValues model first second (sideCollectedNone model (first.union second) collected)
  | [] => rfl
  | ⟨_, holder⟩ :: rest =>
      cons_congr (Held.left_of (first holder) (second holder) _).symm
        (sideCollectedNone_left rest)

theorem sideCollectedNone_right :
    ∀ (collected : List Located),
      sideCollectedNone model second collected =
        rightValues model first second (sideCollectedNone model (first.union second) collected)
  | [] => rfl
  | ⟨_, holder⟩ :: rest =>
      cons_congr (Held.right_of (first holder) (second holder) _).symm
        (sideCollectedNone_right rest)

theorem sideCollectedPush_left {done : Nat} :
    ∀ (collected : List Located)
      (values : Values (SideValue model (first.union second)) collected)
      (earlier : Values (SideValue model (first.union second))
        (collectedSequencesAt (some done) collected)),
      sideCollectedPush model first collected (leftValues model first second values)
          (leftValues model first second earlier) =
        leftValues model first second
          (sideCollectedPush model (first.union second) collected values earlier)
  | [], _, _ => rfl
  | ⟨_, holder⟩ :: rest, .cons value values, .cons sequence earlier =>
      cons_congr (Held.left_map₂ _ (first holder) (second holder) value sequence)
        (sideCollectedPush_left rest values earlier)

theorem sideCollectedPush_right {done : Nat} :
    ∀ (collected : List Located)
      (values : Values (SideValue model (first.union second)) collected)
      (earlier : Values (SideValue model (first.union second))
        (collectedSequencesAt (some done) collected)),
      sideCollectedPush model second collected (rightValues model first second values)
          (rightValues model first second earlier) =
        rightValues model first second
          (sideCollectedPush model (first.union second) collected values earlier)
  | [], _, _ => rfl
  | ⟨_, holder⟩ :: rest, .cons value values, .cons sequence earlier =>
      cons_congr (Held.right_map₂ _ (first holder) (second holder) value sequence)
        (sideCollectedPush_right rest values earlier)

theorem sideCollectedLists_left {total : Nat} :
    ∀ (collected : List Located)
      (values : Values (SideValue model (first.union second))
        (collectedSequencesAt (some total) collected)),
      sideCollectedLists model first collected (leftValues model first second values) =
        leftValues model first second
          (sideCollectedLists model (first.union second) collected values)
  | [], _ => rfl
  | ⟨_, holder⟩ :: rest, .cons sequence values =>
      cons_congr (Held.left_map _ (first holder) (second holder) sequence)
        (sideCollectedLists_left rest values)

theorem sideCollectedLists_right {total : Nat} :
    ∀ (collected : List Located)
      (values : Values (SideValue model (first.union second))
        (collectedSequencesAt (some total) collected)),
      sideCollectedLists model second collected (rightValues model first second values) =
        rightValues model first second
          (sideCollectedLists model (first.union second) collected values)
  | [], _ => rfl
  | ⟨_, holder⟩ :: rest, .cons sequence values =>
      cons_congr (Held.right_map _ (first holder) (second holder) sequence)
        (sideCollectedLists_right rest values)

theorem sideCollectedSized_left {total count : Nat} (same : total = count) :
    ∀ (collected : List Located)
      (values : Values (SideValue model (first.union second))
        (collectedSequencesAt (some total) collected)),
      sideCollectedSized model first same collected (leftValues model first second values) =
        leftValues model first second
          (sideCollectedSized model (first.union second) same collected values)
  | [], _ => rfl
  | ⟨_, holder⟩ :: rest, .cons sequence values =>
      cons_congr (Held.left_map _ (first holder) (second holder) sequence)
        (sideCollectedSized_left same rest values)

theorem sideCollectedSized_right {total count : Nat} (same : total = count) :
    ∀ (collected : List Located)
      (values : Values (SideValue model (first.union second))
        (collectedSequencesAt (some total) collected)),
      sideCollectedSized model second same collected (rightValues model first second values) =
        rightValues model first second
          (sideCollectedSized model (first.union second) same collected values)
  | [], _ => rfl
  | ⟨_, holder⟩ :: rest, .cons sequence values =>
      cons_congr (Held.right_map _ (first holder) (second holder) sequence)
        (sideCollectedSized_right same rest values)

/-- The loop of a `repeat`: the parts run the same number of iterations and collect their
shares of what the grouped process collects. -/
theorem repeatProcess_together (count : RepeatCount) (carried collected : List Located)
    {wholeStep : Nat → Values (SideValue model (first.union second)) carried →
      PIR.Process (Effects model)
        (Values (SideValue model (first.union second)) (collected ++ carried))}
    {firstStep : Nat → Values (SideValue model first) carried →
      PIR.Process (Effects model) (Values (SideValue model first) (collected ++ carried))}
    {secondStep : Nat → Values (SideValue model second) carried →
      PIR.Process (Effects model) (Values (SideValue model second) (collected ++ carried))}
    (step : ∀ iteration value,
      Together sampler listeners (leftValues model first second) (rightValues model first second)
        (wholeStep iteration value) (firstStep iteration (leftValues model first second value))
        (secondStep iteration (rightValues model first second value)))
    (agreed : Nat) (value : Values (SideValue model (first.union second)) carried) :
    Together sampler listeners (leftValues model first second) (rightValues model first second)
      (repeatProcess model (first.union second) count carried collected wholeStep agreed value)
      (repeatProcess model first count carried collected firstStep agreed
        (leftValues model first second value))
      (repeatProcess model second count carried collected secondStep agreed
        (rightValues model first second value)) := by
  have iterated : ∀ number : Nat,
      Together sampler listeners
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
      exact Together.iterations
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
      refine Together.bind (iterated number) fun final => Together.done ?_ ?_
      · exact (congrArg (fun sequences => Values.append sequences _)
          (sideCollectedSized_left _ collected final.2)).trans (Values.map_append _ _ _).symm
      · exact (congrArg (fun sequences => Values.append sequences _)
          (sideCollectedSized_right _ collected final.2)).trans (Values.map_append _ _ _).symm
  | runtime maximum =>
      show Together sampler listeners _ _
        (if agreed ≤ maximum then PIR.Process.bind _ _ else .halt .undefined)
        (if agreed ≤ maximum then PIR.Process.bind _ _ else .halt .undefined)
        (if agreed ≤ maximum then PIR.Process.bind _ _ else .halt .undefined)
      split
      · refine Together.bind (iterated agreed) fun final => Together.done ?_ ?_
        · exact (congrArg (fun sequences => Values.append sequences _)
            (sideCollectedLists_left collected final.2)).trans (Values.map_append _ _ _).symm
        · exact (congrArg (fun sequences => Values.append sequences _)
            (sideCollectedLists_right collected final.2)).trans (Values.map_append _ _ _).symm
      · exact Together.halt

/-- A loop of a `repeat` whose region returns without an effect returns, unless its count
is a value above the maximum. -/
theorem repeatProcess_idle (side : Side) (count : RepeatCount)
    (carried collected : List Located)
    {step : Nat → Values (SideValue model side) carried →
      PIR.Process (Effects model) (Values (SideValue model side) (collected ++ carried))}
    (idle : ∀ iteration state, ∃ produced, step iteration state = .done produced)
    (agreed : Nat) (initial : Values (SideValue model side) carried) :
    (∃ result, repeatProcess model side count carried collected step agreed initial =
        .done result) ∨
      ∃ maximum, count = .runtime maximum ∧ maximum < agreed := by
  have returns : ∀ number : Nat, ∃ final,
      repeatIterations model side carried collected step number 0 initial
        (sideCollectedNone model side collected) = .done final :=
    fun number => iterations_idle
      (Collected := fun done => Values (SideValue model side)
        (collectedSequencesAt (some done) collected))
      (carry := fun produced => (produced.split collected).2)
      (push := fun _ produced earlier =>
        sideCollectedPush model side collected (produced.split collected).1 earlier)
      idle number 0 initial (sideCollectedNone model side collected)
  cases count with
  | static number =>
      obtain ⟨final, same⟩ := returns number
      exact Or.inl ⟨_, by rw [repeatProcess_static, same]; rfl⟩
  | runtime maximum =>
      by_cases within : agreed ≤ maximum
      · obtain ⟨final, same⟩ := returns agreed
        exact Or.inl ⟨_, by rw [repeatProcess_within model side within, same]; rfl⟩
      · exact Or.inr ⟨maximum, rfl, Nat.not_le.mp within⟩

/-- `repeat`: the parts that have a participant run the iterations that the grouped
process runs; a part without one does nothing. -/
theorem repeat_together (participants : List Nat) (count : RepeatCount)
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
    (related : RegionsTogether sampler listeners first second
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
    Together sampler listeners (leftValues model first second) (rightValues model first second)
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
      Together sampler listeners (leftValues model first second) (rightValues model first second)
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
    Together.congr
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
    repeatProcess_together (sampler := sampler) count carried collected
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
  refine agreed_together nat_beq_decides participants _ _ _
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
    · exact Together.congr rfl
        (returns.trans (congrArg PIR.Process.done
          (outside_values_unique (outside outSecond) _ _))).symm
        both
    · rw [repeatProcess_beyond model _ beyond]
      exact Together.halt
  · have both := together agreed
    rcases repeatProcess_idle first count carried collected
      (step := fun iteration values => (firstPart.get .here)
        ((heldCopies model first .nat iteration participants).append
          (values.append (leftValues model first second captured))))
      (fun iteration value => (idleFirst outFirst).1 _) agreed
      (leftValues model first second initial) with ⟨result, returns⟩ | ⟨maximum, rfl, beyond⟩
    · exact Together.congr
        (returns.trans (congrArg PIR.Process.done
          (outside_values_unique (outside outFirst) _ _))).symm
        rfl both
    · rw [repeatProcess_beyond model _ beyond]
      exact Together.halt

/-- `choose`: the parts that have a participant run the arm that the grouped process
runs; a part without one holds none of the outputs. -/
theorem choose_together (participants : List Nat) (tag : ChoiceTag) (captures outputs : List Located)
    (covered : Located.heldBy participants outputs = true)
    (arguments : Values (SideValue model (first.union second))
      (Located.ofRoles tag.type participants ++ captures))
    (whole : Values (RegionFunction (SideValue model (first.union second)) (Effects model))
      (tag.regions participants captures outputs))
    (firstPart : Values (RegionFunction (SideValue model first) (Effects model))
      (tag.regions participants captures outputs))
    (secondPart : Values (RegionFunction (SideValue model second) (Effects model))
      (tag.regions participants captures outputs))
    (related : RegionsTogether sampler listeners first second (tag.regions participants captures outputs)
      whole firstPart secondPart)
    (idleFirst : participants.any first = false →
      RegionsIdle first (tag.regions participants captures outputs) firstPart)
    (idleSecond : participants.any second = false →
      RegionsIdle second (tag.regions participants captures outputs) secondPart) :
    Together sampler listeners (leftValues model first second) (rightValues model first second)
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
    exact agreed_together agreeBool_decides participants _ _ _ rfl rfl none
      (fun _ _ value => selectArm_together (captures, outputs) 2 whole firstPart secondPart
        related (ChoiceTag.select model.Carrier .condition value) captured)
      (fun _ outSecond value => selectArm_first (captures, outputs)
        (fun one other => outside_values_unique
          (fun _ member => not_held_of_heldBy covered outSecond member) one other)
        2 whole firstPart secondPart related (idleSecond outSecond)
        (ChoiceTag.select model.Carrier .condition value) captured _)
      (fun outFirst _ value => selectArm_second (captures, outputs)
        (fun one other => outside_values_unique
          (fun _ member => not_held_of_heldBy covered outFirst member) one other)
        2 whole firstPart secondPart related (idleFirst outFirst)
        (ChoiceTag.select model.Carrier .condition value) captured _)
  | arm count =>
    rw [copiesFirst, copiesSecond]
    exact agreed_together (ChoiceTag.same_decides model.Carrier (.arm count)) participants _ _ _
      rfl rfl none
      (fun _ _ value => selectArm_together (captures, outputs) count whole firstPart secondPart
        related (ChoiceTag.select model.Carrier (.arm count) value) captured)
      (fun _ outSecond value => selectArm_first (captures, outputs)
        (fun one other => outside_values_unique
          (fun _ member => not_held_of_heldBy covered outSecond member) one other)
        count whole firstPart secondPart related (idleSecond outSecond)
        (ChoiceTag.select model.Carrier (.arm count) value) captured _)
      (fun outFirst _ value => selectArm_second (captures, outputs)
        (fun one other => outside_values_unique
          (fun _ member => not_held_of_heldBy covered outFirst member) one other)
        count whole firstPart secondPart related (idleFirst outFirst)
        (ChoiceTag.select model.Carrier (.arm count) value) captured _)
  | alternative declaration alternatives =>
    -- The participants agree on the number of the alternative; the region of that
    -- alternative takes the payloads that each part holds.
    rw [copiesFirst, copiesSecond]
    exact agreed_together_keyed (alternativeNumber alternatives) nat_beq_decides participants _ _ _
      rfl rfl none
      (fun _ _ number => alternativeProcess_together alternatives whole firstPart secondPart
        related number _ captured)
      (fun _ outSecond number => alternativeProcess_onlyFirst
        (fun one other => outside_values_unique
          (fun _ member => not_held_of_heldBy covered outSecond member) one other)
        alternatives whole firstPart secondPart related (idleSecond outSecond) number _ captured _)
      (fun outFirst _ number => alternativeProcess_onlySecond
        (fun one other => outside_values_unique
          (fun _ member => not_held_of_heldBy covered outFirst member) one other)
        alternatives whole firstPart secondPart related (idleFirst outFirst) number _ captured _)

/-- `apply`: the law for the callee, at the preimages of the two parts. -/
theorem apply_together {listens : ListenTable protocols}
    (sound : TableTogether sampler listeners listens table) (disjoint : first.Disjoint second)
    {header : ProtocolHeader} (callee : Var protocols header) (roleMap : RoleMap) (site : Nat)
    (permitted : (deployed && header.specificationOnly) = false)
    (calleeListens : (listens.get callee) (label site).below (Side.preimage roleMap first)
      (Side.preimage roleMap second))
    (arguments : Values (SideValue model (first.union second))
      (header.inputs.map (Located.rename roleMap)))
    (whole : Values (RegionFunction (SideValue model (first.union second)) (Effects model)) [])
    (firstPart : Values (RegionFunction (SideValue model first) (Effects model)) [])
    (secondPart : Values (RegionFunction (SideValue model second) (Effects model)) []) :
    Together sampler listeners (leftValues model first second) (rightValues model first second)
      (labelledOperation model label functionTable table (first.union second)
        (operations := operations) (.apply callee roleMap site permitted) arguments whole)
      (labelledOperation model label functionTable table first
        (operations := operations) (.apply callee roleMap site permitted)
        (leftValues model first second arguments) firstPart)
      (labelledOperation model label functionTable table second
        (operations := operations) (.apply callee roleMap site permitted)
        (rightValues model first second arguments) secondPart) := by
  have calleeTogether := sound.together callee (label site).below (Side.preimage roleMap first)
    (Side.preimage roleMap second) (fun role => disjoint (roleMap.apply role)) calleeListens
    (unmapValues (F := SideValue model (first.union second)) (Located.rename roleMap) header.inputs
      arguments)
  refine Together.congr ?_ ?_ (Together.bind
    (firstNext := fun values => .done
      (remapValues (F := SideValue model first) (Located.rename roleMap) _ values))
    (secondNext := fun values => .done
      (remapValues (F := SideValue model second) (Located.rename roleMap) _ values))
    calleeTogether fun values =>
    Together.done
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

/-! ## A side without any role of a region -/

theorem roleMap_apply_mem (roleMap : RoleMap) {role : Nat} (below : role < roleMap.length) :
    roleMap.apply role ∈ roleMap := by
  unfold RoleMap.apply
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem below]
  exact List.getElem_mem below

section Idle

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}
  {functionTable : FunctionTable model functions} {table : ProtocolTable model protocols}
  {label : Nat → Site}

/-- An applied protocol does nothing for a side without any of its roles. -/
@[expose] def CalleesIdle (table : ProtocolTable model protocols) : Prop :=
  ∀ {header : ProtocolHeader} (callee : Var protocols header) (path : List Nat) (side : Side),
    (∀ role, role < header.roles → side role = false) →
    ∀ (arguments : Values (SideValue model side) header.inputs),
      ∃ values, (table.get callee) path side arguments = .done values

/-- An operation none of whose roles is in the side returns without an effect. -/
theorem operation_idle (calleesIdle : CalleesIdle table) (side : Side) :
    ∀ (op : ProtocolOp operations functions protocols deployed)
      (bodies : Regions (ProtocolDialect operations functions protocols deployed)
        (ProtocolOp.regions op)),
      (∀ role ∈ ProtocolOp.roles op, side role = false) → opCovers op →
      ∀ (arguments : Values (SideValue model side) (ProtocolOp.arguments op)),
        ∃ results, labelledOperation model label functionTable table side op arguments
          (bodies.denote (labelledMeaning model label functionTable table side)) = .done results
  | .at role op bodies, _, named, _, _ =>
      ⟨_, labelled_at_absent (named role (List.mem_cons_self ..))⟩
  | .exchange sender receiver site type, _, named, _, _ =>
      ⟨_, labelled_exchange_outside (named sender (List.mem_cons_self ..))
        (named receiver (List.mem_cons_of_mem _ (List.mem_cons_self ..)))⟩
  | .draw owner receivers site (output := output) law populated, _, named, _, _ => by
      obtain ⟨replies, returns⟩ := receiverReplies_idle (model := model) side (label site) output
        receivers fun role member => named role (List.mem_cons_of_mem _ member)
      rw [labelled_draw_outside (side := side) (named owner (List.mem_cons_self ..)), returns]
      exact ⟨_, rfl⟩
  | .sample owner site law populated, _, named, _, _ =>
      ⟨_, labelled_sample_outside (named owner (List.mem_cons_self ..))⟩
  | .repeat participants count carried collected captures covered, .cons body .nil, named, _, _ =>
      ⟨_, labelled_repeat_meaning.trans (agreed_none Nat.beq side _ _ participants _ _ named)⟩
  | .choose participants tag captures outputs covered, _, named, _, _ =>
      ⟨_, labelled_choose_meaning.trans
        (agreed_none (tag.same model.Carrier) side _ _ participants _ _ named)⟩
  | .apply (header := header) callee roleMap site permitted, _, named, covers, arguments => by
      obtain ⟨values, returns⟩ := calleesIdle callee (label site).below (Side.preimage roleMap side)
        (fun role below => named _ (roleMap_apply_mem roleMap (Nat.lt_of_lt_of_le below covers)))
        (unmapValues (F := SideValue model side) (Located.rename roleMap) _ arguments)
      rw [labelled_apply_meaning, returns]
      exact ⟨_, rfl⟩

/-- A region none of whose roles is in the side returns without an effect. -/
theorem region_idle (calleesIdle : CalleesIdle table) (side : Side) (roles : List Nat)
    (absent : ∀ role ∈ roles, side role = false) {Γ out : List Located} :
    ∀ (region : Region (ProtocolDialect operations functions protocols deployed) Γ out),
      regionWithin roles region →
      ∀ (env : Environment (SideValue model side) Γ),
        ∃ values, region.denote (labelledMeaning model label functionTable table side) env =
          .done values
  | .ret _, _, _ => ⟨_, rfl⟩
  | .stop _, within, _ => within.elim
  | .bind body rest, within, env => by
      obtain ⟨values, returns⟩ := region_idle calleesIdle side roles absent body within.1 env
      obtain ⟨results, continues⟩ := region_idle calleesIdle side roles absent rest within.2
        (Environment.bindAll env values)
      refine ⟨results, ?_⟩
      have unfolded : (Region.bind body rest).denote
            (labelledMeaning model label functionTable table side) env =
          (body.denote (labelledMeaning model label functionTable table side) env).bind fun values =>
            rest.denote (labelledMeaning model label functionTable table side)
              (Environment.bindAll env values) := rfl
      rw [unfolded, returns]
      exact continues
  | .letOp op arguments bodies rest, within, env => by
      obtain ⟨results, step⟩ := operation_idle (label := label) (functionTable := functionTable)
        calleesIdle side op bodies (fun role member => absent role (within.1 role member))
        within.2.1 (Operands.eval env arguments)
      obtain ⟨values, continues⟩ := region_idle calleesIdle side roles absent rest within.2.2
        (Environment.bindAll env results)
      exact ⟨values, (labelled_step_done step).trans continues⟩

/-- Nested regions none of whose roles is in the side return without an effect. -/
theorem regions_idle (calleesIdle : CalleesIdle table) (side : Side) (roles : List Nat)
    (absent : ∀ role ∈ roles, side role = false) :
    ∀ {signatures : List (List Located × List Located)}
      (regions : Regions (ProtocolDialect operations functions protocols deployed) signatures),
      regionsWithin roles regions →
        RegionsIdle side signatures
          (regions.denote (labelledMeaning model label functionTable table side))
  | _, .nil, _ => trivial
  | _, .cons body tail, within =>
      ⟨fun _ => region_idle calleesIdle side roles absent body within.1 _,
        regions_idle calleesIdle side roles absent tail within.2⟩

end Idle

/-! ## Regions, definitions and programs -/

section Regions

variable {model : Model} {sampler : Sampler model} {listeners : Listeners} {operations : List OperationSignature}
  {functions : List FunctionHeader} {protocols : List ProtocolHeader} {deployed : Bool}
  {functionTable : FunctionTable model functions} {table : ProtocolTable model protocols}
  {label : Nat → Site} {first second : Side} {listens : ListenTable protocols}

/-- One operation followed by the rest of its region. -/
theorem letOp_together {Γ out : List Located}
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
    (operation : Together sampler listeners (leftValues model first second) (rightValues model first second)
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
      Together sampler listeners (leftValues model first second) (rightValues model first second)
        (rest.denote (labelledMeaning model label functionTable table (first.union second))
          (Environment.bindAll env values))
        (rest.denote (labelledMeaning model label functionTable table first)
          (Environment.bindAll envFirst (leftValues model first second values)))
        (rest.denote (labelledMeaning model label functionTable table second)
          (Environment.bindAll envSecond (rightValues model first second values)))) :
    Together sampler listeners (leftValues model first second) (rightValues model first second)
      ((Region.letOp (dialect := ProtocolDialect operations functions protocols deployed) op
        arguments bodies rest).denote
        (labelledMeaning model label functionTable table (first.union second)) env)
      ((Region.letOp (dialect := ProtocolDialect operations functions protocols deployed) op
        arguments bodies rest).denote (labelledMeaning model label functionTable table first)
        envFirst)
      ((Region.letOp (dialect := ProtocolDialect operations functions protocols deployed) op
        arguments bodies rest).denote (labelledMeaning model label functionTable table second)
        envSecond) :=
  Together.bind
    (Together.congr
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

mutual
  /-- The restriction law for a region: the process of a union of two disjoint sides and
  the processes of the two sides, in environments that hold the two sides' shares. -/
  theorem region_together (quiet : QuietTable functionTable)
      (sound : TableTogether sampler listeners listens table) (disjoint : first.Disjoint second)
      {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions protocols deployed) Γ out),
        regionEnclosed region → regionListens listeners label listens first second region →
        ∀ (env : Environment (SideValue model (first.union second)) Γ)
          (envFirst : Environment (SideValue model first) Γ)
          (envSecond : Environment (SideValue model second) Γ),
          Restricts (fun {located} value => restrictLeft model first second (located := located)
            value) env envFirst →
          Restricts (fun {located} value => restrictRight model first second (located := located)
            value) env envSecond →
            Together sampler listeners (leftValues model first second) (rightValues model first second)
              (region.denote (labelledMeaning model label functionTable table (first.union second))
                env)
              (region.denote (labelledMeaning model label functionTable table first) envFirst)
              (region.denote (labelledMeaning model label functionTable table second) envSecond)
    | .ret values, _, _, _, _, _, isLeft, isRight =>
        Together.done (isLeft.eval values) (isRight.eval values)
    | .stop _, _, _, _, _, _, _, _ => Together.halt
    | .bind body rest, enclosed, heard, env, envFirst, envSecond, isLeft, isRight =>
        Together.bind
          (region_together quiet sound disjoint body enclosed.1 heard.1 env envFirst envSecond isLeft
            isRight)
          fun values => region_together quiet sound disjoint rest enclosed.2 heard.2 _ _ _
            (isLeft.bindAll values) (isRight.bindAll values)
    | .letOp (.at role op bodies) arguments nested rest, enclosed, heard, env, envFirst, envSecond,
        isLeft, isRight =>
        letOp_together _ arguments nested rest env envFirst envSecond isLeft isRight
          (at_together quiet disjoint role op bodies _ _ _ _)
          fun values => region_together quiet sound disjoint rest enclosed.2.2 heard.2.2 _ _ _
            (isLeft.bindAll values) (isRight.bindAll values)
    | .letOp (.exchange sender receiver site type) arguments nested rest, enclosed, heard, env,
        envFirst, envSecond, isLeft, isRight =>
        letOp_together _ arguments nested rest env envFirst envSecond isLeft isRight
          (exchange_together disjoint sender receiver site type _ _ _ _)
          fun values => region_together quiet sound disjoint rest enclosed.2.2 heard.2.2 _ _ _
            (isLeft.bindAll values) (isRight.bindAll values)
    | .letOp (.draw owner receivers site law populated) arguments nested rest, enclosed, heard, env,
        envFirst, envSecond, isLeft, isRight =>
        letOp_together _ arguments nested rest env envFirst envSecond isLeft isRight
          (draw_together disjoint owner receivers site law populated heard.1.1 heard.1.2.1
            heard.1.2.2.1 heard.1.2.2.2 _ _ _ _)
          fun values => region_together quiet sound disjoint rest enclosed.2.2 heard.2.2 _ _ _
            (isLeft.bindAll values) (isRight.bindAll values)
    | .letOp (.sample owner site law populated) arguments nested rest, enclosed, heard, env, envFirst, envSecond,
        isLeft, isRight =>
        letOp_together _ arguments nested rest env envFirst envSecond isLeft isRight
          (sample_together disjoint owner site law populated _ _ _ _)
          fun values => region_together quiet sound disjoint rest enclosed.2.2 heard.2.2 _ _ _
            (isLeft.bindAll values) (isRight.bindAll values)
    | .letOp (.repeat participants count carried collected captures covered) arguments
        (.cons body .nil) rest,
        enclosed, heard, env, envFirst, envSecond, isLeft, isRight =>
        letOp_together (.repeat participants count carried collected captures covered) arguments
          (.cons body .nil) rest env envFirst envSecond isLeft isRight
          (repeat_together participants count carried collected captures covered enclosed.1.1
            (Operands.eval env arguments)
            ((Regions.cons body .nil).denote
              (labelledMeaning model label functionTable table (first.union second)))
            ((Regions.cons body .nil).denote (labelledMeaning model label functionTable table first))
            ((Regions.cons body .nil).denote (labelledMeaning model label functionTable table second))
            ⟨fun values => region_together quiet sound disjoint body enclosed.2.1.1 heard.2.1.1 _ _ _
              (Restricts.ofValues values) (Restricts.ofValues values), trivial⟩
            (fun outFirst =>
              (⟨fun values => region_idle (label := label) (functionTable := functionTable)
                  sound.idle first participants (absent_of_any outFirst) body enclosed.1.2.1
                  (Environment.ofValues values), trivial⟩ :
                RegionsIdle first [(Located.ofRoles .nat participants ++ (carried ++ captures), collected ++ carried)]
                  ((Regions.cons body .nil).denote
                    (labelledMeaning model label functionTable table first))))
            (fun outSecond =>
              (⟨fun values => region_idle (label := label) (functionTable := functionTable)
                  sound.idle second participants (absent_of_any outSecond) body enclosed.1.2.1
                  (Environment.ofValues values), trivial⟩ :
                RegionsIdle second [(Located.ofRoles .nat participants ++ (carried ++ captures), collected ++ carried)]
                  ((Regions.cons body .nil).denote
                    (labelledMeaning model label functionTable table second)))))
          fun values => region_together quiet sound disjoint rest enclosed.2.2 heard.2.2 _ _ _
            (isLeft.bindAll values) (isRight.bindAll values)
    | .letOp (.choose participants tag captures outputs covered) arguments bodies rest, enclosed,
        heard, env, envFirst, envSecond, isLeft, isRight =>
        letOp_together _ arguments bodies rest env envFirst envSecond isLeft isRight
          (choose_together participants tag captures outputs covered _ _ _ _
            (regions_together quiet sound disjoint bodies enclosed.2.1 heard.2.1)
            (fun outFirst => regions_idle sound.idle first participants (absent_of_any outFirst)
              bodies enclosed.1)
            (fun outSecond => regions_idle sound.idle second participants (absent_of_any outSecond)
              bodies enclosed.1))
          fun values => region_together quiet sound disjoint rest enclosed.2.2 heard.2.2 _ _ _
            (isLeft.bindAll values) (isRight.bindAll values)
    | .letOp (.apply callee roleMap site permitted) arguments nested rest, enclosed, heard, env,
        envFirst, envSecond, isLeft, isRight =>
        letOp_together _ arguments nested rest env envFirst envSecond isLeft isRight
          (apply_together sound disjoint callee roleMap site permitted heard.1 _ _ _ _)
          fun values => region_together quiet sound disjoint rest enclosed.2.2 heard.2.2 _ _ _
            (isLeft.bindAll values) (isRight.bindAll values)

  /-- The restriction law for nested regions. -/
  theorem regions_together (quiet : QuietTable functionTable)
      (sound : TableTogether sampler listeners listens table) (disjoint : first.Disjoint second)
      {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions protocols deployed) signatures),
        regionsEnclosed regions → regionsListens listeners label listens first second regions →
          RegionsTogether sampler listeners first second signatures
            (regions.denote (labelledMeaning model label functionTable table (first.union second)))
            (regions.denote (labelledMeaning model label functionTable table first))
            (regions.denote (labelledMeaning model label functionTable table second))
    | .nil, _, _ => trivial
    | .cons body tail, enclosed, heard =>
        ⟨fun values => region_together quiet sound disjoint body enclosed.1 heard.1 _ _ _
            (Restricts.ofValues values) (Restricts.ofValues values),
          regions_together quiet sound disjoint tail enclosed.2 heard.2⟩
end

end Regions

end Zkc.Core
