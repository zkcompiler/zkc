module

public import Zkc.Core.SerializeReplayControl

public section

/-! The replay relation over the operations of a protocol, and over a region.

For every operation without a nested region the grouped process and the two parts under
their handlers are related (`PartsReplay`), by cases on the memberships of the roles
involved. What a handler does at an operation is a premise of each statement, so the
statements serve a region that the serialize step threads and a region that it copies.

- `at_replays`: local work is performed by the part that has the role; it performs no
  effect, so every handler passes it.
- `sample_replays`: the owner's part samples, when its handler passes the sample.
- `exchange_replays`: an exchange within one part is no effect in any of the three
  processes; an exchange to or from a role outside both parts is an effect of the grouped
  process, of which no run returns; an exchange from the prover's part to the verifier's is
  the premise `forward`; an exchange from the verifier's part to the prover's is excluded by
  the premise `backward`.
- `draw_replays`: the owner's part draws, when its handler passes the draw and no receiver
  is in the other part; a draw whose owner is outside both parts is announced to a receiver
  in a part, and no run of the grouped process returns.
- `RegionAdmits`, `region_replays`: a region all of whose operations are related, on all
  arguments, is related in environments that hold the two parts' shares.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Zkc.Core

open Zkc.Source

section Steps

variable {model : Model} {Writer Reader : Type} {channel : Channel model Writer Reader}
  {proverHandler : PIR.StatefulInterpretation (Effects model) (Effects model) Writer}
  {verifierHandler : PIR.StatefulInterpretation (Effects model) (Effects model) Reader}

/-- `at`: the part that has the role performs the operation, which performs no effect. -/
theorem performStep_replays {inputs outputs : List Ty}
    (run : Values model.Value inputs → PIR.Process (Effects model) (Values model.Value outputs))
    (quiet : ∀ arguments, (run arguments).Quiet) :
    ∀ (first second : Bool), (first && second) = false →
    ∀ (arguments : Values (fun type => Held (model.Value type) (first || second)) inputs),
      PartsReplay channel proverHandler verifierHandler
        (Values.map (fun {type} value => Held.left (X := model.Value type) first second value))
        (Values.map (fun {type} value => Held.right (X := model.Value type) first second value))
        (performStep model run (first || second) arguments)
        (performStep model run first
          (arguments.map (fun {type} value => Held.left (X := model.Value type) first second value)))
        (performStep model run second
          (arguments.map (fun {type} value => Held.right (X := model.Value type) first second value)))
  | true, true, both, _ => Bool.noConfusion both
  | true, false, _, arguments =>
      PartsReplay.congr (congrArg run (map_left_present false arguments)) rfl
        (PartsReplay.proverMirrors (Mirrors.refl (map_left_present false) (run arguments))
          ((quiet arguments).passes _) fun _ => absent_values_unique _ _)
  | false, true, _, arguments =>
      PartsReplay.congr rfl (congrArg run (map_right_present arguments))
        (PartsReplay.verifierMirrors (Mirrors.refl map_right_present (run arguments))
          ((quiet arguments).passes _) fun _ => absent_values_unique _ _)
  | false, false, _, _ => PartsReplay.done (absent_values_unique _ _) (absent_values_unique _ _)

/-- `exchange` that is not from the prover's part to the verifier's: no effect within one
part; to or from a role outside both, no run of the grouped process returns. -/
theorem exchangeStep_replays (site : Site) (type : Ty) :
    ∀ (senderFirst senderSecond receiverFirst receiverSecond : Bool),
      (senderFirst && senderSecond) = false → (receiverFirst && receiverSecond) = false →
      ¬(senderFirst = true ∧ receiverSecond = true) →
      ¬(senderSecond = true ∧ receiverFirst = true) →
      ∀ (value : Held (model.Value type) (senderFirst || senderSecond)),
        PartsReplay channel proverHandler verifierHandler (Held.left receiverFirst receiverSecond)
          (Held.right receiverFirst receiverSecond)
          (exchangeStep model site type (senderFirst || senderSecond)
            (receiverFirst || receiverSecond) value)
          (exchangeStep model site type senderFirst receiverFirst
            (Held.left senderFirst senderSecond value))
          (exchangeStep model site type senderSecond receiverSecond
            (Held.right senderFirst senderSecond value))
  | true, true, _, _, both, _, _, _, _ => Bool.noConfusion both
  | _, _, true, true, _, both, _, _, _ => Bool.noConfusion both
  | true, false, true, false, _, _, _, _, _ => PartsReplay.done rfl rfl
  | false, true, false, true, _, _, _, _, _ => PartsReplay.done rfl rfl
  | false, false, false, false, _, _, _, _, _ => PartsReplay.done rfl rfl
  | true, false, false, true, _, _, forward, _, _ => (forward ⟨rfl, rfl⟩).elim
  | false, true, true, false, _, _, _, backward, _ => (backward ⟨rfl, rfl⟩).elim
  | true, false, false, false, _, _, _, _, _ => PartsReplay.send
  | false, true, false, false, _, _, _, _, _ => PartsReplay.send
  | false, false, true, false, _, _, _, _, _ => PartsReplay.receive
  | false, false, false, true, _, _, _, _, _ => PartsReplay.receive

end Steps

section Leaves

variable {model : Model} {Writer Reader : Type} {channel : Channel model Writer Reader}
  {proverHandler : PIR.StatefulInterpretation (Effects model) (Effects model) Writer}
  {verifierHandler : PIR.StatefulInterpretation (Effects model) (Effects model) Reader}
  {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}
  {functionTable : FunctionTable model functions} {table : ProtocolTable model protocols}
  {label : Nat → Site} {first second : Side}

/-- Local work of one role. -/
theorem at_replays (quiet : QuietTable functionTable) (disjoint : first.Disjoint second) (role : Nat)
    (op : LocalOp operations functions deployed)
    (bodies : Regions (LocalDialect operations functions deployed) op.regions)
    (arguments : Values (SideValue model (first.union second)) (Located.atRole role op.arguments))
    (whole : Values (RegionFunction (SideValue model (first.union second)) (Effects model)) [])
    (firstPart : Values (RegionFunction (SideValue model first) (Effects model)) [])
    (secondPart : Values (RegionFunction (SideValue model second) (Effects model)) []) :
    PartsReplay channel proverHandler verifierHandler (leftValues model first second) (rightValues model first second)
      (labelledOperation model label functionTable table (first.union second) (.at role op bodies)
        arguments whole)
      (labelledOperation model label functionTable table first (.at role op bodies)
        (leftValues model first second arguments) firstPart)
      (labelledOperation model label functionTable table second (.at role op bodies)
        (rightValues model first second arguments) secondPart) := by
  have step := performStep_replays (channel := channel) (proverHandler := proverHandler) (verifierHandler := verifierHandler)
    (fun values => localOperation model functionTable op values
      (bodies.denote (localMeaning model functionTable)))
    (fun values => localOperation_quiet quiet op values _ (localRegions_quiet quiet bodies))
    (first role) (second role) (disjoint role)
    (unmapValues (F := SideValue model (first.union second)) (fun type => ⟨type, role⟩) _ arguments)
  refine PartsReplay.congr ?_ ?_ (PartsReplay.bind
    (proverNext := fun values => .done
      (remapValues (F := SideValue model first) (fun type => ⟨type, role⟩) _ values))
    (verifierNext := fun values => .done
      (remapValues (F := SideValue model second) (fun type => ⟨type, role⟩) _ values))
    step fun values =>
    PartsReplay.done
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
/-- An announcement from outside both parts: the grouped process waits for it and does
not return alone, unless no receiver is in either part. -/
theorem receiverReplies_replays (site : Site) (type : Ty) :
    ∀ (receivers : List Nat),
      PartsReplay channel proverHandler verifierHandler (leftValues model first second) (rightValues model first second)
        (receiverReplies model (first.union second) site type receivers)
        (receiverReplies model first site type receivers)
        (receiverReplies model second site type receivers)
  | [] => PartsReplay.done rfl rfl
  | role :: rest => by
      rcases Bool.eq_false_or_eq_true (first role) with inFirst | outFirst
      · rw [receiverReplies_present model (first.union second) site type role rest
          (union_first inFirst)]
        exact PartsReplay.receive
      · rcases Bool.eq_false_or_eq_true (second role) with inSecond | outSecond
        · rw [receiverReplies_present model (first.union second) site type role rest
            (union_second inSecond)]
          exact PartsReplay.receive
        · rw [receiverReplies_absent model (first.union second) site type role rest
              (union_neither outFirst outSecond),
            receiverReplies_absent model first site type role rest outFirst,
            receiverReplies_absent model second site type role rest outSecond]
          exact PartsReplay.bind (receiverReplies_replays site type rest) fun replies =>
            PartsReplay.done
              (congrArg
                (fun head => Values.cons (Value := SideValue model first) (ty := ⟨type, role⟩) head
                  (leftValues model first second replies))
                (Held.absent_unique (first role) outFirst _ _))
              (congrArg
                (fun head => Values.cons (Value := SideValue model second) (ty := ⟨type, role⟩) head
                  (rightValues model first second replies))
                (Held.absent_unique (second role) outSecond _ _))

/-- A message from one role to another. An exchange from the prover's part to the
verifier's is related by the premise; one from the verifier's part to the prover's does not
occur. -/
theorem exchange_replays (disjoint : first.Disjoint second) (sender receiver site : Nat)
    (type : Ty)
    (forward : first sender = true → second receiver = true →
      ∀ (arguments : Values (SideValue model (first.union second)) [⟨type, sender⟩]),
        PartsReplay channel proverHandler verifierHandler (leftValues model first second)
          (rightValues model first second)
          (labelledOperation model label functionTable table (first.union second)
            (operations := operations) (deployed := deployed) (.exchange sender receiver site type)
            arguments .nil)
          (labelledOperation model label functionTable table first
            (operations := operations) (deployed := deployed) (.exchange sender receiver site type)
            (leftValues model first second arguments) .nil)
          (labelledOperation model label functionTable table second
            (operations := operations) (deployed := deployed) (.exchange sender receiver site type)
            (rightValues model first second arguments) .nil))
    (backward : ¬(second sender = true ∧ first receiver = true))
    (arguments : Values (SideValue model (first.union second)) [⟨type, sender⟩])
    (whole : Values (RegionFunction (SideValue model (first.union second)) (Effects model)) [])
    (firstPart : Values (RegionFunction (SideValue model first) (Effects model)) [])
    (secondPart : Values (RegionFunction (SideValue model second) (Effects model)) []) :
    PartsReplay channel proverHandler verifierHandler (leftValues model first second)
      (rightValues model first second)
      (labelledOperation model label functionTable table (first.union second)
        (operations := operations) (deployed := deployed) (.exchange sender receiver site type)
        arguments whole)
      (labelledOperation model label functionTable table first
        (operations := operations) (deployed := deployed) (.exchange sender receiver site type)
        (leftValues model first second arguments) firstPart)
      (labelledOperation model label functionTable table second
        (operations := operations) (deployed := deployed) (.exchange sender receiver site type)
        (rightValues model first second arguments) secondPart) := by
  cases whole
  cases firstPart
  cases secondPart
  by_cases between : first sender = true ∧ second receiver = true
  · exact forward between.1 between.2 arguments
  · have step := exchangeStep_replays (channel := channel) (proverHandler := proverHandler)
      (verifierHandler := verifierHandler) (label site) type (first sender)
      (second sender) (first receiver) (second receiver) (disjoint sender) (disjoint receiver)
      between backward (arguments.get .here)
    refine PartsReplay.congr ?_ ?_ (PartsReplay.bind
      (proverNext := fun result => .done
        (Values.cons (Value := SideValue model first) (ty := ⟨type, receiver⟩) result .nil))
      (verifierNext := fun result => .done
        (Values.cons (Value := SideValue model second) (ty := ⟨type, receiver⟩) result .nil))
      step fun result => PartsReplay.done rfl rfl)
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

/-- A secret sample of one role: the owner's part samples, when its handler passes the
sample. -/
theorem sample_replays (disjoint : first.Disjoint second) (owner site : Nat) {inputs : List Ty}
    {output : Ty} (law : Var operations ⟨inputs, [output], .sampling⟩)
    (populated : output.populated = true)
    (passesProver : first owner = true →
      ∀ arguments : Values (SideValue model first) (Located.atRole owner inputs),
        PIR.Passes proverHandler
          (labelledOperation model label functionTable table first (deployed := deployed)
            (.sample owner site law populated) arguments .nil))
    (passesVerifier : second owner = true →
      ∀ arguments : Values (SideValue model second) (Located.atRole owner inputs),
        PIR.Passes verifierHandler
          (labelledOperation model label functionTable table second (deployed := deployed)
            (.sample owner site law populated) arguments .nil))
    (arguments : Values (SideValue model (first.union second)) (Located.atRole owner inputs))
    (whole : Values (RegionFunction (SideValue model (first.union second)) (Effects model)) [])
    (firstPart : Values (RegionFunction (SideValue model first) (Effects model)) [])
    (secondPart : Values (RegionFunction (SideValue model second) (Effects model)) []) :
    PartsReplay channel proverHandler verifierHandler (leftValues model first second)
      (rightValues model first second)
      (labelledOperation model label functionTable table (first.union second) (deployed := deployed)
        (.sample owner site law populated) arguments whole)
      (labelledOperation model label functionTable table first (deployed := deployed)
        (.sample owner site law populated) (leftValues model first second arguments) firstPart)
      (labelledOperation model label functionTable table second (deployed := deployed)
        (.sample owner site law populated) (rightValues model first second arguments) secondPart) := by
  cases whole
  cases firstPart
  cases secondPart
  rcases Bool.eq_false_or_eq_true (first owner) with inFirst | outFirst
  · have outSecond := disjoint.second_absent inFirst
    have passes := passesProver inFirst (leftValues model first second arguments)
    rw [labelled_sample_owner (side := first) inFirst] at passes
    rw [labelled_sample_owner (side := first.union second) (union_first inFirst),
      labelled_sample_owner (side := first) inFirst,
      labelled_sample_outside (side := second) outSecond]
    exact PartsReplay.proverMirrors
      (.sample fun reply => .done
        (congrArg (fun head => Values.cons (Value := SideValue model first) (ty := ⟨output, owner⟩)
            head .nil)
          (Held.left_of (X := model.Value output) (first owner) (second owner) reply).symm))
      passes
      fun value => outside_values_unique
        (fun located member => by rw [List.mem_singleton.mp member]; exact outSecond) _ _
  · rcases Bool.eq_false_or_eq_true (second owner) with inSecond | outSecond
    · have passes := passesVerifier inSecond (rightValues model first second arguments)
      rw [labelled_sample_owner (side := second) inSecond] at passes
      rw [labelled_sample_owner (side := first.union second) (union_second inSecond),
        labelled_sample_owner (side := second) inSecond,
        labelled_sample_outside (side := first) outFirst]
      exact PartsReplay.verifierMirrors
        (.sample fun reply => .done
          (congrArg (fun head => Values.cons (Value := SideValue model second)
              (ty := ⟨output, owner⟩) head .nil)
            (Held.right_of (X := model.Value output) (first owner) (second owner) reply).symm))
        passes
        fun value => outside_values_unique
          (fun located member => by rw [List.mem_singleton.mp member]; exact outFirst) _ _
    · rw [labelled_sample_outside (side := first.union second) (union_neither outFirst outSecond),
        labelled_sample_outside (side := first) outFirst,
        labelled_sample_outside (side := second) outSecond]
      exact PartsReplay.done
        (congrArg (fun head => Values.cons (Value := SideValue model first) (ty := ⟨output, owner⟩)
            head .nil) (Held.absent_unique (first owner) outFirst _ _))
        (congrArg (fun head => Values.cons (Value := SideValue model second) (ty := ⟨output, owner⟩)
            head .nil) (Held.absent_unique (second owner) outSecond _ _))

/-- The results of a draw are held by the owner and the receivers. -/
theorem draw_results_outside {side : Side} {owner : Nat} {receivers : List Nat} (output : Ty)
    (ownerOutside : side owner = false) (receiversOutside : ∀ receiver ∈ receivers, side receiver = false) :
    ∀ located ∈ (⟨output, owner⟩ : Located) :: Located.ofRoles output receivers,
      side located.holder = false := by
  intro located member
  rcases List.mem_cons.mp member with rfl | later
  · exact ownerOutside
  · obtain ⟨receiver, inside, rfl⟩ := List.mem_map.mp later
    exact receiversOutside receiver inside

/-- A public coin: the owner's part draws, when its handler passes the draw and no receiver
is in the other part. A draw whose owner is outside both parts is announced. -/
theorem draw_replays (disjoint : first.Disjoint second) (owner : Nat) (receivers : List Nat)
    (site : Nat) {inputs : List Ty} {output : Ty}
    (law : Var operations ⟨inputs, [output], .sampling⟩) (populated : output.populated = true)
    (passesProver : first owner = true →
      ∀ arguments : Values (SideValue model first) (Located.atRole owner inputs),
        PIR.Passes proverHandler
          (labelledOperation model label functionTable table first (deployed := deployed)
            (.draw owner receivers site law populated) arguments .nil))
    (passesVerifier : second owner = true →
      ∀ arguments : Values (SideValue model second) (Located.atRole owner inputs),
        PIR.Passes verifierHandler
          (labelledOperation model label functionTable table second (deployed := deployed)
            (.draw owner receivers site law populated) arguments .nil))
    (apartProver : first owner = true → ∀ receiver ∈ receivers, second receiver = false)
    (apartVerifier : second owner = true → ∀ receiver ∈ receivers, first receiver = false)
    (arguments : Values (SideValue model (first.union second)) (Located.atRole owner inputs))
    (whole : Values (RegionFunction (SideValue model (first.union second)) (Effects model)) [])
    (firstPart : Values (RegionFunction (SideValue model first) (Effects model)) [])
    (secondPart : Values (RegionFunction (SideValue model second) (Effects model)) []) :
    PartsReplay channel proverHandler verifierHandler (leftValues model first second)
      (rightValues model first second)
      (labelledOperation model label functionTable table (first.union second) (deployed := deployed)
        (.draw owner receivers site law populated) arguments whole)
      (labelledOperation model label functionTable table first (deployed := deployed)
        (.draw owner receivers site law populated) (leftValues model first second arguments) firstPart)
      (labelledOperation model label functionTable table second (deployed := deployed)
        (.draw owner receivers site law populated) (rightValues model first second arguments) secondPart) := by
  cases whole
  cases firstPart
  cases secondPart
  rcases Bool.eq_false_or_eq_true (first owner) with inFirst | outFirst
  · have outSecond := disjoint.second_absent inFirst
    obtain ⟨replies, idle⟩ := receiverReplies_idle (model := model) second (label site) output
      receivers (apartProver inFirst)
    have passes := passesProver inFirst (leftValues model first second arguments)
    rw [labelled_draw_owner (side := first) inFirst] at passes
    rw [labelled_draw_owner (side := first.union second) (union_first inFirst),
      labelled_draw_owner (side := first) inFirst, labelled_draw_outside (side := second) outSecond,
      idle]
    exact PartsReplay.proverMirrors
      (.draw fun reply => .done (broadcast_left owner receivers output reply).symm) passes
      fun value => outside_values_unique
        (draw_results_outside output outSecond (apartProver inFirst)) _ _
  · rcases Bool.eq_false_or_eq_true (second owner) with inSecond | outSecond
    · obtain ⟨replies, idle⟩ := receiverReplies_idle (model := model) first (label site) output
        receivers (apartVerifier inSecond)
      have passes := passesVerifier inSecond (rightValues model first second arguments)
      rw [labelled_draw_owner (side := second) inSecond] at passes
      rw [labelled_draw_owner (side := first.union second) (union_second inSecond),
        labelled_draw_owner (side := second) inSecond,
        labelled_draw_outside (side := first) outFirst, idle]
      exact PartsReplay.verifierMirrors
        (.draw fun reply => .done (broadcast_right owner receivers output reply).symm) passes
        fun value => outside_values_unique
          (draw_results_outside output outFirst (apartVerifier inSecond)) _ _
    · rw [labelled_draw_outside (side := first.union second) (union_neither outFirst outSecond),
        labelled_draw_outside (side := first) outFirst,
        labelled_draw_outside (side := second) outSecond]
      exact PartsReplay.bind (receiverReplies_replays (label site) output receivers) fun replies =>
        PartsReplay.done
          (congrArg
            (fun head => Values.cons (Value := SideValue model first) (ty := ⟨output, owner⟩) head
              (leftValues model first second replies))
            (Held.absent_unique (first owner) outFirst _ _))
          (congrArg
            (fun head => Values.cons (Value := SideValue model second) (ty := ⟨output, owner⟩) head
              (rightValues model first second replies))
            (Held.absent_unique (second owner) outSecond _ _))

end Leaves

/-! ## Regions -/

section Regions

variable {model : Model} {Writer Reader : Type} (channel : Channel model Writer Reader)
  (proverHandler : PIR.StatefulInterpretation (Effects model) (Effects model) Writer)
  (verifierHandler : PIR.StatefulInterpretation (Effects model) (Effects model) Reader)
  {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}
  (functionTable : FunctionTable model functions) (table : ProtocolTable model protocols)
  (label : Nat → Site) (first second : Side)

/-- The three processes of an operation, the grouped one and the two parts under their
handlers, are related on all arguments. -/
@[expose] def OperationReplays (op : ProtocolOp operations functions protocols deployed)
    (bodies : Regions (ProtocolDialect operations functions protocols deployed)
      (ProtocolOp.regions op)) : Prop :=
  ∀ arguments : Values (SideValue model (first.union second)) (ProtocolOp.arguments op),
    PartsReplay channel proverHandler verifierHandler (leftValues model first second)
      (rightValues model first second)
      (labelledOperation model label functionTable table (first.union second) op arguments
        (bodies.denote (labelledMeaning model label functionTable table (first.union second))))
      (labelledOperation model label functionTable table first op
        (leftValues model first second arguments)
        (bodies.denote (labelledMeaning model label functionTable table first)))
      (labelledOperation model label functionTable table second op
        (rightValues model first second arguments)
        (bodies.denote (labelledMeaning model label functionTable table second)))

/-- Every operation of the region, outside its nested regions, is related. -/
@[expose] def RegionAdmits {Γ out : List Located} :
    Region (ProtocolDialect operations functions protocols deployed) Γ out → Prop
  | .ret _ => True
  | .stop _ => True
  | .bind body rest => RegionAdmits body ∧ RegionAdmits rest
  | .letOp op _ bodies rest =>
      OperationReplays channel proverHandler verifierHandler functionTable table label first second
        op bodies ∧ RegionAdmits rest

/-- Every operation of each of several closed regions is related. -/
@[expose] def RegionsAdmit {signatures : List (List Located × List Located)} :
    Regions (ProtocolDialect operations functions protocols deployed) signatures → Prop
  | .nil => True
  | .cons body tail =>
      RegionAdmits channel proverHandler verifierHandler functionTable table label first second
        body ∧ RegionsAdmit tail

variable {channel} {proverHandler} {verifierHandler} {functionTable} {table} {label} {first}
  {second}

/-- A region whose operations are related: the process of the union of the two parts and
the processes of the two parts under their handlers, in environments that hold the two
parts' shares. -/
theorem region_replays {Γ out : List Located} :
    ∀ (region : Region (ProtocolDialect operations functions protocols deployed) Γ out),
      RegionAdmits channel proverHandler verifierHandler functionTable table label first second
        region →
      ∀ (env : Environment (SideValue model (first.union second)) Γ)
        (envFirst : Environment (SideValue model first) Γ)
        (envSecond : Environment (SideValue model second) Γ),
        Restricts (fun {located} value => restrictLeft model first second (located := located)
          value) env envFirst →
        Restricts (fun {located} value => restrictRight model first second (located := located)
          value) env envSecond →
          PartsReplay channel proverHandler verifierHandler (leftValues model first second)
            (rightValues model first second)
            (region.denote (labelledMeaning model label functionTable table (first.union second))
              env)
            (region.denote (labelledMeaning model label functionTable table first) envFirst)
            (region.denote (labelledMeaning model label functionTable table second) envSecond)
  | .ret values, _, _, _, _, isLeft, isRight =>
      PartsReplay.done (isLeft.eval values) (isRight.eval values)
  | .stop _, _, _, _, _, _, _ => PartsReplay.halt
  | .bind body rest, admits, env, envFirst, envSecond, isLeft, isRight =>
      PartsReplay.bind (region_replays body admits.1 env envFirst envSecond isLeft isRight)
        fun values => region_replays rest admits.2 _ _ _ (isLeft.bindAll values)
          (isRight.bindAll values)
  | .letOp op arguments bodies rest, admits, env, envFirst, envSecond, isLeft, isRight =>
      letOp_replays op arguments bodies rest env envFirst envSecond isLeft isRight (admits.1 _)
        fun values => region_replays rest admits.2 _ _ _ (isLeft.bindAll values)
          (isRight.bindAll values)

/-- Closed regions whose operations are related are related one by one. -/
theorem regions_replay {signatures : List (List Located × List Located)} :
    ∀ (regions : Regions (ProtocolDialect operations functions protocols deployed) signatures),
      RegionsAdmit channel proverHandler verifierHandler functionTable table label first second
        regions →
      RegionsReplay channel proverHandler verifierHandler first second signatures
        (regions.denote (labelledMeaning model label functionTable table (first.union second)))
        (regions.denote (labelledMeaning model label functionTable table first))
        (regions.denote (labelledMeaning model label functionTable table second))
  | .nil, _ => trivial
  | .cons body tail, admits =>
      ⟨fun values => region_replays body admits.1 _ _ _ (Restricts.ofValues values)
          (Restricts.ofValues values),
        regions_replay tail admits.2⟩

/-- Handlers that pass the region functions of the two parts may replace the handlers that
perform every effect as it is. -/
theorem RegionsReplay.ofPasses :
    ∀ (signatures : List (List Located × List Located))
      (whole : Values (RegionFunction (SideValue model (first.union second)) (Effects model))
        signatures)
      (firstPart : Values (RegionFunction (SideValue model first) (Effects model)) signatures)
      (secondPart : Values (RegionFunction (SideValue model second) (Effects model)) signatures),
      RegionsReplay channel (passHandler model Writer) (passHandler model Reader) first second
        signatures whole firstPart secondPart →
      PassAll proverHandler firstPart → PassAll verifierHandler secondPart →
        RegionsReplay channel proverHandler verifierHandler first second signatures whole firstPart
          secondPart
  | [], _, _, _, _, _, _ => trivial
  | _ :: rest, whole, firstPart, secondPart, related, passesProver, passesVerifier =>
      ⟨fun values => (related.1 values).ofPasses (passesProver.1 _) (passesVerifier.1 _),
        RegionsReplay.ofPasses rest whole.tail firstPart.tail secondPart.tail related.2
          passesProver.2 passesVerifier.2⟩

end Regions

end Zkc.Core
