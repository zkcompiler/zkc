module

public import Zkc.Core.NormalLocal

public section

/-! The normal form of a protocol body.

What the protocol dialect gives the pass of `Zkc.Core.Normal`.

- **Shared operations.** `at(r, ℓ)` for a shared local operation `ℓ` (`LocalOp.same`): the
  same role applying the same operation to the same operands. An exchange, a draw, a sample
  and an application are never shared.
- **Rebuilt operations.** `choose` and `repeat` capture every value in scope. The typed model
  does not ask that a capture be held by a participant; that is a residual condition of a body
  as written, and the normal form is read by the check of facts only.

`protocolNormalizer_sound`: these choices are sound for the meaning of a protocol body at
every side.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}

/-! ## The values that a role holds

A local operation of a role reads values that the role holds. To rebuild `at(r, ℓ)` so that
the regions of `ℓ` take every value in scope, the pass needs the values of the context that
`r` holds, as local values: their types, the operands that name them, and, for a value of the
context that `r` holds, its position among them. -/

/-- The values of a context that a role holds. -/
structure RoleView (role : Nat) (Δ : List Located) where
  types : List Ty
  operands : Operands Δ (Located.atRole role types)
  back : Mapping (fun (located : Located) (type : Ty) => located = ⟨type, role⟩) Δ types

namespace RoleView

variable {role : Nat}

/-- The view of a context with one more value: among the role's values when the role holds
it. -/
@[expose] def push {rest : List Located} (view : RoleView role rest) (located : Located) :
    RoleView role (located :: rest) :=
  if held : located.holder = role then
    { types := located.type :: view.types
      operands :=
        .cons ((Var.here : Var (located :: rest) located).retype (by rw [← held]))
          (view.operands.lift located)
      back := view.back.keep located located.type fun other related => by rw [related] }
  else
    { types := view.types
      operands := view.operands.lift located
      back := view.back.skip located fun target related => held (by rw [related]) }

/-- The view of a context. -/
@[expose] def of (role : Nat) : (Δ : List Located) → RoleView role Δ
  | [] => ⟨[], .nil, Mapping.start 0 rfl⟩
  | located :: rest => (of role rest).push located

/-- Operands that the role holds, as values of its view. -/
@[expose] def local_ {Δ : List Located} (view : RoleView role Δ) :
    (types : List Ty) → Operands Δ (Located.atRole role types) → Operands view.types types
  | [], _ => .nil
  | _ :: rest, operands =>
      .cons (view.back.apply (operands.get .here) rfl) (view.local_ rest operands.tail)

/-- Values of the role's view, as operands of the context. -/
@[expose] def located {Δ : List Located} (view : RoleView role Δ) :
    (types : List Ty) → Operands view.types types → Operands Δ (Located.atRole role types)
  | [], _ => .nil
  | _ :: rest, operands =>
      .cons (view.operands.get ((operands.get .here).mapped fun type => (⟨type, role⟩ : Located)))
        (view.located rest operands.tail)

/-- The operand at the position of a value that the role holds is that value. -/
def Faithful {Δ : List Located} (view : RoleView role Δ) : Prop :=
  ∀ {located : Located} {type : Ty} (reference : Var Δ located) (related : located = ⟨type, role⟩),
    (view.operands.get
        ((view.back.apply reference related).mapped fun type => (⟨type, role⟩ : Located))).index =
      reference.index

theorem push_faithful {rest : List Located} (view : RoleView role rest) (faithful : view.Faithful)
    (located : Located) : (view.push located).Faithful := by
  unfold push
  by_cases held : located.holder = role
  · rw [dite_eq_left_of_eq_true (eq_true held)]
    intro reference related
    cases reference with
    | here =>
        subst related
        show (Values.get (Values.cons _ (view.operands.lift _))
            ((Mapping.apply (view.back.keep _ _ _) Var.here rfl).mapped
              fun type => (⟨type, role⟩ : Located))).index = 0
        rw [Mapping.apply_keep_here]
        rfl
    | there reference =>
        subst related
        show (Values.get (Values.cons _ (view.operands.lift located))
            ((Mapping.apply (view.back.keep _ _ _) reference.there rfl).mapped
              fun type => (⟨type, role⟩ : Located))).index = reference.index + 1
        rw [Mapping.apply_keep_there]
        show ((view.operands.lift located).get
            ((view.back.apply reference rfl).mapped fun type => (⟨type, role⟩ : Located))).index = _
        rw [Operands.get_lift]
        exact congrArg (· + 1) (faithful reference rfl)
  · rw [dite_eq_right_of_eq_false (eq_false held)]
    intro reference related
    cases reference with
    | here => exact absurd (by rw [related]) held
    | there reference =>
        subst related
        show ((view.operands.lift located).get
            ((Mapping.apply (view.back.skip _ _) reference.there rfl).mapped
              fun type => (⟨type, role⟩ : Located))).index = reference.index + 1
        rw [Mapping.apply_skip_there, Operands.get_lift]
        exact congrArg (· + 1) (faithful reference rfl)

theorem of_faithful (role : Nat) : ∀ (Δ : List Located), (of role Δ).Faithful
  | [] => fun reference _ => reference.elimNil
  | located :: rest => push_faithful (of role rest) (of_faithful role rest) located

end RoleView

/-- When a shared local operation with its nested regions is another with its regions: a
shared operation has no region. -/
@[expose] def LocalOp.sameWith :
    (first second : LocalOp operations functions deployed) →
      (firstBodies : Regions (LocalDialect operations functions deployed) first.regions) →
      (secondBodies : Regions (LocalDialect operations functions deployed) second.regions) →
      Option (PLift ((⟨first, firstBodies⟩ :
          (op : LocalOp operations functions deployed) ×
            Regions (LocalDialect operations functions deployed) op.regions) =
        ⟨second, secondBodies⟩))
  | .builtin first, .builtin second, .nil, .nil =>
      if equal : first = second then some ⟨by rw [equal]⟩ else none
  | .literal (.bool _), _, _, _ => none
  | .literal first, .literal second, .nil, .nil =>
      if equal : first = second then some ⟨by rw [equal]⟩ else none
  | .op (inputs := firstInputs) (outputs := firstOutputs) (kind := firstKind) first _,
      .op (inputs := secondInputs) (outputs := secondOutputs) (kind := secondKind) second _,
      .nil, .nil =>
      if equal : firstInputs = secondInputs ∧ firstOutputs = secondOutputs ∧
          firstKind = secondKind ∧ first.index = second.index then
        some ⟨by
          obtain ⟨rfl, rfl, rfl, index⟩ := equal
          cases Var.ext index
          rfl⟩
      else none
  | .call (header := firstHeader) first _, .call (header := secondHeader) second _, .nil, .nil =>
      if equal : firstHeader = secondHeader ∧ first.index = second.index then
        some ⟨by
          obtain ⟨rfl, index⟩ := equal
          cases Var.ext index
          rfl⟩
      else none
  | _, _, _, _ => none

/-- An application of the table that the role made, as an application of its view: a shared
local operation of that role. -/
@[expose] def RoleView.entryOf {role : Nat} {Δ : List Located} (view : RoleView role Δ) :
    (op : ProtocolOp operations functions protocols deployed) → Operands Δ op.arguments →
      Operands Δ op.results → Option (Entry (LocalDialect operations functions deployed) view.types)
  | .at other op _, arguments, results =>
      if same : other = role then
        cond (LocalOp.same op op).isSome
          (some ⟨op, view.local_ _ (same ▸ arguments), view.local_ _ (same ▸ results)⟩) none
      else none
  | _, _, _ => none

@[expose] def RoleView.entry {role : Nat} {Δ : List Located} (view : RoleView role Δ)
    (entry : Entry (ProtocolDialect operations functions protocols deployed) Δ) :
    Option (Entry (LocalDialect operations functions deployed) view.types) :=
  view.entryOf entry.op entry.arguments entry.results

/-- The applications of the table that the role made, as applications of its view. -/
@[expose] def RoleView.table {role : Nat} {Δ : List Located} (view : RoleView role Δ)
    (table : List (Entry (ProtocolDialect operations functions protocols deployed) Δ)) :
    List (Entry (LocalDialect operations functions deployed) view.types) :=
  table.filterMap view.entry

namespace ProtocolOp

/-- When two protocol operations are one shared operation: the same role applying the same
shared local operation. -/
@[expose] def same : SameOp (ProtocolDialect operations functions protocols deployed)
  | .at firstRole first firstBodies, .at secondRole second secondBodies =>
      if roles : firstRole = secondRole then
        match LocalOp.sameWith first second firstBodies secondBodies with
        | some ⟨equal⟩ =>
            some ⟨by
              subst roles
              cases equal
              rfl⟩
        | none => none
      else none
  | _, _ => none

/-- The plan of equal regions without inputs of their own, each over every value of `Δ`. -/
@[expose] def replicatePlan {Δ captures : List Located} (outputs : List Located)
    (captured : Operands Δ captures)
    (table : List (Entry (ProtocolDialect operations functions protocols deployed) Δ)) :
    (count : Nat) →
      Plan (ProtocolDialect operations functions protocols deployed)
        (List.replicate count (captures, outputs)) (List.replicate count (Δ, outputs))
  | 0 => .nil
  | count + 1 =>
      .cons (Renaming.inward captured [] (Mapping.start (Δ := ([] : List Located)) 0 rfl))
        (Entry.inwardAll (dialect := ProtocolDialect operations functions protocols deployed) []
              (base := []) table)
        (replicatePlan outputs captured table count)

/-- The plan of the regions of a `choose` on a variant: the region of an alternative takes
each participant's payload and then every value of `Δ`. -/
@[expose] def alternativesPlan {Δ captures : List Located} (participants : List Nat)
    (outputs : List Located) (captured : Operands Δ captures)
    (table : List (Entry (ProtocolDialect operations functions protocols deployed) Δ)) :
    (alternatives : List Ty) →
      Plan (ProtocolDialect operations functions protocols deployed)
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs))
        (alternatives.map fun payload => (Located.ofRoles payload participants ++ Δ, outputs))
  | [] => .nil
  | payload :: rest =>
      .cons
        (Renaming.inward captured (Located.ofRoles payload participants)
          (Mapping.start (Δ := ([] : List Located)) 0 rfl))
        (Entry.inwardAll (dialect := ProtocolDialect operations functions protocols deployed) (Located.ofRoles payload participants)
              (base := []) table)
        (alternativesPlan participants outputs captured table rest)

/-- The plan of the regions of a `choose` that captures every value of `Δ`. -/
@[expose] def choosePlan {Δ captures : List Located} (participants : List Nat)
    (outputs : List Located) (captured : Operands Δ captures)
    (table : List (Entry (ProtocolDialect operations functions protocols deployed) Δ)) :
    (tag : ChoiceTag) →
      Plan (ProtocolDialect operations functions protocols deployed)
        (tag.regions participants captures outputs) (tag.regions participants Δ outputs)
  | .condition => replicatePlan outputs captured table 2
  | .arm count => replicatePlan outputs captured table count
  | .alternative _ alternatives => alternativesPlan participants outputs captured table alternatives

/-- A protocol operation rebuilt at a context: `choose` and `repeat` capture every value of
the context; every other operation is itself. -/
@[expose] def reopen {Δ : List Located} :
    (op : ProtocolOp operations functions protocols deployed) → Operands Δ op.arguments →
      List (Entry (ProtocolDialect operations functions protocols deployed) Δ) →
        Reopened (ProtocolDialect operations functions protocols deployed) Δ op
  | .choose participants tag _ outputs covered, arguments, table =>
      { regions := tag.regions participants Δ outputs
        plan :=
          choosePlan participants outputs
            (arguments.split (Located.ofRoles tag.type participants)).2 table tag
        build := fun bodies rest =>
          .letOp (.choose participants tag Δ outputs covered)
            ((arguments.split (Located.ofRoles tag.type participants)).1.append
              (Operands.every Δ)) bodies rest }
  | .repeat participants count carried collected _ covered, arguments, table =>
      { regions := [(Located.ofRoles .nat participants ++ (carried ++ Δ), collected ++ carried)]
        plan :=
          .cons
            (Renaming.inwardAfter
              ((arguments.split (count.operands participants)).2.split carried).2 carried
              (Located.ofRoles .nat participants)
              (Mapping.start (Δ := ([] : List Located)) 0 rfl))
            (Entry.inwardAfterAll (dialect := ProtocolDialect operations functions protocols deployed)
                carried (Located.ofRoles .nat participants) (base := []) table)
            .nil
        build := fun bodies rest =>
          .letOp (.repeat participants count carried collected Δ covered)
            ((arguments.split (count.operands participants)).1.append
              (((arguments.split (count.operands participants)).2.split carried).1.append
                (Operands.every Δ))) bodies rest }
  | .at role (.conditional captures outputs) bodies, arguments, table =>
      { regions := [], plan := .nil
        build := fun _ rest =>
          .letOp
            (.at role (.conditional (RoleView.of role Δ).types outputs)
              (Regions.normalize localNormalizer (Regions.flatten bodies)
                (LocalOp.reopen (.conditional captures outputs)
                  ((RoleView.of role Δ).local_ _ arguments) ((RoleView.of role Δ).table table)).plan))
            ((RoleView.of role Δ).located _
              (.cons (((RoleView.of role Δ).local_ _ arguments).get .here)
                (Operands.every (RoleView.of role Δ).types)))
            .nil rest }
  | .at role (.match declaration alternatives captures outputs) bodies, arguments, table =>
      { regions := [], plan := .nil
        build := fun _ rest =>
          .letOp
            (.at role (.match declaration alternatives (RoleView.of role Δ).types outputs)
              (Regions.normalize localNormalizer (Regions.flatten bodies)
                (LocalOp.reopen (.match declaration alternatives captures outputs)
                  ((RoleView.of role Δ).local_ _ arguments) ((RoleView.of role Δ).table table)).plan))
            ((RoleView.of role Δ).located _
              (.cons (((RoleView.of role Δ).local_ _ arguments).get .here)
                (Operands.every (RoleView.of role Δ).types)))
            .nil rest }
  | .at role (.loop (.static count) carried collected captures) bodies, arguments, table =>
      { regions := [], plan := .nil
        build := fun _ rest =>
          .letOp
            (.at role (.loop (.static count) carried collected (RoleView.of role Δ).types)
              (Regions.normalize localNormalizer (Regions.flatten bodies)
                (LocalOp.reopen (.loop (.static count) carried collected captures)
                  ((RoleView.of role Δ).local_ _ arguments) ((RoleView.of role Δ).table table)).plan))
            ((RoleView.of role Δ).located _
              ((((RoleView.of role Δ).local_ _ arguments).split carried).1.append
                (Operands.every (RoleView.of role Δ).types)))
            .nil rest }
  | .at role (.loop (.runtime maximum) carried collected captures) bodies, arguments, table =>
      { regions := [], plan := .nil
        build := fun _ rest =>
          .letOp
            (.at role (.loop (.runtime maximum) carried collected (RoleView.of role Δ).types)
              (Regions.normalize localNormalizer (Regions.flatten bodies)
                (LocalOp.reopen (.loop (.runtime maximum) carried collected captures)
                  ((RoleView.of role Δ).local_ _ arguments) ((RoleView.of role Δ).table table)).plan))
            ((RoleView.of role Δ).located _
              (.cons (((RoleView.of role Δ).local_ _ arguments).get .here)
                ((((RoleView.of role Δ).local_ _ arguments).tail.split carried).1.append
                  (Operands.every (RoleView.of role Δ).types))))
            .nil rest }
  | .at role (.op row applies) bodies, arguments, _ =>
      { regions := [], plan := .nil
        build := fun _ rest => .letOp (.at role (.op row applies) bodies) arguments .nil rest }
  | .at role (.call callee permitted) bodies, arguments, _ =>
      { regions := [], plan := .nil
        build := fun _ rest => .letOp (.at role (.call callee permitted) bodies) arguments .nil rest }
  | .at role (.guard reason) bodies, arguments, _ =>
      { regions := [], plan := .nil
        build := fun _ rest => .letOp (.at role (.guard reason) bodies) arguments .nil rest }
  | .at role (.literal value) bodies, arguments, _ =>
      { regions := [], plan := .nil
        build := fun _ rest => .letOp (.at role (.literal value) bodies) arguments .nil rest }
  | .at role (.builtin operation) bodies, arguments, _ =>
      { regions := [], plan := .nil
        build := fun _ rest => .letOp (.at role (.builtin operation) bodies) arguments .nil rest }
  | .exchange sender receiver site type, arguments, _ =>
      { regions := [], plan := .nil
        build := fun _ rest => .letOp (.exchange sender receiver site type) arguments .nil rest }
  | .draw owner receivers site law populated, arguments, _ =>
      { regions := [], plan := .nil
        build := fun _ rest =>
          .letOp (.draw owner receivers site law populated) arguments .nil rest }
  | .sample owner site law populated, arguments, _ =>
      { regions := [], plan := .nil
        build := fun _ rest => .letOp (.sample owner site law populated) arguments .nil rest }
  | .apply callee roleMap site permitted, arguments, _ =>
      { regions := [], plan := .nil
        build := fun _ rest => .letOp (.apply callee roleMap site permitted) arguments .nil rest }

end ProtocolOp

section Sound

variable {model : Model} {functionTable : FunctionTable model functions}
  {table : ProtocolTable model protocols} {label : Nat → Site} {side : Side}

/-- The values of a present holder, by position. -/
theorem presentValues_get {X : Ty → Type} :
    ∀ (present : Bool) (inside : present = true) {types : List Ty}
      (values : Values (fun type => Held (X type) present) types) {type : Ty}
      (position : Var types type),
      (presentValues present inside values).get position =
        Held.value present inside (values.get position)
  | true, _, _, _, _, _ => rfl

theorem presentValues_nil {X : Ty → Type} :
    ∀ (present : Bool) (inside : present = true),
      presentValues (X := X) present inside (Values.nil) = Values.nil
  | true, _ => rfl

/-- A value among values indexed by the original list, by position. -/
theorem get_unmapValues {α β : Type} {F : β → Type} (f : α → β) :
    ∀ (items : List α) (values : Values F (items.map f)) {item : α} (position : Var items item),
      (unmapValues f items values).get position = values.get (position.mapped f)
  | [], _, _, position => position.elimNil
  | _ :: rest, .cons _ values, _, position => by
      cases position with
      | here => rfl
      | there position => exact get_unmapValues f rest values position

/-- The step of a role is the step of another local operation when the two agree on the
values of a present role. -/
theorem performStep_congr {inputs inputs' outputs : List Ty}
    (run : Values model.Value inputs → PIR.Process (Effects model) (Values model.Value outputs))
    (run' : Values model.Value inputs' → PIR.Process (Effects model) (Values model.Value outputs)) :
    ∀ (present : Bool) (arguments : Values (fun type => Held (model.Value type) present) inputs)
      (arguments' : Values (fun type => Held (model.Value type) present) inputs'),
      (∀ inside : present = true,
        run' (presentValues present inside arguments') =
          run (presentValues present inside arguments)) →
      performStep model run' present arguments' = performStep model run present arguments
  | true, _, _, same => same rfl
  | false, _, _, _ => rfl

namespace RoleView

variable {role : Nat} {Δ : List Located}

/-- The values that a role holds, in an environment of a side that contains the role. -/
def values (view : RoleView role Δ) (image : Environment (SideValue model side) Δ)
    (inside : side role = true) : Values model.Value view.types :=
  presentValues (side role) inside
    (unmapValues (F := SideValue model side) (fun type => (⟨type, role⟩ : Located)) view.types
      (Operands.eval image view.operands))

/-- The environment of the values that a role holds. -/
def environment (view : RoleView role Δ) (image : Environment (SideValue model side) Δ)
    (inside : side role = true) : Environment model.Value view.types :=
  fun {_} reference => (view.values image inside).get reference

theorem environment_located (view : RoleView role Δ) (image : Environment (SideValue model side) Δ)
    (inside : side role = true) {type : Ty} (reference : Var view.types type) :
    view.environment image inside reference =
      Held.value (side role) inside
        (image (view.operands.get (reference.mapped fun type => (⟨type, role⟩ : Located)))) := by
  show (presentValues (side role) inside _).get reference = _
  rw [presentValues_get, get_unmapValues, Operands.get_eval]

theorem environment_back (view : RoleView role Δ) (faithful : view.Faithful)
    (image : Environment (SideValue model side) Δ) (inside : side role = true) {type : Ty}
    (reference : Var Δ ⟨type, role⟩) :
    view.environment image inside (view.back.apply reference rfl) =
      Held.value (side role) inside (image reference) := by
  rw [environment_located, Var.ext (faithful reference rfl)]

/-- The values of operands that the role holds are the values of their positions in the
role's view. -/
theorem eval_local (view : RoleView role Δ) (faithful : view.Faithful)
    (image : Environment (SideValue model side) Δ) (inside : side role = true) :
    ∀ (types : List Ty) (operands : Operands Δ (Located.atRole role types)),
      presentValues (side role) inside
          (unmapValues (F := SideValue model side) (fun type => (⟨type, role⟩ : Located)) types
            (Operands.eval image operands)) =
        Operands.eval (view.environment image inside) (view.local_ types operands)
  | [], _ => presentValues_nil (side role) inside
  | _ :: rest, operands => by
      show presentValues (side role) inside
          (Values.cons ((Operands.eval image operands).get .here)
            (unmapValues _ rest (Operands.eval image operands).tail)) =
        Values.cons (view.environment image inside (view.back.apply (operands.get .here) rfl))
          (Operands.eval (view.environment image inside) (view.local_ rest operands.tail))
      rw [presentValues_cons, Operands.get_eval, Operands.eval_tail,
        eval_local view faithful image inside rest operands.tail,
        environment_back view faithful image inside]

/-- The values of the operands made from values of the role's view are those values. -/
theorem eval_located (view : RoleView role Δ) (image : Environment (SideValue model side) Δ)
    (inside : side role = true) :
    ∀ (types : List Ty) (operands : Operands view.types types),
      presentValues (side role) inside
          (unmapValues (F := SideValue model side) (fun type => (⟨type, role⟩ : Located)) types
            (Operands.eval image (view.located types operands))) =
        Operands.eval (view.environment image inside) operands
  | [], .nil => presentValues_nil (side role) inside
  | _ :: rest, operands => by
      rw [Operands.eval_cons (view.environment image inside) operands]
      show presentValues (side role) inside
          (Values.cons
            (image (view.operands.get
              ((operands.get .here).mapped fun type => (⟨type, role⟩ : Located))))
            (unmapValues _ rest (Operands.eval image (view.located rest operands.tail)))) = _
      rw [presentValues_cons, eval_located view image inside rest operands.tail,
        environment_located]

end RoleView

theorem unmapValues_remapValues {α β : Type} {F : β → Type} (f : α → β) :
    ∀ (items : List α) (values : Values (fun item => F (f item)) items),
      unmapValues f items (remapValues f items values) = values
  | [], .nil => rfl
  | _ :: rest, .cons value values => by
      show Values.cons (Value := fun item => F (f item)) value
          (unmapValues f rest (remapValues f rest values)) = _
      rw [unmapValues_remapValues f rest values]

/-- A step of a present role that returned: its local operation returned those values. -/
theorem performStep_returned {inputs outputs : List Ty}
    (run : Values model.Value inputs → PIR.Process (Effects model) (Values model.Value outputs)) :
    ∀ (present : Bool) (inside : present = true)
      (arguments : Values (fun type => Held (model.Value type) present) inputs)
      (results : Values (fun type => Held (model.Value type) present) outputs),
      performStep model run present arguments = .done results →
        run (presentValues present inside arguments) = .done (presentValues present inside results)
  | true, _, _, _, returned => returned

/-- A process followed by a return that returned: the process returned. -/
theorem bind_done_returned {I : PIR.Signature} {A B : Type} (process : PIR.Process I A)
    (after : A → B) (result : B)
    (returned : (process.bind fun value => .done (after value)) = .done result) :
    ∃ value, process = .done value ∧ after value = result := by
  cases process with
  | done value =>
      exact ⟨value, rfl, PIR.Process.done.inj returned⟩
  | halt _ => cases returned
  | call _ _ => cases returned

namespace RoleView

variable {role : Nat} {Δ : List Located}

/-- The role's applications of a table that holds, hold of the role's values. -/
theorem table_holds (view : RoleView role Δ) (faithful : view.Faithful)
    (quiet : QuietTable functionTable)
    {entries : List (Entry (ProtocolDialect operations functions protocols deployed) Δ)}
    {image : Environment (SideValue model side) Δ} (inside : side role = true)
    (known : TableHolds (labelledMeaning model label functionTable table side) entries image) :
    TableHolds (localMeaning model functionTable) (view.table entries)
      (view.environment image inside) := by
  intro entry member bodies
  obtain ⟨original, inTable, found⟩ := List.mem_filterMap.mp member
  obtain ⟨op, arguments, results⟩ := original
  cases op with
  | «at» other op regions =>
      by_cases same : other = role
      · subst same
        simp only [RoleView.entry, RoleView.entryOf, ↓reduceDIte] at found
        cases shared : (LocalOp.same op op).isSome with
        | false =>
            rw [shared] at found
            cases found
        | true =>
            rw [shared] at found
            cases found
            have held := known _ inTable .nil
            obtain ⟨values, returned, remapped⟩ := bind_done_returned _ _ _ held
            have local_ := performStep_returned (model := model) _ (side other) inside _ _ returned
            rw [view.eval_local faithful image inside] at local_
            have results_ : presentValues (side other) inside values =
                Operands.eval (view.environment image inside) (view.local_ _ results) := by
              rw [← view.eval_local faithful image inside, ← remapped, unmapValues_remapValues]
            rw [results_] at local_
            rw [(LocalOp.same_deterministic quiet op shared).closed _ bodies
              (regions.denote (localMeaning model functionTable))]
            exact local_
      · simp [RoleView.entry, RoleView.entryOf, same] at found
  | _ => simp [RoleView.entry, RoleView.entryOf] at found

end RoleView

/-- The step of a role whose local operation returns or stops, returns or stops. -/
theorem performStep_ends {inputs outputs : List Ty}
    (run : Values model.Value inputs → PIR.Process (Effects model) (Values model.Value outputs))
    (ends : ∀ values, (∃ results, run values = .done results) ∨ (∃ reason, run values = .halt reason)) :
    ∀ (present : Bool) (arguments : Values (fun type => Held (model.Value type) present) inputs),
      (∃ results, performStep model run present arguments = .done results) ∨
        (∃ reason, performStep model run present arguments = .halt reason)
  | true, arguments => ends arguments
  | false, _ => .inl ⟨_, rfl⟩

/-- `at(r, ℓ)` is deterministic at every side when `ℓ` is. -/
theorem ProtocolOp.at_deterministic (role : Nat) (op : LocalOp operations functions deployed)
    (bodies : Regions (LocalDialect operations functions deployed) op.regions)
    (local_ : Deterministic (localMeaning model functionTable) op) :
    Deterministic
      (labelledMeaning (protocols := protocols) model label functionTable table side)
      (.at role op bodies) where
  ends arguments _ := by
    obtain ⟨results, returned⟩ | ⟨reason, stopped⟩ :=
      performStep_ends (model := model)
        (fun values => localOperation model functionTable op values
          (bodies.denote (localMeaning model functionTable)))
        (fun values => local_.ends values _) (side role)
        (unmapValues (F := SideValue model side) (fun type => (⟨type, role⟩ : Located))
          op.arguments arguments)
    · exact .inl ⟨remapValues (F := SideValue model side) (fun type => (⟨type, role⟩ : Located))
          op.results results,
        congrArg (fun process => process.bind fun values =>
          PIR.Process.done (remapValues (F := SideValue model side)
            (fun type => (⟨type, role⟩ : Located)) op.results values)) returned⟩
    · exact .inr ⟨reason,
        congrArg (fun process => process.bind fun values =>
          PIR.Process.done (remapValues (F := SideValue model side)
            (fun type => (⟨type, role⟩ : Located)) op.results values)) stopped⟩
  closed _ _ _ := rfl

/-- A shared protocol operation is deterministic at every side, over functions that perform
no effect. -/
theorem ProtocolOp.same_deterministic (quiet : QuietTable functionTable) :
    ∀ (op : ProtocolOp operations functions protocols deployed),
      (ProtocolOp.same op op).isSome = true →
        Deterministic (labelledMeaning model label functionTable table side) op
  | .at role (.builtin operation) bodies, _ =>
      ProtocolOp.at_deterministic role _ bodies
        (LocalOp.same_deterministic quiet (.builtin operation) (by simp [LocalOp.same]))
  | .at role (.literal value) bodies, _ =>
      ProtocolOp.at_deterministic role (.literal value) bodies
        { ends := fun _ _ => .inl ⟨_, rfl⟩, closed := fun _ _ _ => rfl }
  | .at role (.op row applies) bodies, _ =>
      ProtocolOp.at_deterministic role _ bodies
        (LocalOp.same_deterministic quiet (.op row applies) (by simp [LocalOp.same]))
  | .at role (.call callee permitted) bodies, _ =>
      ProtocolOp.at_deterministic role _ bodies
        (LocalOp.same_deterministic quiet (.call callee permitted) (by simp [LocalOp.same]))
  | .at _ (.conditional ..) _, shared => by simp [ProtocolOp.same, LocalOp.sameWith] at shared
  | .at _ (.match ..) _, shared => by simp [ProtocolOp.same, LocalOp.sameWith] at shared
  | .at _ (.loop ..) _, shared => by simp [ProtocolOp.same, LocalOp.sameWith] at shared
  | .at _ (.guard _) _, shared => by simp [ProtocolOp.same, LocalOp.sameWith] at shared
  | .exchange .., shared => by cases shared
  | .draw .., shared => by cases shared
  | .sample .., shared => by cases shared
  | .repeat .., shared => by cases shared
  | .choose .., shared => by cases shared
  | .apply .., shared => by cases shared

/-- Equal regions over every value of a context do what the old ones do on the values of
their captures. -/
theorem ProtocolOp.selectArm_inward {Δ captures : List Located} (outputs : List Located)
    (captured : Operands Δ captures)
    {entries : List (Entry (ProtocolDialect operations functions protocols deployed) Δ)}
    {image : Environment (SideValue model side) Δ}
    (known : TableHolds (labelledMeaning model label functionTable table side) entries image) :
    ∀ (count : Nat)
      (old : Values (RegionFunction (SideValue model side) (Effects model))
        (List.replicate count (captures, outputs)))
      (new : Values (RegionFunction (SideValue model side) (Effects model))
        (List.replicate count (Δ, outputs))),
      Plan.Agrees (labelledMeaning model label functionTable table side)
        (ProtocolOp.replicatePlan outputs captured entries count) old new →
      ∀ (number : Fin count),
        selectArm (Δ, outputs) count new number
            (Operands.eval image (Operands.every Δ)) =
          selectArm (captures, outputs) count old number (Operands.eval image captured)
  | 0, _, _, _, number => number.elim0
  | _ + 1, .cons _ _, .cons _ _, agrees, ⟨0, _⟩ =>
      Plan.agrees_inward (own := []) (labelledMeaning model label functionTable table side)
        captured known _ _ agrees.1 .nil
  | count + 1, .cons _ old, .cons _ new, agrees, ⟨number + 1, below⟩ =>
      ProtocolOp.selectArm_inward outputs captured known count old new agrees.2
        ⟨number, Nat.lt_of_succ_lt_succ below⟩

/-- The regions of a `choose` on a variant over every value of a context do what the old ones
do on the values of their captures. -/
theorem ProtocolOp.alternativeProcess_inward {Δ captures : List Located} (participants : List Nat)
    (outputs : List Located) (captured : Operands Δ captures)
    {entries : List (Entry (ProtocolDialect operations functions protocols deployed) Δ)}
    {image : Environment (SideValue model side) Δ}
    (known : TableHolds (labelledMeaning model label functionTable table side) entries image) :
    ∀ (alternatives : List Ty)
      (old : Values (RegionFunction (SideValue model side) (Effects model))
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs)))
      (new : Values (RegionFunction (SideValue model side) (Effects model))
        (alternatives.map fun payload => (Located.ofRoles payload participants ++ Δ, outputs))),
      Plan.Agrees (labelledMeaning model label functionTable table side)
        (ProtocolOp.alternativesPlan participants outputs captured entries alternatives) old new →
      ∀ (number : Nat)
        (copies : Values (fun role => Held (Ty.Variant model.Carrier alternatives) (side role))
          participants),
        alternativeProcess model side participants Δ outputs alternatives new number copies
            (Operands.eval image (Operands.every Δ)) =
          alternativeProcess model side participants captures outputs alternatives old number
            copies (Operands.eval image captured)
  | [], _, _, _, _, _ => rfl
  | payload :: rest, .cons _ _, .cons _ _, agrees, 0, copies => by
      unfold alternativeProcess
      cases firstPayloads model side payload rest participants copies with
      | some payloads =>
          exact Plan.agrees_inward (labelledMeaning model label functionTable table side) captured
            known _ _ agrees.1 _
      | none => rfl
  | payload :: rest, .cons _ old, .cons _ new, agrees, number + 1, copies => by
      unfold alternativeProcess
      cases laterCopies model side payload rest participants copies with
      | some later =>
          exact ProtocolOp.alternativeProcess_inward participants outputs captured known rest old
            new agrees.2 number later
      | none => rfl

/-- The region that a tag selects, over every value of a context, does what the old one does
on the values of its captures. -/
theorem ProtocolOp.chosenRegion_inward {Δ captures : List Located} (participants : List Nat)
    (outputs : List Located) (captured : Operands Δ captures)
    {entries : List (Entry (ProtocolDialect operations functions protocols deployed) Δ)}
    {image : Environment (SideValue model side) Δ}
    (known : TableHolds (labelledMeaning model label functionTable table side) entries image) :
    ∀ (tag : ChoiceTag)
      (old : Values (RegionFunction (SideValue model side) (Effects model))
        (tag.regions participants captures outputs))
      (new : Values (RegionFunction (SideValue model side) (Effects model))
        (tag.regions participants Δ outputs)),
      Plan.Agrees (labelledMeaning model label functionTable table side)
        (ProtocolOp.choosePlan participants outputs captured entries tag) old new →
      ∀ (copies : Values (fun role => Held (model.Value tag.type) (side role)) participants),
        chosenRegion model side participants Δ outputs tag new copies
            (Operands.eval image (Operands.every Δ)) =
          chosenRegion model side participants captures outputs tag old copies
            (Operands.eval image captured)
  | .condition, old, new, agrees, _ => by
      funext value
      exact ProtocolOp.selectArm_inward outputs captured known 2 old new agrees _
  | .arm count, old, new, agrees, _ => by
      funext value
      exact ProtocolOp.selectArm_inward outputs captured known count old new agrees _
  | .alternative _ alternatives, old, new, agrees, copies => by
      funext value
      exact ProtocolOp.alternativeProcess_inward participants outputs captured known alternatives
        old new agrees _ copies

/-- A rebuilt protocol operation whose regions agree with the old ones is the operation, at
every side. -/
theorem ProtocolOp.reopen_denote (quiet : QuietTable functionTable) {Δ : List Located} :
    ∀ (op : ProtocolOp operations functions protocols deployed) (arguments : Operands Δ op.arguments)
      (entries : List (Entry (ProtocolDialect operations functions protocols deployed) Δ))
      (image : Environment (SideValue model side) Δ),
      TableHolds (labelledMeaning model label functionTable table side) entries image →
      ∀ (old : Values (RegionFunction (SideValue model side) (Effects model)) op.regions)
        (bodies : Regions (ProtocolDialect operations functions protocols deployed)
          (ProtocolOp.reopen op arguments entries).regions),
        Plan.Agrees (labelledMeaning model label functionTable table side)
          (ProtocolOp.reopen op arguments entries).plan old
          (bodies.denote (labelledMeaning model label functionTable table side)) →
        ∀ {out : List Located}
          (rest : Region (ProtocolDialect operations functions protocols deployed)
            (bindAll Δ op.results) out),
          ((ProtocolOp.reopen op arguments entries).build bodies rest).denote
              (labelledMeaning model label functionTable table side) image =
            (labelledOperation model label functionTable table side op
                (Operands.eval image arguments) old).bind fun values =>
              rest.denote (labelledMeaning model label functionTable table side)
                (Environment.bindAll image values)
  | .choose participants tag captures outputs covered, arguments, entries, image, known, old,
      bodies, agrees, _, rest => by
      have chosen := ProtocolOp.chosenRegion_inward participants outputs
        (arguments.split (Located.ofRoles tag.type participants)).2 known tag old
        (bodies.denote (labelledMeaning model label functionTable table side)) agrees
      have left : (Operands.eval image
            ((arguments.split (Located.ofRoles tag.type participants)).1.append
              (Operands.every Δ))).split (Located.ofRoles tag.type participants) =
          (Operands.eval image (arguments.split (Located.ofRoles tag.type participants)).1,
            Operands.eval image (Operands.every Δ)) := by
        rw [Operands.eval_append, Values.split_append]
      have right := Operands.eval_split image (Located.ofRoles tag.type participants) arguments
      show (agreed (tag.same model.Carrier) side
          (chosenRegion model side participants Δ outputs tag
            (bodies.denote (labelledMeaning model label functionTable table side))
            (unmapValues (F := SideValue model side) (fun role => ⟨tag.type, role⟩) _
              ((Operands.eval image
                ((arguments.split (Located.ofRoles tag.type participants)).1.append
                  (Operands.every Δ))).split (Located.ofRoles tag.type participants)).1)
            ((Operands.eval image
              ((arguments.split (Located.ofRoles tag.type participants)).1.append
                (Operands.every Δ))).split (Located.ofRoles tag.type participants)).2)
          (.halt .incomplete) participants
          (unmapValues (F := SideValue model side) (fun role => ⟨tag.type, role⟩) _
            ((Operands.eval image
              ((arguments.split (Located.ofRoles tag.type participants)).1.append
                (Operands.every Δ))).split (Located.ofRoles tag.type participants)).1)
          fun none =>
            .done (absentOutputs model side outputs fun _ member =>
              not_held_of_heldBy covered none member)).bind _ =
        (agreed (tag.same model.Carrier) side
          (chosenRegion model side participants captures outputs tag old
            (unmapValues (F := SideValue model side) (fun role => ⟨tag.type, role⟩) _
              ((Operands.eval image arguments).split (Located.ofRoles tag.type participants)).1)
            ((Operands.eval image arguments).split (Located.ofRoles tag.type participants)).2)
          (.halt .incomplete) participants
          (unmapValues (F := SideValue model side) (fun role => ⟨tag.type, role⟩) _
            ((Operands.eval image arguments).split (Located.ofRoles tag.type participants)).1)
          fun none =>
            .done (absentOutputs model side outputs fun _ member =>
              not_held_of_heldBy covered none member)).bind _
      rw [left, right, chosen]
  | .repeat participants count carried collected captures covered, arguments, entries, image,
      known, .cons body .nil, .cons region .nil, agrees, _, rest => by
      have step : (fun (iteration : Nat) (values : Values (SideValue model side) carried) =>
            (((Regions.cons region Regions.nil).denote
                (labelledMeaning model label functionTable table side)).get .here)
              ((heldCopies model side .nat iteration participants).append
                (values.append (Operands.eval image (Operands.every Δ))))) =
          fun iteration values =>
            body ((heldCopies model side .nat iteration participants).append
              (values.append (Operands.eval image
                ((arguments.split (count.operands participants)).2.split carried).2))) := by
        funext iteration values
        exact Plan.agrees_inwardAfter (labelledMeaning model label functionTable table side)
          ((arguments.split (count.operands participants)).2.split carried).2 known _ _ agrees.1
          (heldCopies model side .nat iteration participants) values
      show (repeatOperation model side participants count carried collected Δ covered
          (((Regions.cons region Regions.nil).denote
            (labelledMeaning model label functionTable table side)).get .here)
          (repeatCopies model side participants count
            ((Operands.eval image
              ((arguments.split (count.operands participants)).1.append
                (((arguments.split (count.operands participants)).2.split carried).1.append
                  (Operands.every Δ)))).split (count.operands participants)).1)
          (((Operands.eval image
              ((arguments.split (count.operands participants)).1.append
                (((arguments.split (count.operands participants)).2.split carried).1.append
                  (Operands.every Δ)))).split (count.operands participants)).2.split carried).1
          (((Operands.eval image
              ((arguments.split (count.operands participants)).1.append
                (((arguments.split (count.operands participants)).2.split carried).1.append
                  (Operands.every Δ)))).split (count.operands participants)).2.split carried).2).bind
            _ =
        (repeatOperation model side participants count carried collected captures covered body
          (repeatCopies model side participants count
            ((Operands.eval image arguments).split (count.operands participants)).1)
          (((Operands.eval image arguments).split (count.operands participants)).2.split carried).1
          (((Operands.eval image arguments).split (count.operands participants)).2.split
            carried).2).bind _
      simp only [Operands.eval_append, Values.split_append, Operands.eval_split]
      unfold repeatOperation
      rw [step]
  | .at role (.conditional captures outputs) bodies, arguments, entries, image, known, _, .nil, _, _, rest => by
      show PIR.Process.bind
          (PIR.Process.bind (performStep model _ (side role) _) _) _ =
        PIR.Process.bind (PIR.Process.bind (performStep model _ (side role) _) _) _
      congr 2
      refine performStep_congr _ _ (side role) _ _ fun inside => ?_
      rw [RoleView.eval_located, RoleView.eval_local _ (RoleView.of_faithful role Δ)]
      have local_ := LocalOp.reopen_denote (table := functionTable) (.conditional captures outputs)
        ((RoleView.of role Δ).local_ _ arguments) ((RoleView.of role Δ).table entries)
        ((RoleView.of role Δ).environment image inside)
        ((RoleView.of role Δ).table_holds (RoleView.of_faithful role Δ) quiet inside known)
        (bodies.denote (localMeaning model functionTable)) _
        (Regions.flatten_denote (localMeaning model functionTable) bodies ▸
          Regions.normalize_agrees (localNormalizer_sound quiet) (Regions.flatten bodies) _)
        (.ret (Operands.bound outputs))
      exact ((Region.denote_letOp_bound (localMeaning model functionTable) _ _ _ _).symm.trans
        local_).trans (Region.bind_ret_bound (localMeaning model functionTable) _ _)
  | .at role (.match declaration alternatives captures outputs) bodies, arguments, entries, image, known, _, .nil, _, _, rest => by
      show PIR.Process.bind
          (PIR.Process.bind (performStep model _ (side role) _) _) _ =
        PIR.Process.bind (PIR.Process.bind (performStep model _ (side role) _) _) _
      congr 2
      refine performStep_congr _ _ (side role) _ _ fun inside => ?_
      rw [RoleView.eval_located, RoleView.eval_local _ (RoleView.of_faithful role Δ)]
      have local_ := LocalOp.reopen_denote (table := functionTable) (.match declaration alternatives captures outputs)
        ((RoleView.of role Δ).local_ _ arguments) ((RoleView.of role Δ).table entries)
        ((RoleView.of role Δ).environment image inside)
        ((RoleView.of role Δ).table_holds (RoleView.of_faithful role Δ) quiet inside known)
        (bodies.denote (localMeaning model functionTable)) _
        (Regions.flatten_denote (localMeaning model functionTable) bodies ▸
          Regions.normalize_agrees (localNormalizer_sound quiet) (Regions.flatten bodies) _)
        (.ret (Operands.bound outputs))
      exact ((Region.denote_letOp_bound (localMeaning model functionTable) _ _ _ _).symm.trans
        local_).trans (Region.bind_ret_bound (localMeaning model functionTable) _ _)
  | .at role (.loop (.static count) carried collected captures) bodies, arguments, entries, image, known, _, .nil, _, _, rest => by
      show PIR.Process.bind
          (PIR.Process.bind (performStep model _ (side role) _) _) _ =
        PIR.Process.bind (PIR.Process.bind (performStep model _ (side role) _) _) _
      congr 2
      refine performStep_congr _ _ (side role) _ _ fun inside => ?_
      rw [RoleView.eval_located, RoleView.eval_local _ (RoleView.of_faithful role Δ)]
      have local_ := LocalOp.reopen_denote (table := functionTable) (.loop (.static count) carried collected captures)
        ((RoleView.of role Δ).local_ _ arguments) ((RoleView.of role Δ).table entries)
        ((RoleView.of role Δ).environment image inside)
        ((RoleView.of role Δ).table_holds (RoleView.of_faithful role Δ) quiet inside known)
        (bodies.denote (localMeaning model functionTable)) _
        (Regions.flatten_denote (localMeaning model functionTable) bodies ▸
          Regions.normalize_agrees (localNormalizer_sound quiet) (Regions.flatten bodies) _)
        (.ret (Operands.bound (collectedSequences (some count) collected ++ carried)))
      exact ((Region.denote_letOp_bound (localMeaning model functionTable) _ _ _ _).symm.trans
        local_).trans (Region.bind_ret_bound (localMeaning model functionTable) _ _)
  | .at role (.loop (.runtime maximum) carried collected captures) bodies, arguments, entries, image, known, _, .nil, _, _, rest => by
      show PIR.Process.bind
          (PIR.Process.bind (performStep model _ (side role) _) _) _ =
        PIR.Process.bind (PIR.Process.bind (performStep model _ (side role) _) _) _
      congr 2
      refine performStep_congr _ _ (side role) _ _ fun inside => ?_
      rw [RoleView.eval_located, RoleView.eval_local _ (RoleView.of_faithful role Δ)]
      have local_ := LocalOp.reopen_denote (table := functionTable) (.loop (.runtime maximum) carried collected captures)
        ((RoleView.of role Δ).local_ _ arguments) ((RoleView.of role Δ).table entries)
        ((RoleView.of role Δ).environment image inside)
        ((RoleView.of role Δ).table_holds (RoleView.of_faithful role Δ) quiet inside known)
        (bodies.denote (localMeaning model functionTable)) _
        (Regions.flatten_denote (localMeaning model functionTable) bodies ▸
          Regions.normalize_agrees (localNormalizer_sound quiet) (Regions.flatten bodies) _)
        (.ret (Operands.bound (collectedSequences none collected ++ carried)))
      exact ((Region.denote_letOp_bound (localMeaning model functionTable) _ _ _ _).symm.trans
        local_).trans (Region.bind_ret_bound (localMeaning model functionTable) _ _)
  | .at _ (.op _ _) _, _, _, _, _, _, .nil, _, _, _ => rfl
  | .at _ (.call _ _) _, _, _, _, _, _, .nil, _, _, _ => rfl
  | .at _ (.guard _) _, _, _, _, _, _, .nil, _, _, _ => rfl
  | .at _ (.literal _) _, _, _, _, _, _, .nil, _, _, _ => rfl
  | .at _ (.builtin _) _, _, _, _, _, _, .nil, _, _, _ => rfl
  | .exchange .., _, _, _, _, _, .nil, _, _, _ => rfl
  | .draw .., _, _, _, _, _, .nil, _, _, _ => rfl
  | .sample .., _, _, _, _, _, .nil, _, _, _ => rfl
  | .apply .., _, _, _, _, _, .nil, _, _, _ => rfl

end Sound

/-- The regions that a protocol operation carries inside itself: the local regions of
`at(r, ℓ)`, and what the normal form keeps of them. -/
@[expose] def protocolTracer : Tracer (ProtocolDialect operations functions protocols deployed) where
  traces
    | .at _ _ bodies, path => Regions.traces Tracer.none bodies path 0
    | _, _ => []
  kept := fun {Δ} op arguments table =>
    match op, arguments with
    | .at role (.conditional captures outputs) bodies, arguments =>
        Regions.kept localNormalizer Tracer.none (Regions.flatten bodies)
          (LocalOp.reopen (.conditional captures outputs) ((RoleView.of role Δ).local_ _ arguments)
            ((RoleView.of role Δ).table table)).plan
    | .at role (.match declaration alternatives captures outputs) bodies, arguments =>
        Regions.kept localNormalizer Tracer.none (Regions.flatten bodies)
          (LocalOp.reopen (.match declaration alternatives captures outputs)
            ((RoleView.of role Δ).local_ _ arguments) ((RoleView.of role Δ).table table)).plan
    | .at role (.loop (.static count) carried collected captures) bodies, arguments =>
        Regions.kept localNormalizer Tracer.none (Regions.flatten bodies)
          (LocalOp.reopen (.loop (.static count) carried collected captures)
            ((RoleView.of role Δ).local_ _ arguments) ((RoleView.of role Δ).table table)).plan
    | .at role (.loop (.runtime maximum) carried collected captures) bodies, arguments =>
        Regions.kept localNormalizer Tracer.none (Regions.flatten bodies)
          (LocalOp.reopen (.loop (.runtime maximum) carried collected captures)
            ((RoleView.of role Δ).local_ _ arguments) ((RoleView.of role Δ).table table)).plan
    | _, _ => []

/-- What the protocol dialect gives the normal form. -/
@[expose] def protocolNormalizer :
    Normalizer (ProtocolDialect operations functions protocols deployed) :=
  ⟨ProtocolOp.same, ProtocolOp.reopen⟩

/-- The choices of the protocol dialect are sound for the meaning of a protocol body at every
side, over functions that perform no effect. -/
theorem protocolNormalizer_sound {model : Model} {functionTable : FunctionTable model functions}
    (quiet : QuietTable functionTable) (table : ProtocolTable model protocols)
    (label : Nat → Site) (side : Side) :
    (protocolNormalizer (operations := operations) (deployed := deployed)).Sound
      (labelledMeaning model label functionTable table side) :=
  ⟨ProtocolOp.same_deterministic quiet,
    fun op arguments entries image known old bodies agrees _ rest =>
      ProtocolOp.reopen_denote quiet op arguments entries image known old bodies agrees rest⟩

end Zkc.Core
