module

public import Zkc.Core.Labelled
public import Zkc.Core.Project

public section

/-! The meaning of a projected role program is the meaning of the one-role side.

For a side whose only member, among the roles of the definition, is the role, the
process of the projected program in the role's environment is the side's process of the
protocol region, with the results restricted to the values the role holds. The proof is
a structural induction on the region, one case per operation and per membership of the
roles the operation names. The side `single role` is such a side for every bound; the
callee's side of an application is such a side for the formal role that the role map
sends to the role, which is why the statement is not about `single role` alone.

The invariant `Agrees` relates the two environments through the translation. Each of
its lemmas adds one bound value: a case analysis on the reference (`Var.cases`) and
the equation of the translation for the most recent value or for an earlier one.

`repeat` and `choose`: the participants are distinct and below the bound, so at most
one of them is in the side; its copy of the count or tag is the agreed one and the
side never stops `incomplete`. The loop of the role and the loop of the side are
related step by step (`repeatProcess_own`); the arms of a choice are related
region by region (`RegionsAgree`).
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- The side whose only member is one role. -/
abbrev single (role : Nat) : Side := fun other => Nat.beq other role

/-- A side whose only member, among the roles below a bound, is the role. -/
@[expose] def Side.Only (side : Side) (role bound : Nat) : Prop :=
  ∀ other, Nat.blt other bound = true → side other = Nat.beq other role

theorem Side.only_single (role bound : Nat) : (single role).Only role bound := fun _ _ => rfl

/-- The side whose only member is a role contains it. -/
theorem Side.single_inside (role : Nat) : single role role = true := Nat.beq_refl role

/-- A side whose only member below a bound is a role below the bound contains the role. -/
theorem Side.Only.inside {side : Side} {role bound : Nat} (only : side.Only role bound)
    (below : Nat.blt role bound = true) : side role = true :=
  (only role below).trans (Nat.beq_refl role)

theorem presentValues_nil {X : Ty → Type} (present : Bool) (member : present = true) :
    presentValues (X := X) present member .nil = .nil := by
  subst member; rfl

theorem presentValues_holdValues {X : Ty → Type} (present : Bool) (member : present = true)
    {types : List Ty} (values : Values X types) :
    presentValues present member (holdValues present values) = values := by
  subst member; rfl

section Values

variable {model : Model} {side : Side} {role : Nat} {inside : side role = true}

/-- A side that contains a role holds what the role holds. -/
theorem Side.holds_own {side : Side} {role holder : Nat} (inside : side role = true)
    (member : Nat.beq holder role = true) : side holder = true := by
  rw [Nat.eq_of_beq_eq_true member]; exact inside

/-- What the role's program holds for a located value that the side holds: the value. No
value is invented for a holder outside the side, so no type needs a value. -/
def roleValue (model : Model) (side : Side) (located : Located)
    (held : side located.holder = true) (value : SideValue model side located) :
    model.Value located.type :=
  Held.value (side located.holder) held value

/-- The values of a side's result that a role of the side holds. -/
def ownValues (model : Model) (side : Side) (role : Nat) (inside : side role = true) :
    (out : List Located) → Values (SideValue model side) out → Values model.Value (own role out)
  | [], _ => .nil
  | located :: rest, .cons value values =>
      consKept (Nat.beq located.holder role)
        (fun member => roleValue model side located (Side.holds_own inside member) value)
        (ownValues model side role inside rest values)

/-- A value that is kept when its holder is the role, apart from the values after it. -/
@[expose] def unkeep {model : Model} {type : Ty} {rest : List Ty} : (present : Bool) →
    Values model.Value (keep present type rest) →
      Held (model.Value type) present × Values model.Value rest
  | true, .cons value values => (value, values)
  | false, values => (PUnit.unit, values)

/-- The values of the side whose only member is a role, from the values that the role
holds: a value of another holder is not there. -/
@[expose] def onlyValues (model : Model) (role : Nat) : (ports : List Located) →
    Values model.Value (own role ports) → Values (SideValue model (single role)) ports
  | [], _ => .nil
  | located :: rest, values =>
      .cons (ty := located) (unkeep (Nat.beq located.holder role) values).1
        (onlyValues model role rest (unkeep (Nat.beq located.holder role) values).2)

theorem consKept_unkeep {model : Model} {type : Ty} {rest : List Ty} : ∀ (present : Bool)
    (member : present = true → present = true)
    (values : Values model.Value (keep present type rest)),
    consKept present (fun inside => Held.value present (member inside) (unkeep present values).1)
        (unkeep present values).2 =
      values
  | true, _, .cons _ _ => rfl
  | false, _, _ => rfl

/-- The values that a role holds of the side made from its values are those values: every
tuple of values of a role is that of a side with the role alone. -/
theorem ownValues_onlyValues (model : Model) (role : Nat) : ∀ (ports : List Located)
    (values : Values model.Value (own role ports)),
    ownValues model (single role) role (Side.single_inside role) ports
        (onlyValues model role ports values) =
      values
  | [], .nil => rfl
  | located :: rest, values => by
      show consKept (Nat.beq located.holder role)
          (fun member => Held.value (Nat.beq located.holder role) _
            (unkeep (Nat.beq located.holder role) values).1)
          (ownValues model (single role) role (Side.single_inside role) rest
            (onlyValues model role rest (unkeep (Nat.beq located.holder role) values).2)) =
        values
      rw [ownValues_onlyValues model role rest]
      exact consKept_unkeep _ _ values

/-- The environment of a role of the side holds, for every value of the role, the value
that the side's environment holds. -/
structure Agrees (inside : side role = true) {Γ : List Located} {Δ : List Ty}
    (translate : Translation role Γ Δ)
    (env : Environment (SideValue model side) Γ) (mine : Environment model.Value Δ) : Prop where
  value : ∀ {located : Located} (reference : Var Γ located)
    (member : Nat.beq located.holder role = true),
    mine (translate.own reference member) =
      roleValue model side located (Side.holds_own inside member) (env reference)

theorem eval_consKept {Δ : List Ty} (mine : Environment model.Value Δ) {type : Ty}
    {rest : List Ty} :
    ∀ (present : Bool) (value : present = true → Var Δ type) (values : Operands Δ rest),
      Operands.eval mine (consKept present value values) =
        consKept present (fun member => mine (value member)) (Operands.eval mine values)
  | true, _, _ => rfl
  | false, _, _ => rfl

theorem eval_ownOperands {Γ : List Located} {Δ : List Ty} {translate : Translation role Γ Δ}
    {env : Environment (SideValue model side) Γ} {mine : Environment model.Value Δ}
    (agrees : Agrees inside translate env mine) :
    ∀ (out : List Located) (values : Operands Γ out),
      Operands.eval mine (ownOperands translate out values) =
        ownValues model side role inside out (Operands.eval env values)
  | [], .nil => rfl
  | located :: rest, .cons reference values => by
      show Operands.eval mine (consKept _ _ (ownOperands translate rest values)) =
        consKept _ _ (ownValues model side role inside rest (Operands.eval env values))
      rw [eval_consKept, eval_ownOperands agrees rest values]
      congr 1
      funext member
      exact agrees.value reference member

/-- A new value of another role. -/
theorem Agrees.absent {Γ : List Located} {Δ : List Ty} {translate : Translation role Γ Δ}
    {env : Environment (SideValue model side) Γ} {mine : Environment model.Value Δ}
    (agrees : Agrees inside translate env mine) (located : Located)
    (outside : Nat.beq located.holder role = false) (value : SideValue model side located) :
    Agrees inside (translate.absent located outside) (env.push value) mine := by
  refine ⟨fun {other} reference => ?_⟩
  cases reference with
  | here => intro member; rw [outside] at member; cases member
  | there reference =>
      intro member
      exact (congrArg mine (Mapping.apply_skip_there ..)).trans (agrees.value reference member)

/-- A new value of the role. -/
theorem Agrees.present {Γ : List Located} {Δ : List Ty} {translate : Translation role Γ Δ}
    {env : Environment (SideValue model side) Γ} {mine : Environment model.Value Δ}
    (agrees : Agrees inside translate env mine) (located : Located)
    (value : SideValue model side located) (own : model.Value located.type)
    (same : ∀ member : Nat.beq located.holder role = true,
      own = roleValue model side located (Side.holds_own inside member) value) :
    Agrees inside (translate.present located) (env.push value) (mine.push own) := by
  refine ⟨fun {other} reference => ?_⟩
  cases reference with
  | here =>
      intro member
      exact (congrArg (mine.push own) (Mapping.apply_keep_here ..)).trans (same member)
  | there reference =>
      intro member
      exact (congrArg (mine.push own) (Mapping.apply_keep_there ..)).trans
        (agrees.value reference member)

/-- A new value that is, for the role, a value the role already has. -/
theorem Agrees.same {Γ : List Located} {Δ : List Ty} {translate : Translation role Γ Δ}
    {env : Environment (SideValue model side) Γ} {mine : Environment model.Value Δ}
    (agrees : Agrees inside translate env mine) (located : Located) (source : Var Δ located.type)
    (value : SideValue model side located)
    (same : ∀ member : Nat.beq located.holder role = true,
      mine source = roleValue model side located (Side.holds_own inside member) value) :
    Agrees inside (translate.same located source) (env.push value) mine := by
  refine ⟨fun {other} reference => ?_⟩
  cases reference with
  | here =>
      intro member
      exact (congrArg mine (Mapping.apply_bind_here ..)).trans (same member)
  | there reference =>
      intro member
      exact (congrArg mine (Mapping.apply_bind_there ..)).trans (agrees.value reference member)

/-- The operands of an operation of the role are the present values of the side. -/
theorem eval_ownArguments {Γ : List Located} {Δ : List Ty} {translate : Translation role Γ Δ}
    {env : Environment (SideValue model side) Γ} {mine : Environment model.Value Δ}
    (agrees : Agrees inside translate env mine) (holder : Nat) (member : Nat.beq holder role = true)
    (holderInside : side holder = true) :
    ∀ (types : List Ty) (arguments : Operands Γ (Located.atRole holder types)),
      Operands.eval mine (ownArguments translate holder member types arguments) =
        presentValues (side holder) holderInside
          (unmapValues (F := SideValue model side) (fun type => ⟨type, holder⟩) types
            (Operands.eval env arguments))
  | [], .nil => (presentValues_nil _ holderInside).symm
  | type :: types, .cons reference rest => by
      show Values.cons _ _ = presentValues _ holderInside (Values.cons _ _)
      rw [presentValues_cons, eval_ownArguments agrees holder member holderInside types rest]
      congr 1
      exact agrees.value (located := ⟨type, holder⟩) reference member

/-- The results of an operation that the role performed. -/
theorem Agrees.presentAll (holder : Nat) (holderInside : side holder = true) :
    ∀ (types : List Ty) {Γ : List Located} {Δ : List Ty} {translate : Translation role Γ Δ}
      {env : Environment (SideValue model side) Γ} {mine : Environment model.Value Δ},
      Agrees inside translate env mine →
      ∀ (held : Values (fun type => Held (model.Value type) (side holder)) types),
        Agrees inside (Translation.presentAll holder translate types)
          (Environment.bindAll env (remapValues (F := SideValue model side)
            (fun type => ⟨type, holder⟩) types held))
          (Environment.bindAll mine (presentValues (side holder) holderInside held))
  | [], _, _, _, _, _, agrees, .nil => by
      rw [presentValues_nil]
      exact agrees
  | type :: types, _, _, _, _, _, agrees, .cons value held => by
      rw [presentValues_cons]
      exact Agrees.presentAll holder holderInside types
        (agrees.present ⟨type, holder⟩ value _ fun _ => rfl) held

/-- The results of an operation that another role performed. -/
theorem Agrees.absentAll (holder : Nat) (outside : Nat.beq holder role = false) :
    ∀ (types : List Ty) {Γ : List Located} {Δ : List Ty} {translate : Translation role Γ Δ}
      {env : Environment (SideValue model side) Γ} {mine : Environment model.Value Δ},
      Agrees inside translate env mine →
      ∀ (held : Values (fun type => Held (model.Value type) (side holder)) types),
        Agrees inside (Translation.absentAll holder outside translate types)
          (Environment.bindAll env (remapValues (F := SideValue model side)
            (fun type => ⟨type, holder⟩) types held)) mine
  | [], _, _, _, _, _, agrees, .nil => agrees
  | type :: types, _, _, _, _, _, agrees, .cons value held =>
      Agrees.absentAll holder outside types (agrees.absent ⟨type, holder⟩ outside value) held

/-- The copies of a coin that the role drew: each that the role holds is the coin. -/
theorem Agrees.coins {Δ : List Ty} (output : Ty) (reply : model.Value output)
    {mine : Environment model.Value Δ} :
    ∀ (receivers : List Nat), (∀ receiver ∈ receivers, side receiver = Nat.beq receiver role) →
      ∀ {Γ : List Located} {translate : Translation role Γ (output :: Δ)}
        {env : Environment (SideValue model side) Γ},
        Agrees inside translate env (mine.push reply) →
          Agrees inside (Translation.coins output translate receivers)
            (Environment.bindAll env (heldCopies model side output reply receivers))
            (mine.push reply)
  | [], _, _, _, _, agrees => agrees
  | receiver :: receivers, only, _, _, _, agrees =>
      Agrees.coins output reply receivers
        (fun other member => only other (List.mem_cons_of_mem _ member))
        (agrees.same ⟨output, receiver⟩ .here _ fun _ => (Held.value_of _ _ reply).symm)

/-- The results of a draw by the role: every copy that the role holds is the coin. -/
theorem Agrees.drawn {Γ : List Located} {Δ : List Ty} {translate : Translation role Γ Δ}
    {env : Environment (SideValue model side) Γ} {mine : Environment model.Value Δ}
    (agrees : Agrees inside translate env mine) (owner : Nat) (output : Ty)
    (receivers : List Nat) (only : ∀ receiver ∈ receivers, side receiver = Nat.beq receiver role)
    (reply : model.Value output) :
    Agrees inside (translate.drawn owner output receivers)
      (Environment.bindAll env (broadcast model side owner receivers output reply))
      (mine.push reply) :=
  Agrees.coins output reply receivers only
    (agrees.present ⟨output, owner⟩ _ reply fun _ => (Held.value_of _ _ reply).symm)

/-- One more value, kept when its holder is the role, before the values that follow. -/
theorem Agrees.extendOne {Γ Γ' : List Located} {Δ : List Ty} {translate : Translation role Γ Δ}
    {env : Environment (SideValue model side) Γ} {mine : Environment model.Value Δ}
    (agrees : Agrees inside translate env mine) (located : Located)
    (value : SideValue model side located) {later : List Ty}
    (tail : Values model.Value later)
    (next : {Δ' : List Ty} → Translation role (located :: Γ) Δ' →
      Translation role Γ' (bindAll Δ' later))
    (env' : Environment (SideValue model side) Γ')
    (nextAgrees : ∀ {Δ' : List Ty} (translate' : Translation role (located :: Γ) Δ')
      (mine' : Environment model.Value Δ'), Agrees inside translate' (env.push value) mine' →
        Agrees inside (next translate') env' (Environment.bindAll mine' tail)) :
    ∀ (present : Bool) (known : Nat.beq located.holder role = present),
      Agrees inside (Translation.extendOne translate located later next present known) env'
        (Environment.bindAll mine (consKept present
          (fun kept => roleValue model side located (Side.holds_own inside (known.trans kept)) value)
          tail))
  | true, _ => nextAgrees _ _ (agrees.present located value _ fun _ => rfl)
  | false, known => nextAgrees _ _ (agrees.absent located known value)

/-- New values of any holders. -/
theorem Agrees.extend :
    ∀ (added : List Located) {Γ : List Located} {Δ : List Ty} {translate : Translation role Γ Δ}
      {env : Environment (SideValue model side) Γ} {mine : Environment model.Value Δ},
      Agrees inside translate env mine →
      ∀ (values : Values (SideValue model side) added),
        Agrees inside (translate.extend added) (Environment.bindAll env values)
          (Environment.bindAll mine (ownValues model side role inside added values))
  | [], _, _, _, _, _, agrees, .nil => agrees
  | located :: added, _, _, _, _, _, agrees, .cons value values =>
      Agrees.extendOne agrees located value (ownValues model side role inside added values)
        (fun later => Translation.extend later added) _
        (fun _ _ agrees' => Agrees.extend added agrees' values) _ rfl

/-- The inputs of a definition. -/
theorem Agrees.initial (inputs : List Located)
    (values : Values (SideValue model side) inputs) :
    Agrees inside (Translation.initial role inputs) (Environment.ofValues values)
      (Environment.ofValues (ownValues model side role inside inputs values)) :=
  Agrees.extend inputs ⟨fun reference => reference.elimNil⟩ values

/-- One more value of a first list, before the rest of it and a second list. -/
theorem Agrees.extendOneAppend {Γ Γ' : List Located} {Δ : List Ty}
    {translate : Translation role Γ Δ} {env : Environment (SideValue model side) Γ}
    {mine : Environment model.Value Δ} (agrees : Agrees inside translate env mine) (located : Located)
    (value : SideValue model side located) {first second : List Ty}
    (tail : Values model.Value first) (last : Values model.Value second)
    (next : {Δ' : List Ty} → Translation role (located :: Γ) Δ' →
      Translation role Γ' (bindAll Δ' (first ++ second)))
    (env' : Environment (SideValue model side) Γ')
    (nextAgrees : ∀ {Δ' : List Ty} (translate' : Translation role (located :: Γ) Δ')
      (mine' : Environment model.Value Δ'), Agrees inside translate' (env.push value) mine' →
        Agrees inside (next translate') env' (Environment.bindAll mine' (tail.append last))) :
    ∀ (present : Bool) (known : Nat.beq located.holder role = present),
      Agrees inside (Translation.extendOneAppend translate located first second next present known) env'
        (Environment.bindAll mine ((consKept present
          (fun kept => roleValue model side located (Side.holds_own inside (known.trans kept)) value)
          tail).append last))
  | true, _ => nextAgrees _ _ (agrees.present located value _ fun _ => rfl)
  | false, known => nextAgrees _ _ (agrees.absent located known value)

/-- New values of two lists. -/
theorem Agrees.extendAppend (second : List Located) (last : Values (SideValue model side) second) :
    ∀ (first : List Located) {Γ : List Located} {Δ : List Ty} {translate : Translation role Γ Δ}
      {env : Environment (SideValue model side) Γ} {mine : Environment model.Value Δ},
      Agrees inside translate env mine →
      ∀ (values : Values (SideValue model side) first),
        Agrees inside (translate.extendAppend first second) (Environment.bindAll env (values.append last))
          (Environment.bindAll mine ((ownValues model side role inside first values).append
            (ownValues model side role inside second last)))
  | [], _, _, _, _, _, agrees, .nil => Agrees.extend second agrees last
  | located :: first, _, _, _, _, _, agrees, .cons value values =>
      Agrees.extendOneAppend agrees located value (ownValues model side role inside first values)
        (ownValues model side role inside second last)
        (fun later => Translation.extendAppend later first second) _
        (fun _ _ agrees' => Agrees.extendAppend second last first agrees' values) _ rfl

/-- The copies of the iteration number of a loop, then new values of two lists. -/
theorem Agrees.iterationAppend {Δ : List Ty} (iteration : Nat)
    {mine : Environment model.Value Δ} (first second : List Located)
    (values : Values (SideValue model side) first) (last : Values (SideValue model side) second) :
    ∀ (participants : List Nat) {Γ : List Located} {translate : Translation role Γ (.nat :: Δ)}
      {env : Environment (SideValue model side) Γ},
      Agrees inside translate env (mine.push (ty := .nat) iteration) →
        Agrees inside (Translation.iterationAppend translate participants first second)
          (Environment.bindAll env
            ((heldCopies model side .nat iteration participants).append (values.append last)))
          (Environment.bindAll (mine.push (ty := .nat) iteration)
            ((ownValues model side role inside first values).append
              (ownValues model side role inside second last)))
  | [], _, _, _, agrees => Agrees.extendAppend second last first agrees values
  | participant :: participants, _, _, _, agrees =>
      Agrees.iterationAppend iteration first second values last participants
        (agrees.same ⟨.nat, participant⟩ .here _ fun _ => (Held.value_of _ _ iteration).symm)

/-- The inputs of a loop's region: the iteration number, the carried values, then the
captures. -/
theorem Agrees.initialLoop (iteration : Nat) (participants : List Nat)
    (first second : List Located) (values : Values (SideValue model side) first)
    (last : Values (SideValue model side) second) :
    Agrees inside (Translation.initialLoop role participants first second)
      (Environment.ofValues
        ((heldCopies model side .nat iteration participants).append (values.append last)))
      (Environment.ofValues (Values.cons (ty := Ty.nat) iteration
        ((ownValues model side role inside first values).append
          (ownValues model side role inside second last)))) :=
  Agrees.iterationAppend iteration first second values last participants
    ⟨fun reference => reference.elimNil⟩

/-- The copies of the payload of an alternative, then new values: the role's payload is
the payload of every participant in the side that is the role. -/
theorem Agrees.payloadAppend {Δ : List Ty} (payload : Ty) (value : model.Value payload)
    {mine : Environment model.Value Δ} (later : List Located)
    (last : Values (SideValue model side) later) :
    ∀ (participants : List Nat)
      (payloads : Values (fun participant => Held (model.Value payload) (side participant))
        participants),
      (∀ {participant : Nat} (position : Var participants participant)
        (member : side participant = true),
        Held.value (side participant) member (payloads.get position) = value) →
      ∀ {Γ : List Located} {translate : Translation role Γ (payload :: Δ)}
        {env : Environment (SideValue model side) Γ},
        Agrees inside translate env (mine.push (ty := payload) value) →
          Agrees inside (Translation.payloadAppend payload translate participants later)
            (Environment.bindAll env
              ((remapValues (F := SideValue model side) (fun participant => ⟨payload, participant⟩)
                participants payloads).append last))
            (Environment.bindAll (mine.push (ty := payload) value)
              (ownValues model side role inside later last))
  | [], .nil, _, _, _, _, agrees => Agrees.extend later agrees last
  | participant :: participants, .cons head tail, same, _, _, _, agrees =>
      Agrees.payloadAppend payload value later last participants tail
        (fun position member => same position.there member)
        (agrees.same ⟨payload, participant⟩ .here head fun member =>
          (same .here (Side.holds_own inside member)).symm)

/-- The inputs of the region of an alternative of a variant: the payloads of the
participants, then the captures. -/
theorem Agrees.initialAlternative (payload : Ty) (value : model.Value payload)
    (participants : List Nat) (captures : List Located)
    (payloads : Values (fun participant => Held (model.Value payload) (side participant))
      participants)
    (same : ∀ {participant : Nat} (position : Var participants participant)
      (member : side participant = true),
      Held.value (side participant) member (payloads.get position) = value)
    (captured : Values (SideValue model side) captures) :
    Agrees inside (Translation.initialAlternative role payload participants captures)
      (Environment.ofValues
        ((remapValues (F := SideValue model side) (fun participant => ⟨payload, participant⟩)
          participants payloads).append captured))
      (Environment.ofValues (Values.cons (ty := payload) value
        (ownValues model side role inside captures captured))) :=
  Agrees.payloadAppend payload value captures captured participants payloads same
    ⟨fun reference => reference.elimNil⟩

/-- One carried result of a loop that the role is outside of. -/
theorem Agrees.passedOne {Γ₀ Γ Γ' : List Located} {Δ : List Ty} {base : Translation role Γ₀ Δ}
    {env₀ : Environment (SideValue model side) Γ₀} {mine : Environment model.Value Δ}
    (agrees₀ : Agrees inside base env₀ mine) {translate : Translation role Γ Δ}
    {env : Environment (SideValue model side) Γ} (agrees : Agrees inside translate env mine)
    (located : Located) (reference : Var Γ₀ located)
    (next : Translation role (located :: Γ) Δ → Translation role Γ' Δ)
    (env' : Environment (SideValue model side) Γ')
    (nextAgrees : ∀ (translate' : Translation role (located :: Γ) Δ),
      Agrees inside translate' (env.push (env₀ reference)) mine → Agrees inside (next translate') env' mine) :
    ∀ (present : Bool) (known : Nat.beq located.holder role = present),
      Agrees inside (Translation.passedOne base translate located reference next present known) env' mine
  | true, known =>
      nextAgrees _ (agrees.same located _ (env₀ reference) fun _ => agrees₀.value reference known)
  | false, known => nextAgrees _ (agrees.absent located known (env₀ reference))

/-- The carried results of a loop that the role is outside of. -/
theorem Agrees.passed {Γ₀ : List Located} {Δ : List Ty} {base : Translation role Γ₀ Δ}
    {env₀ : Environment (SideValue model side) Γ₀} {mine : Environment model.Value Δ}
    (agrees₀ : Agrees inside base env₀ mine) :
    ∀ (carried : List Located) {Γ : List Located} {translate : Translation role Γ Δ}
      {env : Environment (SideValue model side) Γ}, Agrees inside translate env mine →
      ∀ (operands : Operands Γ₀ carried),
        Agrees inside (Translation.passed base translate carried operands)
          (Environment.bindAll env (Operands.eval env₀ operands)) mine
  | [], _, _, _, agrees, .nil => agrees
  | located :: rest, _, _, _, agrees, .cons reference values =>
      Agrees.passedOne agrees₀ agrees located reference _ _
        (fun _ agrees' => Agrees.passed agrees₀ rest agrees' values) _ rfl

/-- New values none of which the role holds. -/
theorem Agrees.unheld {Δ : List Ty} {mine : Environment model.Value Δ} :
    ∀ (added : List Located) {Γ : List Located} {translate : Translation role Γ Δ}
      {env : Environment (SideValue model side) Γ}
      (later : Translation role (bindAll Γ added) Δ), translate.unheld added = some later →
      Agrees inside translate env mine → ∀ (values : Values (SideValue model side) added),
        Agrees inside later (Environment.bindAll env values) mine
  | [], _, _, _, later, found, agrees, .nil => by
      cases found
      exact agrees
  | located :: rest, _, translate, env, later, found, agrees, .cons value values => by
      unfold Translation.unheld at found
      split at found
      · rename_i outside
        exact Agrees.unheld rest later found (agrees.absent located outside value) values
      · cases found

/-! ### What a `repeat` collects, for the role -/

/-- One more sequence of a collected type, kept when the role holds it. -/
@[expose] def consKeptSequence {F : Ty → Type} {type : Ty} {rest : List Ty} (size : Option Nat) :
    (present : Bool) → (present = true → F (.seq type size)) →
      Values F (collectedSequences size rest) →
        Values F (collectedSequences size (keep present type rest))
  | true, value, values => .cons (value rfl) values
  | false, _, values => values

/-- One more sequence of a collected type, kept when the role holds it, before the sequences
and the carried values that follow. -/
@[expose] def consKeptCollected {F : Ty → Type} {type : Ty} {later carried : List Ty}
    (size : Option Nat) :
    (present : Bool) → (present = true → F (.seq type size)) →
      Values F (collectedSequences size later ++ carried) →
        Values F (collectedSequences size (keep present type later) ++ carried)
  | true, value, values => .cons (value rfl) values
  | false, _, values => values

theorem consKeptSequence_append {F : Ty → Type} {type : Ty} {later carried : List Ty}
    (size : Option Nat) (last : Values F carried) :
    ∀ (present : Bool) (value : present = true → F (.seq type size))
      (values : Values F (collectedSequences size later)),
      (consKeptSequence size present value values).append last =
        consKeptCollected size present value (values.append last)
  | true, _, _ => rfl
  | false, _, _ => rfl

theorem collectedNone_keep (model : Model) (type : Ty) (rest : List Ty) :
    ∀ (present : Bool),
      collectedNone model (keep present type rest) =
        consKeptSequence (some 0) present (fun _ => ⟨[], rfl⟩) (collectedNone model rest)
  | true => rfl
  | false => rfl

theorem collectedPush_keep (model : Model) {done : Nat} (type : Ty) (rest : List Ty) :
    ∀ (present : Bool) (value : present = true → model.Value type)
      (sequence : present = true → model.Value (.seq type (some done)))
      (values : Values model.Value rest)
      (earlier : Values model.Value (collectedSequences (some done) rest)),
      collectedPush model (keep present type rest) (consKept present value values)
          (consKeptSequence (some done) present sequence earlier) =
        consKeptSequence (some (done + 1)) present
          (fun member => ⟨value member :: (sequence member).val,
            congrArg (· + 1) (sequence member).property⟩)
          (collectedPush model rest values earlier)
  | true, _, _, _, _ => rfl
  | false, _, _, _, _ => rfl

theorem collectedLists_keep (model : Model) {total : Nat} (type : Ty) (rest : List Ty) :
    ∀ (present : Bool) (sequence : present = true → model.Value (.seq type (some total)))
      (values : Values model.Value (collectedSequences (some total) rest)),
      collectedLists model (keep present type rest)
          (consKeptSequence (some total) present sequence values) =
        consKeptSequence none present (fun member => (sequence member).val.reverse)
          (collectedLists model rest values)
  | true, _, _ => rfl
  | false, _, _ => rfl

theorem collectedSized_keep (model : Model) {total count : Nat} (same : total = count)
    (type : Ty) (rest : List Ty) :
    ∀ (present : Bool) (sequence : present = true → model.Value (.seq type (some total)))
      (values : Values model.Value (collectedSequences (some total) rest)),
      collectedSized model same (keep present type rest)
          (consKeptSequence (some total) present sequence values) =
        consKeptSequence (some count) present
          (fun member => ⟨(sequence member).val.reverse,
            List.length_reverse.trans ((sequence member).property.trans same)⟩)
          (collectedSized model same rest values)
  | true, _, _ => rfl
  | false, _, _ => rfl

/-- The sequences of collected values of a side's `repeat` that a role of the side holds. -/
def ownSequences (model : Model) (side : Side) (role : Nat) (inside : side role = true)
    (size : Option Nat) :
    (collected : List Located) →
      Values (SideValue model side) (collectedSequencesAt size collected) →
        Values model.Value (collectedSequences size (own role collected))
  | [], _ => .nil
  | located :: rest, .cons value values =>
      consKeptSequence size (Nat.beq located.holder role)
        (fun member => roleValue model side ⟨.seq located.type size, located.holder⟩
          (Side.holds_own inside member) value)
        (ownSequences model side role inside size rest values)

/-- The results of a side's `repeat` that a role of the side holds: its sequences of
collected values, then its carried values. -/
def ownCollected (model : Model) (side : Side) (role : Nat) (inside : side role = true)
    (size : Option Nat) (carried : List Located) :
    (collected : List Located) →
      Values (SideValue model side) (collectedSequencesAt size collected ++ carried) →
        Values model.Value (collectedSequences size (own role collected) ++ own role carried)
  | [], values => ownValues model side role inside carried values
  | located :: rest, .cons value values =>
      consKeptCollected size (Nat.beq located.holder role)
        (fun member => roleValue model side ⟨.seq located.type size, located.holder⟩
          (Side.holds_own inside member) value)
        (ownCollected model side role inside size carried rest values)

theorem ownSequences_none :
    ∀ (collected : List Located),
      collectedNone model (own role collected) =
        ownSequences model side role inside (some 0) collected
          (sideCollectedNone model side collected)
  | [] => rfl
  | ⟨type, holder⟩ :: rest => by
      refine (collectedNone_keep model type (own role rest) (Nat.beq holder role)).trans ?_
      rw [ownSequences_none rest]
      show consKeptSequence _ _ _ _ = consKeptSequence _ _ _ _
      congr 1
      funext member
      exact (Held.value_of _ _ _).symm

theorem ownSequences_push {done : Nat} :
    ∀ (collected : List Located) (values : Values (SideValue model side) collected)
      (earlier : Values (SideValue model side) (collectedSequencesAt (some done) collected)),
      collectedPush model (own role collected) (ownValues model side role inside collected values)
          (ownSequences model side role inside (some done) collected earlier) =
        ownSequences model side role inside (some (done + 1)) collected
          (sideCollectedPush model side collected values earlier)
  | [], _, _ => rfl
  | ⟨type, holder⟩ :: rest, .cons value values, .cons sequence earlier => by
      refine (collectedPush_keep model type (own role rest) (Nat.beq holder role) _ _ _ _).trans ?_
      rw [ownSequences_push rest values earlier]
      show consKeptSequence _ _ _ _ = consKeptSequence _ _ _ _
      congr 1
      funext member
      exact (Held.value_map₂
        (fun (value : model.Value type) (sequence : model.Value (.seq type (some done))) =>
          (⟨value :: sequence.val, congrArg (· + 1) sequence.property⟩ :
            model.Value (.seq type (some (done + 1)))))
        (side holder) (Side.holds_own inside member) value sequence).symm

/-- The results of a finished loop over a count that is a value, for the role. -/
theorem ownCollected_lists {total : Nat} (carried : List Located)
    (state : Values (SideValue model side) carried) :
    ∀ (collected : List Located)
      (values : Values (SideValue model side) (collectedSequencesAt (some total) collected)),
      (collectedLists model (own role collected)
          (ownSequences model side role inside (some total) collected values)).append
          (ownValues model side role inside carried state) =
        ownCollected model side role inside none carried collected
          ((sideCollectedLists model side collected values).append state)
  | [], _ => rfl
  | ⟨type, holder⟩ :: rest, .cons sequence values => by
      refine (congrArg (fun sequences => Values.append sequences _)
        (collectedLists_keep model type (own role rest) (Nat.beq holder role) _ _)).trans ?_
      rw [consKeptSequence_append, ownCollected_lists carried state rest values]
      show consKeptCollected _ _ _ _ = consKeptCollected _ _ _ _
      congr 1
      funext member
      exact (Held.value_map
        (fun (sequence : model.Value (.seq type (some total))) =>
          (sequence.val.reverse : model.Value (.seq type none)))
        (side holder) (Side.holds_own inside member) sequence).symm

/-- The results of a finished loop over a count of the operation, for the role. -/
theorem ownCollected_sized {total count : Nat} (same : total = count) (carried : List Located)
    (state : Values (SideValue model side) carried) :
    ∀ (collected : List Located)
      (values : Values (SideValue model side) (collectedSequencesAt (some total) collected)),
      (collectedSized model same (own role collected)
          (ownSequences model side role inside (some total) collected values)).append
          (ownValues model side role inside carried state) =
        ownCollected model side role inside (some count) carried collected
          ((sideCollectedSized model side same collected values).append state)
  | [], _ => rfl
  | ⟨type, holder⟩ :: rest, .cons sequence values => by
      refine (congrArg (fun sequences => Values.append sequences _)
        (collectedSized_keep model same type (own role rest) (Nat.beq holder role) _ _)).trans ?_
      rw [consKeptSequence_append, ownCollected_sized same carried state rest values]
      show consKeptCollected _ _ _ _ = consKeptCollected _ _ _ _
      congr 1
      funext member
      exact (Held.value_map
        (fun (sequence : model.Value (.seq type (some total))) =>
          (⟨sequence.val.reverse,
            List.length_reverse.trans (sequence.property.trans same)⟩ :
            model.Value (.seq type (some count))))
        (side holder) (Side.holds_own inside member) sequence).symm

/-- The role's values among those of a kept value and the values of two lists that follow,
read at the appended lists. -/
theorem split_retype_consKept {F : Ty → Type} {type : Ty} {first second whole : List Ty}
    (tail : whole = first ++ second) :
    ∀ (present : Bool) (same : keep present type whole = keep present type first ++ second)
      (value : present = true → F type) (values : Values F whole),
      ((consKept present value values).retype same).split (keep present type first) =
        (consKept present value ((values.retype tail).split first).1,
          ((values.retype tail).split first).2)
  | true, _, _, _ => by subst tail; rfl
  | false, _, _, _ => by subst tail; rfl

/-- The values that a region of a `repeat` yields, for the role: its collected values, then
its carried ones. -/
theorem split_retype_own (carried : List Located) :
    ∀ (collected : List Located)
      (same : own role (collected ++ carried) = own role collected ++ own role carried)
      (produced : Values (SideValue model side) (collected ++ carried)),
      ((ownValues model side role inside (collected ++ carried) produced).retype same).split
          (own role collected) =
        (ownValues model side role inside collected (produced.split collected).1,
          ownValues model side role inside carried (produced.split collected).2)
  | [], _, _ => rfl
  | located :: rest, same, .cons value produced => by
      have tail := split_retype_own carried rest (own_append role rest carried) produced
      refine (split_retype_consKept (own_append role rest carried) (Nat.beq located.holder role)
        same _ _).trans ?_
      exact congr
        (congrArg
          (fun first second =>
            (consKept (Nat.beq located.holder role)
              (fun member => roleValue model side located (Side.holds_own inside member) value)
              first, second))
          (congrArg Prod.fst tail))
        (congrArg Prod.snd tail)

/-- The loop of a `repeat` for a side that contains the role, and the role's loop: when the
role's region on the role's carried values is the region, for the role, the role's loop is
the loop, for the role. -/
theorem repeatProcess_own (count : RepeatCount) (carried collected : List Located)
    (step : Nat → Values (SideValue model side) carried →
      PIR.Process (Effects model) (Values (SideValue model side) (collected ++ carried)))
    (mineStep : Nat → Values model.Value (own role carried) →
      PIR.Process (Effects model) (Values model.Value (own role collected ++ own role carried)))
    (related : ∀ iteration state,
      mineStep iteration (ownValues model side role inside carried state) =
        (step iteration state).bind fun produced =>
          .done ((ownValues model side role inside (collected ++ carried) produced).retype
            (own_append role collected carried)))
    (agreed : Nat) (initial : Values (SideValue model side) carried) :
    ownRepeatProcess model count (own role carried) (own role collected) mineStep agreed
        (ownValues model side role inside carried initial) =
      (repeatProcess model side count carried collected step agreed initial).bind fun final =>
        .done (ownCollected model side role inside count.size carried collected final) := by
  have iterated : ∀ number : Nat,
      loopIterations model (own role carried) (own role collected) mineStep number 0
          (ownValues model side role inside carried initial)
          (collectedNone model (own role collected)) =
        (repeatIterations model side carried collected step number 0 initial
            (sideCollectedNone model side collected)).bind fun final =>
          .done (ownValues model side role inside carried final.1,
            ownSequences model side role inside _ collected final.2) := fun number => by
    rw [ownSequences_none (side := side) (inside := inside)]
    exact iterations_restrict (ownValues model side role inside carried)
      (fun done => ownSequences model side role inside (some done) collected)
      (fun produced => (ownValues model side role inside (collected ++ carried) produced).retype
        (own_append role collected carried))
      related
      (fun produced => congrArg Prod.snd (split_retype_own carried collected _ produced))
      (fun done produced earlier =>
        (congrArg
          (fun values => collectedPush model (own role collected) values
            (ownSequences model side role inside (some done) collected earlier))
          (congrArg Prod.fst (split_retype_own carried collected _ produced))).trans
          (ownSequences_push collected _ earlier))
      number 0 initial _
  cases count with
  | static number =>
      show PIR.Process.bind _ _ = PIR.Process.bind (PIR.Process.bind _ _) _
      rw [iterated number, PIR.Process.bind_assoc, PIR.Process.bind_assoc]
      refine congrArg (PIR.Process.bind _) (funext fun final => ?_)
      exact congrArg PIR.Process.done
        (ownCollected_sized (iterationsAfter_eq number 0) carried final.1 collected final.2)
  | runtime maximum =>
      show (if agreed ≤ maximum then PIR.Process.bind _ _ else .halt .undefined) =
        PIR.Process.bind (if agreed ≤ maximum then PIR.Process.bind _ _ else .halt .undefined) _
      split
      · rw [iterated agreed, PIR.Process.bind_assoc, PIR.Process.bind_assoc]
        refine congrArg (PIR.Process.bind _) (funext fun final => ?_)
        exact congrArg PIR.Process.done (ownCollected_lists carried final.1 collected final.2)
      · rfl

/-- One more sequence of a collected value, kept when its holder is the role. -/
theorem Agrees.extendOneCollected {Γ Γ' : List Located} {Δ : List Ty}
    {translate : Translation role Γ Δ} {env : Environment (SideValue model side) Γ}
    {mine : Environment model.Value Δ} (agrees : Agrees inside translate env mine)
    (size : Option Nat) (located : Located)
    (value : SideValue model side ⟨.seq located.type size, located.holder⟩)
    {later carried : List Ty}
    (tail : Values model.Value (collectedSequences size later ++ carried))
    (next : {Δ' : List Ty} →
      Translation role (⟨.seq located.type size, located.holder⟩ :: Γ) Δ' →
        Translation role Γ' (bindAll Δ' (collectedSequences size later ++ carried)))
    (env' : Environment (SideValue model side) Γ')
    (nextAgrees : ∀ {Δ' : List Ty}
      (translate' : Translation role (⟨.seq located.type size, located.holder⟩ :: Γ) Δ')
      (mine' : Environment model.Value Δ'), Agrees inside translate' (env.push value) mine' →
        Agrees inside (next translate') env' (Environment.bindAll mine' tail)) :
    ∀ (present : Bool) (known : Nat.beq located.holder role = present),
      Agrees inside
        (Translation.extendOneCollected translate size located later carried next present known)
        env'
        (Environment.bindAll mine (consKeptCollected size present
          (fun kept => roleValue model side ⟨.seq located.type size, located.holder⟩
            (Side.holds_own inside (known.trans kept)) value)
          tail))
  | true, _ =>
      nextAgrees _ _ (agrees.present ⟨.seq located.type size, located.holder⟩ value _ fun _ => rfl)
  | false, known =>
      nextAgrees _ _ (agrees.absent ⟨.seq located.type size, located.holder⟩ known value)

/-- The results of a loop of which the role is a participant. -/
theorem Agrees.extendCollected (size : Option Nat) (carried : List Located) :
    ∀ (collected : List Located) {Γ : List Located} {Δ : List Ty}
      {translate : Translation role Γ Δ} {env : Environment (SideValue model side) Γ}
      {mine : Environment model.Value Δ},
      Agrees inside translate env mine →
      ∀ (values : Values (SideValue model side) (collectedSequencesAt size collected ++ carried)),
        Agrees inside (translate.extendCollected size collected carried)
          (Environment.bindAll env values)
          (Environment.bindAll mine
            (ownCollected model side role inside size carried collected values))
  | [], _, _, _, _, _, agrees, values => Agrees.extend carried agrees values
  | located :: rest, _, _, _, _, _, agrees, .cons value values =>
      Agrees.extendOneCollected agrees size located value
        (ownCollected model side role inside size carried rest values)
        (fun later => Translation.extendCollected size later rest carried) _
        (fun _ _ agrees' => Agrees.extendCollected size carried rest agrees' values) _ rfl

/-- The results of a loop that the role is outside of. -/
theorem Agrees.passedCollected {Γ₀ : List Located} {Δ : List Ty} {base : Translation role Γ₀ Δ}
    {env₀ : Environment (SideValue model side) Γ₀} {mine : Environment model.Value Δ}
    (agrees₀ : Agrees inside base env₀ mine) (size : Option Nat) (carried : List Located)
    (operands : Operands Γ₀ carried) :
    ∀ (collected : List Located) {Γ : List Located} {translate : Translation role Γ Δ}
      {env : Environment (SideValue model side) Γ}
      (later : Translation role (bindAll Γ (collectedSequencesAt size collected ++ carried)) Δ),
      Translation.passedCollected base size translate collected carried operands = some later →
      Agrees inside translate env mine →
      ∀ (sequences : Values (SideValue model side) (collectedSequencesAt size collected)),
        Agrees inside later
          (Environment.bindAll env (sequences.append (Operands.eval env₀ operands))) mine
  | [], _, _, _, later, found, agrees, .nil => by
      cases found
      exact Agrees.passed agrees₀ carried agrees operands
  | located :: rest, _, translate, env, later, found, agrees, .cons value sequences => by
      unfold Translation.passedCollected at found
      split at found
      · rename_i outside
        exact Agrees.passedCollected agrees₀ size carried operands rest later found
          (agrees.absent ⟨.seq located.type size, located.holder⟩ outside value) sequences
      · cases found

end Values

/-! ## Agreement on the role's copy -/

theorem rolesBelow_mem {bound : Nat} {roles : List Nat} (below : rolesBelow bound roles = true)
    {role : Nat} (member : role ∈ roles) : Nat.blt role bound = true := by
  simp only [rolesBelow, List.all_eq_true] at below
  exact below role member

section Copies

variable {model : Model} {side : Side} {role : Nat} {inside : side role = true}
  {Γ : List Located} {Δ : List Ty}
  {translate : Translation role Γ Δ} {env : Environment (SideValue model side) Γ}
  {mine : Environment model.Value Δ}

theorem ownCopyOne_none {type : Ty} {participant : Nat} {reference : Var Γ ⟨type, participant⟩}
    {later : Option (Var Δ type)} :
    ∀ (present : Bool) (known : Nat.beq participant role = present),
      ownCopyOne translate type participant reference later present known = none →
        present = false ∧ later = none
  | true, _, missing => nomatch missing
  | false, _, missing => ⟨rfl, missing⟩

theorem ownCopyOne_some {type : Ty} {participant : Nat} {reference : Var Γ ⟨type, participant⟩}
    {later : Option (Var Δ type)} {copy : Var Δ type} :
    ∀ (present : Bool) (known : Nat.beq participant role = present),
      ownCopyOne translate type participant reference later present known = some copy →
        (∃ member : Nat.beq participant role = true,
          copy = translate.own (located := ⟨type, participant⟩) reference member) ∨
        (Nat.beq participant role = false ∧ later = some copy)
  | true, known, found => .inl ⟨known, (Option.some.inj found).symm⟩
  | false, known, found => .inr ⟨known, found⟩

/-- The role is not a participant: no copy is the role's. -/
theorem ownCopy_none (type : Ty) :
    ∀ (participants : List Nat) (operands : Operands Γ (Located.ofRoles type participants)),
      ownCopy translate type participants operands = none →
        ∀ participant ∈ participants, Nat.beq participant role = false
  | [], _, _, _, member => nomatch member
  | head :: rest, .cons reference values, missing, participant, member => by
      have parts := ownCopyOne_none (translate := translate) (Nat.beq head role) rfl missing
      rcases List.mem_cons.mp member with rfl | later
      · exact parts.1
      · exact ownCopy_none type rest values parts.2 participant later

/-- The role is a participant, the participants are distinct, and the role is the only
one of them in the side: the side agrees on the role's copy. -/
theorem ownCopy_agreed (agrees : Agrees inside translate env mine) (type : Ty) {α : Type}
    (same : model.Value type → model.Value type → Bool) (onValue : model.Value type → α)
    (onDisagree : α) :
    ∀ (participants : List Nat) (operands : Operands Γ (Located.ofRoles type participants))
      (copy : Var Δ type), ownCopy translate type participants operands = some copy →
      distinctNumbers participants = true →
      (∀ participant ∈ participants, side participant = Nat.beq participant role) →
      ∀ (onNone : participants.any side = false → α),
        agreed same side onValue onDisagree participants
            (unmapValues (F := SideValue model side) (fun role => ⟨type, role⟩) participants
              (Operands.eval env operands)) onNone =
          onValue (mine copy)
  | [], _, _, found, _, _, _ => by cases found
  | head :: rest, .cons reference values, copy, found, distinct, only, onNone => by
      have parts : occursIn rest head = false ∧ distinctNumbers rest = true := by
        simpa only [distinctNumbers, Bool.and_eq_true, Bool.not_eq_true'] using distinct
      have restOnly : ∀ participant ∈ rest, side participant = Nat.beq participant role :=
        fun participant member => only participant (List.mem_cons_of_mem _ member)
      rcases ownCopyOne_some (translate := translate) (Nat.beq head role) rfl found with
        ⟨present, rfl⟩ | ⟨outside, found⟩
      · have headInside : side head = true := (only head List.mem_cons_self).trans present
        rw [agreed_present headInside]
        refine (agreeWith_none same side onValue onDisagree _ rest _ fun other member => ?_).trans ?_
        · rw [restOnly other member]
          cases decided : Nat.beq other role with
          | false => rfl
          | true =>
              have equal : other = head :=
                (Nat.eq_of_beq_eq_true decided).trans (Nat.eq_of_beq_eq_true present).symm
              exact Bool.noConfusion (parts.1.symm.trans ((occursIn_iff rest head).mpr (equal ▸ member)))
        · exact congrArg onValue (agrees.value (located := ⟨type, head⟩) reference present).symm
      · have absent : side head = false := (only head List.mem_cons_self).trans outside
        rw [agreed_absent absent]
        exact ownCopy_agreed agrees type same onValue onDisagree rest values copy found parts.2
          restOnly _

/-- The role is a participant, the participants are distinct, and the role is the only
one of them in the side: every copy held in the side is the role's. -/
theorem ownCopy_held (agrees : Agrees inside translate env mine) (type : Ty) :
    ∀ (participants : List Nat) (operands : Operands Γ (Located.ofRoles type participants))
      (copy : Var Δ type), ownCopy translate type participants operands = some copy →
      distinctNumbers participants = true →
      (∀ participant ∈ participants, side participant = Nat.beq participant role) →
      ∀ {participant : Nat} (position : Var participants participant)
        (member : side participant = true),
        Held.value (side participant) member
            ((unmapValues (F := SideValue model side) (fun role => ⟨type, role⟩) participants
              (Operands.eval env operands)).get position) =
          mine copy
  | [], _, _, found, _, _, _, _, _ => by cases found
  | head :: rest, .cons reference values, copy, found, distinct, only, participant, position,
      member => by
      have parts : occursIn rest head = false ∧ distinctNumbers rest = true := by
        simpa only [distinctNumbers, Bool.and_eq_true, Bool.not_eq_true'] using distinct
      have restOnly : ∀ participant ∈ rest, side participant = Nat.beq participant role :=
        fun participant member => only participant (List.mem_cons_of_mem _ member)
      rcases ownCopyOne_some (translate := translate) (Nat.beq head role) rfl found with
        ⟨present, rfl⟩ | ⟨outside, found⟩
      · cases position with
        | here => exact (agrees.value (located := ⟨type, head⟩) reference present).symm
        | there position =>
            have inside' := position_mem position
            have decided : Nat.beq participant role = true :=
              (restOnly participant inside').symm.trans member
            have equal : participant = head :=
              (Nat.eq_of_beq_eq_true decided).trans (Nat.eq_of_beq_eq_true present).symm
            exact Bool.noConfusion
              (parts.1.symm.trans ((occursIn_iff rest head).mpr (equal ▸ inside')))
      · cases position with
        | here =>
            exact Bool.noConfusion
              (((only head List.mem_cons_self).trans outside).symm.trans member)
        | there position =>
            exact ownCopy_held agrees type rest values copy found parts.2 restOnly position member

/-- The role is not a participant of a `repeat` when it has no count operand of its own. -/
theorem ownCountOperands_none (participants : List Nat) :
    ∀ (count : RepeatCount) (operands : Operands Γ (count.operands participants)),
      ownCountOperands translate participants count operands = none →
        ∀ participant ∈ participants, Nat.beq participant role = false
  | .static _, _, missing, participant, member => by
      cases outside : Nat.beq participant role with
      | false => rfl
      | true =>
          have found : occursIn participants role = true :=
            (occursIn_iff participants role).mpr (Nat.eq_of_beq_eq_true outside ▸ member)
          simp only [ownCountOperands, found, Bool.cond_true] at missing
          cases missing
  | .runtime _, operands, missing, participant, member => by
      change (match ownCopy translate .nat participants operands with
        | some copy => some (Values.cons copy Values.nil)
        | none => none) = none at missing
      split at missing
      · cases missing
      · rename_i none_
        exact ownCopy_none .nat participants operands none_ participant member

/-- The role is a participant of a `repeat`, the participants are distinct, and the role is
the only one of them in the side: the side agrees on the count of the role's loop. -/
theorem ownCountOperands_agreed (agrees : Agrees inside translate env mine) {α : Type}
    (onValue : Nat → α) (onDisagree : α) (participants : List Nat) :
    ∀ (count : RepeatCount) (operands : Operands Γ (count.operands participants))
      (copies : Operands Δ count.ownOperands),
      ownCountOperands translate participants count operands = some copies →
      distinctNumbers participants = true →
      (∀ participant ∈ participants, side participant = Nat.beq participant role) →
      ∀ (onNone : participants.any side = false → α),
        agreed Nat.beq side onValue onDisagree participants
            (repeatCopies model side participants count (Operands.eval env operands)) onNone =
          onValue (ownCount model count (Operands.eval mine copies))
  | .static number, _, _, found, _, only, onNone => by
      have member : occursIn participants role = true := by
        cases known : occursIn participants role with
        | true => rfl
        | false =>
            simp only [ownCountOperands, known, Bool.cond_false] at found
            cases found
      have present : participants.any side = true :=
        List.any_eq_true.mpr ⟨role, (occursIn_iff participants role).mp member, inside⟩
      exact agreed_equal Nat.beq side _ _ Nat.beq_refl number participants _ _
        (staticCopies_get model side number participants) present
  | .runtime _, operands, copies, found, distinct, only, onNone => by
      change (match ownCopy translate .nat participants operands with
        | some copy => some (Values.cons copy Values.nil)
        | none => none) = some copies at found
      split at found
      · rename_i copy counted
        cases found
        exact ownCopy_agreed agrees .nat Nat.beq _ _ participants operands copy counted distinct
          only onNone
      · cases found

end Copies

/-! ## Applications -/

section Applied

variable {model : Model} {side : Side} {role : Nat} {inside : side role = true}

/-- The callee's side of an application has the formal role as its only member, when
the role map sends exactly the formal role to the role. -/
theorem calleeSide_only {bound formal roles : Nat} {roleMap : RoleMap}
    (within : calleeSide bound role formal roles roleMap = true) (only : side.Only role bound) :
    (Side.preimage roleMap side).Only formal roles := by
  intro callee below
  simp only [calleeSide, List.all_eq_true, Bool.and_eq_true] at within
  have facts := within callee (List.mem_range.mpr (Nat.blt_eq.mp below))
  exact (only _ facts.1).trans ((agreeBool_decides _ _).mp facts.2)

theorem eval_consCalled {Δ : List Ty} (mine : Environment model.Value Δ) {type : Ty}
    {rest : List Ty} (expectedRest : Values model.Value rest) :
    ∀ (returned : Bool) (expected : returned = true → model.Value type)
      (candidate : Option (Var Δ type)) (tail : Option (Operands Δ rest))
      (operands : Operands Δ (keep returned type rest)),
      consCalled returned candidate tail = some operands →
      (∀ reference, candidate = some reference → ∀ kept, mine reference = expected kept) →
      (∀ values, tail = some values → Operands.eval mine values = expectedRest) →
        Operands.eval mine operands = consKept returned expected expectedRest
  | true, expected, some reference, some values, _, found, head, later => by
      cases found
      have first := head reference rfl rfl
      have others := later values rfl
      show Values.cons (mine reference) (Operands.eval mine values) =
        Values.cons (expected rfl) expectedRest
      rw [first, others]
  | false, _, _, some values, _, found, _, later => by
      cases found
      exact later values rfl
  | true, _, none, _, _, found, _, _ => by cases found
  | true, _, some _, none, _, found, _, _ => by cases found
  | false, _, _, none, _, found, _, _ => by cases found

theorem heldArgument_value {Γ : List Located} {Δ : List Ty} {translate : Translation role Γ Δ}
    {env : Environment (SideValue model side) Γ} {mine : Environment model.Value Δ}
    (agrees : Agrees inside translate env mine) (located : Located) (reference : Var Γ located) :
    ∀ (held : Bool) (known : Nat.beq located.holder role = held) (image : Var Δ located.type),
      heldArgument translate located reference held known = some image →
        ∀ (holderInside : side located.holder = true),
          mine image = roleValue model side located holderInside (env reference)
  | true, known, _, found, _ => by
      cases found
      exact agrees.value reference known
  | false, _, _, found, _ => by cases found

/-- The operands of a call are the values of the callee's side that the formal role
holds. -/
theorem eval_calledArguments {Γ : List Located} {Δ : List Ty} {translate : Translation role Γ Δ}
    {env : Environment (SideValue model side) Γ} {mine : Environment model.Value Δ}
    (agrees : Agrees inside translate env mine) (roleMap : RoleMap) (formal : Nat)
    (calleeInside : Side.preimage roleMap side formal = true) :
    ∀ (inputs : List Located) (arguments : Operands Γ (inputs.map (Located.rename roleMap)))
      (operands : Operands Δ (own formal inputs)),
      calledArguments translate roleMap formal inputs arguments = some operands →
        Operands.eval mine operands =
          ownValues model (Side.preimage roleMap side) formal calleeInside inputs
            (unmapValues (F := SideValue model side) (Located.rename roleMap) inputs
              (Operands.eval env arguments))
  | [], .nil, _, found => by cases found; rfl
  | located :: rest, .cons reference values, operands, found =>
      eval_consCalled mine _ _ _ _ _ operands found
        (fun image at_ kept => heldArgument_value agrees (located.rename roleMap) reference _ rfl
          image at_ (Side.holds_own (side := Side.preimage roleMap side) calleeInside kept))
        (fun tail at_ => eval_calledArguments agrees roleMap formal calleeInside rest values tail at_)

/-- One result of a call. `own` is what the role's program gets for it when the call
returns it; it is the role's value of the result. -/
theorem Agrees.calledOne {Γ Γ' : List Located} {Δ : List Ty} {translate : Translation role Γ Δ}
    {env : Environment (SideValue model side) Γ} {mine : Environment model.Value Δ}
    (agrees : Agrees inside translate env mine) (located : Located)
    (value : SideValue model side located) {later : List Ty} (tail : Values model.Value later)
    (next : {Δ' : List Ty} → Translation role (located :: Γ) Δ' →
      Option (Translation role Γ' (bindAll Δ' later)))
    (env' : Environment (SideValue model side) Γ')
    (nextAgrees : ∀ {Δ' : List Ty} (translate' : Translation role (located :: Γ) Δ')
      (mine' : Environment model.Value Δ'), Agrees inside translate' (env.push value) mine' →
        ∀ result, next translate' = some result →
          Agrees inside result env' (Environment.bindAll mine' tail)) :
    ∀ (returned held : Bool) (own : returned = true → model.Value located.type),
      (∀ (member : Nat.beq located.holder role = true) (kept : returned = true),
        own kept = roleValue model side located (Side.holds_own inside member) value) →
      ∀ (known : Nat.beq located.holder role = held)
        (result : Translation role Γ' (bindAll Δ (keep returned located.type later))),
        Translation.calledOne translate located later next returned held known = some result →
          Agrees inside result env' (Environment.bindAll mine (consKept returned own tail))
  | true, true, _, same, known, result, found =>
      nextAgrees _ _ (agrees.present located value _ fun member => same member rfl) result found
  | false, false, _, _, known, result, found =>
      nextAgrees _ _ (agrees.absent located known value) result found
  | true, false, _, _, _, _, found => by cases found
  | false, true, _, _, _, _, found => by cases found

/-- The results of a call: what the callee's program returns for the formal role is
what the role holds of the application's results. -/
theorem Agrees.called (roleMap : RoleMap) (formal : Nat)
    (calleeInside : Side.preimage roleMap side formal = true) :
    ∀ (outputs : List Located) {Γ : List Located} {Δ : List Ty} {translate : Translation role Γ Δ}
      {env : Environment (SideValue model side) Γ} {mine : Environment model.Value Δ}
      (later : Translation role (bindAll Γ (outputs.map (Located.rename roleMap)))
        (bindAll Δ (own formal outputs))),
      translate.called roleMap formal outputs = some later → Agrees inside translate env mine →
      ∀ (values : Values (SideValue model (Side.preimage roleMap side)) outputs),
        Agrees inside later
          (Environment.bindAll env
            (remapValues (F := SideValue model side) (Located.rename roleMap) outputs values))
          (Environment.bindAll mine
            (ownValues model (Side.preimage roleMap side) formal calleeInside outputs values))
  | [], _, _, _, _, _, later, found, agrees, .nil => by
      cases found
      exact agrees
  | located :: rest, _, _, _, _, _, later, found, agrees, .cons value values =>
      Agrees.calledOne agrees (located.rename roleMap) value
        (ownValues model (Side.preimage roleMap side) formal calleeInside rest values)
        (fun later => Translation.called roleMap formal later rest) _
        (fun _ _ agrees' result at_ =>
          Agrees.called roleMap formal calleeInside rest result at_ agrees' values)
        _ _ _ (fun _ _ => rfl) rfl later found

end Applied

/-! ## Nested regions -/

/-- The role's regions and the side's regions agree along the translations of their
inputs: each of the role's, on values that are the role's part of the side's inputs, is the
side's with the results restricted to the role's. -/
def RegionsAgree (model : Model) (side : Side) (role : Nat) (inside : side role = true) :
    {signatures : List (List Located × List Located)} → {targets : List (List Ty × List Ty)} →
      RegionTranslations role signatures targets →
      Values (RegionFunction (SideValue model side) (Effects model)) signatures →
      Values (RegionFunction model.Value (Effects model)) targets → Prop
  | _, _, .nil, _, _ => True
  | _, _, .cons (inputs := inputs) (outputs := outputs) (mine := owned) translate tail,
      sideRegions, roleRegions =>
      (∀ (values : Values (SideValue model side) inputs) (mine : Values model.Value owned),
        Agrees inside translate (Environment.ofValues values) (Environment.ofValues mine) →
        (roleRegions.get .here) mine =
          ((sideRegions.get .here) values).bind fun results =>
            .done (ownValues model side role inside outputs results)) ∧
        RegionsAgree model side role inside tail sideRegions.tail roleRegions.tail

section Chosen

variable {model : Model} {side : Side} {role : Nat} {inside : side role = true}

/-- The arm that a number selects: the role's arm is the side's arm, restricted. -/
theorem selectArm_agrees {captures outputs : List Located} :
    ∀ (count : Nat)
      (sideRegions : Values (RegionFunction (SideValue model side) (Effects model))
        (List.replicate count (captures, outputs)))
      (roleRegions : Values (RegionFunction model.Value (Effects model))
        (List.replicate count (own role captures, own role outputs))),
      RegionsAgree model side role inside (armTranslations role captures outputs count)
        sideRegions roleRegions →
      ∀ (number : Fin count) (values : Values (SideValue model side) captures),
        selectArm (own role captures, own role outputs) count roleRegions number
            (ownValues model side role inside captures values) =
          (selectArm (captures, outputs) count sideRegions number values).bind fun results =>
            .done (ownValues model side role inside outputs results)
  | 0, _, _, _, number, _ => number.elim0
  | _ + 1, _, _, agree, ⟨0, _⟩, values => agree.1 values _ (Agrees.initial captures values)
  | count + 1, sideRegions, roleRegions, agree, ⟨number + 1, below⟩, values =>
      selectArm_agrees count sideRegions.tail roleRegions.tail agree.2
        ⟨number, Nat.lt_of_succ_lt_succ below⟩ values

/-- A copy that is the first alternative, when it is held: its payload. -/
theorem firstPayload_same {First Later : Type} (payload : First) :
    ∀ (present : Bool) (copy : Held (First ⊕ Later) present),
      (∀ member : present = true, Held.value present member copy = .inl payload) →
      ∃ head, firstPayload present copy = some head ∧
        ∀ member : present = true, Held.value present member head = payload
  | true, .inl found, same => ⟨found, rfl, fun _ => Sum.inl.inj (same rfl)⟩
  | true, .inr _, same => nomatch same rfl
  | false, _, _ => ⟨PUnit.unit, rfl, fun member => nomatch member⟩

/-- A copy that is a later alternative, when it is held: the copy among the later ones. -/
theorem laterCopy_same {First Later : Type} (later : Later) :
    ∀ (present : Bool) (copy : Held (First ⊕ Later) present),
      (∀ member : present = true, Held.value present member copy = .inr later) →
      ∃ head, laterCopy present copy = some head ∧
        ∀ member : present = true, Held.value present member head = later
  | true, .inr found, same => ⟨found, rfl, fun _ => Sum.inr.inj (same rfl)⟩
  | true, .inl _, same => nomatch same rfl
  | false, _, _ => ⟨PUnit.unit, rfl, fun member => nomatch member⟩

/-- Copies held in the side that are all the first alternative with one payload: every
payload held in the side is that payload. -/
theorem firstPayloads_same (payload : Ty) (rest : List Ty) (value : model.Value payload) :
    ∀ (roles : List Nat)
      (copies : Values (fun role => Held (Ty.Variant model.Carrier (payload :: rest)) (side role))
        roles),
      (∀ {role : Nat} (position : Var roles role) (member : side role = true),
        Held.value (side role) member (copies.get position) = .inl value) →
      ∃ payloads, firstPayloads model side payload rest roles copies = some payloads ∧
        ∀ {role : Nat} (position : Var roles role) (member : side role = true),
          Held.value (side role) member (payloads.get position) = value
  | [], _, _ => ⟨.nil, rfl, fun position => position.elimNil⟩
  | role :: roles, .cons copy copies, same => by
      obtain ⟨tail, found, each⟩ := firstPayloads_same payload rest value roles copies
        (fun position member => same position.there member)
      obtain ⟨head, headFound, headValue⟩ := firstPayload_same value (side role) copy
        (fun member => same .here member)
      refine ⟨.cons head tail, ?_, ?_⟩
      · show consFound (firstPayload (side role) copy)
          (firstPayloads model side payload rest roles copies) = _
        rw [headFound, found]
        rfl
      · intro other position member
        cases position with
        | here => exact headValue member
        | there position => exact each position member

/-- Copies held in the side that are all one later alternative: every copy held in the
side, as a copy of the variant of the later alternatives, is that one. -/
theorem laterCopies_same (payload : Ty) (rest : List Ty) (value : Ty.Variant model.Carrier rest) :
    ∀ (roles : List Nat)
      (copies : Values (fun role => Held (Ty.Variant model.Carrier (payload :: rest)) (side role))
        roles),
      (∀ {role : Nat} (position : Var roles role) (member : side role = true),
        Held.value (side role) member (copies.get position) = .inr value) →
      ∃ later, laterCopies model side payload rest roles copies = some later ∧
        ∀ {role : Nat} (position : Var roles role) (member : side role = true),
          Held.value (side role) member (later.get position) = value
  | [], _, _ => ⟨.nil, rfl, fun position => position.elimNil⟩
  | role :: roles, .cons copy copies, same => by
      obtain ⟨tail, found, each⟩ := laterCopies_same payload rest value roles copies
        (fun position member => same position.there member)
      obtain ⟨head, headFound, headValue⟩ := laterCopy_same value (side role) copy
        (fun member => same .here member)
      refine ⟨.cons head tail, ?_, ?_⟩
      · show consFound (laterCopy (side role) copy)
          (laterCopies model side payload rest roles copies) = _
        rw [headFound, found]
        rfl
      · intro other position member
        cases position with
        | here => exact headValue member
        | there position => exact each position member

/-- The region of the alternative that the role's copy is: the role's region, on its
payload, is the side's region of that alternative, on the payloads held in the side,
restricted. Every copy held in the side is the role's. -/
theorem matchProcess_agrees {participants : List Nat} {captures outputs : List Located} :
    ∀ (alternatives : List Ty)
      (sideRegions : Values (RegionFunction (SideValue model side) (Effects model))
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs)))
      (roleRegions : Values (RegionFunction model.Value (Effects model))
        (alternatives.map fun payload => (payload :: own role captures, own role outputs))),
      RegionsAgree model side role inside
        (alternativeTranslations role participants captures outputs alternatives) sideRegions
        roleRegions →
      ∀ (copies : Values
          (fun participant => Held (Ty.Variant model.Carrier alternatives) (side participant))
          participants)
        (value : Ty.Variant model.Carrier alternatives),
        (∀ {participant : Nat} (position : Var participants participant)
          (member : side participant = true),
          Held.value (side participant) member (copies.get position) = value) →
        ∀ (values : Values (SideValue model side) captures),
          matchProcess model (own role captures) (own role outputs) alternatives roleRegions value
              (ownValues model side role inside captures values) =
            (alternativeProcess model side participants captures outputs alternatives sideRegions
              (alternativeNumber alternatives value) copies values).bind fun results =>
              .done (ownValues model side role inside outputs results)
  | [], _, _, _, _, value, _, _ => nomatch value
  | payload :: rest, sideRegions, roleRegions, agree, copies, .inl mine, same, values => by
      obtain ⟨payloads, found, each⟩ :=
        firstPayloads_same payload rest mine participants copies same
      show (roleRegions.get .here) (.cons mine (ownValues model side role inside captures values)) =
        (alternativeProcess model side participants captures outputs (payload :: rest) sideRegions 0
          copies values).bind _
      rw [alternativeProcess_first found]
      exact agree.1 _ _ (Agrees.initialAlternative payload mine participants captures payloads each
        values)
  | payload :: rest, sideRegions, roleRegions, agree, copies, .inr later, same, values => by
      obtain ⟨laters, found, each⟩ :=
        laterCopies_same payload rest later participants copies same
      show matchProcess model (own role captures) (own role outputs) rest roleRegions.tail later _ =
        (alternativeProcess model side participants captures outputs (payload :: rest) sideRegions
          (alternativeNumber rest later + 1) copies values).bind _
      rw [alternativeProcess_later _ found]
      exact matchProcess_agrees rest sideRegions.tail roleRegions.tail agree.2 laters later each
        values

/-- The region that the role's tag selects is the region that the side selects, restricted,
when every copy of the tag held in the side is the role's. -/
theorem ownChosenRegion_agrees {participants : List Nat} {captures outputs : List Located} :
    ∀ (tag : ChoiceTag)
      (sideRegions : Values (RegionFunction (SideValue model side) (Effects model))
        (tag.regions participants captures outputs))
      (roleRegions : Values (RegionFunction model.Value (Effects model))
        (tag.ownRegions (own role captures) (own role outputs))),
      RegionsAgree model side role inside
        (choiceTranslations role participants captures outputs tag) sideRegions roleRegions →
      ∀ (copies : Values (fun participant => Held (model.Value tag.type) (side participant))
          participants)
        (value : model.Value tag.type),
        (∀ {participant : Nat} (position : Var participants participant)
          (member : side participant = true),
          Held.value (side participant) member (copies.get position) = value) →
        ∀ (values : Values (SideValue model side) captures),
          ownChosenRegion model (own role captures) (own role outputs) tag roleRegions value
              (ownValues model side role inside captures values) =
            (chosenRegion model side participants captures outputs tag sideRegions copies values
              value).bind fun results => .done (ownValues model side role inside outputs results)
  | .condition, sideRegions, roleRegions, agree, _, _, _, values =>
      selectArm_agrees 2 sideRegions roleRegions agree _ values
  | .arm count, sideRegions, roleRegions, agree, _, _, _, values =>
      selectArm_agrees count sideRegions roleRegions agree _ values
  | .alternative _ alternatives, sideRegions, roleRegions, agree, copies, value, same, values =>
      matchProcess_agrees alternatives sideRegions roleRegions agree copies value same values

end Chosen

section Meaning

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {programs : List RoleHeader} {deployed : Bool}
  {functionTable : FunctionTable model functions} {table : ProtocolTable model protocols}
  {called : RoleTable model programs} {label : Nat → Site} {side : Side} {role bound : Nat}
  {inside : side role = true} {callees : ProjectedCallees protocols programs}

/-- A step of a role program. -/
theorem roleMeaning_step {Δ out : List Ty}
    {op : RoleOp operations functions programs deployed} {arguments : Operands Δ op.arguments}
    {bodies : Regions (RoleDialect operations functions programs deployed) op.regions}
    {next : Region (RoleDialect operations functions programs deployed) (bindAll Δ op.results) out}
    {mine : Environment model.Value Δ} :
    (Region.letOp (dialect := RoleDialect operations functions programs deployed) op arguments bodies
        next).denote (roleMeaning model functionTable called label) mine =
      (roleOperation model functionTable called label op (Operands.eval mine arguments)
          (bodies.denote (roleMeaning model functionTable called label))).bind
        fun values =>
          next.denote (roleMeaning model functionTable called label) (Environment.bindAll mine values) :=
  rfl

/-- The announcements of a coin that another role drew: the role's `receive`s, then the
rest, are the side's replies followed by the side's rest. -/
theorem projectReceives_meaning (site : Nat) (output : Ty) {out : List Ty} :
    ∀ (receivers : List Nat), (∀ receiver ∈ receivers, side receiver = Nat.beq receiver role) →
      ∀ {Γ : List Located} {Δ : List Ty} (translate : Translation role Γ Δ)
      (rest : {Δ' : List Ty} → Translation role (bindAll Γ (Located.ofRoles output receivers)) Δ' →
        Except ProjectionRefusal (Region (RoleDialect operations functions programs deployed) Δ' out))
      (env : Environment (SideValue model side) Γ)
      (after : Values (SideValue model side) (Located.ofRoles output receivers) →
        PIR.Process (Effects model) (Values model.Value out)),
      (∀ {Δ' : List Ty} (later : Translation role (bindAll Γ (Located.ofRoles output receivers)) Δ')
        (projected : Region (RoleDialect operations functions programs deployed) Δ' out),
        rest later = .ok projected →
        ∀ (replies : Values (SideValue model side) (Located.ofRoles output receivers))
          (mine : Environment model.Value Δ'), Agrees inside later (Environment.bindAll env replies) mine →
          projected.denote (roleMeaning model functionTable called label) mine = after replies) →
      ∀ (projected : Region (RoleDialect operations functions programs deployed) Δ out),
        projectReceives role site output receivers translate rest = .ok projected →
        ∀ (mine : Environment model.Value Δ), Agrees inside translate env mine →
          projected.denote (roleMeaning model functionTable called label) mine =
            (receiverReplies model side (label site) output receivers).bind after
  | [], _, _, _, translate, rest, env, after, restMeaning, projected, projects, mine, agrees =>
      restMeaning translate projected projects .nil mine agrees
  | receiver :: receivers, only, _, _, translate, rest, env, after, restMeaning, projected, projects,
      mine, agrees => by
      have restOnly : ∀ other ∈ receivers, side other = Nat.beq other role :=
        fun other member => only other (List.mem_cons_of_mem _ member)
      unfold projectReceives at projects
      split at projects
      · rename_i present
        have receiverInside : side receiver = true := (only receiver List.mem_cons_self).trans present
        split at projects
        · rename_i next projectsNext
          simp only [Except.ok.injEq] at projects
          subst projects
          rw [receiverReplies_present model side _ output receiver receivers receiverInside, call_bind]
          show PIR.Process.call (I := Effects model) (Effect.receive _ output) _ = _
          congr 1
          funext reply
          rw [PIR.Process.bind_assoc]
          refine projectReceives_meaning site output receivers restOnly _ rest
            (env.push (ty := ⟨output, receiver⟩) (Held.of _ reply))
            (fun replies => after (.cons (Held.of _ reply) replies)) ?_ next projectsNext _
            (agrees.present ⟨output, receiver⟩ _ _ fun _ => (Held.value_of _ _ reply).symm)
          intro _ later projected projects replies mine agrees
          exact restMeaning later projected projects (.cons (Held.of _ reply) replies) mine agrees
        · cases projects
      · rename_i outside
        have absent : side receiver = false := (only receiver List.mem_cons_self).trans outside
        rw [receiverReplies_absent model side _ output receiver receivers absent,
          PIR.Process.bind_assoc]
        refine projectReceives_meaning site output receivers restOnly _ rest
          (env.push (ty := ⟨output, receiver⟩) (Held.absent _ absent))
          (fun replies => after (.cons (Held.absent _ absent) replies)) ?_ projected projects mine
          (agrees.absent ⟨output, receiver⟩ outside _)
        intro _ later projected projects replies mine agrees
        exact restMeaning later projected projects (.cons (Held.absent _ absent) replies) mine agrees

/-- The programs that the table of callees names have the meaning of the callees: the
program of a formal role is the callee for a side whose only member is the formal role,
and every callee returns without an effect for a side without any of its roles. -/
structure CalleesSound (model : Model) (table : ProtocolTable model protocols)
    (called : RoleTable model programs) (callees : ProjectedCallees protocols programs) : Prop where
  program : ∀ {header : ProtocolHeader} (callee : Var protocols header) (formal : Nat)
    (program : Var programs (roleHeader formal header)), callees.find callee formal = some program →
    ∀ (path : List Nat) (side : Side), side.Only formal header.roles →
      ∀ (inside : side formal = true) (arguments : Values (SideValue model side) header.inputs),
        called.get program path (ownValues model side formal inside header.inputs arguments) =
          ((table.get callee) path side arguments).bind fun values =>
            .done (ownValues model side formal inside header.outputs values)
  silent : ∀ {header : ProtocolHeader} (callee : Var protocols header)
    (path : List Nat) (side : Side),
      (∀ other, Nat.blt other header.roles = true → side other = false) →
      ∀ (arguments : Values (SideValue model side) header.inputs),
        ∃ values, (table.get callee) path side arguments = .done values

mutual
  /-- The projected program of a region has the meaning of the one-role side. -/
  theorem projectRegion_meaning (sound : CalleesSound model table called callees)
      (only : side.Only role bound) (inside : side role = true) {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions protocols deployed) Γ out)
        {Δ : List Ty} (translate : Translation role Γ Δ)
        (projected : Region (RoleDialect operations functions programs deployed) Δ (own role out)),
        projectRegion role bound callees region translate = .ok projected →
        ∀ (env : Environment (SideValue model side) Γ) (mine : Environment model.Value Δ),
          Agrees inside translate env mine →
          projected.denote (roleMeaning model functionTable called label) mine =
            (region.denote (labelledMeaning model label functionTable table side) env).bind
              fun values => .done (ownValues model side role inside out values)
    | .ret values, _, translate, projected, projects, env, mine, agrees => by
        simp only [projectRegion, Except.ok.injEq] at projects
        subst projects
        show PIR.Process.done _ = PIR.Process.done _
        rw [eval_ownOperands agrees]
    | .stop reason, _, _, projected, projects, _, _, _ => by
        simp only [projectRegion, Except.ok.injEq] at projects
        subst projects
        rfl
    | .bind (mid := mid) body rest, _, translate, projected, projects, env, mine, agrees => by
        unfold projectRegion at projects
        split at projects
        · rename_i projectedBody projectedRest projectsBody projectsRest
          simp only [Except.ok.injEq] at projects
          subst projects
          have bodyMeaning :
              projectedBody.denote (roleMeaning model functionTable called label) mine = _ :=
            projectRegion_meaning sound only inside body translate projectedBody projectsBody env mine agrees
          show (projectedBody.denote (roleMeaning model functionTable called label) mine).bind _ =
            ((body.denote (labelledMeaning model label functionTable table side) env).bind _).bind _
          rw [bodyMeaning, PIR.Process.bind_assoc, PIR.Process.bind_assoc]
          congr 1
          funext values
          exact projectRegion_meaning sound only inside rest _ projectedRest projectsRest _ _
            (Agrees.extend mid agrees values)
        · cases projects
        · cases projects
    | .letOp (.at holder op bodies) arguments nested rest, _, translate, projected, projects, env,
        mine, agrees => by
        cases nested
        unfold projectRegion at projects
        split at projects
        · cases projects
        · rename_i within present
          have holderInside : side holder = true := (only holder within).trans present
          split at projects
          · rename_i projectedRest projectsRest
            simp only [Except.ok.injEq] at projects
            subst projects
            rw [labelled_step (labelled_at_present (model := model) (label := label)
              (functionTable := functionTable) (table := table) (side := side) holderInside),
              roleMeaning_step]
            show (localOperation model functionTable op _ _).bind _ = _
            rw [eval_ownArguments agrees holder present holderInside, PIR.Process.bind_assoc,
              PIR.Process.bind_assoc]
            congr 1
            funext values
            have later := Agrees.presentAll holder holderInside (LocalOp.results op) agrees
              (holdValues (side holder) values)
            rw [presentValues_holdValues] at later
            exact projectRegion_meaning sound only inside rest _ projectedRest projectsRest _ _ later
          · cases projects
        · rename_i within outside
          have absent : side holder = false := (only holder within).trans outside
          rw [labelled_step_done (labelled_at_absent (model := model) (label := label)
            (functionTable := functionTable) (table := table) (side := side) absent)]
          exact projectRegion_meaning sound only inside rest _ projected projects _ mine
            (Agrees.absentAll holder outside (LocalOp.results op) agrees _)
    | .letOp (.exchange sender receiver site type) arguments nested rest, _, translate, projected,
        projects, env, mine, agrees => by
        cases nested
        have sent : ∀ (sends : Nat.beq sender role = true) (senderIn : side sender = true),
            mine (translate.own (located := ⟨type, sender⟩) (arguments.get .here) sends) =
              Held.value (side sender) senderIn ((Operands.eval env arguments).get .here) := by
          intro sends senderIn
          exact (agrees.value (located := ⟨type, sender⟩) (arguments.get .here) sends).trans
            (congrArg _ (Operands.get_eval env arguments .here).symm)
        unfold projectRegion at projects
        split at projects
        · cases projects
        · rename_i within sends receives
          simp only [Bool.and_eq_true] at within
          have senderInside : side sender = true := (only sender within.1).trans sends
          have receiverInside : side receiver = true := (only receiver within.2).trans receives
          rw [labelled_step_done (labelled_exchange_internal (model := model) (label := label)
            (functionTable := functionTable) (table := table) (side := side) senderInside
            receiverInside)]
          refine projectRegion_meaning sound only inside rest _ projected projects _ mine
            (agrees.same ⟨type, receiver⟩ _ _ ?_)
          intro _
          rw [sent sends senderInside]
          exact (Held.value_of _ _ _).symm
        · rename_i within sends receives
          simp only [Bool.and_eq_true] at within
          have senderInside : side sender = true := (only sender within.1).trans sends
          have receiverAbsent : side receiver = false := (only receiver within.2).trans receives
          split at projects
          · rename_i projectedRest projectsRest
            simp only [Except.ok.injEq] at projects
            subst projects
            rw [labelled_step_call (labelled_exchange_send (model := model) (label := label)
              (functionTable := functionTable) (table := table) (side := side) senderInside
              receiverAbsent), call_bind]
            show PIR.Process.call (I := Effects model) (Effect.send _ type
              (mine (translate.own (located := ⟨type, sender⟩) (arguments.get .here) sends))) _ = _
            rw [sent sends senderInside]
            congr 1
            funext reply
            exact projectRegion_meaning sound only inside rest _ projectedRest projectsRest _ mine
              (agrees.absent ⟨type, receiver⟩ receives _)
          · cases projects
        · rename_i within sends receives
          simp only [Bool.and_eq_true] at within
          have senderAbsent : side sender = false := (only sender within.1).trans sends
          have receiverInside : side receiver = true := (only receiver within.2).trans receives
          split at projects
          · rename_i projectedRest projectsRest
            simp only [Except.ok.injEq] at projects
            subst projects
            rw [labelled_step_call (labelled_exchange_receive (model := model) (label := label)
              (functionTable := functionTable) (table := table) (side := side) senderAbsent
              receiverInside), call_bind]
            show PIR.Process.call (I := Effects model) (Effect.receive _ type) _ = _
            congr 1
            funext reply
            exact projectRegion_meaning sound only inside rest _ projectedRest projectsRest _ _
              (agrees.present ⟨type, receiver⟩ _ _ fun _ => (Held.value_of _ _ reply).symm)
          · cases projects
        · rename_i within sends receives
          simp only [Bool.and_eq_true] at within
          have senderAbsent : side sender = false := (only sender within.1).trans sends
          have receiverAbsent : side receiver = false := (only receiver within.2).trans receives
          rw [labelled_step_done (labelled_exchange_outside (model := model) (label := label)
            (functionTable := functionTable) (table := table) (side := side) senderAbsent
            receiverAbsent)]
          exact projectRegion_meaning sound only inside rest _ projected projects _ mine
            (agrees.absent ⟨type, receiver⟩ receives _)
    | .letOp (.sample owner site (inputs := inputs) (output := output) law populated) arguments nested rest, _,
        translate, projected, projects, env, mine, agrees => by
        cases nested
        unfold projectRegion at projects
        split at projects
        · cases projects
        · rename_i within owns
          have ownerInside : side owner = true := (only owner within).trans owns
          split at projects
          · rename_i projectedRest projectsRest
            simp only [Except.ok.injEq] at projects
            subst projects
            rw [labelled_step_call (labelled_sample_owner (model := model) (label := label)
              (functionTable := functionTable) (table := table) (side := side) ownerInside),
              call_bind]
            show PIR.Process.call (I := Effects model) (Effect.sample _ _ (Operands.eval mine _)) _ = _
            rw [eval_ownArguments agrees owner owns ownerInside]
            congr 1
            funext reply
            exact projectRegion_meaning sound only inside rest _ projectedRest projectsRest _ _
              (agrees.present ⟨output, owner⟩ _ _ fun _ => (Held.value_of _ _ reply).symm)
          · cases projects
        · rename_i within outside
          have absent : side owner = false := (only owner within).trans outside
          rw [labelled_step_done (labelled_sample_outside (model := model) (label := label)
            (functionTable := functionTable) (table := table) (side := side) absent)]
          exact projectRegion_meaning sound only inside rest _ projected projects _ mine
            (agrees.absent ⟨output, owner⟩ outside _)
    | .letOp (.draw owner receivers site (inputs := inputs) (output := output) law populated) arguments nested
        rest, _, translate, projected, projects, env, mine, agrees => by
        cases nested
        unfold projectRegion at projects
        split at projects
        · cases projects
        · rename_i within owns
          simp only [Bool.and_eq_true] at within
          have ownerInside : side owner = true := (only owner within.1).trans owns
          have receiversOnly : ∀ receiver ∈ receivers, side receiver = Nat.beq receiver role :=
            fun receiver member => only receiver (rolesBelow_mem within.2 member)
          split at projects
          · rename_i projectedRest projectsRest
            simp only [Except.ok.injEq] at projects
            subst projects
            rw [labelled_step_call (labelled_draw_owner (model := model) (label := label)
              (functionTable := functionTable) (table := table) (side := side) ownerInside),
              call_bind]
            show PIR.Process.call (I := Effects model) (Effect.draw _ _ (Operands.eval mine _)) _ = _
            rw [eval_ownArguments agrees owner owns ownerInside]
            congr 1
            funext reply
            exact projectRegion_meaning sound only inside rest _ projectedRest projectsRest _ _
              (agrees.drawn owner output receivers receiversOnly reply)
          · cases projects
        · rename_i within outside
          simp only [Bool.and_eq_true] at within
          have absent : side owner = false := (only owner within.1).trans outside
          have receiversOnly : ∀ receiver ∈ receivers, side receiver = Nat.beq receiver role :=
            fun receiver member => only receiver (rolesBelow_mem within.2 member)
          rw [labelled_step (labelled_draw_outside (model := model) (label := label)
            (functionTable := functionTable) (table := table) (side := side) absent),
            PIR.Process.bind_assoc, PIR.Process.bind_assoc]
          refine projectReceives_meaning site output receivers receiversOnly _ _
            (env.push (ty := ⟨output, owner⟩) (Held.absent _ absent)) _ ?_ projected projects mine
            (agrees.absent ⟨output, owner⟩ outside _)
          intro _ later projected projects replies mine agrees
          exact projectRegion_meaning sound only inside rest later projected projects _ mine agrees
    | .letOp (.repeat participants count carried collected captures covered) arguments
        (.cons body .nil) rest, _, translate, projected, projects, env, mine, agrees => by
        obtain ⟨countOperands, stateOperands, rfl⟩ :
            ∃ counts state, arguments = Values.append counts state :=
          ⟨_, _, (Values.append_split (count.operands participants) arguments).symm⟩
        obtain ⟨carriedOperands, captureOperands, rfl⟩ :
            ∃ initial captured, stateOperands = Values.append initial captured :=
          ⟨_, _, (Values.append_split carried stateOperands).symm⟩
        unfold projectRegion at projects
        simp only [Values.split_append] at projects
        split at projects
        · cases projects
        · cases projects
        · rename_i within distinct
          have participantsOnly : ∀ participant ∈ participants,
              side participant = Nat.beq participant role :=
            fun participant member => only participant (rolesBelow_mem within member)
          rw [labelled_step labelled_repeat_meaning]
          simp only [repeatCounts, repeatInitial, repeatCaptured, repeatOutside, eval_append,
            Values.split_append]
          split at projects
          · rename_i copies counted
            rw [Values.split_append] at counted
            split at projects
            · rename_i projectedBody projectedRest projectsBody projectsRest
              simp only [Except.ok.injEq] at projects
              subst projects
              rw [ownCountOperands_agreed agrees _ _ participants count countOperands copies counted
                distinct participantsOnly, roleMeaning_step]
              show (ownRepeatProcess model count (own role carried) (own role collected)
                (fun iteration values =>
                  (projectedBody.retype (own_append role collected carried)).denote
                    (roleMeaning model functionTable called label)
                    (Environment.ofValues (Values.cons (ty := Ty.nat) iteration
                      (values.append (Values.split (own role carried)
                        (Values.split count.ownOperands
                          (Operands.eval mine (copies.append
                            ((ownOperands translate carried carriedOperands).append
                              (ownOperands translate captures captureOperands))))).2).2))))
                (ownCount model count (Values.split count.ownOperands
                  (Operands.eval mine (copies.append
                    ((ownOperands translate carried carriedOperands).append
                      (ownOperands translate captures captureOperands))))).1)
                (Values.split (own role carried)
                  (Values.split count.ownOperands
                    (Operands.eval mine (copies.append
                      ((ownOperands translate carried carriedOperands).append
                        (ownOperands translate captures captureOperands))))).2).1).bind _ = _
              rw [eval_append, Values.split_append, eval_append, Values.split_append,
                eval_ownOperands agrees, eval_ownOperands agrees]
              have related : ∀ (iteration : Nat) (state : Values (SideValue model side) carried),
                  (projectedBody.retype (own_append role collected carried)).denote
                      (roleMeaning model functionTable called label)
                      (Environment.ofValues (Values.cons (ty := Ty.nat) iteration
                        ((ownValues model side role inside carried state).append
                          (ownValues model side role inside captures
                            (Operands.eval env captureOperands))))) =
                    (body.denote (labelledMeaning model label functionTable table side)
                        (Environment.ofValues
                          ((heldCopies model side .nat iteration participants).append
                            (state.append (Operands.eval env captureOperands))))).bind
                      fun produced =>
                        .done ((ownValues model side role inside (collected ++ carried)
                          produced).retype (own_append role collected carried)) :=
                fun iteration state =>
                  (Region.denote_retype _ _ _ _).trans
                    ((congrArg (fun process => PIR.Process.bind process _)
                      (projectRegion_meaning sound only inside body _ projectedBody projectsBody
                        _ _
                        (Agrees.initialLoop iteration participants carried captures state
                          (Operands.eval env captureOperands)))).trans
                      (PIR.Process.bind_assoc _ _ _))
              refine (congrArg (fun process => PIR.Process.bind process _)
                (repeatProcess_own (inside := inside) count carried collected
                  (fun iteration state =>
                    body.denote (labelledMeaning model label functionTable table side)
                      (Environment.ofValues
                        ((heldCopies model side .nat iteration participants).append
                          (state.append (Operands.eval env captureOperands)))))
                  (fun iteration values =>
                    (projectedBody.retype (own_append role collected carried)).denote
                      (roleMeaning model functionTable called label)
                      (Environment.ofValues (Values.cons (ty := Ty.nat) iteration
                        (values.append (ownValues model side role inside captures
                          (Operands.eval env captureOperands))))))
                  related (ownCount model count (Operands.eval mine copies))
                  (Operands.eval env carriedOperands))).trans ?_
              rw [PIR.Process.bind_assoc, PIR.Process.bind_assoc]
              congr 1
              funext values
              exact projectRegion_meaning sound only inside rest _ projectedRest projectsRest _ _
                (Agrees.extendCollected count.size carried collected agrees values)
            · cases projects
            · cases projects
          · rename_i missing
            rw [Values.split_append] at missing
            have absent : ∀ participant ∈ participants, side participant = false :=
              fun participant member => (participantsOnly participant member).trans
                (ownCountOperands_none participants count countOperands missing participant
                  member)
            rw [agreed_none Nat.beq side _ _ participants _ _ absent]
            split at projects
            · rename_i later passed
              rw [Values.split_append, Values.split_append] at passed
              exact projectRegion_meaning sound only inside rest later projected projects _ mine
                (Agrees.passedCollected agrees count.size carried carriedOperands collected later
                  passed agrees _)
            · cases projects
    | .letOp (.choose participants tag captures outputs covered) arguments bodies rest, _, translate,
        projected, projects, env, mine, agrees => by
        obtain ⟨tagOperands, captureOperands, rfl⟩ :
            ∃ tags captured, arguments = Values.append tags captured :=
          ⟨_, _, (Values.append_split (Located.ofRoles tag.type participants) arguments).symm⟩
        unfold projectRegion at projects
        split at projects
        · cases projects
        · cases projects
        · rename_i within distinct
          have participantsOnly : ∀ participant ∈ participants,
              side participant = Nat.beq participant role :=
            fun participant member => only participant (rolesBelow_mem within member)
          rw [labelled_step labelled_choose_meaning]
          simp only [chooseTags, eval_append, Values.split_append]
          split at projects
          · rename_i copy tagged
            rw [Values.split_append] at tagged
            split at projects
            · rename_i arms projectedRest projectsArms projectsRest
              simp only [Except.ok.injEq] at projects
              subst projects
              simp only [Values.split_append]
              rw [ownCopy_agreed agrees tag.type (tag.same model.Carrier) _ _ participants tagOperands
                copy tagged distinct participantsOnly, roleMeaning_step]
              show (ownChosenRegion model (own role captures) (own role outputs) tag _ (mine copy)
                (Operands.eval mine _)).bind _ = _
              rw [eval_ownOperands agrees,
                ownChosenRegion_agrees tag _ _
                  (projectRegions_meaning sound only inside bodies _ arms projectsArms) _
                  (mine copy)
                  (ownCopy_held agrees tag.type participants tagOperands copy tagged distinct
                    participantsOnly),
                PIR.Process.bind_assoc, PIR.Process.bind_assoc]
              congr 1
              funext values
              exact projectRegion_meaning sound only inside rest _ projectedRest projectsRest _ _
                (Agrees.extend outputs agrees values)
            · cases projects
            · cases projects
          · rename_i missing
            rw [Values.split_append] at missing
            have absent : ∀ participant ∈ participants, side participant = false :=
              fun participant member => (participantsOnly participant member).trans
                (ownCopy_none tag.type participants tagOperands missing participant member)
            rw [agreed_none (tag.same model.Carrier) side _ _ participants _ _ absent]
            split at projects
            · rename_i later unheld
              exact projectRegion_meaning sound only inside rest later projected projects _ mine
                (Agrees.unheld outputs later unheld agrees _)
            · cases projects
    | .letOp (.apply (header := header) callee roleMap site permitted) arguments nested rest, _,
        translate, projected, projects, env, mine, agrees => by
        cases nested
        unfold projectRegion at projects
        split at projects
        · cases projects
        · rename_i within below
          have calleeOnly := calleeSide_only (side := side) within only
          have calleeInside := calleeOnly.inside below
          split at projects
          · cases projects
          · rename_i program found
            split at projects
            · rename_i operands later passed returned
              split at projects
              · rename_i projectedRest projectsRest
                simp only [Except.ok.injEq] at projects
                subst projects
                rw [labelled_step labelled_apply_meaning, roleMeaning_step]
                show (called.get program _ (Operands.eval mine operands)).bind _ = _
                have calleeMeaning := sound.program callee _ program found (label site).below _
                  calleeOnly calleeInside
                  (unmapValues (F := SideValue model side) (Located.rename roleMap) _
                    (Operands.eval env arguments))
                rw [eval_calledArguments agrees roleMap _ calleeInside header.inputs arguments operands
                  passed]
                refine (congrArg (fun process => PIR.Process.bind process _) calleeMeaning).trans ?_
                rw [PIR.Process.bind_assoc, PIR.Process.bind_assoc, PIR.Process.bind_assoc]
                congr 1
                funext values
                exact projectRegion_meaning sound only inside rest later projectedRest projectsRest _ _
                  (Agrees.called roleMap _ calleeInside header.outputs later returned agrees values)
              · cases projects
            · cases projects
        · rename_i within outside
          have calleeOnly := calleeSide_only (side := side) within only
          have absent : ∀ other, Nat.blt other header.roles = true →
              Side.preimage roleMap side other = false := by
            intro other below
            rw [calleeOnly other below]
            cases same : Nat.beq other (formalRole role roleMap) with
            | false => rfl
            | true =>
                rw [← Nat.eq_of_beq_eq_true same, below] at outside
                cases outside
          split at projects
          · rename_i later unheld
            obtain ⟨values, returns⟩ := sound.silent callee (label site).below _ absent
              (unmapValues (F := SideValue model side) (Located.rename roleMap) _
                (Operands.eval env arguments))
            have step : labelledOperation model label functionTable table side
                (operations := operations)
                (.apply callee roleMap site permitted) (Operands.eval env arguments)
                (Regions.denote (dialect := ProtocolDialect operations functions protocols deployed)
                  (labelledMeaning model label functionTable table side) .nil) =
                .done (remapValues (F := SideValue model side) (Located.rename roleMap) _ values) := by
              rw [labelled_apply_meaning, returns]
              rfl
            rw [labelled_step_done step]
            exact projectRegion_meaning sound only inside rest later projected projects _ mine
              (Agrees.unheld _ later unheld agrees _)
          · cases projects

  /-- The projected programs of closed regions agree with the regions of the side, along
  the translations of their inputs. -/
  theorem projectRegions_meaning (sound : CalleesSound model table called callees)
      (only : side.Only role bound) (inside : side role = true)
      {signatures : List (List Located × List Located)} {targets : List (List Ty × List Ty)} :
      ∀ (regions : Regions (ProtocolDialect operations functions protocols deployed) signatures)
        (translations : RegionTranslations role signatures targets)
        (projected : Regions (RoleDialect operations functions programs deployed) targets),
        projectRegions role bound callees regions translations = .ok projected →
          RegionsAgree model side role inside translations
            (regions.denote (labelledMeaning model label functionTable table side))
            (projected.denote (roleMeaning model functionTable called label))
    | .nil, .nil, _, _ => trivial
    | .cons body tail, .cons translate translations, projected, projects => by
        simp only [projectRegions] at projects
        split at projects
        · rename_i projectedBody projectedTail projectsBody projectsTail
          cases projects
          exact ⟨fun values mine agrees =>
              projectRegion_meaning sound only inside body _ projectedBody projectsBody _ _ agrees,
            projectRegions_meaning sound only inside tail translations projectedTail projectsTail⟩
        · cases projects
        · cases projects
end

end Meaning

end Zkc.Core
