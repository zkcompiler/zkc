module

public import Zkc.Core.Elaborate

public section

/-! Projection of a typed protocol region to one role.

A role program is a region over the role dialect: the local operations of the role, the
effects `send`, `receive`, `draw` and `sample`, a loop with the role's own count, a
choice by the role's own tag, and a call of another role program. Its context holds the
role's values only. The projection carries a translation of the role's values, from the
protocol context to the role's context; a value held by another role has no
translation.

The translation is a `Mapping` whose relation says "the role holds the value, at this
type". It is data: binding a result extends it in constant time whatever the length of
the body.

- `repeat`: a participant runs the loop with its own iteration number and, when the count
  is a value, its own count, and collects the values that it holds; for a role outside the
  participants the carried results are the carried operands, and it holds no collected
  value.
- `choose`: a participant selects the arm by its own tag, and the region of an alternative
  of a variant takes the role's own payload; a role outside holds none of the outputs.
- `apply`: the role that the role map assigns to a formal role of the callee calls the
  callee's program of that formal role; a role outside the map does nothing. The
  programs of the callees are named through a table (`ProjectedCallees`). After
  expansion a region has no `apply`, and the table is empty.

The projection decides, by evaluation, the facts about role numbers that its meaning
theorem uses: the roles an operation names are below a bound (the role count of the
definition), the participants of a `repeat` or `choose` are distinct, and the role map
of an `apply` sends exactly the chosen formal role to the role.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-! ## Role programs -/

/-- What a caller knows of a role program: the types of its inputs and outputs. -/
structure RoleHeader where
  inputs : List Ty
  outputs : List Ty
  deriving Repr, DecidableEq

/-- The operations of one role. Like local code, they do not mention protocol
headers; a call names another role program. -/
inductive RoleOp (operations : List OperationSignature) (functions : List FunctionHeader)
    (programs : List RoleHeader) (deployed : Bool) where
  /-- A local operation. -/
  | perform (op : LocalOp operations functions deployed)
      (bodies : Regions (LocalDialect operations functions deployed) op.regions)
  | send (site : Nat) (type : Ty)
  | receive (site : Nat) (type : Ty)
  /-- A draw of the role, of a law whose output type is populated. -/
  | draw (site : Nat) {inputs : List Ty} {output : Ty}
      (law : Var operations ⟨inputs, [output], .sampling⟩) (populated : output.populated = true)
  /-- A sample of the role, of a law whose output type is populated. -/
  | sample (site : Nat) {inputs : List Ty} {output : Ty}
      (law : Var operations ⟨inputs, [output], .sampling⟩) (populated : output.populated = true)
  /-- A loop of a shared `repeat`: carried values and captures, after the role's count
  when the count is a value; one region from the iteration number, the carried values and
  the captures to one value of each collected type and then the carried values. Its results
  are, per collected type, the values of the iterations in order, and then the carried
  values, as those of a local `loop`. -/
  | «repeat» (count : RepeatCount) (carried collected captures : List Ty)
  /-- A choice of a shared `choose`: the role's tag and captures; one region per arm. The
  region of an alternative of a variant takes the role's payload before the captures. -/
  | choose (tag : ChoiceTag) (captures outputs : List Ty)
  /-- A call of the program of one role of an applied protocol, at the application's
  site. -/
  | call (site : Nat) {header : RoleHeader} (callee : Var programs header)

namespace RoleOp

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {programs : List RoleHeader} {deployed : Bool}

@[expose, reducible] def arguments : RoleOp operations functions programs deployed → List Ty
  | .perform op _ => op.arguments
  | .send _ type => [type]
  | .receive .. => []
  | .draw _ (inputs := inputs) _ _ => inputs
  | .sample _ (inputs := inputs) _ _ => inputs
  | .repeat count carried _ captures => count.ownOperands ++ (carried ++ captures)
  | .choose tag captures _ => tag.type :: captures
  | .call _ (header := header) _ => header.inputs

@[expose, reducible] def results : RoleOp operations functions programs deployed → List Ty
  | .perform op _ => op.results
  | .send .. => []
  | .receive _ type => [type]
  | .draw _ (output := output) _ _ => [output]
  | .sample _ (output := output) _ _ => [output]
  | .repeat count carried collected _ => collectedSequences count.size collected ++ carried
  | .choose _ _ outputs => outputs
  | .call _ (header := header) _ => header.outputs

@[expose, reducible] def regions : RoleOp operations functions programs deployed → List (List Ty × List Ty)
  | .repeat _ carried collected captures =>
      [(.nat :: (carried ++ captures), collected ++ carried)]
  | .choose tag captures outputs => tag.ownRegions captures outputs
  | .perform .. | .send .. | .receive .. | .draw .. | .sample .. | .call .. => []

end RoleOp

@[expose, reducible] def RoleDialect (operations : List OperationSignature)
    (functions : List FunctionHeader) (programs : List RoleHeader) (deployed : Bool) : Dialect where
  Ty := Ty
  Op := RoleOp operations functions programs deployed
  arguments := RoleOp.arguments
  results := RoleOp.results
  regions := RoleOp.regions

section Meaning

variable (model : Model) {operations : List OperationSignature} {functions : List FunctionHeader}
  {programs : List RoleHeader} {deployed : Bool}

/-- The meaning of a role program with the given header, under the sites of the
applications that reached it. -/
@[expose, reducible] def RoleHeader.Meaning (header : RoleHeader) : Type :=
  (path : List Nat) → Values model.Value header.inputs →
    PIR.Process (Effects model) (Values model.Value header.outputs)

/-- The meanings of the role programs, most recent first. -/
abbrev RoleTable (programs : List RoleHeader) : Type :=
  Values (RoleHeader.Meaning model) programs

/-- The count of the loop of one role: the count of the operation, or the role's copy. -/
@[expose] def ownCount : (count : RepeatCount) → Values model.Value count.ownOperands → Nat
  | .static number, _ => number
  | .runtime _, copies => copies.get .here

/-- The region of the choice of one role that its tag selects: the region with the number
of a condition or of an arm, on the captures, or the region of the alternative of a
variant, on its payload and the captures. -/
@[expose] def ownChosenRegion (captures outputs : List Ty) :
    (tag : ChoiceTag) →
      Values (RegionFunction model.Value (Effects model)) (tag.ownRegions captures outputs) →
      model.Value tag.type → Values model.Value captures →
        PIR.Process (Effects model) (Values model.Value outputs)
  | .condition, regions, value, captured =>
      selectArm (captures, outputs) ChoiceTag.condition.arms regions
        (ChoiceTag.select model.Carrier .condition value) captured
  | .arm count, regions, value, captured =>
      selectArm (captures, outputs) (ChoiceTag.arm count).arms regions
        (ChoiceTag.select model.Carrier (.arm count) value) captured
  | .alternative _ alternatives, regions, value, captured =>
      matchProcess model captures outputs alternatives regions value captured

/-- The meaning of a role operation: its local computation, its one effect, its loop,
its selected arm, or the called program. The site of an effect is the label of the
operation's site number; a called program runs under the path of the call's site. -/
@[expose] def roleOperation (table : FunctionTable model functions) (called : RoleTable model programs)
    (label : Nat → Site) :
    (op : RoleOp operations functions programs deployed) → Values model.Value op.arguments →
      Values (RegionFunction model.Value (Effects model)) op.regions →
        PIR.Process (Effects model) (Values model.Value op.results)
  | .perform op bodies => fun arguments _ =>
      localOperation model table op arguments (bodies.denote (localMeaning model table))
  | .send site type => fun arguments _ =>
      .call (.send (label site) type (arguments.get .here)) fun _ => .done .nil
  | .receive site type => fun _ _ =>
      .call (.receive (label site) type) fun reply => .done (.cons reply .nil)
  | .draw site law populated => fun arguments _ =>
      .call (.draw (label site) (.of law populated) arguments) fun reply =>
        .done (.cons reply .nil)
  | .sample site law populated => fun arguments _ =>
      .call (.sample (label site) (.of law populated) arguments) fun reply =>
        .done (.cons reply .nil)
  | .repeat count carried collected _ => fun arguments regions =>
      let parts := arguments.split count.ownOperands
      ownRepeatProcess model count carried collected
        (fun iteration values => (regions.get .here)
          (.cons iteration (values.append (parts.2.split carried).2)))
        (ownCount model count parts.1) (parts.2.split carried).1
  | .choose tag captures outputs => fun arguments regions =>
      ownChosenRegion model captures outputs tag regions (arguments.get .here) arguments.tail
  | .call site callee => fun arguments _ => called.get callee (label site).below arguments

@[expose, reducible] def roleMeaning (table : FunctionTable model functions) (called : RoleTable model programs)
    (label : Nat → Site) :
    RegionMeaning (RoleDialect operations functions programs deployed) (Effects model) :=
  ⟨model.Value, roleOperation model table called label⟩

end Meaning

/-! ## The role's part of a context -/

/-- Keep a type when its holder is the role. -/
@[expose] def keep : Bool → Ty → List Ty → List Ty
  | true, type, rest => type :: rest
  | false, _, rest => rest

/-- The types of the values that the role holds. -/
@[expose] def own (role : Nat) : List Located → List Ty
  | [] => []
  | located :: rest => keep (Nat.beq located.holder role) located.type (own role rest)

/-- The role's values of two lists are its values of the first, then its values of the
second. -/
theorem own_append (role : Nat) :
    ∀ (first second : List Located),
      own role (first ++ second) = own role first ++ own role second
  | [], _ => rfl
  | located :: first, second => by
      show keep (Nat.beq located.holder role) located.type (own role (first ++ second)) =
        keep (Nat.beq located.holder role) located.type (own role first) ++ own role second
      rw [own_append role first second]
      cases Nat.beq located.holder role <;> rfl

/-- The header of the program of one role of a protocol. -/
@[expose, reducible] def roleHeader (role : Nat) (header : ProtocolHeader) : RoleHeader :=
  ⟨own role header.inputs, own role header.outputs⟩

/-- The role holds a located value, at this type. -/
@[expose] def Owned (role : Nat) (located : Located) (type : Ty) : Prop :=
  Nat.beq located.holder role = true ∧ located.type = type

/-- A translation of the role's values into the role's context. -/
abbrev Translation (role : Nat) (Γ : List Located) (Δ : List Ty) : Type :=
  Mapping (Owned role) Γ Δ

namespace Translation

variable {role : Nat} {Γ : List Located} {Δ : List Ty}

/-- The role's reference to a value it holds. -/
@[expose] def own (translate : Translation role Γ Δ) {located : Located} (reference : Var Γ located)
    (member : Nat.beq located.holder role = true) : Var Δ located.type :=
  translate.apply reference ⟨member, rfl⟩

/-- A new value of another role. -/
@[expose] def absent (translate : Translation role Γ Δ) (added : Located)
    (outside : Nat.beq added.holder role = false) : Translation role (added :: Γ) Δ :=
  translate.skip added fun _ owned => Bool.noConfusion (outside.symm.trans owned.1)

/-- A new value of the role. -/
@[expose] def present (translate : Translation role Γ Δ) (added : Located) :
    Translation role (added :: Γ) (added.type :: Δ) :=
  translate.keep added added.type fun _ owned => owned.2.symm

/-- A new value that is, for the role, a value the role already has. -/
@[expose] def same (translate : Translation role Γ Δ) (added : Located) (source : Var Δ added.type) :
    Translation role (added :: Γ) Δ :=
  translate.bind added source fun _ owned => owned.2.symm

/-- New values of one holder, the role. -/
@[expose] def presentAll (holder : Nat) : {Γ : List Located} → {Δ : List Ty} → Translation role Γ Δ →
    (types : List Ty) → Translation role (bindAll Γ (Located.atRole holder types)) (bindAll Δ types)
  | _, _, translate, [] => translate
  | _, _, translate, type :: types => presentAll holder (translate.present ⟨type, holder⟩) types

/-- New values of one holder, another role. -/
@[expose] def absentAll (holder : Nat) (outside : Nat.beq holder role = false) :
    {Γ : List Located} → Translation role Γ Δ →
      (types : List Ty) → Translation role (bindAll Γ (Located.atRole holder types)) Δ
  | _, translate, [] => translate
  | _, translate, type :: types =>
      absentAll holder outside (translate.absent ⟨type, holder⟩ outside) types

/-- The copies of a coin that the role drew: for the role each is the coin, the most
recent value of its context. -/
@[expose] def coins (output : Ty) : {Γ : List Located} → Translation role Γ (output :: Δ) →
    (receivers : List Nat) →
      Translation role (bindAll Γ (Located.ofRoles output receivers)) (output :: Δ)
  | _, translate, [] => translate
  | _, translate, receiver :: receivers =>
      coins output (translate.same ⟨output, receiver⟩ .here) receivers

/-- The results of a draw by the role: its copy and every receiver's copy are the coin. -/
@[expose] def drawn (translate : Translation role Γ Δ) (owner : Nat) (output : Ty) (receivers : List Nat) :
    Translation role (bindAll Γ (⟨output, owner⟩ :: Located.ofRoles output receivers))
      (output :: Δ) :=
  coins output (translate.present ⟨output, owner⟩) receivers

/-- One more value, kept when its holder is the role, before the values that follow. -/
@[expose] def extendOne {Γ' : List Located} (translate : Translation role Γ Δ) (added : Located)
    (later : List Ty)
    (next : {Δ' : List Ty} → Translation role (added :: Γ) Δ' → Translation role Γ' (bindAll Δ' later)) :
    (present : Bool) → Nat.beq added.holder role = present →
      Translation role Γ' (bindAll Δ (keep present added.type later))
  | true, _ => next (translate.present added)
  | false, outside => next (translate.absent added outside)

/-- New values of any holders. -/
@[expose] def extend : {Γ : List Located} → {Δ : List Ty} → Translation role Γ Δ →
    (added : List Located) → Translation role (bindAll Γ added) (bindAll Δ (Core.own role added))
  | _, _, translate, [] => translate
  | _, _, translate, located :: added =>
      extendOne translate located (Core.own role added) (fun later => extend later added)
        (Nat.beq located.holder role) rfl

/-- One more sequence of a collected value, kept when its holder is the role, before the
sequences and the carried values that follow. -/
@[expose] def extendOneCollected {Γ' : List Located} (translate : Translation role Γ Δ)
    (size : Option Nat) (located : Located) (later carried : List Ty)
    (next : {Δ' : List Ty} →
      Translation role (⟨.seq located.type size, located.holder⟩ :: Γ) Δ' →
        Translation role Γ' (bindAll Δ' (collectedSequences size later ++ carried))) :
    (present : Bool) → Nat.beq located.holder role = present →
      Translation role Γ'
        (bindAll Δ (collectedSequences size (keep present located.type later) ++ carried))
  | true, _ => next (translate.present ⟨.seq located.type size, located.holder⟩)
  | false, outside => next (translate.absent ⟨.seq located.type size, located.holder⟩ outside)

/-- The results of a loop of which the role is a participant: its sequences of collected
values, then its carried values. -/
@[expose] def extendCollected (size : Option Nat) :
    {Γ : List Located} → {Δ : List Ty} → Translation role Γ Δ →
      (collected carried : List Located) →
        Translation role (bindAll Γ (collectedSequencesAt size collected ++ carried))
          (bindAll Δ (collectedSequences size (Core.own role collected) ++ Core.own role carried))
  | _, _, translate, [], carried => translate.extend carried
  | _, _, translate, located :: rest, carried =>
      extendOneCollected translate size located (Core.own role rest) (Core.own role carried)
        (fun later => extendCollected size later rest carried) (Nat.beq located.holder role) rfl

/-- The translation of a definition's inputs. -/
@[expose] def initial (role : Nat) (inputs : List Located) :
    Translation role (bindAll [] inputs) (bindAll [] (Core.own role inputs)) :=
  extend (Mapping.start (Δ := ([] : List Ty)) 0 rfl) inputs

/-- One more value of a first list, before the rest of it and a second list. -/
@[expose] def extendOneAppend {Γ' : List Located} (translate : Translation role Γ Δ) (added : Located)
    (first second : List Ty)
    (next : {Δ' : List Ty} → Translation role (added :: Γ) Δ' →
      Translation role Γ' (bindAll Δ' (first ++ second))) :
    (present : Bool) → Nat.beq added.holder role = present →
      Translation role Γ' (bindAll Δ (keep present added.type first ++ second))
  | true, _ => next (translate.present added)
  | false, outside => next (translate.absent added outside)

/-- New values of two lists: the role's context grows by its values of the first list,
then by its values of the second. -/
@[expose] def extendAppend : {Γ : List Located} → {Δ : List Ty} → Translation role Γ Δ →
    (first second : List Located) →
      Translation role (bindAll Γ (first ++ second))
        (bindAll Δ (Core.own role first ++ Core.own role second))
  | _, _, translate, [], second => translate.extend second
  | _, _, translate, located :: first, second =>
      extendOneAppend translate located (Core.own role first) (Core.own role second)
        (fun later => extendAppend later first second) (Nat.beq located.holder role) rfl

/-- The copies of the iteration number of a loop, then new values of two lists: for the
role every copy is its iteration number, the most recent value of its context. -/
@[expose] def iterationAppend : {Γ : List Located} → Translation role Γ (.nat :: Δ) →
    (participants : List Nat) → (first second : List Located) →
      Translation role (bindAll Γ (Located.ofRoles .nat participants ++ (first ++ second)))
        (bindAll (.nat :: Δ) (Core.own role first ++ Core.own role second))
  | _, translate, [], first, second => translate.extendAppend first second
  | _, translate, participant :: rest, first, second =>
      iterationAppend (translate.same ⟨.nat, participant⟩ .here) rest first second

/-- The translation of the inputs of a loop's region: the iteration number, which is one
value of the role for the copies of all participants, the carried values, then the
captures. -/
@[expose] def initialLoop (role : Nat) (participants : List Nat) (first second : List Located) :
    Translation role (bindAll [] (Located.ofRoles .nat participants ++ (first ++ second)))
      (bindAll [] (.nat :: (Core.own role first ++ Core.own role second))) :=
  iterationAppend (Mapping.start (Δ := [Ty.nat]) 1 rfl) participants first second

/-- The copies of the payload of an alternative, then new values: for the role every copy
is its payload, the most recent value of its context. -/
@[expose] def payloadAppend (payload : Ty) : {Γ : List Located} →
    Translation role Γ (payload :: Δ) → (participants : List Nat) → (later : List Located) →
      Translation role (bindAll Γ (Located.ofRoles payload participants ++ later))
        (bindAll (payload :: Δ) (Core.own role later))
  | _, translate, [], later => translate.extend later
  | _, translate, participant :: rest, later =>
      payloadAppend payload (translate.same ⟨payload, participant⟩ .here) rest later

/-- The translation of the inputs of the region of an alternative of a variant: the
payload, which is one value of the role for the copies of all participants, then the
captures. -/
@[expose] def initialAlternative (role : Nat) (payload : Ty) (participants : List Nat)
    (captures : List Located) :
    Translation role (bindAll [] (Located.ofRoles payload participants ++ captures))
      (bindAll [] (payload :: Core.own role captures)) :=
  payloadAppend payload (Mapping.start (Δ := [payload]) 1 rfl) participants captures

/-- One carried result of a loop that the role is outside of: the carried operand when
the role holds it. -/
@[expose] def passedOne {Γ₀ Γ' : List Located} (base : Translation role Γ₀ Δ)
    (translate : Translation role Γ Δ) (located : Located) (reference : Var Γ₀ located)
    (next : Translation role (located :: Γ) Δ → Translation role Γ' Δ) :
    (present : Bool) → Nat.beq located.holder role = present → Translation role Γ' Δ
  | true, member => next (translate.same located (base.own reference member))
  | false, outside => next (translate.absent located outside)

/-- The carried results of a loop that the role is outside of: each one that the role
holds is the carried operand. `base` translates the context of the operands. -/
@[expose] def passed {Γ₀ : List Located} (base : Translation role Γ₀ Δ) :
    {Γ : List Located} → Translation role Γ Δ → (carried : List Located) → Operands Γ₀ carried →
      Translation role (bindAll Γ carried) Δ
  | _, translate, [], _ => translate
  | _, translate, located :: rest, .cons reference values =>
      passedOne base translate located reference (fun later => passed base later rest values)
        (Nat.beq located.holder role) rfl

/-- The results of a loop that the role is outside of: it holds none of the sequences of
collected values, and each carried result that it holds is the carried operand. Nothing
when it holds a collected value. -/
@[expose] def passedCollected {Γ₀ : List Located} (base : Translation role Γ₀ Δ)
    (size : Option Nat) :
    {Γ : List Located} → Translation role Γ Δ → (collected carried : List Located) →
      Operands Γ₀ carried →
        Option (Translation role (bindAll Γ (collectedSequencesAt size collected ++ carried)) Δ)
  | _, translate, [], carried, operands => some (passed base translate carried operands)
  | _, translate, located :: rest, carried, operands =>
      match outside : Nat.beq located.holder role with
      | false =>
          passedCollected base size
            (translate.absent ⟨.seq located.type size, located.holder⟩ outside) rest carried
            operands
      | true => none

/-- New values none of which the role holds; nothing when it holds one. -/
@[expose] def unheld : {Γ : List Located} → Translation role Γ Δ → (added : List Located) →
    Option (Translation role (bindAll Γ added) Δ)
  | _, translate, [] => some translate
  | _, translate, located :: rest =>
      match outside : Nat.beq located.holder role with
      | false => unheld (translate.absent located outside) rest
      | true => none

/-- One result of a call: the callee's program returns it exactly when the role holds
it; nothing otherwise. -/
@[expose] def calledOne {Γ' : List Located} (translate : Translation role Γ Δ) (added : Located)
    (later : List Ty)
    (next : {Δ' : List Ty} → Translation role (added :: Γ) Δ' →
      Option (Translation role Γ' (bindAll Δ' later))) :
    (returned held : Bool) → Nat.beq added.holder role = held →
      Option (Translation role Γ' (bindAll Δ (keep returned added.type later)))
  | true, true, _ => next (translate.present added)
  | false, false, outside => next (translate.absent added outside)
  | true, false, _ => none
  | false, true, _ => none

/-- The results of a call of the callee's program of a formal role: the outputs that
the formal role holds, which are the results of the application that the role holds. -/
@[expose] def called (roleMap : RoleMap) (formal : Nat) :
    {Γ : List Located} → {Δ : List Ty} → Translation role Γ Δ → (outputs : List Located) →
      Option (Translation role (bindAll Γ (outputs.map (Located.rename roleMap)))
        (bindAll Δ (Core.own formal outputs)))
  | _, _, translate, [] => some translate
  | _, _, translate, located :: rest =>
      calledOne translate (located.rename roleMap) (Core.own formal rest)
        (fun later => called roleMap formal later rest)
        (Nat.beq located.holder formal) (Nat.beq (roleMap.apply located.holder) role) rfl

end Translation

section Operands

variable {role : Nat} {Γ : List Located} {Δ : List Ty}

/-- The operands of an operation that the role performs. -/
@[expose] def ownArguments (translate : Translation role Γ Δ) (holder : Nat)
    (member : Nat.beq holder role = true) :
    (types : List Ty) → Operands Γ (Located.atRole holder types) → Operands Δ types
  | [], _ => .nil
  | type :: types, .cons reference rest =>
      .cons (translate.own (located := ⟨type, holder⟩) reference member)
        (ownArguments translate holder member types rest)

@[expose] def consKept {F : Ty → Type} {type : Ty} {rest : List Ty} :
    (present : Bool) → (present = true → F type) → Values F rest → Values F (keep present type rest)
  | true, value, values => .cons (value rfl) values
  | false, _, values => values

/-- The returned values that the role holds. -/
@[expose] def ownOperands (translate : Translation role Γ Δ) :
    (out : List Located) → Operands Γ out → Operands Δ (own role out)
  | [], _ => .nil
  | located :: rest, .cons reference values =>
      consKept (Nat.beq located.holder role) (fun member => translate.own reference member)
        (ownOperands translate rest values)

/-- One participant's copy of a count or tag: the role's when the participant is the
role, and otherwise the copy found among the later participants. -/
@[expose] def ownCopyOne (translate : Translation role Γ Δ) (type : Ty) (participant : Nat)
    (reference : Var Γ ⟨type, participant⟩) (later : Option (Var Δ type)) :
    (present : Bool) → Nat.beq participant role = present → Option (Var Δ type)
  | true, member => some (translate.own (located := ⟨type, participant⟩) reference member)
  | false, _ => later

/-- The role's copy of a count or tag of which each participant holds one: the copy of
the first participant that is the role. -/
@[expose] def ownCopy (translate : Translation role Γ Δ) (type : Ty) :
    (participants : List Nat) → Operands Γ (Located.ofRoles type participants) → Option (Var Δ type)
  | [], _ => none
  | participant :: rest, .cons reference values =>
      ownCopyOne translate type participant reference (ownCopy translate type rest values)
        (Nat.beq participant role) rfl

/-- The count operand of the loop of the role, when the role is a participant: none for a
count of the operation, and the role's copy of a count that is a value. Nothing when the
role is not a participant. -/
@[expose] def ownCountOperands (translate : Translation role Γ Δ) (participants : List Nat) :
    (count : RepeatCount) → Operands Γ (count.operands participants) →
      Option (Operands Δ count.ownOperands)
  | .static _, _ => cond (occursIn participants role) (some .nil) none
  | .runtime _, operands =>
      match ownCopy translate .nat participants operands with
      | some copy => some (.cons copy .nil)
      | none => none

/-- The role's reference to an operand of an application, when the role holds it. -/
@[expose] def heldArgument (translate : Translation role Γ Δ) (located : Located) (reference : Var Γ located) :
    (held : Bool) → Nat.beq located.holder role = held → Option (Var Δ located.type)
  | true, member => some (translate.own reference member)
  | false, _ => none

@[expose] def consCalled {F : Ty → Type} {type : Ty} {rest : List Ty} :
    (returned : Bool) → Option (F type) → Option (Values F rest) →
      Option (Values F (keep returned type rest))
  | true, some value, some values => some (.cons value values)
  | false, _, some values => some values
  | true, none, _ => none
  | _, _, none => none

/-- The operands of a call of the callee's program of a formal role: the inputs that
the formal role holds. Nothing when the role does not hold one of them. -/
@[expose] def calledArguments (translate : Translation role Γ Δ) (roleMap : RoleMap) (formal : Nat) :
    (inputs : List Located) → Operands Γ (inputs.map (Located.rename roleMap)) →
      Option (Operands Δ (own formal inputs))
  | [], _ => some .nil
  | located :: rest, .cons reference values =>
      consCalled (Nat.beq located.holder formal)
        (heldArgument translate (located.rename roleMap) reference
          (Nat.beq (roleMap.apply located.holder) role) rfl)
        (calledArguments translate roleMap formal rest values)

end Operands

/-! ## The programs of applied protocols -/

/-- The formal role that a role map sends to a role: the position of its first entry
equal to the role, or the number of entries when there is none. -/
@[expose] def formalRole (role : Nat) : RoleMap → Nat
  | [] => 0
  | entry :: rest => cond (Nat.beq entry role) 0 (formalRole role rest + 1)

/-- Every role of a list is below a bound. -/
@[expose] def rolesBelow (bound : Nat) (roles : List Nat) : Bool := roles.all fun role => Nat.blt role bound

/-- For the roles of an application's callee: each runs as a role below the bound, and
it runs as the role exactly when it is the formal role. -/
@[expose] def calleeSide (bound role formal roles : Nat) (roleMap : RoleMap) : Bool :=
  (List.range roles).all fun callee =>
    Nat.blt (roleMap.apply callee) bound &&
      agreeBool (Nat.beq (roleMap.apply callee) role) (Nat.beq callee formal)

/-- For every protocol that a region may apply: where the programs of its formal roles
are among the role programs, by level. -/
structure ProjectedCallees (protocols : List ProtocolHeader) (programs : List RoleHeader) where
  /-- For each protocol, the most recent first: the levels of the programs of its formal
  roles in order, and the mark of a protocol whose outside program is a bare return. -/
  images : Sequence (List Nat)
  depth : Nat
  counted : depth = programs.length
  sound : ∀ (index : Nat) (header : ProtocolHeader), protocols[index]? = some header →
    ∃ entry, images.toList[index]? = some entry ∧
      ∀ (formal level : Nat), entry[formal]? = some level →
        atLevel? programs depth level = some (roleHeader formal header)

namespace ProjectedCallees

variable {protocols : List ProtocolHeader} {programs : List RoleHeader}

/-- The table of a region that applies nothing. -/
def empty : ProjectedCallees [] programs :=
  ⟨.empty, programs.length, rfl, fun _ _ found => nomatch found⟩

/-- The same table after one more role program. -/
@[expose] def weaken (table : ProjectedCallees protocols programs) (added : RoleHeader) :
    ProjectedCallees protocols (added :: programs) :=
  ⟨table.images, table.depth + 1, by rw [table.counted, List.length_cons],
    fun index header found => by
      obtain ⟨entry, at_, valid⟩ := table.sound index header found
      exact ⟨entry, at_, fun formal level member =>
        atLevel?_cons programs added (valid formal level member)⟩⟩

/-- One more protocol with the levels of the programs of its formal roles. -/
@[expose] def extend (table : ProjectedCallees protocols programs) (header : ProtocolHeader)
    (levels : List Nat)
    (valid : ∀ (formal level : Nat), levels[formal]? = some level →
      atLevel? programs table.depth level = some (roleHeader formal header)) :
    ProjectedCallees (header :: protocols) programs :=
  ⟨table.images.push levels, table.depth, table.counted, fun index found at_ => by
    rw [Sequence.toList_push]
    cases index with
    | zero =>
        have same : header = found := Option.some.inj at_
        subst same
        exact ⟨levels, rfl, valid⟩
    | succ index => exact table.sound index found at_⟩

/-- The level of the program of a formal role of the protocol at a position. -/
@[expose] def level? (table : ProjectedCallees protocols programs) (index formal : Nat) : Option Nat :=
  match table.images.get? index with
  | none => none
  | some entry => entry[formal]?

theorem level?_valid (table : ProjectedCallees protocols programs) {header : ProtocolHeader}
    (callee : Var protocols header) {formal level : Nat}
    (found : table.level? callee.index formal = some level) :
    atLevel? programs table.depth level = some (roleHeader formal header) := by
  obtain ⟨recorded, recordedAt, valid⟩ := table.sound callee.index header callee.valid
  unfold level? at found
  rw [Sequence.get?_eq, recordedAt] at found
  exact valid formal level found

/-- The program of a formal role of an applied protocol. -/
@[expose] def find (table : ProjectedCallees protocols programs) {header : ProtocolHeader}
    (callee : Var protocols header) (formal : Nat) : Option (Var programs (roleHeader formal header)) :=
  match found : table.level? callee.index formal with
  | none => none
  | some level =>
      some ⟨table.depth - 1 - level, by
        have image := table.level?_valid callee found
        unfold atLevel? at image
        split at image
        · exact image
        · cases image⟩

end ProjectedCallees

/-! ## Projection -/

inductive ProjectionRefusal where
  /-- An operation names a role that is not below the role count. -/
  | roleOutOfRange
  /-- The participants of a `repeat` or `choose` are not distinct. -/
  | repeatedParticipant
  /-- An output of a `choose` or a collected value of a `repeat` is held by a role that is
  not a participant. -/
  | outputOutsideParticipants
  /-- The role map of an `apply` does not send exactly one formal role to the role. -/
  | roleMap
  /-- The applied protocol has no program for the formal role. -/
  | missingProgram
  /-- The holders of the callee's ports do not agree with the role map. -/
  | calleePorts
  deriving Repr

/-- For each region of a list, the translation of its inputs into the inputs of the role's
region, whose signature it fixes: the role's inputs, and the outputs that the role holds. -/
inductive RegionTranslations (role : Nat) :
    List (List Located × List Located) → List (List Ty × List Ty) → Type where
  | nil : RegionTranslations role [] []
  | cons {inputs outputs : List Located} {rest : List (List Located × List Located)}
      {mine : List Ty} {targets : List (List Ty × List Ty)}
      (translate : Translation role (bindAll [] inputs) (bindAll [] mine))
      (tail : RegionTranslations role rest targets) :
      RegionTranslations role ((inputs, outputs) :: rest) ((mine, own role outputs) :: targets)

/-- The translations of the regions of a choice on a condition or an arm number: the
inputs of each are the captures. -/
@[expose] def armTranslations (role : Nat) (captures outputs : List Located) :
    (count : Nat) →
      RegionTranslations role (List.replicate count (captures, outputs))
        (List.replicate count (own role captures, own role outputs))
  | 0 => .nil
  | count + 1 =>
      .cons (Translation.initial role captures) (armTranslations role captures outputs count)

/-- The translations of the regions of a choice on a variant: the inputs of the region of
an alternative are the payload copies of the participants and the captures, and the role's
are its payload and its captures. -/
@[expose] def alternativeTranslations (role : Nat) (participants : List Nat)
    (captures outputs : List Located) :
    (alternatives : List Ty) →
      RegionTranslations role
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs))
        (alternatives.map fun payload => (payload :: own role captures, own role outputs))
  | [] => .nil
  | payload :: rest =>
      .cons (Translation.initialAlternative role payload participants captures)
        (alternativeTranslations role participants captures outputs rest)

/-- The translations of the regions of a choice into the regions of the role's choice. -/
@[expose] def choiceTranslations (role : Nat) (participants : List Nat)
    (captures outputs : List Located) :
    (tag : ChoiceTag) →
      RegionTranslations role (tag.regions participants captures outputs)
        (tag.ownRegions (own role captures) (own role outputs))
  | .condition => armTranslations role captures outputs 2
  | .arm count => armTranslations role captures outputs count
  | .alternative _ alternatives =>
      alternativeTranslations role participants captures outputs alternatives

section Projection

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {programs : List RoleHeader} {deployed : Bool}
variable (role bound : Nat)

/-- The announcements of a coin drawn by another role: one `receive` per receiver that
is the role, in order. Each binds the receiver's copy. -/
@[expose] def projectReceives (site : Nat) (output : Ty) {out : List Ty} :
    (receivers : List Nat) → {Γ : List Located} → {Δ : List Ty} → Translation role Γ Δ →
      ({Δ' : List Ty} → Translation role (bindAll Γ (Located.ofRoles output receivers)) Δ' →
        Except ProjectionRefusal (Region (RoleDialect operations functions programs deployed) Δ' out)) →
      Except ProjectionRefusal (Region (RoleDialect operations functions programs deployed) Δ out)
  | [], _, _, translate, rest => rest translate
  | receiver :: receivers, _, _, translate, rest =>
      match present : Nat.beq receiver role with
      | true =>
          match projectReceives site output receivers
              (translate.present ⟨output, receiver⟩) rest with
          | .ok next => .ok (.letOp (.receive site output) .nil .nil next)
          | .error refusal => .error refusal
      | false =>
          projectReceives site output receivers (translate.absent ⟨output, receiver⟩ present) rest

variable (callees : ProjectedCallees protocols programs)

-- The equations that the matches below name are the hypotheses of the meaning theorem.
set_option linter.unusedVariables false in
mutual
  /-- The role's program of a protocol region. -/
  @[expose] def projectRegion {Γ out : List Located} :
      Region (ProtocolDialect operations functions protocols deployed) Γ out → {Δ : List Ty} →
        Translation role Γ Δ →
          Except ProjectionRefusal
            (Region (RoleDialect operations functions programs deployed) Δ (own role out))
    | .ret values, _, translate => .ok (.ret (ownOperands translate out values))
    | .stop reason, _, _ => .ok (.stop reason)
    | .bind (mid := mid) body rest, _, translate =>
        match projectRegion body translate, projectRegion rest (translate.extend mid) with
        | .ok body, .ok rest => .ok (.bind body rest)
        | .error refusal, _ => .error refusal
        | _, .error refusal => .error refusal
    | .letOp (.at holder op bodies) arguments _ rest, _, translate =>
        match within : Nat.blt holder bound, present : Nat.beq holder role with
        | false, _ => .error .roleOutOfRange
        | true, true =>
            match projectRegion rest (Translation.presentAll holder translate op.results) with
            | .ok rest =>
                .ok (.letOp (.perform op bodies)
                  (ownArguments translate holder present op.arguments arguments) .nil rest)
            | .error refusal => .error refusal
        | true, false => projectRegion rest (Translation.absentAll holder present translate op.results)
    | .letOp (.exchange sender receiver site type) arguments _ rest, _, translate =>
        match within : Nat.blt sender bound && Nat.blt receiver bound,
            sends : Nat.beq sender role, receives : Nat.beq receiver role with
        | false, _, _ => .error .roleOutOfRange
        | true, true, true =>
            projectRegion rest (translate.same ⟨type, receiver⟩
              (translate.own (located := ⟨type, sender⟩) (arguments.get .here) sends))
        | true, true, false =>
            match projectRegion rest (translate.absent ⟨type, receiver⟩ receives) with
            | .ok rest =>
                .ok (.letOp (.send site type)
                  (.cons (translate.own (located := ⟨type, sender⟩) (arguments.get .here) sends) .nil)
                  .nil rest)
            | .error refusal => .error refusal
        | true, false, true =>
            match projectRegion rest (translate.present ⟨type, receiver⟩) with
            | .ok rest => .ok (.letOp (.receive site type) .nil .nil rest)
            | .error refusal => .error refusal
        | true, false, false =>
            projectRegion rest (translate.absent ⟨type, receiver⟩ receives)
    | .letOp (.draw owner receivers site (inputs := inputs) (output := output) law populated) arguments _ rest,
        _, translate =>
        match within : Nat.blt owner bound && rolesBelow bound receivers,
            owns : Nat.beq owner role with
        | false, _ => .error .roleOutOfRange
        | true, true =>
            match projectRegion rest (translate.drawn owner output receivers) with
            | .ok rest =>
                .ok (.letOp (.draw site law populated) (ownArguments translate owner owns inputs arguments)
                  .nil rest)
            | .error refusal => .error refusal
        | true, false =>
            projectReceives role site output receivers (translate.absent ⟨output, owner⟩ owns)
              fun later => projectRegion rest later
    | .letOp (.sample owner site (inputs := inputs) (output := output) law populated) arguments _ rest, _,
        translate =>
        match within : Nat.blt owner bound, owns : Nat.beq owner role with
        | false, _ => .error .roleOutOfRange
        | true, true =>
            match projectRegion rest (translate.present ⟨output, owner⟩) with
            | .ok rest =>
                .ok (.letOp (.sample site law populated) (ownArguments translate owner owns inputs arguments)
                  .nil rest)
            | .error refusal => .error refusal
        | true, false => projectRegion rest (translate.absent ⟨output, owner⟩ owns)
    | .letOp (.repeat participants count carried collected captures covered) arguments
        bodies rest, _, translate =>
        match bodies with
        | .cons body .nil =>
        match within : rolesBelow bound participants, distinct : distinctNumbers participants with
        | false, _ => .error .roleOutOfRange
        | true, false => .error .repeatedParticipant
        | true, true =>
            match counted : ownCountOperands translate participants count
                (Values.split (count.operands participants) arguments).1 with
            | some copies =>
                match projectRegion body
                      (Translation.initialLoop role participants carried captures),
                    projectRegion rest
                      (translate.extendCollected count.size collected carried) with
                | .ok body, .ok rest =>
                    -- The region yields the role's collected values, then its carried ones:
                    -- its values of the two lists, appended.
                    .ok (.letOp
                      (.repeat count (own role carried) (own role collected) (own role captures))
                      (copies.append
                        ((ownOperands translate carried
                            (Values.split carried
                              (Values.split (count.operands participants) arguments).2).1).append
                          (ownOperands translate captures
                            (Values.split carried
                              (Values.split (count.operands participants) arguments).2).2)))
                      (.cons (body.retype (own_append role collected carried)) .nil) rest)
                | .error refusal, _ => .error refusal
                | _, .error refusal => .error refusal
            | none =>
                match passed : Translation.passedCollected translate count.size translate
                    collected carried
                    (Values.split carried
                      (Values.split (count.operands participants) arguments).2).1 with
                | some later => projectRegion rest later
                | none => .error .outputOutsideParticipants
    | .letOp (.choose participants tag captures outputs _) arguments bodies rest, _, translate =>
        match within : rolesBelow bound participants, distinct : distinctNumbers participants with
        | false, _ => .error .roleOutOfRange
        | true, false => .error .repeatedParticipant
        | true, true =>
            match tagged : ownCopy translate tag.type participants
                (Values.split (Located.ofRoles tag.type participants) arguments).1 with
            | some copy =>
                match projectRegions bodies
                      (choiceTranslations role participants captures outputs tag),
                    projectRegion rest (translate.extend outputs) with
                | .ok arms, .ok rest =>
                    .ok (.letOp (.choose tag (own role captures) (own role outputs))
                      (.cons copy (ownOperands translate captures
                        (Values.split (Located.ofRoles tag.type participants) arguments).2))
                      arms rest)
                | .error refusal, _ => .error refusal
                | _, .error refusal => .error refusal
            | none =>
                match unheld : translate.unheld outputs with
                | some later => projectRegion rest later
                | none => .error .outputOutsideParticipants
    | .letOp (.apply (header := header) callee roleMap site _) arguments _ rest, _, translate =>
        match within : calleeSide bound role (formalRole role roleMap) header.roles roleMap,
            inside : Nat.blt (formalRole role roleMap) header.roles with
        | false, _ => .error .roleMap
        | true, true =>
            match found : callees.find callee (formalRole role roleMap) with
            | none => .error .missingProgram
            | some program =>
                match passed : calledArguments translate roleMap (formalRole role roleMap)
                      header.inputs arguments,
                    returned : translate.called roleMap (formalRole role roleMap) header.outputs with
                | some operands, some later =>
                    match projectRegion rest later with
                    | .ok rest => .ok (.letOp (.call site program) operands .nil rest)
                    | .error refusal => .error refusal
                | _, _ => .error .calleePorts
        | true, false =>
            match unheld : translate.unheld (header.outputs.map (Located.rename roleMap)) with
            | some later => projectRegion rest later
            | none => .error .calleePorts

  /-- The role's programs of closed regions, each from the role's inputs that a translation
  of the region's inputs fixes. -/
  def projectRegions {signatures : List (List Located × List Located)}
      {targets : List (List Ty × List Ty)} :
      Regions (ProtocolDialect operations functions protocols deployed) signatures →
        RegionTranslations role signatures targets →
          Except ProjectionRefusal
            (Regions (RoleDialect operations functions programs deployed) targets)
    | .nil, .nil => .ok .nil
    | .cons body tail, .cons translate translations =>
        match projectRegion body translate, projectRegions tail translations with
        | .ok body, .ok tail => .ok (.cons body tail)
        | .error refusal, _ => .error refusal
        | _, .error refusal => .error refusal
end

/-- A role's program of a protocol: a region from the role's inputs to its outputs,
typed over the headers of the role programs it may call. -/
structure RoleProgram (operations : List OperationSignature) (functions : List FunctionHeader)
    (programs : List RoleHeader) (header : RoleHeader) where
  deployed : Bool
  body : Region (RoleDialect operations functions programs deployed) (bindAll [] header.inputs)
    header.outputs

/-- The program of one role of a protocol. The bound on role numbers is the protocol's
role count. -/
@[expose] def projectProtocol {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header) :
    Except ProjectionRefusal (RoleProgram operations functions programs (roleHeader role header)) :=
  match projectRegion role header.roles callees definition.body
      (Translation.initial role header.inputs) with
  | .ok body => .ok ⟨!header.specificationOnly, body⟩
  | .error refusal => .error refusal

end Projection

end Zkc.Core
