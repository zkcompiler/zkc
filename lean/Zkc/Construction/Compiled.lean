module

public import Zkc.Construction.ProjectionSoundness

@[expose] public section

/-! Composition of the construction and projection rules.

`checkCompiled` runs the transcript-construction rule and the participant
projection rule on one exported validator. Its subject is an admitted original
(`Structured.Imported original`): the construction rule reads the original
snapshot, and the projection rule reads the program that snapshot admits, so
the two rules cannot be given different originals. `compiled_transform` composes
their soundness theorems: the compiled validator's ideal meaning is the
Fiat–Shamir transform of the admitted original validator's participant process,
read through matching selections of their results. The two rules meet at the
exported program's interactive reading (`spec`): the construction rule relates
it to the ideal meaning and the projection rule to the original.

`compiled_transform` leaves three positional premises to each Entry: where the
export returns its acceptance output, how its data inputs hold the original
validator's inputs, and how many there are. `select` constructs that selection
from the admitted original and the export's policy, `Selection.check` validates
it against the export, and `selection_sound` proves the three premises (and the
reading of the validator's acceptance output) from an accepted check, so that
`compiled_selected` instantiates the composed rules with no positional fact
about an Entry.
-/

set_option autoImplicit false

namespace Zkc.Construction
open Zkc.Source Zkc.Source.Structured

/-- The composed per-compile check of a compiled validator: the
transcript-construction rule against the original snapshot, then the
participant projection rule on the same export against the program that
snapshot admits. -/
def checkCompiled {original : Structured.Snapshot} (imported : Structured.Imported original)
    (participant : Participant) : Except String Unit :=
  match checkExport original participant, exportContext original participant with
  | .ok (), some context => project imported.program context participant
  | .error error, _ => .error error
  | .ok (), none => .error "construction-context"

/-- The checked export's data inputs are the published inputs. -/
theorem exportContext_published {original : Structured.Snapshot} {participant : Participant}
    {context : Context} (found : exportContext original participant = some context) :
    participant.inputs.dropLast.length = participant.policy.publicInputs.length := by
  unfold exportContext at found
  simp only at found
  split at found
  · split at found
    · split at found
      · split_ifs at found with conditions
        have lengths := congrArg List.length conditions.2.2.2
        simpa using lengths
      · cases found
    · cases found
  · cases found

/-- An accepted export has a final transcript input. -/
theorem check_inputs_nonempty (context : Context) (participant : Participant)
    (checked : check context participant = .ok ()) : participant.inputs ≠ [] := by
  intro empty
  simp [check, empty] at checked

section Compiled
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- What one final selection of the returned values may observe: two readings
agree on every returned list of the declared length. -/
theorem spec_bind_congr (context : Context) (handle : Nat) (table : Structured.Meanings F G)
    (returned : List Nat) (instructions : List Instruction) (env : List (Value F G)) {B : Type}
    (first second : List (Value F G) → B)
    (agree : ∀ values, values.length = returned.length → first values = second values) :
    (spec context handle table returned instructions env).bind (fun values => .done (first values)) =
      (spec context handle table returned instructions env).bind (fun values => .done (second values)) := by
  simp only [spec, specK_bind]
  congr 1
  funext final
  cases found : read final returned with
  | none => rfl
  | some values =>
    simp only [PIR.Process.bind]
    rw [agree values (read_length found)]

/-- The composed rules: for every export accepted against an admitted original,
the compiled validator's ideal meaning, read through a selection of its returned
values, is the Fiat–Shamir transform of the admitted original validator's
process read through the matching selection of its outputs, for every challenge
function, service handle, data input related to the original inputs, initial
transcript and proof. -/
theorem compiled_transform {original : Structured.Snapshot} (imported : Structured.Imported original)
    (participant : Participant) (accepted : checkCompiled imported participant = .ok ()) :
    ∃ context, exportContext original participant = some context ∧
      ∀ {m : Type → Type} [Monad m] [LawfulMonad m] {B : Type} (challenge : History F G → m F)
        (select : List (Value F G) → B) (decide : List (Option (Value F G)) → B),
        (∀ values, values.length = participant.returned.length →
          select values = decide (values.dropLast.map some)) →
        ∀ (handle : Nat) (data : List (Value F G)) (initial : History F G) (proof : Proof F G)
          (inputs : Values (Component (assignment F G)) imported.program.payload.entry.inputs),
          HoldsValues handle (data ++ [.transcript initial])
            (inputSlots context participant.policy imported.program.payload.entry.inputs) inputs →
          data.length = participant.policy.publicInputs.length →
          (fun result => (mapOutcome select result.1, result.2)) <$>
              ideal context challenge (helperTable imported.program F G) participant.returned
                participant.instructions (data ++ [.transcript initial]) proof =
            transform context challenge
              (((imported.program.participant F G context.validator inputs).bind fun outputs =>
                .done (decide (validatorOutputs context.validator
                  imported.program.payload.entry.outputScopes outputs))).interpret
                CommonAdapter.project) initial proof := by
  unfold checkCompiled at accepted
  split at accepted
  · rename_i context exported found
    refine ⟨context, found, ?_⟩
    intro m _ _ B challenge select decide agree handle data initial proof inputs related arity
    obtain ⟨context', found', checked⟩ := checkExport_sound exported
    rw [found] at found'
    cases found'
    have inputsArity : data.length + 1 = participant.inputs.length := by
      have published := exportContext_published found
      have nonempty := check_inputs_nonempty context participant checked
      have positive : 0 < participant.inputs.length := List.length_pos_iff.mpr nonempty
      simp only [List.length_dropLast] at published
      omega
    rw [check_sound context challenge handle (helperTable imported.program F G) participant checked data
      initial proof inputsArity, ← transform_bind_done]
    congr 1
    rw [spec_bind_congr context handle (helperTable imported.program F G) participant.returned
      participant.instructions _ select (fun values => decide (values.dropLast.map some)) agree]
    have projected := project_sound imported.program context participant accepted handle data initial
      inputs related arity
    have composed := congrArg (fun process => process.bind fun options => .done (decide options))
      projected
    simp only [PIR.Process.bind_assoc, PIR.Process.bind] at composed
    rw [composed, PIR.Process.interpret_bind, PIR.Process.interpret_bind, PIR.Process.bind_assoc]
    congr 1
  · cases accepted
  · cases accepted

end Compiled

section Selection
variable {F G : Type}

/-- The Boolean value at `position` among returned values. -/
def acceptanceAt (position : Nat) (values : List (Value F G)) : Option Bool :=
  match values[position]? with
  | some (.data (.boolean decision)) => some decision
  | _ => none

/-- The Boolean value at `position` among a validator's optional outputs. -/
def decisionAt (position : Nat) (options : List (Option (Value F G))) : Option Bool :=
  match options[position]? with
  | some (some (.data (.boolean value))) => some value
  | _ => none

theorem acceptanceAt_decisionAt {position : Nat} {values : List (Value F G)}
    (inside : position + 1 < values.length) :
    acceptanceAt position values = decisionAt position (values.dropLast.map some) := by
  have same : values.dropLast[position]? = values[position]? := by
    rw [List.getElem?_dropLast]
    split <;> first | rfl | omega
  simp only [acceptanceAt, decisionAt, List.getElem?_map, same]
  cases values[position]? with
  | none => rfl
  | some value => rcases value with ⟨_ | _ | _⟩ | _ | _ | _ | _ <;> rfl

/-- Whether a slot can hold an original input of type `ty` from published values
of types `publics`. -/
def slotTyped (publics : List Ty) : Slot → Ty → Bool
  | .held reference, ty => publics[reference]? == some ty && dataType ty
  | .service, .service _ => true
  | .absent, _ => true
  | _, _ => false

def slotsTyped (publics : List Ty) : List Slot → List Ty → Bool
  | _, [] => true
  | slots, ty :: rest => slotTyped publics (slots.headD .absent) ty && slotsTyped publics slots.tail rest

/-- The original input a slot holds, read from the published values. -/
def slotValue (handle : Nat) (published : List (Value F G)) : Slot → (ty : Ty) → Option (assignment F G ty)
  | .held reference, ty => (published[reference]?).bind (Value.decode ty)
  | .service, .service _ => some handle
  | _, _ => none

/-- The original validator's inputs that the published values and the handle hold. -/
def heldInputs (handle : Nat) (published : List (Value F G)) :
    (slots : List Slot) → (tys : List Ty) → Values (Component (assignment F G)) tys
  | _, [] => .nil
  | slots, ty :: rest =>
      .cons (slotValue handle published (slots.headD .absent) ty) (heldInputs handle published slots.tail rest)

theorem encodeValues_decode : ∀ {tys : List Ty} (values : Values (assignment F G) tys) (reference : Nat)
    {ty : Ty}, tys[reference]? = some ty → dataType ty = true →
      ∃ x, (encodeValues values)[reference]? = some (Value.encode ty x)
  | [], .nil, _, _, found, _ => by simp at found
  | _ :: _, .cons value _, 0, _, found, _ => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      exact ⟨value, rfl⟩
  | _ :: _, .cons _ rest, reference + 1, _, found, data => by
      simp only [List.getElem?_cons_succ] at found
      exact encodeValues_decode rest reference found data

theorem holdsValues_heldInputs (handle : Nat) {publics : List Ty} (held : Values (assignment F G) publics)
    (extra : List (Value F G)) :
    ∀ (slots : List Slot) (tys : List Ty), slotsTyped publics slots tys = true →
      HoldsValues handle (encodeValues held ++ extra) slots (heldInputs handle (encodeValues held) slots tys)
  | _, [], _ => trivial
  | slots, ty :: rest, typed => by
      simp only [slotsTyped, Bool.and_eq_true] at typed
      refine ⟨?_, holdsValues_heldInputs handle held extra slots.tail rest typed.2⟩
      have head := typed.1
      generalize slots.headD .absent = slot at head ⊢
      cases slot with
      | held reference =>
          simp only [slotTyped, Bool.and_eq_true, beq_iff_eq] at head
          obtain ⟨x, found⟩ := encodeValues_decode held reference head.1 head.2
          have bound : reference < (encodeValues held).length := by
            by_contra outside
            rw [List.getElem?_eq_none (by omega)] at found
            cases found
          refine ⟨x, ?_, ?_⟩
          · simp [slotValue, found, Value.decode_encode head.2]
          · rw [List.getElem?_append_left bound, found]
            simp [Value.decode_encode head.2]
      | service =>
          cases ty <;> simp_all [slotTyped, SlotHolds, ServiceHolds, slotValue]
      | absent => rfl
      | free => simp [slotTyped] at head

/-- The position of an output among the outputs in `self`'s scope. -/
def scopePosition (self : Nat) : List (List Nat) → {tys : List Ty} → {ty : Ty} → Var tys ty → Nat
  | _, _, _, .here => 0
  | scopes, _, _, .there v => (if (scopes.headD []).contains self then 1 else 0) + scopePosition self scopes.tail v

/-- Whether an output is in `self`'s scope. -/
def inScope (self : Nat) : List (List Nat) → {tys : List Ty} → {ty : Ty} → Var tys ty → Bool
  | scopes, _, _, .here => (scopes.headD []).contains self
  | scopes, _, _, .there v => inScope self scopes.tail v

theorem decisionAt_validatorOutputs (self : Nat) :
    ∀ (scopes : List (List Nat)) {tys : List Ty} (outputs : Values (Component (assignment F G)) tys)
      (v : Var tys .boolean), inScope self scopes v = true →
      decisionAt (scopePosition self scopes v) (validatorOutputs self scopes outputs) = outputs.get v
  | scopes, _, .cons value _, .here, inside => by
      simp only [inScope] at inside
      simp only [scopePosition, validatorOutputs, inside, ite_true, List.singleton_append, decisionAt,
        List.getElem?_cons_zero, Values.get]
      cases value <;> rfl
  | scopes, _, .cons _ rest, .there v, inside => by
      simp only [inScope] at inside
      have inner := decisionAt_validatorOutputs self scopes.tail rest v inside
      simp only [scopePosition, validatorOutputs, Values.get]
      split
      · rw [Nat.add_comm]
        exact inner
      · simpa using inner

/-- The positional selection of an export, constructed from the admitted
original and the export's policy: the occurrence context, the position of the
acceptance output among the returned values, the types of the published inputs
in policy order, the validator's input slots and its acceptance output. -/
structure Selection (outputs : List Ty) where
  context : Context
  position : Nat
  publics : List Ty
  slots : List Slot
  output : Var outputs .boolean

/-- The selection of an export, from the admitted original and the policy. -/
def select {original : Structured.Snapshot} (imported : Structured.Imported original)
    (participant : Participant) : Option (Selection imported.program.payload.entry.outputs) :=
  match exportContext original participant, exportAcceptance original participant,
      Var.decode imported.program.payload.entry.outputs .boolean participant.policy.acceptance with
  | some context, some position, some output =>
      some ⟨context, position,
        participant.policy.publicInputs.filterMap (imported.program.payload.entry.inputs[·]?),
        inputSlots context participant.policy imported.program.payload.entry.inputs, output⟩
  | _, _, _ => none

/-- The check of a selection against the export: the acceptance output is
returned before the final transcript, every slot holds a published value of
its type, the replaced service or nothing, as many values are published as the
policy names, and the acceptance output is the validator's output at the
selected position. -/
def Selection.check {original : Structured.Snapshot} (imported : Structured.Imported original)
    (selection : Selection imported.program.payload.entry.outputs) (participant : Participant) : Bool :=
  let entry := imported.program.payload.entry
  selection.publics.all (fun ty => !ty.isService) &&
    (decide (selection.position + 1 < participant.returned.length) &&
    slotsTyped selection.publics selection.slots entry.inputs &&
    selection.publics.length == participant.policy.publicInputs.length &&
    inScope selection.context.validator entry.outputScopes selection.output &&
    scopePosition selection.context.validator entry.outputScopes selection.output == selection.position)

/-- The selection check of an export. -/
def checkSelection {original : Structured.Snapshot} (imported : Structured.Imported original)
    (participant : Participant) : Bool :=
  match select imported participant with
  | some selection => selection.check imported participant
  | none => false

/-- The selection of an export names the context and acceptance position the
construction check derives, and the slots the projection rule reads. -/
theorem select_sound {original : Structured.Snapshot} (imported : Structured.Imported original)
    (participant : Participant) {selection : Selection imported.program.payload.entry.outputs}
    (selected : select imported participant = some selection) :
    exportContext original participant = some selection.context ∧
      exportAcceptance original participant = some selection.position ∧
      selection.slots = inputSlots selection.context participant.policy imported.program.payload.entry.inputs := by
  unfold select at selected
  split at selected
  · rename_i context position output foundContext foundPosition _
    cases selected
    exact ⟨foundContext, foundPosition, rfl⟩
  · cases selected

/-- The canonical selection: an accepted selection check discharges the three
positional premises of `compiled_transform` and reads the validator's
acceptance output. On every list of the returned length the acceptance output
is the decision among the validator's outputs; published values of the
selected types hold the validator's inputs at its slots, with the handle as the
replaced service; they are as many as the policy publishes; and the decision
among the validator's outputs is its acceptance output. -/
theorem selection_sound {original : Structured.Snapshot} (imported : Structured.Imported original)
    (participant : Participant) {selection : Selection imported.program.payload.entry.outputs}
    (selected : select imported participant = some selection)
    (checked : selection.check imported participant = true) :
    (∀ values : List (Value F G), values.length = participant.returned.length →
      acceptanceAt selection.position values = decisionAt selection.position (values.dropLast.map some)) ∧
    (∀ (handle : Nat) (held : Values (assignment F G) selection.publics) (extra : List (Value F G)),
      HoldsValues handle (encodeValues held ++ extra)
        (inputSlots selection.context participant.policy imported.program.payload.entry.inputs)
        (heldInputs handle (encodeValues held) selection.slots imported.program.payload.entry.inputs)) ∧
    (∀ held : Values (assignment F G) selection.publics,
      (encodeValues held).length = participant.policy.publicInputs.length) ∧
    (∀ outputs : Values (Component (assignment F G)) imported.program.payload.entry.outputs,
      decisionAt selection.position
          (validatorOutputs selection.context.validator imported.program.payload.entry.outputScopes outputs) =
        outputs.get selection.output) := by
  obtain ⟨-, -, slots⟩ := select_sound imported participant selected
  simp only [Selection.check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at checked
  obtain ⟨_, ⟨⟨⟨⟨inside, typed⟩, published⟩, scoped'⟩, placed⟩⟩ := checked
  refine ⟨fun values length => acceptanceAt_decisionAt (by omega), fun handle held extra => ?_,
    fun held => by rw [encodeValues_length]; exact published, fun outputs => ?_⟩
  · rw [← slots]
    exact holdsValues_heldInputs handle held extra _ _ typed
  · rw [← placed]
    exact decisionAt_validatorOutputs _ _ outputs selection.output scoped'

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The composed rules on a checked selection: the compiled validator's ideal
meaning, read through its acceptance output, is the Fiat–Shamir transform of
the admitted original validator, read through the same output, for every
challenge function, service handle, published values, initial transcript and
proof. The positional premises of `compiled_transform` are discharged by the
selection check (`selection_sound`), so no positional fact about the Entry is
assumed. -/
theorem compiled_selected {original : Structured.Snapshot} (imported : Structured.Imported original)
    (participant : Participant) (accepted : checkCompiled imported participant = .ok ())
    {selection : Selection imported.program.payload.entry.outputs}
    (selected : select imported participant = some selection)
    (checked : selection.check imported participant = true) :
    exportContext original participant = some selection.context ∧
      ∀ {m : Type → Type} [Monad m] [LawfulMonad m] (challenge : History F G → m F) (handle : Nat)
        (held : Values (assignment F G) selection.publics) (initial : History F G) (proof : Proof F G),
        (fun result => (mapOutcome (acceptanceAt selection.position) result.1, result.2)) <$>
            ideal selection.context challenge (helperTable imported.program F G) participant.returned
              participant.instructions (encodeValues held ++ [.transcript initial]) proof =
          transform selection.context challenge
            (((imported.program.participant F G selection.context.validator
                (heldInputs handle (encodeValues held) selection.slots imported.program.payload.entry.inputs)).bind
              fun outputs => .done (outputs.get selection.output)).interpret CommonAdapter.project)
            initial proof := by
  obtain ⟨foundContext, -, slots⟩ := select_sound imported participant selected
  obtain ⟨agree, related, arity, outputs⟩ := selection_sound (F := F) (G := G) imported participant selected checked
  obtain ⟨context', found, composed⟩ := compiled_transform (F := F) (G := G) imported participant accepted
  rw [foundContext] at found
  cases found
  refine ⟨foundContext, ?_⟩
  intro m _ _ challenge handle held initial proof
  rw [composed challenge (acceptanceAt selection.position) (decisionAt selection.position) agree handle
    (encodeValues held) initial proof _ (related handle held _) (arity held)]
  congr 2
  congr 1
  funext result
  rw [outputs result]

end Selection

end Zkc.Construction
