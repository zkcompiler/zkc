module

public import Zkc.Construction.Projection
public import Zkc.Construction.Soundness
public import Zkc.Source.Structured.CommonAdapter
public import Zkc.Source.Structured.Linking
public import Zkc.Source.Structured.ProtocolLinking
public import Zkc.Source.Structured.OpenLaws

@[expose] public section

/-! Soundness of the participant projection rule.

`Holds` relates the original environment to the exported environment slot by
slot. Each accepted operation transports agreement of continuations
(`OperationSound`): the exported instructions it consumed, followed by any
continuation, equal the original operation followed by any continuation that
agrees on related results. A protocol application is the callee's body walked
in the child context between the callee's masks; a repeat is a loop whose
iterations each implement one step of the repeat's fold, with carried values
related to the masked state (`iterate_projects`). `walkStep_sound` covers one
operation given the soundness of the walk it recurses with, `walk_sound`
composes the steps along a region by induction on the walk's fuel, and
`project_sound` instantiates it at the entry, with the original's input and
output masks.
-/

set_option autoImplicit false

namespace Zkc.Construction
open Zkc.Source Zkc.Source.Structured

section Relation
variable {F G : Type}

/-- The replaced service holds the interactive reading's handle. -/
def ServiceHolds (handle : Nat) : (ty : Ty) → Option (assignment F G ty) → Prop
  | .service _, value => value = some handle
  | _, _ => False

/-- One slot relates an original component to the exported environment. -/
def SlotHolds (handle : Nat) (cenv : List (Value F G)) : Slot → (ty : Ty) →
    Option (assignment F G ty) → Prop
  | .absent, _, value => value = none
  | .free, _, value => value.isSome
  | .held reference, ty, value =>
      ∃ x, value = some x ∧ (cenv[reference]?).bind (Value.decode ty) = some x
  | .service, ty, value => ServiceHolds handle ty value

/-- Slots relate an original environment to the exported environment. -/
def Holds (handle : Nat) (cenv : List (Value F G)) (slots : List Slot) {Γ : List Ty}
    (env : Environment (Component (assignment F G)) Γ) : Prop :=
  ∀ (ty : Ty) (variable_ : Var Γ ty), SlotHolds handle cenv (Slot.at_ slots variable_.index) ty (env variable_)

/-- Slots relate an original result tuple to the exported environment. -/
def HoldsValues (handle : Nat) (cenv : List (Value F G)) :
    List Slot → {tys : List Ty} → Values (Component (assignment F G)) tys → Prop
  | _, [], .nil => True
  | slots, ty :: _, .cons value rest =>
      SlotHolds handle cenv (slots.headD .absent) ty value ∧ HoldsValues handle cenv slots.tail rest

theorem getElem?_of_prefix {α : Type} {list list' : List α} (prefix_ : list <+: list')
    {index : Nat} {value : α} (found : list[index]? = some value) : list'[index]? = some value := by
  obtain ⟨suffix, rfl⟩ := prefix_
  have bound : index < list.length := by
    by_contra outside
    rw [List.getElem?_eq_none (by omega)] at found
    cases found
  rw [List.getElem?_append_left bound]
  exact found

theorem SlotHolds.mono {handle : Nat} {cenv cenv' : List (Value F G)} (prefix_ : cenv <+: cenv')
    {slot : Slot} {ty : Ty} {value : Option (assignment F G ty)}
    (holds : SlotHolds handle cenv slot ty value) : SlotHolds handle cenv' slot ty value := by
  cases slot with
  | held reference =>
      obtain ⟨x, valueEq, decoded⟩ := holds
      refine ⟨x, valueEq, ?_⟩
      cases found : cenv[reference]? with
      | none => simp [found] at decoded
      | some v => rw [getElem?_of_prefix prefix_ found]; simpa [found] using decoded
  | absent => exact holds
  | free => exact holds
  | service => exact holds

theorem Holds.mono {handle : Nat} {cenv cenv' : List (Value F G)} (prefix_ : cenv <+: cenv')
    {slots : List Slot} {Γ : List Ty} {env : Environment (Component (assignment F G)) Γ}
    (holds : Holds handle cenv slots env) : Holds handle cenv' slots env :=
  fun ty variable_ => (holds ty variable_).mono prefix_

theorem HoldsValues.mono {handle : Nat} {cenv cenv' : List (Value F G)} (prefix_ : cenv <+: cenv') :
    ∀ {slots : List Slot} {tys : List Ty} {values : Values (Component (assignment F G)) tys},
      HoldsValues handle cenv slots values → HoldsValues handle cenv' slots values
  | _, [], .nil, _ => trivial
  | _, _ :: _, .cons _ _, holds => by
      obtain ⟨head, tail⟩ := holds
      exact ⟨head.mono prefix_, HoldsValues.mono prefix_ tail⟩

/-- Related results prepended to a related environment. -/
theorem Holds.prepend {handle : Nat} {cenv : List (Value F G)} {slots : List Slot} {Γ : List Ty}
    {env : Environment (Component (assignment F G)) Γ} (holds : Holds handle cenv slots env) :
    ∀ {tys : List Ty} {added : List Slot} (values : Values (Component (assignment F G)) tys),
      added.length = tys.length → HoldsValues handle cenv added values →
      Holds handle cenv (added ++ slots) (env.prepend values)
  | [], added, .nil, length, _ => by
      cases added with
      | nil => exact holds
      | cons => cases length
  | _ :: tys, added, .cons value rest, length, holdsValues => by
      obtain ⟨head, tail⟩ := holdsValues
      cases added with
      | nil => cases length
      | cons slot others =>
        have restHolds := Holds.prepend holds rest (by simpa using length) tail
        intro ty variable_
        cases variable_ with
        | here => exact head
        | there inner =>
          have := restHolds ty inner
          simpa [Slot.at_, Var.index, Environment.prepend, Environment.push] using this

/-- Operands read their slots. -/
theorem Holds.eval {handle : Nat} {cenv : List (Value F G)} {slots : List Slot} {Γ : List Ty}
    {env : Environment (Component (assignment F G)) Γ} (holds : Holds handle cenv slots env) :
    ∀ {tys : List Ty} (operands : Operands Γ tys),
      HoldsValues handle cenv ((Operands.indices operands).map (Slot.at_ slots)) (operands.eval env)
  | [], .nil => trivial
  | _ :: _, .cons variable_ rest => ⟨holds _ variable_, Holds.eval holds rest⟩

/-- A related result tuple is a related environment. -/
theorem HoldsValues.get {handle : Nat} {cenv : List (Value F G)} :
    ∀ {slots : List Slot} {tys : List Ty} {values : Values (Component (assignment F G)) tys},
      HoldsValues handle cenv slots values → Holds handle cenv slots values.get
  | _, [], .nil, _ => fun _ variable_ => nomatch variable_
  | slots, _ :: _, .cons value rest, holdsValues => by
      obtain ⟨head, tail⟩ := holdsValues
      intro ty variable_
      cases variable_ with
      | here =>
        cases slots with
        | nil => exact head
        | cons slot others => exact head
      | there inner =>
        have := HoldsValues.get tail ty inner
        cases slots with
        | nil =>
          simp only [Slot.at_, List.getD_eq_getElem?_getD, List.getElem?_nil, Option.getD_none] at this ⊢
          exact this
        | cons slot others => simpa [Slot.at_, Var.index, Values.get] using this

end Relation


section Reading
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- An absent slot among related arguments makes them absent as a tuple. -/
theorem sequence_none {handle : Nat} {cenv : List (Value F G)} :
    ∀ {slots : List Slot} {tys : List Ty} {values : Values (Component (assignment F G)) tys},
      HoldsValues handle cenv slots values → slots.length = tys.length →
      slots.any Slot.isAbsent = true → RoleFamily.sequence values = none
  | [], [], .nil, _, _, absent => by simp at absent
  | slot :: rest, _ :: _, .cons value others, holds, length, absent => by
      obtain ⟨head, tail⟩ := holds
      simp only [List.any_cons, Bool.or_eq_true] at absent
      rcases absent with here | there
      · cases slot with
        | absent =>
          simp only [SlotHolds, List.headD_cons] at head
          simp [RoleFamily.sequence, head]
        | _ => simp [Slot.isAbsent] at here
      · have := sequence_none tail (by simpa using length) there
        simp [RoleFamily.sequence, this]
  | [], _ :: _, _, _, length, _ => by cases length
  | _ :: _, [], _, _, length, _ => by cases length

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Related arguments without an absent slot are all present. -/
theorem sequence_some {handle : Nat} {cenv : List (Value F G)} :
    ∀ {slots : List Slot} {tys : List Ty} {values : Values (Component (assignment F G)) tys},
      HoldsValues handle cenv slots values → slots.length = tys.length →
      slots.any Slot.isAbsent = false → ∃ present, RoleFamily.sequence values = some present
  | [], [], .nil, _, _, _ => ⟨.nil, rfl⟩
  | slot :: rest, _ :: _, .cons value others, holds, length, notAbsent => by
      obtain ⟨head, tail⟩ := holds
      simp only [List.any_cons, Bool.or_eq_false_iff] at notAbsent
      obtain ⟨present, tailPresent⟩ := sequence_some tail (by simpa using length) notAbsent.2
      have valuePresent : ∃ x, value = some x := by
        cases slot with
        | absent => simp [Slot.isAbsent] at notAbsent
        | free =>
          simp only [SlotHolds, List.headD_cons] at head
          exact Option.isSome_iff_exists.mp head
        | held reference =>
          obtain ⟨x, valueEq, _⟩ := head
          exact ⟨x, valueEq⟩
        | service =>
          simp only [SlotHolds, List.headD_cons] at head
          rename_i ty _
          cases ty <;> simp [ServiceHolds] at head
          exact ⟨_, head⟩
      obtain ⟨x, rfl⟩ := valuePresent
      exact ⟨.cons x present, by simp [RoleFamily.sequence, tailPresent]⟩
  | [], _ :: _, _, _, length, _ => by cases length
  | _ :: _, [], _, _, length, _ => by cases length

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Held related arguments are present and read back from the exported
environment at their types. -/
theorem read_held {handle : Nat} {cenv : List (Value F G)} :
    ∀ {slots : List Slot} {tys : List Ty} {values : Values (Component (assignment F G)) tys}
      {references : List Nat},
      HoldsValues handle cenv slots values → slots.length = tys.length →
      Slot.references slots = some references →
      ∃ present arguments, RoleFamily.sequence values = some present ∧
        read cenv references = some arguments ∧ decodeValues tys arguments = some present
  | [], [], .nil, references, _, _, found => by
      simp only [Slot.references, Option.some.injEq] at found
      subst found
      exact ⟨.nil, [], rfl, rfl, rfl⟩
  | slot :: rest, _ :: _, .cons value others, references, holds, length, found => by
      obtain ⟨head, tail⟩ := holds
      cases slot with
      | held reference =>
        simp only [Slot.references] at found
        cases restFound : Slot.references rest with
        | none => simp [restFound] at found
        | some restReferences =>
          simp only [restFound, Option.map_some, Option.some.injEq] at found
          subst found
          obtain ⟨present, arguments, sequenced, readArguments, decoded⟩ :=
            read_held tail (by simpa using length) restFound
          obtain ⟨x, rfl, decodedHead⟩ := head
          cases at_ : cenv[reference]? with
          | none => simp [at_] at decodedHead
          | some v =>
          simp only [at_, Option.bind_some] at decodedHead
          refine ⟨.cons x present, v :: arguments, ?_, ?_, ?_⟩
          · simp [RoleFamily.sequence, sequenced]
          · simp only [read, List.mapM_cons, at_] at readArguments ⊢
            simp [readArguments]
          · simp [decodeValues, decodedHead, decoded]
      | absent => simp [Slot.references] at found
      | free => simp [Slot.references] at found
      | service => simp [Slot.references] at found
  | [], _ :: _, _, _, _, length, _ => by cases length
  | _ :: _, [], _, _, _, length, _ => by cases length

variable (context : Context) (handle : Nat) (table : Structured.Meanings F G)

/-- Skipped plumbing appends values without any action. -/
theorem skip_spec : ∀ (instructions : List Instruction) (cenv : List (Value F G)),
    ∃ extra : List (Value F G), extra.length = (skip context instructions).2 ∧
      ∀ {A : Type} (next : List (Value F G) → PIR.Process (Actions F G) A),
        specK context handle table instructions cenv next =
          specK context handle table (skip context instructions).1 (cenv ++ extra) next
  | [], cenv => ⟨[], rfl, fun next => by simp [skip]⟩
  | ⟨operation, operands, results, body⟩ :: rest, cenv => by
      cases operation with
      | indicesEmpty =>
        cases operands with
        | nil =>
          obtain ⟨extra, length, equal⟩ := skip_spec rest (cenv ++ [.indices []])
          refine ⟨.indices [] :: extra, by simp [skip, length], fun next => ?_⟩
          simp only [skip, specK, specStep]
          rw [equal]
          simp
        | cons => simp [skip]
      | indicesAppend =>
        match operands with
        | [coordinates, index] =>
          obtain ⟨extra, length, equal⟩ := skip_spec rest
            (cenv ++ [.indices (indicesAt cenv coordinates ++ (indexAt cenv index).toList)])
          refine ⟨.indices (indicesAt cenv coordinates ++ (indexAt cenv index).toList) :: extra,
            by simp [skip, length], fun next => ?_⟩
          simp only [skip, specK, specStep]
          rw [equal]
          simp
        | [] => simp [skip]
        | [_] => simp [skip]
        | _ :: _ :: _ :: _ => simp [skip]
      | observe suite template =>
        match operands with
        | [state, value, coordinates] =>
          by_cases sent : template.sentBy (context.role context.validator) = true
          · simp [skip, sent]
          · have notSent : template.sentBy (context.role context.validator) = false := by
              simpa using sent
            let appended : Value F G :=
              match template.origin context, dataAt cenv value with
              | some origin, some payload =>
                  .transcript ((transcriptAt cenv state).getD [] ++ [.message origin payload])
              | _, _ => .transcript ((transcriptAt cenv state).getD [])
            obtain ⟨extra, length, equal⟩ := skip_spec rest (cenv ++ [appended])
            refine ⟨appended :: extra, by simp [skip, notSent, length], fun next => ?_⟩
            have step : specK context handle table
                (⟨.observe suite template, [state, value, coordinates], results, body⟩ :: rest) cenv next =
                  specK context handle table rest (cenv ++ [appended]) next := by
              cases originEq : template.origin context <;> cases dataEq : dataAt cenv value <;>
                simp [specK, specStep, appended, originEq, dataEq, notSent]
            rw [step, equal]
            simp [skip, notSent]
        | [] => simp [skip]
        | [_] => simp [skip]
        | [_, _] => simp [skip]
        | _ :: _ :: _ :: _ :: _ => simp [skip]
      | _ => simp [skip]

/-- The next action-bearing instruction follows skipped plumbing. -/
theorem next_spec {instructions rest : List Instruction} {instruction : Instruction} {count : Nat}
    (found : next? context instructions = some (instruction, rest, count)) (cenv : List (Value F G)) :
    ∃ extra : List (Value F G), extra.length = count ∧
      ∀ {A : Type} (next : List (Value F G) → PIR.Process (Actions F G) A),
        specK context handle table instructions cenv next =
          specK context handle table (instruction :: rest) (cenv ++ extra) next := by
  unfold next? at found
  split at found
  · rename_i instruction' rest' count' skipped
    simp only [Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, rfl, rfl⟩ := found
    obtain ⟨extra, length, equal⟩ := skip_spec context handle table instructions cenv
    rw [skipped] at length equal
    exact ⟨extra, length, fun next => equal next⟩
  · cases found

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem expectReceive_some {site : String} {ty : Ty} {instructions rest : List Instruction}
    {count : Nat} (found : expectReceive context site ty instructions = some (rest, count)) :
    ∃ schema peer results, next? context instructions =
      some (⟨.receive site schema peer ty, [], results, []⟩, rest, count) := by
  unfold expectReceive at found
  split at found
  · rename_i site' schema peer ty' results rest' count' next
    split_ifs at found with same
    obtain ⟨rfl, rfl⟩ := same
    simp only [Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, rfl⟩ := found
    exact ⟨schema, peer, results, next⟩
  · cases found

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem expectDelivery_some {site : String} {reference : Nat} {instructions rest : List Instruction}
    {count : Nat} (found : expectDelivery context site reference instructions = some (rest, count)) :
    ∃ suite template state coordinates results, next? context instructions =
      some (⟨.observe suite template, [state, reference, coordinates], results, []⟩, rest, count) ∧
      template.sentBy (context.role context.validator) = true ∧
      template.messageSite? = some site ∧ (template.origin context).isSome := by
  unfold expectDelivery at found
  split at found
  · rename_i suite template state value coordinates results rest' count' next
    split_ifs at found with conditions
    obtain ⟨rfl, sent, siteEq, origin⟩ := conditions
    simp only [Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, rfl⟩ := found
    exact ⟨suite, template, state, coordinates, results, next, sent, siteEq, origin⟩
  · cases found

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem expectChallenge_some {site field : String} {instructions rest : List Instruction}
    {count : Nat} (found : expectChallenge context site field instructions = some (rest, count)) :
    ∃ suite template state coordinates results, next? context instructions =
      some (⟨.challenge suite field template, [state, coordinates], results, []⟩, rest, count) ∧
      template.querySite? = some site ∧ (template.origin context).isSome := by
  unfold expectChallenge at found
  split at found
  · rename_i suite field' template state coordinates results rest' count' next
    split_ifs at found with conditions
    obtain ⟨rfl, siteEq, origin⟩ := conditions
    simp only [Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, rfl⟩ := found
    exact ⟨suite, template, state, coordinates, results, next, siteEq, origin⟩
  · cases found

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem expectGuard_some {reference : Nat} {instructions rest : List Instruction} {count : Nat}
    (found : expectGuard context reference instructions = some (rest, count)) :
    ∃ site, next? context instructions = some (⟨.guard site, [reference], [], []⟩, rest, count) := by
  unfold expectGuard at found
  split at found
  · rename_i site condition rest' count' next
    split_ifs at found with same
    subst same
    simp only [Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, rfl⟩ := found
    exact ⟨site, next⟩
  · cases found

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem expectCall_some {helper : Helper} {references : List Nat} {instructions rest : List Instruction}
    {count : Nat} (found : expectCall context helper references instructions = some (rest, count)) :
    next? context instructions =
      some (⟨.call helper.name, references, helper.outputs.map .data, []⟩, rest, count) := by
  unfold expectCall at found
  split at found
  · rename_i name operands results rest' count' next
    split_ifs at found with conditions
    obtain ⟨rfl, rfl, rfl⟩ := conditions
    simp only [Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, rfl⟩ := found
    exact next
  · cases found

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem expectCalculation_some {calculation : Calculation} {references : List Nat}
    {instructions rest : List Instruction} {count : Nat}
    (found : expectCalculation context calculation references instructions = some (rest, count)) :
    next? context instructions =
      some (⟨.calculate calculation, references, calculation.op.results.map .data, []⟩, rest, count) := by
  unfold expectCalculation at found
  split at found
  · rename_i calculation' operands results rest' count' next
    split_ifs at found with conditions
    obtain ⟨rfl, rfl, rfl⟩ := conditions
    simp only [Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, rfl⟩ := found
    exact next
  · cases found

end Reading


section Operations
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (program : Structured.Program) (context : Context) (handle : Nat)

/-- The original program's helper tables in the plain participant view. -/
abbrev plainHelpers : Evaluation.ComponentTables F G (participantInterface F G) :=
  program.payload.definitions.foldl
    (Evaluation.ComponentTables.extend (.silent (participantInterface F G))) ⟨[], []⟩

/-- One original operation at the validator role, in the plain participant view. -/
abbrev originalOperation (ctx : ProtocolContext) (op : ProtocolOp)
    (args : Values (Component (assignment F G)) op.arguments)
    (callbacks : Values (RegionFunction (Component (assignment F G)) (participantInterface F G)) op.regions) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) op.results) :=
  protocolOperationWith (.silent _) (participantActions F G) (plainHelpers program) context.validator op args
    callbacks (program.payload.plainProtocolTable F G) ctx

/-- What one operation's soundness states: the exported program from
`instructions` equals the original operation followed by `next`, whenever the
exported continuation from `rest` and `next` agree on related results. -/
def OperationSound (ctx : ProtocolContext) (n : Nat) (op : ProtocolOp) (arguments : List Slot)
    (instructions rest : List Instruction) (results : List Slot) (n' : Nat) : Prop :=
  ∀ (args : Values (Component (assignment F G)) op.arguments)
    (callbacks : Values (RegionFunction (Component (assignment F G)) (participantInterface F G)) op.regions)
    (cenv : List (Value F G)), HoldsValues handle cenv arguments args →
    arguments.length = op.arguments.length → cenv.length = n →
    ∀ {A : Type} (kS : List (Value F G) → PIR.Process (Actions F G) A)
      (kO : Values (Component (assignment F G)) op.results → PIR.Process (Actions F G) A),
      (∀ cenv' values, cenv <+: cenv' → cenv'.length = n' → HoldsValues handle cenv' results values →
        specK context handle (helperTable program F G) rest cenv' kS = kO values) →
      specK context handle (helperTable program F G) instructions cenv kS =
        ((originalOperation program context ctx op args callbacks).interpret CommonAdapter.project).bind kO

theorem mark_projects (ctx : ProtocolContext) (n : Nat) (site : String) (arguments : List Slot)
    (instructions rest : List Instruction) (results : List Slot) (n' : Nat)
    (accepted : walkOperation program context ctx n (.mark site) arguments instructions =
      .ok (rest, results, n')) :
    OperationSound (F := F) (G := G) program context handle ctx n (.mark site) arguments instructions rest
      results n' := by
  simp only [walkOperation, Except.ok.injEq, Prod.mk.injEq] at accepted
  obtain ⟨rfl, rfl, rfl⟩ := accepted
  intro args callbacks cenv _ _ length A kS kO cont
  cases args
  cases callbacks
  exact cont cenv .nil (List.prefix_refl cenv) length trivial

theorem statement_projects (ctx : ProtocolContext) (n : Nat) (relation : String) (types : List Ty)
    (selectors : List String) (acceptance : Nat) (arguments : List Slot)
    (instructions rest : List Instruction) (results : List Slot) (n' : Nat)
    (accepted : walkOperation program context ctx n (.statement relation types selectors acceptance)
      arguments instructions = .ok (rest, results, n')) :
    OperationSound (F := F) (G := G) program context handle ctx n
      (.statement relation types selectors acceptance) arguments instructions rest results n' := by
  simp only [walkOperation, Except.ok.injEq, Prod.mk.injEq] at accepted
  obtain ⟨rfl, rfl, rfl⟩ := accepted
  intro args callbacks cenv _ _ length A kS kO cont
  cases callbacks
  exact cont cenv .nil (List.prefix_refl cenv) length trivial

theorem restrict_projects (ctx : ProtocolContext) (n : Nat) (ty : Ty) (roles : List Nat)
    (arguments : List Slot) (instructions rest : List Instruction) (results : List Slot) (n' : Nat)
    (accepted : walkOperation program context ctx n (.restrict ty roles) arguments instructions =
      .ok (rest, results, n')) :
    OperationSound (F := F) (G := G) program context handle ctx n (.restrict ty roles) arguments
      instructions rest results n' := by
  simp only [walkOperation, Except.ok.injEq, Prod.mk.injEq] at accepted
  obtain ⟨rfl, rfl, rfl⟩ := accepted
  intro args callbacks cenv argsHold _ length A kS kO cont
  cases callbacks
  rcases args with _ | ⟨value, _ | _⟩
  obtain ⟨head, _⟩ := argsHold
  apply cont cenv _ (List.prefix_refl cenv) length
  refine ⟨?_, trivial⟩
  simp only [List.headD_cons, Participant.restrict]
  split
  · simpa using head
  · rfl

theorem originalOperation_exchange (ctx : ProtocolContext) (ty : Ty) (sender receiver : Nat)
    (site : String) (value : Component (assignment F G) ty) :
    originalOperation program context ctx (.exchange ty sender receiver site) (.cons value .nil) .nil =
      ((Participant.exchange (services := services) context.validator (ctx.roles sender) (ctx.roles receiver)
        (qualifyProtocolSite ctx.applicationPrefix site) value).interpret (participantActions F G)).bind
          fun result => .done (.cons result .nil) := rfl

theorem exchange_other (ctx : ProtocolContext) (ty : Ty) (sender receiver : Nat) (site : String)
    (value : Component (assignment F G) ty)
    (fromOther : ctx.roles sender ≠ context.validator) (toOther : ctx.roles receiver ≠ context.validator) :
    originalOperation program context ctx (.exchange ty sender receiver site) (.cons value .nil) .nil =
      .done (.cons none .nil) := by
  rw [originalOperation_exchange]
  simp [Participant.exchange, fromOther, toOther, PIR.Process.interpret, PIR.Process.bind]

theorem exchange_receive (ctx : ProtocolContext) (ty : Ty) (sender receiver : Nat) (site : String)
    (value : Component (assignment F G) ty)
    (fromOther : ctx.roles sender ≠ context.validator) (toSelf : ctx.roles receiver = context.validator) :
    originalOperation program context ctx (.exchange ty sender receiver site) (.cons value .nil) .nil =
      .call (.receive ty (qualifyProtocolSite ctx.applicationPrefix site) (ctx.roles sender))
        fun received => .done (.cons (some received) .nil) := by
  rw [originalOperation_exchange]
  simp only [Participant.exchange, fromOther, toSelf, ite_false, ite_true, PIR.Process.interpret]
  rfl

theorem exchange_send (ctx : ProtocolContext) (ty : Ty) (sender receiver : Nat) (site : String)
    (value : Component (assignment F G) ty) (sent : assignment F G ty) (present : value = some sent)
    (fromSelf : ctx.roles sender = context.validator) :
    originalOperation program context ctx (.exchange ty sender receiver site) (.cons value .nil) .nil =
      .call (.send (ty := ty) (qualifyProtocolSite ctx.applicationPrefix site) (ctx.roles receiver) sent)
        fun _ => .done (.cons (some sent) .nil) := by
  subst present
  rw [originalOperation_exchange]
  simp only [Participant.exchange, fromSelf, ite_true, PIR.Process.interpret]
  rfl

theorem exchange_projects (ctx : ProtocolContext) (n : Nat) (ty : Ty) (sender receiver : Nat)
    (site : String) (arguments : List Slot) (instructions rest : List Instruction)
    (results : List Slot) (n' : Nat)
    (accepted : walkOperation program context ctx n (.exchange ty sender receiver site) arguments
      instructions = .ok (rest, results, n')) :
    OperationSound (F := F) (G := G) program context handle ctx n (.exchange ty sender receiver site)
      arguments instructions rest results n' := by
  intro args callbacks cenv argsHold _ length A kS kO cont
  cases callbacks
  rcases args with _ | ⟨value, _ | _⟩
  simp only [walkOperation] at accepted
  by_cases same : ctx.roles sender = ctx.roles receiver
  · rw [ite_eq_left same] at accepted
    cases accepted
  rw [ite_eq_right same] at accepted
  by_cases nonScalar : scalarType ty = none
  · rw [ite_eq_left nonScalar] at accepted
    cases accepted
  rw [ite_eq_right nonScalar] at accepted
  obtain ⟨common, scalar⟩ := Option.ne_none_iff_exists'.mp nonScalar
  by_cases fromSelf : ctx.roles sender = context.validator
  · -- The validator sends: the delivery of a challenge.
    rw [ite_eq_left fromSelf] at accepted
    match arguments, argsHold, accepted with
    | [.held reference], argsHold, accepted =>
      by_cases toProducer : ctx.roles receiver = context.producer
      · simp only at accepted
        rw [ite_eq_left toProducer] at accepted
        cases delivered : expectDelivery context (qualifyProtocolSite ctx.applicationPrefix site) reference
            instructions with
        | none => simp [delivered] at accepted
        | some found =>
          obtain ⟨rest', count⟩ := found
          simp only [delivered, Except.ok.injEq, Prod.mk.injEq] at accepted
          obtain ⟨rfl, rfl, rfl⟩ := accepted
          obtain ⟨suite, template, state, coordinates, results', next, sent, siteEq, originSome⟩ :=
            expectDelivery_some context delivered
          obtain ⟨⟨x, present, decodedBind⟩, _⟩ := argsHold
          obtain ⟨v, at_, decoded⟩ : ∃ v, cenv[reference]? = some v ∧ Value.decode ty v = some x := by
            cases found' : cenv[reference]? with
            | none => rw [found'] at decodedBind; cases decodedBind
            | some v => rw [found'] at decodedBind; exact ⟨v, rfl, decodedBind⟩
          rw [exchange_send program context ctx ty sender receiver site value x present fromSelf]
          obtain ⟨extra, extraLength, skipEq⟩ := next_spec context handle (helperTable program F G) next cenv
          rw [skipEq, toProducer]
          obtain ⟨origin, originEq⟩ := Option.isSome_iff_exists.mp originSome
          have readBack : (cenv ++ extra)[reference]? = some v := by
            rw [List.getElem?_append_left (lt_of_getElem?_eq_some at_)]
            exact at_
          have siteGet : (template.messageSite?).getD "" = qualifyProtocolSite ctx.applicationPrefix site := by
            rw [siteEq]
            rfl
          cases ty
          case index | vector | service => simp [scalarType] at scalar
          all_goals
            cases v <;> simp [Value.decode] at decoded
            rename_i payload
            cases payload <;> simp at decoded
            all_goals
              obtain ⟨rfl, rfl⟩ := decoded
              simp only [specK, specStep, originEq, dataAt, readBack, sent, ↓reduceIte,
                sendPayload, PIR.Process.interpret, CommonAdapter.project, PIR.Process.bind]
              rw [siteGet]
              congr 1
              funext _
              apply cont
              · exact List.prefix_append_of_prefix (List.prefix_append cenv extra)
              · simp [length, extraLength, Nat.add_assoc]
              · refine ⟨⟨_, rfl, ?_⟩, trivial⟩
                have bound := lt_of_getElem?_eq_some at_
                rw [List.getElem?_append_left (by simp; omega), readBack]
                simp [Value.decode]
      · simp only at accepted
        rw [ite_eq_right toProducer] at accepted
        cases accepted
    | [], _, accepted => simp at accepted
    | [.absent], _, accepted => simp at accepted
    | [.free], _, accepted => simp at accepted
    | [.service], _, accepted => simp at accepted
    | _ :: _ :: _, _, accepted => simp at accepted
  rw [ite_eq_right fromSelf] at accepted
  by_cases toSelf : ctx.roles receiver = context.validator
  · -- The validator receives.
    rw [ite_eq_left toSelf] at accepted
    by_cases fromProducer : ctx.roles sender = context.producer
    · rw [ite_eq_left fromProducer] at accepted
      cases received : expectReceive context (qualifyProtocolSite ctx.applicationPrefix site) ty
          instructions with
      | none => simp [received] at accepted
      | some found =>
        obtain ⟨rest', count⟩ := found
        simp only [received, Except.ok.injEq, Prod.mk.injEq] at accepted
        obtain ⟨rfl, rfl, rfl⟩ := accepted
        obtain ⟨schema, peer, results', next⟩ := expectReceive_some context received
        rw [exchange_receive program context ctx ty sender receiver site value fromSelf toSelf]
        obtain ⟨extra, extraLength, skipEq⟩ := next_spec context handle (helperTable program F G) next cenv
        rw [skipEq, fromProducer]
        cases ty
        case index | vector | service => simp [scalarType] at scalar
        all_goals
          simp only [specK, specStep, scalarType, PIR.Process.interpret, CommonAdapter.project,
            PIR.Process.bind]
          congr 1
          funext received
          apply cont
          · exact List.prefix_append_of_prefix (List.prefix_append cenv extra)
          · simp [length, extraLength, Nat.add_assoc]
          · refine ⟨⟨received, rfl, ?_⟩, trivial⟩
            rw [List.getElem?_append_right (by simp [length, extraLength])]
            simp [length, extraLength, Value.decode]
    · rw [ite_eq_right fromProducer] at accepted
      cases accepted
  · -- Another role's exchange.
    rw [ite_eq_right toSelf] at accepted
    simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl, rfl⟩ := accepted
    rw [exchange_other program context ctx ty sender receiver site value fromSelf toSelf]
    exact cont cenv _ (List.prefix_refl cenv) length ⟨rfl, trivial⟩

theorem originalOperation_draw (ctx : ProtocolContext) (owner : Nat) (field site : String)
    (service : Component (assignment F G) (.service ("random." ++ field ++ "/0"))) :
    originalOperation program context ctx (.draw owner field site) (.cons service .nil) .nil =
      ((Participant.query (services := services) context.validator (ctx.roles owner)
        (qualifyProtocolSite ctx.applicationPrefix site) field (.cons service .nil)).interpret
          (participantActions F G)).bind fun result => .done (.cons result .nil) := rfl

theorem draw_projects (ctx : ProtocolContext) (n : Nat) (owner : Nat) (field site : String)
    (arguments : List Slot) (instructions rest : List Instruction) (results : List Slot) (n' : Nat)
    (accepted : walkOperation program context ctx n (.draw owner field site) arguments instructions =
      .ok (rest, results, n')) :
    OperationSound (F := F) (G := G) program context handle ctx n (.draw owner field site) arguments
      instructions rest results n' := by
  intro args callbacks cenv argsHold _ length A kS kO cont
  cases callbacks
  rcases args with _ | ⟨service, _ | _⟩
  simp only [walkOperation] at accepted
  by_cases owned : ctx.roles owner = context.validator
  · rw [ite_eq_left owned] at accepted
    match arguments, argsHold, accepted with
    | [.service], argsHold, accepted =>
      simp only at accepted
      cases challenged : expectChallenge context (qualifyProtocolSite ctx.applicationPrefix site) field
          instructions with
      | none => simp [challenged] at accepted
      | some found =>
        obtain ⟨rest', count⟩ := found
        simp only [challenged, Except.ok.injEq, Prod.mk.injEq] at accepted
        obtain ⟨rfl, rfl, rfl⟩ := accepted
        obtain ⟨suite, template, state, coordinates, results', next, siteEq, originSome⟩ :=
          expectChallenge_some context challenged
        obtain ⟨present, _⟩ := argsHold
        simp only [List.headD_cons, SlotHolds, ServiceHolds] at present
        obtain ⟨origin, originEq⟩ := Option.isSome_iff_exists.mp originSome
        obtain ⟨extra, extraLength, skipEq⟩ := next_spec context handle (helperTable program F G) next cenv
        rw [skipEq]
        have original : originalOperation program context ctx (.draw owner field site)
            (.cons service .nil) .nil =
            .call (.query (qualifyProtocolSite ctx.applicationPrefix site) field (.cons handle .nil))
              fun answer => .done (.cons (some answer) .nil) := by
          subst present
          rw [originalOperation_draw]
          simp only [Participant.query, owned, ite_true]
          rfl
        rw [original]
        simp only [specK, specStep, originEq, siteEq, PIR.Process.interpret, CommonAdapter.project]
        congr 1
        funext answer
        apply cont
        · exact List.prefix_append_of_prefix (List.prefix_append cenv extra)
        · simp [length, extraLength, Nat.add_assoc]
        · refine ⟨⟨answer, rfl, ?_⟩, trivial⟩
          rw [List.getElem?_append_right (by simp [length, extraLength])]
          simp [length, extraLength, Value.decode]
    | [], _, accepted => simp at accepted
    | [.absent], _, accepted => simp at accepted
    | [.free], _, accepted => simp at accepted
    | [.held _], _, accepted => simp at accepted
    | _ :: _ :: _, _, accepted => simp at accepted
  · rw [ite_eq_right owned] at accepted
    simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl, rfl⟩ := accepted
    have original : originalOperation program context ctx (.draw owner field site)
        (.cons service .nil) .nil = .done (.cons none .nil) := by
      rw [originalOperation_draw]
      simp only [Participant.query, owned, ite_false, PIR.Process.interpret]
      rfl
    rw [original]
    exact cont cenv _ (List.prefix_refl cenv) length ⟨rfl, trivial⟩

theorem originalOperation_guard (ctx : ProtocolContext) (owner : Nat) (site : String)
    (condition : Component (assignment F G) .boolean) :
    originalOperation program context ctx (.guard owner site) (.cons condition .nil) .nil =
      ((Participant.guard (services := services) (Value := assignment F G) context.validator
        (ctx.roles owner) condition).interpret (participantActions F G)).bind
          fun _ => .done .nil := rfl

theorem guard_projects (ctx : ProtocolContext) (n : Nat) (owner : Nat) (site : String)
    (arguments : List Slot) (instructions rest : List Instruction) (results : List Slot) (n' : Nat)
    (accepted : walkOperation program context ctx n (.guard owner site) arguments instructions =
      .ok (rest, results, n')) :
    OperationSound (F := F) (G := G) program context handle ctx n (.guard owner site) arguments
      instructions rest results n' := by
  intro args callbacks cenv argsHold _ length A kS kO cont
  cases callbacks
  rcases args with _ | ⟨condition, _ | _⟩
  simp only [walkOperation] at accepted
  by_cases owned : ctx.roles owner = context.validator
  · rw [ite_eq_left owned] at accepted
    match arguments, argsHold, accepted with
    | [.held reference], argsHold, accepted =>
      simp only at accepted
      cases guarded : expectGuard context reference instructions with
      | none => simp [guarded] at accepted
      | some found =>
        obtain ⟨rest', count⟩ := found
        simp only [guarded, Except.ok.injEq, Prod.mk.injEq] at accepted
        obtain ⟨rfl, rfl, rfl⟩ := accepted
        obtain ⟨site', next⟩ := expectGuard_some context guarded
        obtain ⟨⟨b, present, decodedBind⟩, _⟩ := argsHold
        obtain ⟨v, at_, decoded⟩ : ∃ v, cenv[reference]? = some v ∧ Value.decode .boolean v = some b := by
          cases found' : cenv[reference]? with
          | none => rw [found'] at decodedBind; cases decodedBind
          | some v => rw [found'] at decodedBind; exact ⟨v, rfl, decodedBind⟩
        obtain ⟨extra, extraLength, skipEq⟩ := next_spec context handle (helperTable program F G) next cenv
        rw [skipEq, originalOperation_guard]
        subst present
        cases v <;> simp [Value.decode] at decoded
        rename_i payload
        cases payload <;> simp at decoded
        subst decoded
        rename_i b
        have readBack' : (cenv ++ extra)[reference]? = some (.data (.boolean b)) := by
          rw [List.getElem?_append_left (lt_of_getElem?_eq_some at_)]
          exact at_
        cases b
        · simp only [specK, specStep, readBack', Participant.guard, owned, ite_true]
          rfl
        · simp only [specK, specStep, readBack', Participant.guard, owned, ite_true,
            PIR.Process.interpret, PIR.Process.bind]
          exact cont _ .nil (List.prefix_append cenv extra) (by simp [length, extraLength]) trivial
    | [], _, accepted => simp at accepted
    | [.absent], _, accepted => simp at accepted
    | [.free], _, accepted => simp at accepted
    | [.service], _, accepted => simp at accepted
    | _ :: _ :: _, _, accepted => simp at accepted
  · rw [ite_eq_right owned] at accepted
    simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl, rfl⟩ := accepted
    rw [originalOperation_guard]
    simp only [Participant.guard, owned, ite_false, PIR.Process.interpret, PIR.Process.bind]
    exact cont cenv .nil (List.prefix_refl cenv) length trivial

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- A process that cannot call is its outcome in every effect interface. -/
theorem closed_interpret {I : PIR.Signature} {A : Type} (process : PIR.Process closedInterface A) :
    process.interpret (closedLift (I := I)) = ofOutcome (closedOutcome process) := by
  cases process with
  | done value => rfl
  | halt reason => rfl
  | call operation _ => exact (show Empty from operation).elim

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- A call by name invokes the checked helper found under that name. -/
theorem callHelper_invoke (table : Structured.Meanings F G) (helper : Helper)
    (found : ∃ entry : HelperDefinition (assignment F G) closedInterface,
      table.find? (fun entry => entry.helper.name == helper.name) = some entry ∧ entry.helper = helper)
    (arguments : List (Value F G)) (values : Values (assignment F G) helper.inputs)
    (decoded : decodeValues helper.inputs arguments = some values) :
    callHelper table helper.name arguments =
      match closedOutcome (invoke table helper values) with
      | .returned results => .returned (encodeValues results)
      | .stopped reason => .stopped reason := by
  obtain ⟨⟨helper', body⟩, found, same⟩ := found
  simp only at same
  subst same
  have invoked : invoke table helper' values = body values := by
    simp [invoke, found]
  rw [invoked]
  simp only [callHelper, found, decoded]
  generalize closedOutcome (body values) = outcome
  cases outcome <;> rfl

/-- The program's checked helpers, looked up in the closed table. -/
theorem helperTable_lookup (helper : Helper)
    (present : helper ∈ program.payload.definitions.map CheckedDefinition.helper) :
    ∃ entry : HelperDefinition (assignment F G) closedInterface,
      (helperTable program F G).find? (fun entry => entry.helper.name == helper.name) = some entry ∧
        entry.helper = helper :=
  Evaluation.linked_lookup .closed program.payload.linked helper present

/-- The plain view's helpers are the closed table's, lifted. -/
theorem plainHelpers_invoke (helper : Helper) (values : Values (assignment F G) helper.inputs) :
    invoke (plainHelpers program (F := F) (G := G)).closed helper values =
      ofOutcome (closedOutcome (invoke (helperTable program F G) helper values)) := by
  rw [← closed_interpret, Evaluation.ComponentTables.closed_fold]
  exact (Evaluation.foldMeanings_closedLift program.payload.definitions helper values).symm

theorem originalOperation_localCall (ctx : ProtocolContext) (helper : Helper)
    (kind : helper.kind = .local) (owner : Nat) (site : String)
    (args : Values (Component (assignment F G)) (ProtocolOp.localCall helper kind owner site).arguments)
    (callbacks : Values (RegionFunction (Component (assignment F G)) (participantInterface F G))
      (ProtocolOp.localCall helper kind owner site).regions) :
    originalOperation program context ctx (.localCall helper kind owner site) args callbacks =
      Participant.owned context.validator (ctx.roles owner)
        (invoke (plainHelpers program).closed helper) args := rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Values encoded at data types decode back, as held results. -/
theorem holdsValues_encoded {handle : Nat} (start : Nat) (cenv : List (Value F G))
    (length : cenv.length = start) {tys : List Ty}
    (data : tys.all dataType = true) (values : Values (assignment F G) tys) :
    HoldsValues handle (cenv ++ encodeValues values)
      ((List.range tys.length).map fun index => .held (start + index)) values.present := by
  induction values generalizing cenv start with
  | nil => trivial
  | @cons ty tys value rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at data
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, Values.present,
      HoldsValues, List.headD_cons, List.tail_cons]
    refine ⟨⟨value, rfl, ?_⟩, ?_⟩
    · simp [encodeValues, ← length, Value.decode_encode data.1]
    · have := ih (start + 1) (cenv ++ [Value.encode ty value]) (by simp [length]) data.2
      simpa [encodeValues, Function.comp_def, Nat.add_assoc, Nat.add_comm 1] using this

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem holdsValues_absent {handle : Nat} (cenv : List (Value F G)) :
    ∀ tys : List Ty, HoldsValues handle cenv (tys.map fun _ => .absent) (Values.absent (assignment F G) tys)
  | [] => trivial
  | _ :: tys => ⟨rfl, holdsValues_absent cenv tys⟩

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem read_append {env extra values : List (Value F G)} {references : List Nat}
    (found : read env references = some values) : read (env ++ extra) references = some values := by
  induction references generalizing values with
  | nil => simpa [read] using found
  | cons reference rest ih =>
    simp only [read, List.mapM_cons, Option.bind_eq_bind] at found ⊢
    cases first : env[reference]? with
    | none => simp [first] at found
    | some value =>
      cases others : rest.mapM (env[·]?) with
      | none => simp [first, others] at found
      | some tail =>
        simp only [first, others, Option.bind_some, Option.pure_def, Option.some.injEq] at found
        subst found
        rw [List.getElem?_append_left (lt_of_getElem?_eq_some first), first]
        have := ih (values := tail) (by simpa [read] using others)
        simp only [read] at this
        simp [this]

theorem localCall_projects (ctx : ProtocolContext) (n : Nat) (helper : Helper)
    (kind : helper.kind = .local) (owner : Nat) (site : String) (arguments : List Slot)
    (instructions rest : List Instruction) (results : List Slot) (n' : Nat)
    (accepted : walkOperation program context ctx n (.localCall helper kind owner site) arguments
      instructions = .ok (rest, results, n')) :
    OperationSound (F := F) (G := G) program context handle ctx n (.localCall helper kind owner site)
      arguments instructions rest results n' := by
  intro args callbacks cenv argsHold argsLength length A kS kO cont
  simp only [walkOperation] at accepted
  by_cases owned : ctx.roles owner = context.validator
  · rw [ite_eq_left owned] at accepted
    cases referenced : Slot.references arguments with
    | none => simp [referenced] at accepted
    | some references =>
      simp only [referenced] at accepted
      cases called : expectCall context helper references instructions with
      | none => simp [called] at accepted
      | some found =>
        obtain ⟨rest', count⟩ := found
        simp only [called] at accepted
        split_ifs at accepted with checked
        simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
        obtain ⟨rfl, rfl, rfl⟩ := accepted
        obtain ⟨present, data⟩ := checked
        have next := expectCall_some context called
        have argsHold' : HoldsValues (tys := helper.inputs) handle cenv arguments args := argsHold
        obtain ⟨values, readArguments, sequenced, readBack, decoded⟩ :=
          read_held argsHold' argsLength referenced
        rw [originalOperation_localCall]
        simp only [Participant.owned, owned, ite_true, sequenced]
        rw [plainHelpers_invoke]
        obtain ⟨extra, extraLength, skipEq⟩ := next_spec context handle (helperTable program F G) next cenv
        rw [skipEq]
        simp only [specK, specStep, read_append readBack,
          callHelper_invoke _ helper (helperTable_lookup program helper present) readArguments values decoded]
        cases outcome : closedOutcome (invoke (helperTable program F G) helper values) with
        | returned outputs =>
          simp only [ofOutcome, encodeValues_length, List.length_map, ite_true, PIR.Process.bind,
            PIR.Process.interpret]
          apply cont
          · exact List.prefix_append_of_prefix (List.prefix_append cenv extra)
          · simp [length, extraLength, encodeValues_length, Nat.add_assoc]
          · exact holdsValues_encoded (n + count) (cenv ++ extra) (by simp [length, extraLength]) data
              outputs
        | stopped reason => simp [ofOutcome, PIR.Process.bind, PIR.Process.interpret]
  · rw [ite_eq_right owned] at accepted
    simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl, rfl⟩ := accepted
    rw [originalOperation_localCall]
    simp only [Participant.owned, owned, ite_false, PIR.Process.interpret, PIR.Process.bind]
    exact cont cenv _ (List.prefix_refl cenv) length (holdsValues_absent cenv helper.outputs)

/-- Carrier calculations take the strict component path of the evaluator. -/
theorem componentOperation_calculation {I : PIR.Signature} (observations : SiteObservations I)
    (tables : Evaluation.ComponentTables F G I) (calculation : Calculation)
    (args : Values (Component (assignment F G)) calculation.op.arguments)
    (bodies : Values (RegionFunction (assignment F G) I) calculation.op.regions) :
    Evaluation.componentOperation observations tables calculation.op args bodies =
      strictComponent (Evaluation.meaning observations tables.closed) calculation.op args bodies := by
  cases calculation <;> rfl

omit [DecidableEq F] [DecidableEq G] in
theorem Calculation.single (calculation : Calculation) : ∃ ty, calculation.op.results = [ty] := by
  cases calculation <;> exact ⟨_, rfl⟩

/-- A total calculation returns. -/
theorem Calculation.total_returns (calculation : Calculation) (total : calculation.total = true)
    (values : Values (assignment F G) calculation.op.arguments) :
    ∃ results, calculation.evaluate values = .returned results := by
  cases calculation <;> simp [Calculation.total] at total
  all_goals
    rcases values with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩
    exact ⟨_, rfl⟩

theorem originalOperation_calculate (ctx : ProtocolContext) (operation : Op)
    (allowed : operation.isCalculation = true)
    (args : Values (Component (assignment F G)) (ProtocolOp.calculate operation allowed).arguments)
    (callbacks : Values (RegionFunction (Component (assignment F G)) (participantInterface F G))
      (ProtocolOp.calculate operation allowed).regions) :
    originalOperation program context ctx (.calculate operation allowed) args callbacks =
      Evaluation.componentOperation (.silent _) (plainHelpers program) operation args
        (operation.calculationRegions allowed) := rfl

theorem originalOperation_calculation (ctx : ProtocolContext) (calculation : Calculation)
    (allowed : calculation.op.isCalculation = true)
    (args : Values (Component (assignment F G)) (ProtocolOp.calculate calculation.op allowed).arguments)
    (callbacks : Values (RegionFunction (Component (assignment F G)) (participantInterface F G))
      (ProtocolOp.calculate calculation.op allowed).regions) :
    originalOperation program context ctx (.calculate calculation.op allowed) args callbacks =
      match RoleFamily.sequence (types := calculation.op.arguments) args with
      | none => .done (Values.absent (assignment F G) calculation.op.results)
      | some values => (ofOutcome (calculation.evaluate values)).bind fun results =>
          .done results.present := by
  have general : ∀ args : Values (Component (assignment F G)) calculation.op.arguments,
      Evaluation.componentOperation (.silent _) (plainHelpers program) calculation.op args
        (calculation.op.calculationRegions allowed) =
      match RoleFamily.sequence args with
      | none => .done (Values.absent (assignment F G) calculation.op.results)
      | some values => (ofOutcome (calculation.evaluate values)).bind fun results =>
          .done results.present := by
    intro args
    rw [componentOperation_calculation]
    simp only [strictComponent]
    cases sequenced : RoleFamily.sequence args with
    | none => rfl
    | some values =>
      dsimp only
      rw [Calculation.operation_eq]
  exact general args

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- A single present result relates to a free slot. -/
theorem holdsValues_free {handle : Nat} (cenv : List (Value F G)) :
    ∀ {tys : List Ty} (values : Values (assignment F G) tys), tys.length = 1 →
      HoldsValues handle cenv [.free] values.present
  | [_], .cons _ .nil, _ => ⟨rfl, trivial⟩
  | [], .nil, length => by cases length
  | _ :: _ :: _, .cons _ (.cons _ _), length => by simp at length

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- A single encoded result is held at the next reference. -/
theorem holdsValues_single {handle : Nat} (cenv : List (Value F G)) :
    ∀ {tys : List Ty} (values : Values (assignment F G) tys), tys.length = 1 →
      tys.all dataType = true →
      HoldsValues handle (cenv ++ encodeValues values) [.held cenv.length] values.present
  | [_], .cons value .nil, _, data => by
      simp only [List.all_cons, List.all_nil, Bool.and_true] at data
      exact ⟨⟨value, rfl, by simp [encodeValues, Value.decode_encode data]⟩, trivial⟩
  | [], .nil, length, _ => by cases length
  | _ :: _ :: _, .cons _ (.cons _ _), length, _ => by simp at length

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem Operands.indices_length {Ty : Type} {Γ : List Ty} :
    ∀ {tys : List Ty} (operands : Operands Γ tys), (Operands.indices operands).length = tys.length
  | [], .nil => rfl
  | _ :: _, .cons _ rest => by simp [Operands.indices, Operands.indices_length rest]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Arguments related to absent slots are absent. -/
theorem holdsValues_all_absent {cenv : List (Value F G)} :
    ∀ {slots : List Slot} {tys : List Ty} {values : Values (Component (assignment F G)) tys},
      HoldsValues handle cenv slots values → slots.length = tys.length → slots.all Slot.isAbsent = true →
      values = Values.absent (assignment F G) tys
  | [], [], .nil, _, _, _ => rfl
  | slot :: rest, _ :: _, .cons value others, holds, length, absent => by
      obtain ⟨head, tail⟩ := holds
      simp only [List.all_cons, Bool.and_eq_true] at absent
      cases slot with
      | absent =>
        simp only [SlotHolds, List.headD_cons] at head
        subst head
        rw [holdsValues_all_absent tail (by simpa using length) absent.2]
        rfl
      | _ => simp [Slot.isAbsent] at absent
  | [], _ :: _, _, _, length, _ => by cases length
  | _ :: _, [], _, _, length, _ => by cases length

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem operands_absent {Γ : List Ty} {env : Environment (Component (assignment F G)) Γ}
    (absent : ∀ ty (v : Var Γ ty), env v = none) :
    ∀ {tys : List Ty} (operands : Operands Γ tys),
      Operands.eval env operands = Values.absent (assignment F G) tys
  | [], .nil => rfl
  | _ :: _, .cons v rest => by
      simp only [Operands.eval, Values.absent, absent, operands_absent absent rest]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem prepend_absent {Γ : List Ty} {env : Environment (Component (assignment F G)) Γ}
    (absent : ∀ ty (v : Var Γ ty), env v = none) (tys : List Ty) :
    ∀ ty (v : Var (tys ++ Γ) ty), (env.prepend (Values.absent (assignment F G) tys)) v = none := by
  intro ty v
  induction tys with
  | nil => exact absent ty v
  | cons head rest ih =>
    cases v with
    | here => rfl
    | there v => exact ih v

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem get_absent {tys : List Ty} :
    ∀ ty (v : Var tys ty), (Values.absent (assignment F G) tys).get v = none := by
  intro ty v
  induction tys with
  | nil => cases v
  | cons head rest ih =>
    cases v with
    | here => rfl
    | there v => exact ih v

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem sequence_absent : ∀ {tys : List Ty}, tys ≠ [] →
    RoleFamily.sequence (Values.absent (assignment F G) tys) = none
  | [], nonempty => absurd rfl nonempty
  | _ :: _, _ => rfl

/-- Strict operations on absent operands are absent. -/
theorem componentOperation_absent {I : PIR.Signature} (observations : SiteObservations I)
    (tables : Evaluation.ComponentTables F G I) (op : Op) (strict : strictOperation op = true)
    (nonempty : op.arguments ≠ []) (bodies : Values (RegionFunction (assignment F G) I) op.regions) :
    Evaluation.componentOperation observations tables op (Values.absent (assignment F G) op.arguments) bodies =
      .done (Values.absent (assignment F G) op.results) := by
  have strictCase : strictComponent (Evaluation.meaning observations tables.closed) op
      (Values.absent (assignment F G) op.arguments) bodies =
      .done (Values.absent (assignment F G) op.results) := by
    simp only [strictComponent, sequence_absent nonempty]
  cases op with
  | exec primitive => simp [strictOperation] at strict
  | map spec => simp [strictOperation] at strict
  | invoke helper =>
    have local_ : helper.kind ≠ .math := by simpa [strictOperation] using strict
    cases bodies
    simp only [Evaluation.componentOperation, local_]
    exact strictCase
  | _ => exact strictCase

/-- A helper body that preserves absence evaluates absent inputs to absent
outputs, with no effect or stop. -/
theorem absentPreserving_component {I : PIR.Signature} (observations : SiteObservations I)
    (tables : Evaluation.ComponentTables F G I) :
    ∀ {Γ out : List Ty} (region : Region dialect Γ out), absentPreserving region = true →
    ∀ (env : Environment (Component (assignment F G)) Γ), (∀ ty (v : Var Γ ty), env v = none) →
      region.component (Evaluation.meaning observations tables.closed)
          (Evaluation.componentOperation observations tables) env =
        .done (Values.absent (assignment F G) out)
  | _, _, .ret values, _, env, absent => by
      simp only [Region.component, operands_absent absent values]
  | _, _, .stop _, preserving, _, _ => by simp [absentPreserving] at preserving
  | _, _, .letOp op arguments bodies next, preserving, env, absent => by
      simp only [absentPreserving, Bool.and_eq_true, bne_iff_ne, ne_eq] at preserving
      obtain ⟨⟨nonempty, strict⟩, rest⟩ := preserving
      have argumentsNonempty : op.arguments ≠ [] := by
        intro empty
        apply nonempty
        have lengths : arguments.indices.length = op.arguments.length := Operands.indices_length arguments
        rw [empty] at lengths
        exact List.eq_nil_of_length_eq_zero lengths
      simp only [Region.component, operands_absent absent arguments]
      rw [componentOperation_absent observations tables op strict argumentsNonempty]
      simp only [PIR.Process.bind]
      exact absentPreserving_component observations tables next rest _ (prepend_absent absent _)
  | _, _, .bind body next, preserving, env, absent => by
      simp only [absentPreserving, Bool.and_eq_true] at preserving
      simp only [Region.component, absentPreserving_component observations tables body preserving.1 env absent,
        PIR.Process.bind]
      exact absentPreserving_component observations tables next preserving.2 _ (prepend_absent absent _)

/-- A checked helper's component meaning in the plain participant tables is its
body's component evaluation. -/
theorem plainHelpers_component (definition : CheckedDefinition)
    (member : definition ∈ program.payload.definitions)
    (args : Values (Component (assignment F G)) definition.inputs) :
    invoke (plainHelpers (F := F) (G := G) program).components definition.helper args =
      definition.body.component (Evaluation.meaning (.silent _) (plainHelpers program).closed)
        (Evaluation.componentOperation (.silent _) (plainHelpers program)) args.get := by
  calc
    _ = (invoke (program.payload.tables F G).components definition.helper args).interpret forgetSites :=
      ((Evaluation.ComponentTables.fold_forgetSites program.payload.definitions).components
        definition.helper args).symm
    _ = _ := by
      rw [program.payload.component_invoke_body definition member args]
      exact Evaluation.component_interpret forgetSites observedSites_forgetSites
        (Evaluation.ComponentTables.fold_forgetSites program.payload.definitions) definition.body args.get

/-- A Math helper whose body preserves absence returns absent outputs on absent
inputs. -/
theorem invoke_absent (definition : CheckedDefinition) (member : definition ∈ program.payload.definitions)
    (preserving : absentPreserving definition.body = true) :
    invoke (plainHelpers (F := F) (G := G) program).components definition.helper
        (Values.absent (assignment F G) definition.inputs) =
      .done (Values.absent (assignment F G) definition.outputs) := by
  rw [plainHelpers_component program definition member]
  exact absentPreserving_component _ _ definition.body preserving _ get_absent

/-- A carrier calculation's component evaluation: absent when an operand is,
and otherwise the evaluator's outcome with present results. -/
theorem componentCalculation (calculation : Calculation)
    (args : Values (Component (assignment F G)) calculation.op.arguments)
    (bodies : Values (RegionFunction (assignment F G) (participantInterface F G)) calculation.op.regions) :
    Evaluation.componentOperation (.silent _) (plainHelpers program) calculation.op args bodies =
      match RoleFamily.sequence (types := calculation.op.arguments) args with
      | none => .done (Values.absent (assignment F G) calculation.op.results)
      | some values => (ofOutcome (calculation.evaluate values)).bind fun results =>
          .done results.present := by
  rw [componentOperation_calculation]
  simp only [strictComponent]
  cases sequenced : RoleFamily.sequence args with
  | none => rfl
  | some values =>
    dsimp only
    rw [Calculation.operation_eq]

/-- Soundness of one carrier calculation step, for any callbacks. -/
theorem vocabulary_projects (n : Nat) (calculation : Calculation) (arguments : List Slot)
    (instructions rest : List Instruction) (results : List Slot) (n' : Nat)
    (accepted : walkVocabulary context n calculation arguments instructions = .ok (rest, results, n'))
    (args : Values (Component (assignment F G)) calculation.op.arguments)
    (bodies : Values (RegionFunction (assignment F G) (participantInterface F G)) calculation.op.regions)
    (cenv : List (Value F G)) (argsHold : HoldsValues handle cenv arguments args)
    (argsLength : arguments.length = calculation.op.arguments.length) (length : cenv.length = n)
    {A : Type} (kS : List (Value F G) → PIR.Process (Actions F G) A)
    (kO : Values (Component (assignment F G)) calculation.op.results → PIR.Process (Actions F G) A)
    (cont : ∀ cenv' values, cenv <+: cenv' → cenv'.length = n' → HoldsValues handle cenv' results values →
      specK context handle (helperTable program F G) rest cenv' kS = kO values) :
    specK context handle (helperTable program F G) instructions cenv kS =
      ((Evaluation.componentOperation (.silent _) (plainHelpers program) calculation.op args bodies).interpret
        CommonAdapter.project).bind kO := by
  simp only [walkVocabulary] at accepted
  rw [componentCalculation]
  have argsHold' : HoldsValues (tys := calculation.op.arguments) handle cenv arguments args := argsHold
  by_cases absent : arguments.any Slot.isAbsent = true
  · rw [ite_eq_left absent] at accepted
    simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl, rfl⟩ := accepted
    rw [sequence_none argsHold' argsLength absent]
    exact cont cenv _ (List.prefix_refl cenv) length (holdsValues_absent cenv _)
  · rw [ite_eq_right absent] at accepted
    have notAbsent : arguments.any Slot.isAbsent = false := by simpa using absent
    cases matched : (if calculation.op.results.all dataType = true then Slot.references arguments
        else none).bind (fun references => expectCalculation context calculation references instructions) with
    | some found' =>
      obtain ⟨rest', count⟩ := found'
      simp only [matched, Except.ok.injEq, Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl, rfl⟩ := accepted
      by_cases data : calculation.op.results.all dataType = true
      · rw [ite_eq_left data] at matched
        cases referenced : Slot.references arguments with
        | none => simp [referenced] at matched
        | some references =>
          simp only [referenced, Option.bind_some] at matched
          have next := expectCalculation_some context matched
          obtain ⟨values, readArguments, sequenced, readBack, decoded⟩ :=
            read_held argsHold' argsLength referenced
          rw [sequenced]
          obtain ⟨extra, extraLength, skipEq⟩ :=
            next_spec context handle (helperTable program F G) next cenv
          rw [skipEq]
          simp only [specK, specStep, read_append readBack, Zkc.Construction.calculate, decoded]
          cases evaluated : calculation.evaluate values with
          | returned outputs =>
            simp only [ofOutcome, PIR.Process.bind, PIR.Process.interpret]
            apply cont
            · exact List.prefix_append_of_prefix (List.prefix_append cenv extra)
            · simp [length, extraLength, encodeValues_length, Nat.add_assoc]
              obtain ⟨ty, single⟩ := calculation.single
              simp [single]
            · obtain ⟨ty, single⟩ := calculation.single
              have := holdsValues_single (handle := handle) (cenv ++ extra) outputs
                (by simp [single]) data
              rw [show (cenv ++ extra).length = n + count by simp [length, extraLength]] at this
              exact this
          | stopped reason => simp [ofOutcome, PIR.Process.bind, PIR.Process.interpret]
      · rw [ite_eq_right data] at matched
        simp at matched
    | none =>
      simp only [matched] at accepted
      split_ifs at accepted with total
      simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl, rfl⟩ := accepted
      obtain ⟨values, sequenced⟩ := sequence_some argsHold' argsLength notAbsent
      rw [sequenced]
      obtain ⟨outputs, evaluated⟩ := calculation.total_returns total values
      simp only [evaluated, ofOutcome, PIR.Process.bind, PIR.Process.interpret]
      obtain ⟨ty, single⟩ := calculation.single
      exact cont cenv _ (List.prefix_refl cenv) length
        (holdsValues_free cenv outputs (by simp [single]))

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem walkVocabulary_length (n : Nat) (calculation : Calculation) (arguments : List Slot)
    (instructions rest : List Instruction) (results : List Slot) (n' : Nat)
    (accepted : walkVocabulary context n calculation arguments instructions = .ok (rest, results, n')) :
    results.length = calculation.op.results.length := by
  obtain ⟨ty, single⟩ := calculation.single
  simp only [walkVocabulary] at accepted
  repeat' split at accepted
  all_goals first
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
       obtain ⟨_, rfl, _⟩ := accepted
       simp [single])
    | cases accepted

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- An inlined helper body's walk returns one slot per output. -/
theorem walkHelper_length : ∀ (fuel : Nat) {Γ out : List Ty} (slots : List Slot) (n : Nat)
    (region : Region dialect Γ out) (instructions rest : List Instruction) (outSlots : List Slot) (n' : Nat),
    walkHelper context fuel slots n region instructions = .ok (rest, outSlots, n') → outSlots.length = out.length
  | 0, _, _, _, _, _, _, _, _, _, accepted => by simp [walkHelper] at accepted
  | fuel + 1, _, _, slots, n, region, instructions, rest, outSlots, n', accepted =>
    match region, accepted with
    | .ret values, accepted => by
      simp only [walkHelper, Except.ok.injEq, Prod.mk.injEq] at accepted
      obtain ⟨_, rfl, _⟩ := accepted
      simp [Operands.indices_length]
    | .stop _, accepted => by simp [walkHelper] at accepted
    | .bind _ _, accepted => by simp [walkHelper] at accepted
    | .letOp op args bodies next, accepted => by
      simp only [walkHelper] at accepted
      cases found : Calculation.ofOp? op with
      | none => simp [found] at accepted
      | some calculation =>
        simp only [found] at accepted
        cases stepped : walkVocabulary context n calculation ((Operands.indices args).map (Slot.at_ slots))
            instructions with
        | error error => simp [stepped] at accepted
        | ok triple =>
          obtain ⟨remaining, results, n''⟩ := triple
          simp only [stepped] at accepted
          exact walkHelper_length fuel (results ++ slots) n'' next remaining rest outSlots n' accepted

/-- Soundness of an inlined Math helper body: the exported instructions equal
the body's component evaluation followed by `kO`, whenever the continuations
agree on related results. -/
theorem walkHelper_sound : ∀ (fuel : Nat) {Γ out : List Ty} (slots : List Slot) (n : Nat)
    (region : Region dialect Γ out) (instructions rest : List Instruction) (outSlots : List Slot) (n' : Nat),
    walkHelper context fuel slots n region instructions = .ok (rest, outSlots, n') →
    outSlots.length = out.length ∧
      ∀ (env : Environment (Component (assignment F G)) Γ) (cenv : List (Value F G)),
        Holds handle cenv slots env → cenv.length = n →
        ∀ {A : Type} (kS : List (Value F G) → PIR.Process (Actions F G) A)
          (kO : Values (Component (assignment F G)) out → PIR.Process (Actions F G) A),
          (∀ cenv' outs, cenv <+: cenv' → cenv'.length = n' → HoldsValues handle cenv' outSlots outs →
            specK context handle (helperTable program F G) rest cenv' kS = kO outs) →
          specK context handle (helperTable program F G) instructions cenv kS =
            ((region.component (Evaluation.meaning (.silent _) (plainHelpers program).closed)
              (Evaluation.componentOperation (.silent _) (plainHelpers program)) env).interpret
                CommonAdapter.project).bind kO
  | 0, _, _, _, _, _, _, _, _, _, accepted => by simp [walkHelper] at accepted
  | fuel + 1, _, _, slots, n, region, instructions, rest, outSlots, n', accepted =>
    match region, accepted with
    | .ret values, accepted => by
      simp only [walkHelper, Except.ok.injEq, Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl, rfl⟩ := accepted
      refine ⟨by simp [Operands.indices_length], ?_⟩
      intro env cenv holds length A kS kO cont
      exact cont cenv _ (List.prefix_refl cenv) length (holds.eval values)
    | .stop _, accepted => by simp [walkHelper] at accepted
    | .bind _ _, accepted => by simp [walkHelper] at accepted
    | .letOp op args bodies next, accepted => by
      simp only [walkHelper] at accepted
      cases found : Calculation.ofOp? op with
      | none => simp [found] at accepted
      | some calculation =>
        have same := Calculation.ofOp?_some found
        subst same
        simp only [found] at accepted
        cases stepped : walkVocabulary context n calculation ((Operands.indices args).map (Slot.at_ slots))
            instructions with
        | error error => simp [stepped] at accepted
        | ok triple =>
          obtain ⟨remaining, results, n''⟩ := triple
          simp only [stepped] at accepted
          have resultsLength := walkVocabulary_length context n calculation _ instructions remaining results n''
            stepped
          obtain ⟨outLength, nextSound⟩ :=
            walkHelper_sound fuel (results ++ slots) n'' next remaining rest outSlots n' accepted
          refine ⟨outLength, ?_⟩
          intro env cenv holds length A kS kO cont
          simp only [Region.component]
          rw [PIR.Process.interpret_bind, PIR.Process.bind_assoc]
          apply vocabulary_projects program context handle n calculation _ instructions remaining results n''
            stepped (args.eval env) _ cenv (holds.eval args) (by simp [Operands.indices_length]) length
          intro cenv' values prefix_ length' valuesHold
          exact nextSound (env.prepend values) cenv'
            ((holds.mono prefix_).prepend values resultsLength valuesHold) length' kS kO
            (fun cenv'' outs prefix'' length'' outsHold =>
              cont cenv'' outs (prefix_.trans prefix'') length'' outsHold)

theorem calculate_projects (ctx : ProtocolContext) (n : Nat) (operation : Op)
    (allowed : operation.isCalculation = true) (arguments : List Slot)
    (instructions rest : List Instruction) (results : List Slot) (n' : Nat)
    (accepted : walkOperation program context ctx n (.calculate operation allowed) arguments
      instructions = .ok (rest, results, n')) :
    OperationSound (F := F) (G := G) program context handle ctx n (.calculate operation allowed)
      arguments instructions rest results n' := by
  intro args callbacks cenv argsHold argsLength length A kS kO cont
  simp only [walkOperation, walkCalculation] at accepted
  cases found : Calculation.ofOp? operation with
  | none =>
    simp only [found] at accepted
    rw [originalOperation_calculate]
    cases operation with
    | invoke helper =>
      dsimp only at accepted
      have math : helper.kind = .math := by simpa [Op.isCalculation] using allowed
      cases defined : program.payload.definitions.find? (fun definition => definition.helper == helper) with
      | none => simp [defined] at accepted
      | some definition =>
        simp only [defined] at accepted
        have member := List.mem_of_find?_eq_some defined
        have same : definition.helper = helper := by simpa using List.find?_some defined
        subst same
        have regions : (Op.invoke definition.helper).calculationRegions (Value := assignment F G)
            (I := participantInterface F G) allowed = .nil := by
          generalize (Op.invoke definition.helper).calculationRegions allowed = regions
          cases regions
          rfl
        by_cases allAbsent : arguments.all Slot.isAbsent = true
        · rw [ite_eq_left allAbsent] at accepted
          by_cases preserving : absentPreserving definition.body = true
          · rw [ite_eq_left preserving] at accepted
            simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
            obtain ⟨rfl, rfl, rfl⟩ := accepted
            have argsAbsent := holdsValues_all_absent handle argsHold argsLength allAbsent
            have value : Evaluation.componentOperation (.silent (participantInterface F G))
                (plainHelpers program) (Op.invoke definition.helper) args Values.nil =
                  .done (Values.absent (assignment F G) definition.helper.outputs) := by
              subst argsAbsent
              exact (Evaluation.componentOperation_math _ _ _ math _).trans
                (invoke_absent program definition member preserving)
            rw [regions, value]
            simp only [PIR.Process.interpret, PIR.Process.bind]
            exact cont cenv _ (List.prefix_refl cenv) length (holdsValues_absent cenv _)
          · rw [ite_eq_right preserving] at accepted
            cases accepted
        · rw [ite_eq_right allAbsent] at accepted
          by_cases anyAbsent : arguments.any Slot.isAbsent = true
          · rw [ite_eq_left anyAbsent] at accepted
            cases accepted
          · rw [ite_eq_right anyAbsent] at accepted
            obtain ⟨_, helperSound⟩ :=
              walkHelper_sound (F := F) (G := G) program context handle projectionFuel arguments n
                definition.body instructions rest results n' accepted
            have value : Evaluation.componentOperation (.silent (participantInterface F G))
                (plainHelpers program) (Op.invoke definition.helper) args Values.nil =
                  definition.body.component (Evaluation.meaning (.silent _) (plainHelpers program).closed)
                    (Evaluation.componentOperation (.silent _) (plainHelpers program)) args.get :=
              (Evaluation.componentOperation_math _ _ _ math _).trans
                (plainHelpers_component program definition member args)
            rw [regions, value]
            exact helperSound args.get cenv argsHold.get length kS kO cont
    | fold spec =>
      dsimp only at accepted
      by_cases anyAbsent : arguments.any Slot.isAbsent = true
      · rw [ite_eq_left anyAbsent] at accepted
        simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
        obtain ⟨rfl, rfl, rfl⟩ := accepted
        have sequenced := sequence_none (tys := (Op.fold spec).arguments) argsHold argsLength anyAbsent
        have value : Evaluation.componentOperation (.silent (participantInterface F G)) (plainHelpers program)
            (Op.fold spec) args ((Op.fold spec).calculationRegions allowed) =
              .done (Values.absent (assignment F G) (Op.fold spec).results) := by
          change strictComponent (Evaluation.meaning (.silent (participantInterface F G))
            (plainHelpers program).closed) (Op.fold spec) args _ = _
          simp only [strictComponent, sequenced]
        rw [value]
        simp only [PIR.Process.interpret, PIR.Process.bind]
        exact cont cenv _ (List.prefix_refl cenv) length (holdsValues_absent cenv _)
      · rw [ite_eq_right anyAbsent] at accepted
        cases accepted
    | _ => cases accepted
  | some calculation =>
    have same := Calculation.ofOp?_some found
    subst same
    simp only [found] at accepted
    exact vocabulary_projects program context handle n calculation arguments instructions rest results n' accepted
      args _ cenv argsHold argsLength length kS kO cont

theorem walkOperation_sound (ctx : ProtocolContext) (n : Nat) (op : ProtocolOp) (arguments : List Slot)
    (instructions rest : List Instruction) (results : List Slot) (n' : Nat)
    (accepted : walkOperation program context ctx n op arguments instructions = .ok (rest, results, n')) :
    OperationSound (F := F) (G := G) program context handle ctx n op arguments instructions rest
      results n' := by
  cases op with
  | calculate operation allowed =>
    exact calculate_projects program context handle ctx n operation allowed arguments instructions rest
      results n' accepted
  | localCall helper kind owner site =>
    exact localCall_projects program context handle ctx n helper kind owner site arguments instructions
      rest results n' accepted
  | guard owner site =>
    exact guard_projects program context handle ctx n owner site arguments instructions rest results n'
      accepted
  | exchange ty sender receiver site =>
    exact exchange_projects program context handle ctx n ty sender receiver site arguments instructions
      rest results n' accepted
  | restrict ty roles =>
    exact restrict_projects program context handle ctx n ty roles arguments instructions rest results n'
      accepted
  | draw owner field site =>
    exact draw_projects program context handle ctx n owner field site arguments instructions rest results
      n' accepted
  | statement relation types selectors acceptance =>
    exact statement_projects program context handle ctx n relation types selectors acceptance arguments
      instructions rest results n' accepted
  | mark site =>
    exact mark_projects program context handle ctx n site arguments instructions rest results n' accepted
  | protocolApply => simp [walkOperation] at accepted
  | «repeat» => simp [walkOperation] at accepted

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem walkOperation_length (ctx : ProtocolContext) (n : Nat) (op : ProtocolOp) (arguments : List Slot)
    (instructions rest : List Instruction) (results : List Slot) (n' : Nat)
    (accepted : walkOperation program context ctx n op arguments instructions = .ok (rest, results, n')) :
    results.length = op.results.length := by
  have finish : ∀ {produced : List Slot} {remaining : List Instruction} {count : Nat},
      (Except.ok (remaining, produced, count) : Except String _) = .ok (rest, results, n') →
        produced.length = op.results.length → results.length = op.results.length := by
    intro produced remaining count equal length
    simp only [Except.ok.injEq, Prod.mk.injEq] at equal
    obtain ⟨_, rfl, _⟩ := equal
    exact length
  cases op with
  | calculate operation allowed =>
    simp only [walkOperation, walkCalculation] at accepted
    cases found : Calculation.ofOp? operation with
    | none =>
      simp only [found] at accepted
      cases operation with
      | invoke helper =>
        dsimp only at accepted
        cases defined : program.payload.definitions.find? (fun definition => definition.helper == helper) with
        | none => simp [defined] at accepted
        | some definition =>
          simp only [defined] at accepted
          have same : definition.helper = helper := by simpa using List.find?_some defined
          subst same
          by_cases allAbsent : arguments.all Slot.isAbsent = true
          · rw [ite_eq_left allAbsent] at accepted
            by_cases preserving : absentPreserving definition.body = true
            · rw [ite_eq_left preserving] at accepted
              exact finish accepted (by simp [ProtocolOp.results])
            · rw [ite_eq_right preserving] at accepted
              cases accepted
          · rw [ite_eq_right allAbsent] at accepted
            by_cases anyAbsent : arguments.any Slot.isAbsent = true
            · rw [ite_eq_left anyAbsent] at accepted
              cases accepted
            · rw [ite_eq_right anyAbsent] at accepted
              exact walkHelper_length context projectionFuel arguments n definition.body instructions rest results
                n' accepted
      | fold spec =>
        dsimp only at accepted
        by_cases anyAbsent : arguments.any Slot.isAbsent = true
        · rw [ite_eq_left anyAbsent] at accepted
          exact finish accepted (by simp [ProtocolOp.results])
        · rw [ite_eq_right anyAbsent] at accepted
          cases accepted
      | _ => cases accepted
    | some calculation =>
      have same := Calculation.ofOp?_some found
      subst same
      simp only [found] at accepted
      exact walkVocabulary_length context n calculation arguments instructions rest results n' accepted
  | localCall helper kind owner site =>
    simp only [walkOperation] at accepted
    by_cases owned : ctx.roles owner = context.validator
    · rw [ite_eq_left owned] at accepted
      cases referenced : Slot.references arguments with
      | none => rw [referenced] at accepted; cases accepted
      | some references =>
        rw [referenced] at accepted
        cases called : expectCall context helper references instructions with
        | none => simp only [called] at accepted; cases accepted
        | some found =>
          simp only [called] at accepted
          split_ifs at accepted
          exact finish accepted (by simp [ProtocolOp.results])
    · rw [ite_eq_right owned] at accepted
      exact finish accepted (by simp [ProtocolOp.results])
  | guard owner site =>
    simp only [walkOperation] at accepted
    by_cases owned : ctx.roles owner = context.validator
    · rw [ite_eq_left owned] at accepted
      match arguments, accepted with
      | [.held reference], accepted =>
        simp only at accepted
        cases guarded : expectGuard context reference instructions with
        | none => simp only [guarded] at accepted; cases accepted
        | some found =>
          simp only [guarded] at accepted
          exact finish accepted rfl
      | [], accepted => simp at accepted
      | [.absent], accepted => simp at accepted
      | [.free], accepted => simp at accepted
      | [.service], accepted => simp at accepted
      | _ :: _ :: _, accepted => simp at accepted
    · rw [ite_eq_right owned] at accepted
      exact finish accepted rfl
  | exchange ty sender receiver site =>
    simp only [walkOperation] at accepted
    by_cases same : ctx.roles sender = ctx.roles receiver
    · rw [ite_eq_left same] at accepted; cases accepted
    rw [ite_eq_right same] at accepted
    by_cases nonScalar : scalarType ty = none
    · rw [ite_eq_left nonScalar] at accepted; cases accepted
    rw [ite_eq_right nonScalar] at accepted
    by_cases fromSelf : ctx.roles sender = context.validator
    · rw [ite_eq_left fromSelf] at accepted
      match arguments, accepted with
      | [.held reference], accepted =>
        simp only at accepted
        by_cases toProducer : ctx.roles receiver = context.producer
        · rw [ite_eq_left toProducer] at accepted
          cases delivered : expectDelivery context (qualifyProtocolSite ctx.applicationPrefix site)
              reference instructions with
          | none => simp only [delivered] at accepted; cases accepted
          | some found =>
            simp only [delivered] at accepted
            exact finish accepted rfl
        · rw [ite_eq_right toProducer] at accepted; cases accepted
      | [], accepted => simp at accepted
      | [.absent], accepted => simp at accepted
      | [.free], accepted => simp at accepted
      | [.service], accepted => simp at accepted
      | _ :: _ :: _, accepted => simp at accepted
    · rw [ite_eq_right fromSelf] at accepted
      by_cases toSelf : ctx.roles receiver = context.validator
      · rw [ite_eq_left toSelf] at accepted
        by_cases fromProducer : ctx.roles sender = context.producer
        · rw [ite_eq_left fromProducer] at accepted
          cases received : expectReceive context (qualifyProtocolSite ctx.applicationPrefix site) ty
              instructions with
          | none => simp only [received] at accepted; cases accepted
          | some found =>
            simp only [received] at accepted
            exact finish accepted rfl
        · rw [ite_eq_right fromProducer] at accepted; cases accepted
      · rw [ite_eq_right toSelf] at accepted
        exact finish accepted rfl
  | restrict ty roles =>
    simp only [walkOperation] at accepted
    exact finish accepted rfl
  | draw owner field site =>
    simp only [walkOperation] at accepted
    by_cases owned : ctx.roles owner = context.validator
    · rw [ite_eq_left owned] at accepted
      match arguments, accepted with
      | [.service], accepted =>
        simp only at accepted
        cases challenged : expectChallenge context (qualifyProtocolSite ctx.applicationPrefix site) field
            instructions with
        | none => simp only [challenged] at accepted; cases accepted
        | some found =>
          simp only [challenged] at accepted
          exact finish accepted rfl
      | [], accepted => simp at accepted
      | [.absent], accepted => simp at accepted
      | [.free], accepted => simp at accepted
      | [.held _], accepted => simp at accepted
      | _ :: _ :: _, accepted => simp at accepted
    · rw [ite_eq_right owned] at accepted
      exact finish accepted rfl
  | statement relation types selectors acceptance =>
    simp only [walkOperation] at accepted
    exact finish accepted rfl
  | mark site =>
    simp only [walkOperation] at accepted
    exact finish accepted rfl
  | protocolApply => simp [walkOperation] at accepted
  | «repeat» => simp [walkOperation] at accepted

end Operations


section Carried
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Masking keeps the related components the role has. -/
theorem HoldsValues.mask {handle : Nat} {cenv : List (Value F G)} (self : Nat) :
    ∀ (scopes : List (List Nat)) {slots : List Slot} {tys : List Ty}
      {values : Values (Component (assignment F G)) tys},
      HoldsValues handle cenv slots values → slots.length = tys.length →
      HoldsValues handle cenv (Slot.mask self scopes slots) (maskValues self scopes values)
  | _, [], [], .nil, _, _ => trivial
  | scopes, slot :: rest, _ :: _, .cons value others, holds, length => by
      obtain ⟨head, tail⟩ := holds
      refine ⟨?_, HoldsValues.mask self scopes.tail tail (by simpa using length)⟩
      simp only [Slot.mask, List.headD_cons, Participant.restrict]
      split
      · simpa using head
      · rfl
  | _, [], _ :: _, _, _, length => by cases length
  | _, _ :: _, [], _, _, length => by cases length

theorem Slot.mask_length (self : Nat) : ∀ (scopes : List (List Nat)) (slots : List Slot),
    (Slot.mask self scopes slots).length = slots.length
  | _, [] => rfl
  | scopes, _ :: rest => by simp [Slot.mask, Slot.mask_length self scopes.tail rest]

theorem carriedSlots_length (self : Nat) : ∀ (scopes : List (List Nat)) (base count : Nat),
    (carriedSlots self scopes base count).length = count
  | _, _, 0 => rfl
  | scopes, base, count + 1 => by
      simp only [carriedSlots]
      split <;> simp [carriedSlots_length]

/-- Masking carried slots changes nothing: the components the role lacks are
already absent. -/
theorem mask_carriedSlots (self : Nat) : ∀ (scopes : List (List Nat)) (base count : Nat),
    Slot.mask self scopes (carriedSlots self scopes base count) = carriedSlots self scopes base count
  | _, _, 0 => rfl
  | scopes, base, count + 1 => by
      by_cases visible : (scopes.headD []).contains self = true
      · simp only [carriedSlots, visible, ite_true, Slot.mask, mask_carriedSlots]
      · have hidden : (scopes.headD []).contains self = false := by simpa using visible
        simp only [carriedSlots, hidden, Bool.false_eq_true, ↓reduceIte, Slot.mask, mask_carriedSlots]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Related tuples concatenate. -/
theorem HoldsValues.append {handle : Nat} {cenv : List (Value F G)} :
    ∀ {first second : List Slot} {tys tys' : List Ty} {left : Values (Component (assignment F G)) tys}
      {right : Values (Component (assignment F G)) tys'},
      HoldsValues handle cenv first left → first.length = tys.length → HoldsValues handle cenv second right →
      HoldsValues handle cenv (first ++ second) (left.append right)
  | [], _, [], _, .nil, _, _, _, holds => holds
  | _ :: _, _, _ :: _, _, .cons _ _, _, holds, length, other => by
      obtain ⟨head, tail⟩ := holds
      exact ⟨head, HoldsValues.append tail (by simpa using length) other⟩
  | [], _, _ :: _, _, _, _, _, length, _ => by cases length
  | _ :: _, _, [], _, _, _, _, length, _ => by cases length

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- A related tuple splits into related parts. -/
theorem HoldsValues.split {handle : Nat} {cenv : List (Value F G)} :
    ∀ (added : List Ty) {tys : List Ty} {slots : List Slot}
      {values : Values (Component (assignment F G)) (added ++ tys)},
      HoldsValues handle cenv slots values →
      HoldsValues handle cenv (slots.take added.length) (Values.split added values).1 ∧
        HoldsValues handle cenv (slots.drop added.length) (Values.split added values).2
  | [], _, _, _, holds => ⟨trivial, holds⟩
  | _ :: added, _, slots, .cons value values, holds => by
      obtain ⟨head, tail⟩ := holds
      obtain ⟨first, second⟩ := HoldsValues.split added tail
      cases slots with
      | nil =>
        exact ⟨⟨head, (by simpa using first : HoldsValues handle cenv [] (Values.split added values).1)⟩,
          (by simpa using second : HoldsValues handle cenv [] (Values.split added values).2)⟩
      | cons slot rest => exact ⟨⟨head, first⟩, second⟩

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Carried slots read the same values after a prefix of the environment. -/
theorem HoldsValues.shift {handle : Nat} (self : Nat) (front : List (Value F G)) :
    ∀ (scopes : List (List Nat)) (base : Nat) {tys : List Ty}
      {values : Values (Component (assignment F G)) tys} {carried : List (Value F G)},
      HoldsValues handle carried (carriedSlots self scopes base tys.length) values →
      HoldsValues handle (front ++ carried) (carriedSlots self scopes (front.length + base) tys.length) values
  | _, _, [], .nil, _, _ => trivial
  | scopes, base, _ :: _, .cons value rest, carried, holds => by
      by_cases visible : (scopes.headD []).contains self = true
      · simp only [List.length_cons, carriedSlots, visible, ite_true] at holds ⊢
        obtain ⟨head, tail⟩ := holds
        refine ⟨?_, ?_⟩
        · obtain ⟨x, valueEq, decoded⟩ := head
          refine ⟨x, valueEq, ?_⟩
          simpa [List.getElem?_append_right] using decoded
        · have shifted := HoldsValues.shift self front scopes.tail (base + 1) tail
          simpa [Nat.add_assoc] using shifted
      · simp only [List.length_cons, carriedSlots, visible] at holds ⊢
        obtain ⟨head, tail⟩ := holds
        exact ⟨head, HoldsValues.shift self front scopes.tail base tail⟩

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Values read at references that hold the role's components are related to
the masked components by carried slots. -/
theorem carried_holds {handle : Nat} {cenv cenv' read_ : List (Value F G)} (self : Nat)
    (prefix_ : cenv <+: cenv') (list : List Nat) (found : read cenv' list = some read_) :
    ∀ (scopes : List (List Nat)) (base : Nat) {slots : List Slot} {tys : List Ty}
      {values : Values (Component (assignment F G)) tys} {references : List Nat},
      outputReferences self scopes slots = some references → HoldsValues handle cenv slots values →
      slots.length = tys.length → (list.drop base).take references.length = references →
      HoldsValues handle read_ (carriedSlots self scopes base tys.length) (maskValues self scopes values)
  | _, _, [], [], .nil, _, _, _, _, _ => trivial
  | scopes, base, slot :: rest, _ :: _, .cons value others, references, referenced, holds, length,
      positioned => by
      obtain ⟨head, tail⟩ := holds
      simp only [outputReferences] at referenced
      by_cases visible : (scopes.headD []).contains self = true
      · simp only [visible, ↓reduceIte] at referenced
        cases slot with
        | held reference =>
          cases restFound : outputReferences self scopes.tail rest with
          | none => simp [restFound] at referenced
          | some restReferences =>
            simp only [restFound, Option.map_some, Option.some.injEq] at referenced
            subst referenced
            cases dropped : list.drop base with
            | nil => simp [dropped] at positioned
            | cons first others =>
            rw [dropped] at positioned
            simp only [List.length_cons, List.take_succ_cons, List.cons.injEq] at positioned
            obtain ⟨rfl, restEq⟩ := positioned
            have atBase : list[base]? = some first := by
              have heads := congrArg List.head? dropped
              simpa [List.head?_drop] using heads
            have restPositioned : (list.drop (base + 1)).take restReferences.length = restReferences := by
              rw [← List.tail_drop, dropped]
              exact restEq
            simp only [List.length_cons, carriedSlots, visible, ite_true, maskValues, Participant.restrict]
            refine ⟨?_, carried_holds self prefix_ list found scopes.tail (base + 1) restFound tail
              (by simpa using length) restPositioned⟩
            obtain ⟨x, valueEq, decoded⟩ := head
            refine ⟨x, valueEq, ?_⟩
            cases at_ : cenv[first]? with
            | none => simp [at_] at decoded
            | some stored =>
              have stored' : cenv'[first]? = some stored := getElem?_of_prefix prefix_ at_
              rw [read_getElem? found base, atBase]
              simpa [stored', at_] using decoded
        | absent => simp at referenced
        | free => simp at referenced
        | service => simp at referenced
      · simp only [visible] at referenced
        simp only [List.length_cons, carriedSlots, visible, maskValues, Participant.restrict]
        exact ⟨rfl, carried_holds self prefix_ list found scopes.tail base referenced tail
          (by simpa using length) positioned⟩
  | _, _, [], _ :: _, _, _, _, _, length, _ => by cases length
  | _, _, _ :: _, [], _, _, _, _, length, _ => by cases length

end Carried


section Walk
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (program : Structured.Program) (context : Context) (handle : Nat)

/-- The original program's participant meaning at the validator, in the plain view. -/
abbrev plainMeaning (ctx : ProtocolContext) : RegionMeaning protocolDialect (participantInterface F G) :=
  participantMeaningWith (.silent _) (participantActions F G) (plainHelpers program) context.validator
    (program.payload.plainProtocolTable F G) ctx

/-- What a walk's soundness states for every region it accepts: one slot per
output, and the exported program from `instructions` equals the original region
followed by `kO` whenever the exported continuation from the remaining
instructions agrees with `kO` on related results. -/
def WalkSound (recurse : Walker) : Prop :=
  ∀ {Γ out : List Ty} (ctx : ProtocolContext) (slots : List Slot) (n : Nat)
    (region : Region protocolDialect Γ out) (instructions rest : List Instruction) (outSlots : List Slot)
    (n' : Nat), recurse ctx slots n region instructions = .ok (rest, outSlots, n') →
    outSlots.length = out.length ∧
      ∀ (env : Environment (Component (assignment F G)) Γ) (cenv : List (Value F G)),
        Holds handle cenv slots env → cenv.length = n →
        ∀ {A : Type} (kS : List (Value F G) → PIR.Process (Actions F G) A)
          (kO : Values (Component (assignment F G)) out → PIR.Process (Actions F G) A),
          (∀ cenv' outs, cenv <+: cenv' → cenv'.length = n' → HoldsValues handle cenv' outSlots outs →
            specK context handle (helperTable program F G) rest cenv' kS = kO outs) →
          specK context handle (helperTable program F G) instructions cenv kS =
            ((region.denote (plainMeaning program context ctx) env).interpret CommonAdapter.project).bind kO

/-- A loop's iterations implement the repeat's fold when each iteration's body
implements one repeat step, with the carried values related to the masked state
by carried slots. -/
theorem iterate_projects {B : Type} (self : Nat) (scopes : List (List Nat)) (spec : RepeatSpec)
    (ctx : ProtocolContext) (env : List (Value F G)) (yielded : List Nat) (loopBody : List Instruction)
    (count : Nat) (captures : Values (Component (assignment F G)) spec.captures)
    (callback : RegionFunction (Component (assignment F G)) (participantInterface F G)
      (.index :: (spec.state ++ spec.captures), spec.state))
    (stepSound : ∀ (index : Nat) (carried : List (Value F G))
      (state : Values (Component (assignment F G)) spec.state),
      carried.length = count → HoldsValues handle carried (carriedSlots self scopes 0 spec.state.length) state →
      ∀ (K : List (Value F G) → PIR.Process (Actions F G) B)
        (K' : Values (Component (assignment F G)) spec.state → PIR.Process (Actions F G) B),
        (∀ carried' state', carried'.length = count →
          HoldsValues handle carried' (carriedSlots self scopes 0 spec.state.length) state' →
            K carried' = K' state') →
        specK context handle (helperTable program F G) loopBody (env ++ .index index :: carried)
            (fun final => match read final yielded with
              | some carried' => K carried'
              | none => .halt .refused) =
          ((Repeat.step spec ctx self captures callback state index).interpret CommonAdapter.project).bind K') :
    ∀ (indices : List Nat) (carried : List (Value F G)) (state : Values (Component (assignment F G)) spec.state),
      carried.length = count → HoldsValues handle carried (carriedSlots self scopes 0 spec.state.length) state →
      ∀ (K : List (Value F G) → PIR.Process (Actions F G) B)
        (K' : Values (Component (assignment F G)) spec.state → PIR.Process (Actions F G) B),
        (∀ carried' state', carried'.length = count →
          HoldsValues handle carried' (carriedSlots self scopes 0 spec.state.length) state' →
            K carried' = K' state') →
        iterate (fun start continuation => specK context handle (helperTable program F G) loopBody start
            continuation) env yielded indices carried K =
          ((Finite.fold (Repeat.step spec ctx self captures callback) indices state).interpret
            CommonAdapter.project).bind K'
  | [], carried, state, length, holds, K, K', agree => by
      simp only [iterate, Finite.fold, PIR.Process.interpret, PIR.Process.bind]
      exact agree carried state length holds
  | index :: rest, carried, state, length, holds, K, K', agree => by
      simp only [iterate, Finite.fold]
      rw [PIR.Process.interpret_bind, PIR.Process.bind_assoc]
      exact stepSound index carried state length holds _ _ (fun carried' state' length' holds' =>
        iterate_projects self scopes spec ctx env yielded loopBody count captures callback stepSound rest
          carried' state' length' holds' K K' agree)

/-- Soundness of one walk step, given the soundness of the walk it recurses
with: applications and repeats, and every other operation through
`walkOperation_sound`. -/
theorem walkStep_sound (recurse : Walker) (sound : WalkSound (F := F) (G := G) program context handle recurse)
    (ctx : ProtocolContext) (n : Nat) (op : ProtocolOp) (arguments : List Slot)
    (bodies : Regions protocolDialect op.regions) (instructions rest : List Instruction)
    (results : List Slot) (n' : Nat)
    (accepted : walkStep program context recurse ctx n op arguments bodies instructions =
      .ok (rest, results, n')) :
    results.length = op.results.length ∧
      ∀ (args : Values (Component (assignment F G)) op.arguments) (cenv : List (Value F G)),
        HoldsValues handle cenv arguments args → arguments.length = op.arguments.length → cenv.length = n →
        ∀ {A : Type} (kS : List (Value F G) → PIR.Process (Actions F G) A)
          (kO : Values (Component (assignment F G)) op.results → PIR.Process (Actions F G) A),
          (∀ cenv' values, cenv <+: cenv' → cenv'.length = n' → HoldsValues handle cenv' results values →
            specK context handle (helperTable program F G) rest cenv' kS = kO values) →
          specK context handle (helperTable program F G) instructions cenv kS =
            (((plainMeaning program context ctx).operation op args
              (bodies.denote (plainMeaning program context ctx))).interpret CommonAdapter.project).bind kO := by
  have generic : walkOperation program context ctx n op arguments instructions = .ok (rest, results, n') →
      results.length = op.results.length ∧
      ∀ (args : Values (Component (assignment F G)) op.arguments) (cenv : List (Value F G)),
        HoldsValues handle cenv arguments args → arguments.length = op.arguments.length → cenv.length = n →
        ∀ {A : Type} (kS : List (Value F G) → PIR.Process (Actions F G) A)
          (kO : Values (Component (assignment F G)) op.results → PIR.Process (Actions F G) A),
          (∀ cenv' values, cenv <+: cenv' → cenv'.length = n' → HoldsValues handle cenv' results values →
            specK context handle (helperTable program F G) rest cenv' kS = kO values) →
          specK context handle (helperTable program F G) instructions cenv kS =
            (((plainMeaning program context ctx).operation op args
              (bodies.denote (plainMeaning program context ctx))).interpret CommonAdapter.project).bind kO :=
    fun stepped => ⟨walkOperation_length program context ctx n op arguments instructions rest results n' stepped,
      fun args cenv argsHold argsLength length _ kS kO cont =>
        walkOperation_sound program context handle ctx n op arguments instructions rest results n' stepped args
          _ cenv argsHold argsLength length kS kO cont⟩
  cases op with
  | protocolApply signature roles site =>
    simp only [walkStep] at accepted
    by_cases contains : (ctx.enter site roles).contains signature context.validator = true
    · simp only [contains, ↓reduceIte] at accepted
      cases found : program.payload.protocols.find? (fun definition => definition.signature == signature) with
      | none => simp [found] at accepted
      | some definition =>
        simp only [found] at accepted
        cases recursed : recurse (ctx.enter site roles)
            (Slot.mask context.validator ((ctx.enter site roles).mapScopes definition.inputScopes) arguments) n
            definition.body instructions with
        | error error => simp [recursed] at accepted
        | ok triple =>
          obtain ⟨remaining, outputs, n''⟩ := triple
          simp only [recursed, Except.ok.injEq, Prod.mk.injEq] at accepted
          obtain ⟨rfl, rfl, rfl⟩ := accepted
          have member := List.mem_of_find?_eq_some found
          have same : definition.signature = signature := by simpa using List.find?_some found
          subst same
          obtain ⟨outputsLength, bodySound⟩ := sound _ _ _ definition.body _ _ _ _ recursed
          refine ⟨by rw [Slot.mask_length, outputsLength]; rfl, ?_⟩
          intro args cenv argsHold argsLength length A kS kO cont
          have invoked := protocol_invoke_body (.silent _) (participantActions F G) (plainHelpers program)
            program.payload.protocols program.payload.protocolsLinked definition member (ctx.enter site roles)
            context.validator args
          change specK context handle (helperTable program F G) instructions cenv kS =
            ((if (ctx.enter site roles).contains definition.signature context.validator then
                invokeProtocol (program.payload.plainProtocolTable F G) definition.signature
                  (ctx.enter site roles) context.validator args
              else .done (Values.absent (assignment F G) definition.signature.outputs)).interpret
                CommonAdapter.project).bind kO
          rw [ite_eq_left contains, show invokeProtocol (program.payload.plainProtocolTable F G) definition.signature
            (ctx.enter site roles) context.validator args = _ from invoked]
          simp only [CheckedProtocol.denoteWith, PIR.Process.interpret_bind]
          refine (bodySound _ cenv (HoldsValues.mask context.validator _ argsHold
            (by simpa using argsLength)).get length kS _ ?_).trans (PIR.Process.bind_assoc _ _ _).symm
          intro cenv' outs prefix_ length' outsHold
          simp only [PIR.Process.interpret, PIR.Process.bind]
          exact cont cenv' _ prefix_ length' (HoldsValues.mask context.validator _ outsHold outputsLength)
    · simp only [contains, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl, rfl⟩ := accepted
      refine ⟨by simp [ProtocolOp.results], ?_⟩
      intro args cenv argsHold argsLength length A kS kO cont
      change specK context handle (helperTable program F G) instructions cenv kS =
        ((if (ctx.enter site roles).contains signature context.validator then
            invokeProtocol (program.payload.plainProtocolTable F G) signature (ctx.enter site roles)
              context.validator args
          else .done (Values.absent (assignment F G) signature.outputs)).interpret CommonAdapter.project).bind kO
      rw [ite_eq_right contains]
      simp only [PIR.Process.interpret, PIR.Process.bind]
      exact cont cenv _ (List.prefix_refl cenv) length (holdsValues_absent cenv _)
  | «repeat» spec site =>
    match bodies with
    | .cons body .nil =>
    simp only [walkStep] at accepted
    by_cases participates : (spec.roles.map ctx.roles).contains context.validator = true
    · simp only [participates, ↓reduceIte] at accepted
      split at accepted
      · rename_i _ _ _ site' maximum yielded count initial sorts loopBody rest' skipped countReference
          references nexted countSlot referenced
        split_ifs at accepted with conditions
        obtain ⟨siteEq, maximumEq, countEq, initialEq, initialBound, yieldedLength⟩ := conditions
        split at accepted
        · rename_i bodyRest outputs bodyEnd recursed
          split at accepted
          · rename_i _ _ bodySkipped yieldedReferences bodySkip yieldedFound
            split_ifs at accepted with yieldConditions
            obtain ⟨yieldedEq, yieldedBound⟩ := yieldConditions
            simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
            obtain ⟨rfl, rfl, rfl⟩ := accepted
            subst maximumEq countEq
            refine ⟨by simp [carriedSlots_length, ProtocolOp.results], ?_⟩
            intro args cenv argsHold argsLength length A kS kO cont
            cases arguments with
            | nil => simp at countSlot
            | cons countSlot' argumentsTail =>
            simp only [List.headD_cons] at countSlot
            subst countSlot
            simp only [List.drop_succ_cons, List.drop_zero] at referenced recursed
            match args, argsHold with
            | .cons countValue values, ⟨countHolds, valuesHold⟩ =>
            obtain ⟨bound, countSome, countDecoded⟩ := countHolds
            subst countSome
            have tailHold : HoldsValues handle cenv argumentsTail values := valuesHold
            obtain ⟨stateHold, captureHold⟩ := HoldsValues.split spec.state tailHold
            have tailLength : argumentsTail.length = spec.state.length + spec.captures.length := by
              simpa [ProtocolOp.arguments] using argsLength
            have stateLength : (argumentsTail.take spec.state.length).length = spec.state.length := by
              simp [tailLength]
            obtain ⟨outputsLength, bodySound⟩ := sound ctx _ _ body loopBody bodyRest outputs bodyEnd recursed
            obtain ⟨extra, extraLength, nextEq⟩ :=
              next_spec context handle (helperTable program F G) nexted cenv
            rw [nextEq]
            have envLength : (cenv ++ extra).length = n + skipped := by simp [length, extraLength]
            have countAt : indexAt (cenv ++ extra) count = some bound := by
              cases at_ : cenv[count]? with
              | none => simp [at_] at countDecoded
              | some stored =>
                have stored' : (cenv ++ extra)[count]? = some stored :=
                  getElem?_of_prefix (List.prefix_append cenv extra) at_
                simp only [at_, Option.bind_some] at countDecoded
                cases stored <;> simp [Value.decode] at countDecoded
                subst countDecoded
                simp [indexAt, stored']
            obtain ⟨carried, readInitial⟩ := read_some (env := cenv ++ extra) (references := initial)
              (fun reference member => by
                have bounded := List.all_eq_true.mp initialBound reference member
                simp only [decide_eq_true_eq] at bounded
                rw [envLength]
                exact bounded)
            have initialHolds := carried_holds context.validator (List.prefix_append cenv extra) initial
              readInitial (ctx.mapScopes spec.stateScopes) 0 referenced stateHold stateLength
              (by simpa using initialEq)
            have stepSound : ∀ (index : Nat) (carried : List (Value F G))
                (state : Values (Component (assignment F G)) spec.state),
                carried.length = initial.length →
                HoldsValues handle carried
                  (carriedSlots context.validator (ctx.mapScopes spec.stateScopes) 0 spec.state.length) state →
                ∀ (K : List (Value F G) → PIR.Process (Actions F G) A)
                  (K' : Values (Component (assignment F G)) spec.state → PIR.Process (Actions F G) A),
                  (∀ carried' state', carried'.length = initial.length →
                    HoldsValues handle carried'
                      (carriedSlots context.validator (ctx.mapScopes spec.stateScopes) 0 spec.state.length) state' →
                      K carried' = K' state') →
                  specK context handle (helperTable program F G) loopBody
                      ((cenv ++ extra) ++ .index index :: carried)
                      (fun final => match read final yielded with
                        | some carried' => K carried'
                        | none => .halt .refused) =
                    ((Repeat.step spec ctx context.validator (Values.split spec.state values).2
                      (fun vs => body.denote (plainMeaning program context ctx) vs.get) state index).interpret
                        CommonAdapter.project).bind K' := by
              intro index carried state carriedLength carriedHolds K K' agree
              simp only [Repeat.step, PIR.Process.interpret_bind]
              have masked : HoldsValues handle ((cenv ++ extra) ++ .index index :: carried)
                  (carriedSlots context.validator (ctx.mapScopes spec.stateScopes) (n + skipped + 1)
                    spec.state.length)
                  (maskValues context.validator (ctx.mapScopes spec.stateScopes) state) := by
                have shifted := HoldsValues.shift context.validator ((cenv ++ extra) ++ [.index index])
                  (ctx.mapScopes spec.stateScopes) 0 carriedHolds
                have maskedShifted := HoldsValues.mask context.validator (ctx.mapScopes spec.stateScopes) shifted
                  (carriedSlots_length _ _ _ _)
                rw [mask_carriedSlots] at maskedShifted
                simpa [length, extraLength, Nat.add_assoc] using maskedShifted
              have bodyHolds : HoldsValues handle ((cenv ++ extra) ++ .index index :: carried)
                  (.held (n + skipped) :: (carriedSlots context.validator (ctx.mapScopes spec.stateScopes)
                    (n + skipped + 1) spec.state.length ++ argumentsTail.drop spec.state.length))
                  (show Values (Component (assignment F G)) (.index :: (spec.state ++ spec.captures)) from
                    .cons (some index) ((maskValues context.validator (ctx.mapScopes spec.stateScopes)
                      state).append (Values.split spec.state values).2)) := by
                refine ⟨⟨index, rfl, ?_⟩, ?_⟩
                · rw [List.getElem?_append_right (by omega)]
                  simp [envLength, Value.decode]
                · exact HoldsValues.append masked (carriedSlots_length _ _ _ _)
                    (captureHold.mono ((List.prefix_append cenv extra).trans (List.prefix_append _ _)))
              refine (bodySound _ ((cenv ++ extra) ++ .index index :: carried) bodyHolds.get
                (by simp [carriedLength]; omega) _ _ ?_).trans (PIR.Process.bind_assoc _ _ _).symm
              intro cenv'' outs prefix'' length'' outsHold
              obtain ⟨extra', extraLength', skipEq⟩ :=
                skip_spec context handle (helperTable program F G) bodyRest cenv''
              rw [skipEq, bodySkip]
              simp only [specK]
              obtain ⟨carried', readYielded⟩ := read_some (env := cenv'' ++ extra') (references := yielded)
                (fun reference member => by
                  have bounded := List.all_eq_true.mp yieldedBound reference member
                  simp only [decide_eq_true_eq] at bounded
                  simp only [bodySkip] at extraLength'
                  simp [length'', extraLength']
                  omega)
              simp only [readYielded, PIR.Process.interpret, PIR.Process.bind]
              exact agree carried' _ (by rw [read_length readYielded, yieldedLength])
                (carried_holds context.validator (List.prefix_append cenv'' extra') yielded readYielded
                  (ctx.mapScopes spec.stateScopes) 0 yieldedFound outsHold outputsLength (by simpa using yieldedEq))
            change specK context handle (helperTable program F G) (_ :: rest') (cenv ++ extra) kS =
              ((denoteRepeat spec ctx context.validator (some bound) (Values.split spec.state values).1
                (Values.split spec.state values).2
                (fun vs => body.denote (plainMeaning program context ctx) vs.get)).interpret
                  CommonAdapter.project).bind kO
            simp only [denoteRepeat, participates, ↓reduceIte, specK, specStep, countAt, readInitial]
            by_cases bounded : bound ≤ spec.maximum
            · simp only [bounded, ↓reduceIte]
              exact iterate_projects program context handle context.validator (ctx.mapScopes spec.stateScopes) spec
                ctx (cenv ++ extra) yielded loopBody initial.length (Values.split spec.state values).2
                (fun vs => body.denote (plainMeaning program context ctx) vs.get) stepSound (List.range bound) carried _
                (read_length readInitial) initialHolds _ _ (fun carried' state' carriedLength' holds' => by
                  have shifted := HoldsValues.shift context.validator (cenv ++ extra)
                    (ctx.mapScopes spec.stateScopes) 0 holds'
                  rw [envLength] at shifted
                  exact cont ((cenv ++ extra) ++ carried') state'
                    ((List.prefix_append cenv extra).trans (List.prefix_append _ _))
                    (by simp [length, extraLength, carriedLength']; omega) shifted)
            · simp only [bounded, ↓reduceIte, PIR.Process.interpret, PIR.Process.bind]
          · cases accepted
          · cases accepted
        · cases accepted
      · cases accepted
    · simp only [participates, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl, rfl⟩ := accepted
      refine ⟨by simp [ProtocolOp.results], ?_⟩
      intro args cenv argsHold argsLength length A kS kO cont
      match args with
      | .cons countValue values =>
      change specK context handle (helperTable program F G) instructions cenv kS =
        ((denoteRepeat spec ctx context.validator countValue (Values.split spec.state values).1
          (Values.split spec.state values).2
          (fun vs => body.denote (plainMeaning program context ctx) vs.get)).interpret
            CommonAdapter.project).bind kO
      simp only [denoteRepeat, participates, Bool.false_eq_true, ↓reduceIte, PIR.Process.interpret, PIR.Process.bind]
      exact cont cenv _ (List.prefix_refl cenv) length (holdsValues_absent cenv _)
  | calculate => exact generic accepted
  | localCall => exact generic accepted
  | guard => exact generic accepted
  | exchange => exact generic accepted
  | restrict => exact generic accepted
  | draw => exact generic accepted
  | statement => exact generic accepted
  | mark => exact generic accepted

/-- Soundness of the projection walk for one region. -/
theorem walk_sound : ∀ (fuel : Nat), WalkSound (F := F) (G := G) program context handle (walk program context fuel)
  | 0 => by
    intro ctx slots n region instructions rest outSlots n' accepted
    simp [walk] at accepted
  | fuel + 1 => by
    intro ctx slots n region instructions rest outSlots n' accepted
    match region, accepted with
    | .ret values, accepted =>
      simp only [walk, Except.ok.injEq, Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl, rfl⟩ := accepted
      refine ⟨by simp [Operands.indices_length], ?_⟩
      intro env cenv holds length A kS kO cont
      exact cont cenv _ (List.prefix_refl cenv) length (holds.eval values)
    | .stop _, accepted => simp [walk] at accepted
    | .bind _ _, accepted => simp [walk] at accepted
    | .letOp op args bodies next, accepted =>
      simp only [walk] at accepted
      cases stepped : walkStep program context (walk program context fuel) ctx n op
          ((Operands.indices args).map (Slot.at_ slots)) bodies instructions with
      | error error => simp [stepped] at accepted
      | ok triple =>
        obtain ⟨remaining, results, n''⟩ := triple
        simp only [stepped] at accepted
        obtain ⟨resultsLength, stepSound⟩ := walkStep_sound program context handle (walk program context fuel)
          (walk_sound fuel) ctx n op _ bodies instructions remaining results n'' stepped
        obtain ⟨outLength, nextSound⟩ := walk_sound fuel ctx (results ++ slots) n'' next remaining rest outSlots
          n' accepted
        refine ⟨outLength, ?_⟩
        intro env cenv holds length A kS kO cont
        simp only [Region.denote]
        rw [PIR.Process.interpret_bind, PIR.Process.bind_assoc]
        apply stepSound (args.eval env) cenv (holds.eval args) (by simp [Operands.indices_length]) length
        intro cenv' values prefix_ length' valuesHold
        exact nextSound (env.prepend values) cenv' ((holds.mono prefix_).prepend values resultsLength valuesHold)
          length' kS kO (fun cenv'' outs prefix'' length'' outsHold =>
            cont cenv'' outs (prefix_.trans prefix'') length'' outsHold)

end Walk


section Continuation
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (context : Context) (handle : Nat) (table : Structured.Meanings F G)

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem iterate_bind {I : PIR.Signature} {A B : Type} (f : A → PIR.Process I B)
    (body : ∀ {C : Type}, List (Value F G) → (List (Value F G) → PIR.Process I C) → PIR.Process I C)
    (bodyBind : ∀ start (next : List (Value F G) → PIR.Process I A),
      (body start next).bind f = body start fun final => (next final).bind f)
    (env : List (Value F G)) (yielded : List Nat) :
    ∀ (items : List Nat) (carried : List (Value F G)) (next : List (Value F G) → PIR.Process I A),
      (iterate (fun start continuation => body start continuation) env yielded items carried next).bind f =
        iterate (fun start continuation => body start continuation) env yielded items carried
          fun final => (next final).bind f
  | [], carried, next => rfl
  | index :: rest, carried, next => by
      simp only [iterate]
      rw [bodyBind]
      congr 1
      funext final
      split
      · exact iterate_bind f body bodyBind env yielded rest _ next
      · rfl

mutual
/-- A final bind moves into the interactive reading's continuation. -/
theorem specK_bind {A B : Type} (f : A → PIR.Process (Actions F G) B) :
    ∀ (instructions : List Instruction) (env : List (Value F G))
      (next : List (Value F G) → PIR.Process (Actions F G) A),
      (specK context handle table instructions env next).bind f =
        specK context handle table instructions env fun final => (next final).bind f
  | [], env, next => rfl
  | instruction :: rest, env, next => by
      simp only [specK]
      rw [specStep_bind f instruction env]
      congr 1
      funext env'
      exact specK_bind f rest env' next

theorem specStep_bind {A B : Type} (f : A → PIR.Process (Actions F G) B) :
    ∀ (instruction : Instruction) (env : List (Value F G))
      (next : List (Value F G) → PIR.Process (Actions F G) A),
      (specStep context handle table instruction env next).bind f =
        specStep context handle table instruction env fun final => (next final).bind f
  | ⟨operation, operands, results, body⟩, env, next => by
      cases operation with
      | loop site maximum yielded =>
        match operands with
        | [] => rfl
        | count :: initial =>
          simp only [specStep]
          split
          · split
            · exact iterate_bind f (fun start continuation => specK context handle table body start continuation)
                (fun start next' => specK_bind f body start next') env yielded _ _ _
            · rfl
          · rfl
      | receive site schema peer ty =>
        cases operands with
        | nil =>
          simp only [specStep]
          split
          · simp only [PIR.Process.bind]
            congr 1
            funext value
            split <;> rfl
          · rfl
        | cons => rfl
      | observe suite template =>
        match operands with
        | [state, value, coordinates] =>
          simp only [specStep]
          split
          · split
            · cases ‹Payload F G› <;> rfl
            · rfl
          · rfl
        | [] => rfl
        | [_] => rfl
        | [_, _] => rfl
        | _ :: _ :: _ :: _ :: _ => rfl
      | challenge suite field template =>
        match operands with
        | [state, coordinates] =>
          simp only [specStep]
          split
          · rfl
          · rfl
        | [] => rfl
        | [_] => rfl
        | _ :: _ :: _ :: _ => rfl
      | calculate calculation =>
        simp only [specStep]
        split
        · split <;> rfl
        · rfl
      | call name =>
        simp only [specStep]
        split
        · split
          · split <;> rfl
          · rfl
        · rfl
      | guard site =>
        match operands with
        | [condition] =>
          simp only [specStep]
          split <;> rfl
        | [] => rfl
        | _ :: _ :: _ => rfl
      | indicesEmpty => cases operands <;> rfl
      | indicesAppend =>
        match operands with
        | [_, _] => rfl
        | [] => rfl
        | [_] => rfl
        | _ :: _ :: _ :: _ => rfl
      | send => rfl
      | unsupported => rfl
end

end Continuation


section RootSoundness
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (program : Structured.Program) (context : Context)

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem Value.decode_some {ty : Ty} {v : Value F G} {x : assignment F G ty}
    (decoded : Value.decode ty v = some x) : v = Value.encode ty x := by
  cases ty <;> cases v <;> simp [Value.decode] at decoded
  all_goals
    first
    | (rename_i payload; cases payload <;> simp at decoded <;> (obtain ⟨rfl, rfl⟩ := decoded; rfl))
    | (subst decoded; rfl)
    | (obtain ⟨rfl, rfl⟩ := decoded; rfl)

/-- The original validator's outputs as exported values, in order: each
component the validator has, encoded. -/
def validatorOutputs (self : Nat) : List (List Nat) → {tys : List Ty} →
    Values (Component (assignment F G)) tys → List (Option (Value F G))
  | _, [], .nil => []
  | scopes, ty :: _, .cons value rest =>
      (if (scopes.headD []).contains self then [value.map (Value.encode ty)] else []) ++
        validatorOutputs self scopes.tail rest

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The returned references read the validator's outputs. -/
theorem outputs_read {handle : Nat} {cenv : List (Value F G)} (self : Nat) :
    ∀ (scopes : List (List Nat)) {slots : List Slot} {tys : List Ty}
      {values : Values (Component (assignment F G)) tys} {references : List Nat},
      outputReferences self scopes slots = some references → HoldsValues handle cenv slots values →
      slots.length = tys.length →
      ∃ read_, read cenv references = some read_ ∧
        read_.map some = validatorOutputs self scopes (maskValues self scopes values)
  | _, [], [], .nil, references, found, _, _ => by
      simp only [outputReferences, Option.some.injEq] at found
      subst found
      exact ⟨[], rfl, rfl⟩
  | scopes, slot :: rest, ty :: _, .cons value others, references, found, holds, length => by
      obtain ⟨head, tail⟩ := holds
      simp only [outputReferences] at found
      split_ifs at found with inScope
      · have inScope' : self ∈ scopes.head?.getD [] := by simpa using inScope
        cases slot with
        | held reference =>
          cases restFound : outputReferences self scopes.tail rest with
          | none => simp [restFound] at found
          | some restReferences =>
            simp only [restFound, Option.map_some, Option.some.injEq] at found
            subst found
            obtain ⟨tail', readTail, tailEq⟩ := outputs_read self scopes.tail restFound tail
              (by simpa using length)
            obtain ⟨x, rfl, decodedBind⟩ := head
            cases at_ : cenv[reference]? with
            | none => simp [at_] at decodedBind
            | some v =>
              simp only [at_, Option.bind_some] at decodedBind
              refine ⟨v :: tail', ?_, ?_⟩
              · simp only [read, List.mapM_cons, at_] at readTail ⊢
                simp [readTail]
              · simp [validatorOutputs, maskValues, Participant.restrict, inScope', tailEq,
                  Value.decode_some decodedBind]
        | absent => simp at found
        | free => simp at found
        | service => simp at found
      · have outScope : self ∉ scopes.head?.getD [] := by simpa using inScope
        obtain ⟨tail', readTail, tailEq⟩ := outputs_read self scopes.tail found tail (by simpa using length)
        exact ⟨tail', readTail, by simp [validatorOutputs, maskValues, Participant.restrict, outScope, tailEq]⟩
  | _, [], _ :: _, _, _, _, _, length => by cases length
  | _, _ :: _, [], _, _, _, _, length => by cases length

/-- The admitted program's participant in the plain view of its entry's body. -/
theorem participant_plain (self : Nat)
    (inputs : Values (Component (assignment F G)) program.payload.entry.inputs) :
    program.participant F G self inputs =
      (program.payload.entry.body.denote
        (participantMeaningWith (.silent _) (participantActions F G) (plainHelpers program) self
          (program.payload.plainProtocolTable F G) {})
        (maskValues self program.payload.entry.inputScopes inputs).get).bind fun results =>
          .done (maskValues self program.payload.entry.outputScopes results) := by
  unfold Program.participant Program.observed
  refine (program.payload.protocolTable_forgetSites (F := F) (G := G) _ _ _ _).trans ?_
  refine (protocol_invoke_body (.silent _) (participantActions F G) (plainHelpers program)
    program.payload.protocols program.payload.protocolsLinked program.payload.entry
    program.payload.entry_mem {} self inputs).trans ?_
  simp only [CheckedProtocol.denoteWith, ProtocolContext.mapScopes_root]
  rfl

end RootSoundness


section ProjectSound
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (program : Structured.Program) (context : Context)

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem read_eq_some {env values : List (Value F G)} :
    ∀ {references : List Nat}, read env references = some values ↔
      references.map (env[·]?) = values.map some
  | [] => by cases values <;> simp [read]
  | reference :: rest => by
      cases values with
      | nil =>
        simp only [read, List.mapM_cons, List.map_cons, List.map_nil, reduceCtorEq, iff_false]
        cases env[reference]? <;> simp
        cases rest.mapM (env[·]?) <;> simp
      | cons value others =>
        have tail := read_eq_some (env := env) (values := others) (references := rest)
        simp only [read] at tail
        simp only [read, List.mapM_cons, List.map_cons, List.cons.injEq]
        cases first : env[reference]? <;> cases tailFound : rest.mapM (env[·]?) <;>
          simp_all

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem read_dropLast {env values : List (Value F G)} {references : List Nat}
    (found : read env references = some values) : read env references.dropLast = some values.dropLast := by
  rw [read_eq_some] at found ⊢
  rw [List.map_dropLast, found, List.map_dropLast]

/-- Soundness of the participant projection rule: for every accepted export,
every service handle, data input and initial transcript, the exported program's
interactive reading returns the validator's original outputs, with every action,
reply and stop of the original validator. -/
theorem project_sound (participant : Participant)
    (accepted : project program context participant = .ok ())
    (handle : Nat) (data : List (Value F G)) (initial : History F G)
    (inputs : Values (Component (assignment F G)) program.payload.entry.inputs)
    (related : HoldsValues handle (data ++ [.transcript initial])
      (inputSlots context participant.policy program.payload.entry.inputs) inputs)
    (arity : data.length = participant.policy.publicInputs.length) :
    (spec context handle (helperTable program F G) participant.returned participant.instructions
        (data ++ [.transcript initial])).bind (fun values => .done (values.dropLast.map some)) =
      ((program.participant F G context.validator inputs).bind fun outputs =>
        .done (validatorOutputs context.validator program.payload.entry.outputScopes outputs)).interpret
          CommonAdapter.project := by
  unfold project at accepted
  simp only at accepted
  split at accepted
  · cases accepted
  · rename_i rest outputs count walked
    split at accepted
    · rename_i skipped skipEq
      split at accepted
      · rename_i references referenced
        split_ifs at accepted with conditions
        obtain ⟨returnedEq, nonempty, bounded⟩ := conditions
        rw [participant_plain program context.validator inputs]
        simp only [spec, specK_bind]
        rw [PIR.Process.bind_assoc, PIR.Process.interpret_bind]
        obtain ⟨outputsLength, walkedSound⟩ :=
          walk_sound (F := F) (G := G) program context handle projectionFuel {} _ _ _ _ _ _ _ walked
        apply walkedSound
        · exact (HoldsValues.mask context.validator _ related (by simp [inputSlots])).get
        · simp [arity]
        · intro cenv' outs prefix_ length' outsHold
          obtain ⟨extra, extraLength, skipSpec⟩ :=
            skip_spec context handle (helperTable program F G) rest cenv'
          rw [skipSpec, skipEq]
          simp only [skipEq] at extraLength
          simp only [specK]
          obtain ⟨read_, readReferences, readEq⟩ := outputs_read context.validator _ referenced outsHold
            outputsLength
          obtain ⟨values, readValues⟩ := read_some (env := cenv' ++ extra) (references := participant.returned)
            (fun reference member => by
              have := List.all_eq_true.mp bounded reference member
              simp only [decide_eq_true_eq] at this
              simp [length', extraLength]
              omega)
          have dropped := read_dropLast readValues
          rw [returnedEq, read_append readReferences] at dropped
          simp only [Option.some.injEq] at dropped
          simp only [readValues, PIR.Process.bind, PIR.Process.interpret]
          rw [← dropped, readEq]
      · cases accepted
    · cases accepted

end ProjectSound


end Zkc.Construction
