module

public import Zkc.Executable.Lowering
public import Zkc.Construction.Soundness

@[expose] public section

/-! The relation between an executable run and the metered ideal meaning.

A run is observed through its outcome class, in the stop vocabulary of the ideal
meaning, and, after a normal return, whether the whole proof was read. A budget
stop is exhaustion; an explicit stop or a stop of an installed operation keeps
its reason; decoding, truncation and contract failures are refusals.

The simulation invariant ties a machine state to a reading state and an ideal
environment: the instructions charged so far, the sorts of the ideal values, the
live transcript, the data inputs at the front of the environment, and for every
active participant frame a scope whose names denote the frame's values. This
module proves the generic facts about frames, scopes and sorts the soundness
proofs use.
-/

set_option autoImplicit false

namespace Zkc.Executable
open Zkc.Construction Zkc.Source

variable {F G : Type}

/-- Whether a value has a sort: a data value is the encoding of a value of its
structured type. Transcript values carry no suite and coordinates no length. -/
def HasSort : Value F G → ValueSort → Prop
  | value, .data ty => ∃ decoded, Value.encode ty decoded = value
  | .transcript _, .transcript _ => True
  | .indices _, .indices => True
  | _, _ => False

/-- The class of a stop cause in the stop vocabulary of the ideal meaning. -/
@[simp] def Cause.outcome : Cause → PIR.Stop
  | .limit => .exhausted
  | .kernel reason => reason
  | .explicit reason => reason
  | .decode | .truncated | .contract => .refused

/-- The outcome class of a run. -/
def Result.outcome : Result F G → PIR.Outcome (List (Value F G))
  | .returned values => .returned values
  | .stopped cause _ _ => .stopped cause.outcome

/-- What the relation compares: the outcome class and, after a normal return,
whether the whole proof was read. -/
def observation {α : Type} (outcome : PIR.Outcome α) (complete : Bool) : PIR.Outcome α × Bool :=
  match outcome with
  | .returned _ => (outcome, complete)
  | .stopped _ => (outcome, true)

def Run.observe (run : Run F G) : PIR.Outcome (List (Value F G)) × Bool :=
  observation run.result.outcome run.unread.isEmpty

def idealObservation (result : PIR.Outcome (List (Value F G)) × Proof F G) :
    PIR.Outcome (List (Value F G)) × Bool :=
  observation result.1 result.2.isEmpty

@[simp] theorem State.stop_observe (s : State F G) (cause : Cause) (site : Option String)
    (call : Option (String × String)) :
    (s.stop cause site call).observe = (.stopped cause.outcome, true) := rfl

@[simp] theorem idealObservation_stopped (stop : PIR.Stop) (proof : Proof F G) :
    idealObservation ((.stopped stop, proof) : PIR.Outcome (List (Value F G)) × Proof F G) =
      (.stopped stop, true) := rfl

/-- The names of a scope denote values of an ideal environment in an
executable environment. -/
def EnvAgrees (env : List (Value F G)) (named : Env F G) (scope : List (String × Nat)) : Prop :=
  ∀ name reference, List.lookup name scope = some reference →
    reference < env.length ∧ List.lookup name named = env[reference]?

/-- A frame and a reading scope agree. -/
abbrev FrameAgrees (env : List (Value F G)) (frame : Frame F G) (scope : List (String × Nat)) : Prop :=
  EnvAgrees env frame.env scope

/-- The simulation invariant between a machine state, a reading state and the
ideal environment, for data inputs `data`. -/
structure Simulates (data : List (Value F G)) (R : Reading) (s : State F G)
    (env : List (Value F G)) : Prop where
  length : env.length = R.sorts.length
  sorted : ∀ (index : Nat) (value : Value F G) (sort : ValueSort),
    env[index]? = some value → R.sorts[index]? = some sort → HasSort value sort
  live : env[R.current]? = some (.transcript s.live)
  inputs : ∀ index, index < data.length → env[index]? = data[index]?

/-! ## Names, frames and scopes -/

theorem lookup_append_some {α β : Type} [BEq α] (name : α) :
    ∀ (first second : List (α × β)),
      List.lookup name (first ++ second) = (List.lookup name first).or (List.lookup name second)
  | [], second => by simp [List.lookup]
  | (key, value) :: first, second => by
      cases h : name == key <;> simp [List.lookup, h, lookup_append_some name first second]

theorem lookupAll_eq {env : List (Value F G)} {named : Env F G} {scope : List (String × Nat)}
    (agrees : EnvAgrees env named scope) :
    ∀ {names : List String} {references : List Nat}, names.mapM (lookupName scope) = .ok references →
      lookupAll named names = references.mapM (fun reference => env[reference]?) ∧
        ∀ reference ∈ references, reference < env.length := by
  intro names
  induction names with
  | nil =>
      intro references read
      change Except.ok [] = Except.ok references at read
      cases read
      simp [lookupAll]
  | cons name names ih =>
      intro references read
      simp only [List.mapM_cons, lookupName] at read
      split at read
      · rename_i reference found
        simp only [bind, Except.bind] at read
        split at read
        · cases read
        · rename_i others othersRead
          cases read
          obtain ⟨bound, same⟩ := agrees name reference found
          obtain ⟨rest, bounds⟩ := ih othersRead
          refine ⟨?_, ?_⟩
          · simp only [lookupAll, List.mapM_cons] at rest ⊢
            rw [same, rest]
          · intro r member
            rcases List.mem_cons.mp member with rfl | member
            · exact bound
            · exact bounds r member
      · cases read

theorem lookupName_eq {env : List (Value F G)} {named : Env F G} {scope : List (String × Nat)}
    (agrees : EnvAgrees env named scope) {name : String} {reference : Nat}
    (read : lookupName scope name = .ok reference) :
    reference < env.length ∧ List.lookup name named = env[reference]? := by
  unfold lookupName at read
  split at read
  · rename_i found found'
    cases read
    exact agrees name _ found'
  · cases read

theorem lookup_zip_mapM (env : List (Value F G)) :
    ∀ {formals : List String} {references : List Nat} {values : List (Value F G)},
      references.mapM (fun reference => env[reference]?) = some values →
      ∀ name reference, List.lookup name (formals.zip references) = some reference →
        reference ∈ references ∧ List.lookup name (formals.zip values) = env[reference]?
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | formal :: formals, reference :: references, values, found => by
      simp only [List.mapM_cons] at found
      cases first : env[reference]? with
      | none => simp [first] at found
      | some value =>
          cases others : references.mapM (fun reference => env[reference]?) with
          | none => simp [first, others] at found
          | some rest =>
              simp [first, others] at found
              subst found
              intro name target lookup
              by_cases same : name = formal
              · subst same
                simp at lookup
                subst lookup
                simp [first]
              · have hb : (name == formal) = false := by simpa using same
                simp only [List.zip_cons_cons, List.lookup, hb] at lookup ⊢
                obtain ⟨member, value⟩ := lookup_zip_mapM env others name target lookup
                exact ⟨List.mem_cons_of_mem _ member, value⟩

theorem lookup_zip_range' :
    ∀ {outputs : List String} {results : List (Value F G)} (env : List (Value F G)),
      outputs.length = results.length →
      ∀ name reference,
        List.lookup name (outputs.zip (List.range' env.length results.length)) = some reference →
        reference < env.length + results.length ∧
          List.lookup name (outputs.zip results) = (env ++ results)[reference]?
  | [], _, _, _ => by simp
  | _ :: _, [], _, lengths => by simp at lengths
  | output :: outputs, result :: results, env, lengths => by
      intro name reference found
      simp only [List.length_cons, List.range'_succ, List.zip_cons_cons] at found
      by_cases same : name = output
      · subst same
        simp at found
        subst found
        simp
      · have hb : (name == output) = false := by simpa using same
        simp only [List.lookup, hb] at found
        have tail := lookup_zip_range' (outputs := outputs) (results := results) (env ++ [result])
          (by simpa using lengths) name reference (by simpa [Nat.add_comm] using found)
        simp only [List.length_append, List.length_cons, List.length_nil] at tail
        refine ⟨by simp only [List.length_cons]; omega, ?_⟩
        simp only [List.zip_cons_cons, List.lookup, hb]
        simpa using tail.2

theorem EnvAgrees.extend {env : List (Value F G)} {named : Env F G}
    {scope : List (String × Nat)} (agrees : EnvAgrees env named scope) (more : List (Value F G)) :
    EnvAgrees (env ++ more) named scope := by
  intro name reference found
  obtain ⟨bound, same⟩ := agrees name reference found
  exact ⟨by simp; omega, by rw [same, List.getElem?_append_left bound]⟩

theorem frames_extend {env : List (Value F G)} {frames : List (Frame F G)}
    {scopes : List (List (String × Nat))} (agree : List.Forall₂ (FrameAgrees env) frames scopes)
    (more : List (Value F G)) : List.Forall₂ (FrameAgrees (env ++ more)) frames scopes := by
  induction agree with
  | nil => exact .nil
  | cons head _ ih => exact .cons (EnvAgrees.extend head more) ih

theorem length_of_mapM_some {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → xs.length = ys.length
  | [], ys, found => by
      change some [] = some ys at found
      cases found
      rfl
  | x :: xs, ys, found => by
      simp only [List.mapM_cons] at found
      cases first : f x with
      | none => simp [first] at found
      | some y =>
          cases others : xs.mapM f with
          | none => simp [first, others] at found
          | some zs =>
              simp [first, others] at found
              subst found
              simp [length_of_mapM_some others]

theorem length_of_mapM_ok {α β ε : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → xs.length = ys.length
  | [], ys, found => by
      change Except.ok [] = Except.ok ys at found
      cases found
      rfl
  | x :: xs, ys, found => by
      simp only [List.mapM_cons, bind, Except.bind] at found
      split at found
      · cases found
      · rename_i y first
        split at found
        · cases found
        · rename_i zs others
          cases found
          simp [length_of_mapM_ok others]

theorem mapM_getElem?_some {α : Type} (env : List α) :
    ∀ {references : List Nat}, (∀ reference ∈ references, reference < env.length) →
      ∃ values, references.mapM (fun reference => env[reference]?) = some values
  | [], _ => ⟨[], rfl⟩
  | reference :: references, bounds => by
      obtain ⟨values, found⟩ := mapM_getElem?_some env (references := references)
        (fun r member => bounds r (List.mem_cons_of_mem _ member))
      refine ⟨env[reference]'(bounds reference List.mem_cons_self) :: values, ?_⟩
      simp [List.mapM_cons, found, List.getElem?_eq_getElem (bounds reference List.mem_cons_self)]

theorem lookup_zip_isNone {α β γ : Type} [BEq α] (name : α) :
    ∀ {keys : List α} {first : List β} {second : List γ},
      keys.length = first.length → keys.length = second.length →
      (List.lookup name (keys.zip first)).isNone = (List.lookup name (keys.zip second)).isNone
  | [], _, _, _, _ => by simp
  | _ :: _, [], _, lengths, _ => by simp at lengths
  | _ :: _, _ :: _, [], _, lengths => by simp at lengths
  | key :: keys, _ :: first, _ :: second, lengths, others => by
      simp only [List.zip_cons_cons, List.lookup]
      cases name == key
      · exact lookup_zip_isNone name (by simpa using lengths) (by simpa using others)
      · rfl

theorem EnvAgrees.pushAll {env : List (Value F G)} {named : Env F G}
    {scope : List (String × Nat)} (agrees : EnvAgrees env named scope)
    (outputs : List String) (results : List (Value F G)) (lengths : outputs.length = results.length) :
    EnvAgrees (env ++ results) (outputs.zip results ++ named)
      (outputs.zip (List.range' env.length results.length) ++ scope) := by
  intro name reference found
  rw [lookup_append_some] at found
  simp only [lookup_append_some]
  cases inner : List.lookup name (outputs.zip (List.range' env.length results.length)) with
  | some target =>
      rw [inner] at found
      simp only [Option.some_or, Option.some.injEq] at found
      subst found
      obtain ⟨bound, same⟩ := lookup_zip_range' env lengths name target inner
      refine ⟨by simp; omega, ?_⟩
      obtain ⟨value, present⟩ : ∃ value, (env ++ results)[target]? = some value :=
        ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩
      rw [same, present, Option.some_or]
  | none =>
      rw [inner] at found
      simp only [Option.none_or] at found
      have absent : List.lookup name (outputs.zip results) = none := by
        have := lookup_zip_isNone name (keys := outputs) (first := List.range' env.length results.length)
          (second := results) (by simp [lengths]) lengths
        rw [inner] at this
        simpa using this.symm
      rw [absent, Option.none_or]
      exact (agrees.extend results) name reference found

theorem EnvAgrees.push {env : List (Value F G)} {named : Env F G}
    {scope : List (String × Nat)} (agrees : EnvAgrees env named scope)
    (name : String) (value : Value F G) :
    EnvAgrees (env ++ [value]) ((name, value) :: named) ((name, env.length) :: scope) := by
  simpa using agrees.pushAll [name] [value] rfl

theorem EnvAgrees.enter {env : List (Value F G)} {references : List Nat} {values : List (Value F G)}
    (formals : List String)
    (bounds : ∀ reference ∈ references, reference < env.length)
    (found : references.mapM (fun reference => env[reference]?) = some values) :
    EnvAgrees env (formals.zip values) (formals.zip references) := by
  intro name reference lookup
  obtain ⟨member, same⟩ := lookup_zip_mapM env found name reference lookup
  exact ⟨bounds reference member, same⟩

theorem EnvAgrees.leave {env : List (Value F G)} {named : Env F G}
    {scope : List (String × Nat)} (agrees : EnvAgrees env named scope)
    {outputs : List String} {references : List Nat} {values : List (Value F G)}
    (lengths : outputs.length = references.length)
    (bounds : ∀ reference ∈ references, reference < env.length)
    (found : references.mapM (fun reference => env[reference]?) = some values) :
    EnvAgrees env (outputs.zip values ++ named) (outputs.zip references ++ scope) := by
  intro name reference lookup
  rw [lookup_append_some] at lookup
  simp only [lookup_append_some]
  have valuesLength : references.length = values.length := length_of_mapM_some found
  cases inner : List.lookup name (outputs.zip references) with
  | some target =>
      rw [inner] at lookup
      simp only [Option.some_or, Option.some.injEq] at lookup
      subst lookup
      obtain ⟨member, same⟩ := lookup_zip_mapM env found name target inner
      refine ⟨bounds target member, ?_⟩
      obtain ⟨value, present⟩ : ∃ value, env[target]? = some value :=
        ⟨_, List.getElem?_eq_getElem (bounds target member)⟩
      rw [same, present, Option.some_or]
  | none =>
      rw [inner] at lookup
      simp only [Option.none_or] at lookup
      have absent : List.lookup name (outputs.zip values) = none := by
        have := lookup_zip_isNone name (keys := outputs) (first := references) (second := values)
          lengths (lengths.trans valuesLength)
        rw [inner] at this
        simpa using this.symm
      rw [absent, Option.none_or]
      exact agrees name reference lookup

theorem sorted_extend {env : List (Value F G)} {sorts : List ValueSort}
    (length : env.length = sorts.length)
    (sorted : ∀ (index : Nat) (value : Value F G) (sort : ValueSort),
      env[index]? = some value → sorts[index]? = some sort → HasSort value sort)
    {more : List (Value F G)} {moreSorts : List ValueSort}
    (moreSorted : ∀ (index : Nat) (value : Value F G) (sort : ValueSort),
      more[index]? = some value → moreSorts[index]? = some sort → HasSort value sort) :
    ∀ (index : Nat) (value : Value F G) (sort : ValueSort),
      (env ++ more)[index]? = some value → (sorts ++ moreSorts)[index]? = some sort →
        HasSort value sort := by
  intro index value sort found sortFound
  rcases Nat.lt_or_ge index env.length with lt | ge
  · rw [List.getElem?_append_left lt] at found
    rw [List.getElem?_append_left (length ▸ lt)] at sortFound
    exact sorted index value sort found sortFound
  · rw [List.getElem?_append_right ge] at found
    rw [List.getElem?_append_right (length ▸ ge), ← length] at sortFound
    exact moreSorted _ value sort found sortFound

theorem payloadType_scalar (payload : Payload F G) : scalarType (payloadType payload) = some payload.ty := by
  cases payload <;> rfl

theorem scalarType_payload {ty : Structured.Ty} {payload : Payload F G}
    (scalar : scalarType ty = some payload.ty) : ty = payloadType payload := by
  cases ty <;> cases payload <;> simp_all [scalarType, payloadType, Payload.ty]

/-- A decoded payload has its own structured type as a sort. -/
theorem payload_sorted (payload : Payload F G) : HasSort (.data payload) (.data (payloadType payload)) := by
  cases payload with
  | boolean value => exact ⟨value, rfl⟩
  | field domain value => exact ⟨value, rfl⟩
  | group domain value => exact ⟨value, rfl⟩

/-- A data value of a scalar type is a payload of that type. -/
theorem sorted_payload {value : Value F G} {payload : Payload F G} {ty : Structured.Ty}
    (sorted : HasSort value (.data ty)) (found : value = .data payload) : payloadType payload = ty := by
  obtain ⟨decoded, encoded⟩ := sorted
  subst found
  cases ty <;> simp [Value.encode] at encoded <;> subst encoded <;> rfl

/-- A data input has the sort it reports. -/
theorem dataSort_sorted {value : Value F G} {sort : ValueSort} (reported : dataSort? value = some sort) :
    HasSort value sort := by
  cases value with
  | data payload =>
      simp only [dataSort?, Option.some.injEq] at reported
      subst reported
      exact payload_sorted payload
  | index n =>
      simp only [dataSort?, Option.some.injEq] at reported
      subst reported
      exact ⟨n, rfl⟩
  | vector domain values =>
      simp only [dataSort?, Option.some.injEq] at reported
      subst reported
      exact ⟨values, rfl⟩
  | transcript => simp [dataSort?] at reported
  | indices => simp [dataSort?] at reported

/-- Encoded values have the sorts of their types. -/
theorem encodeValues_sorted :
    ∀ {tys : List Structured.Ty} (values : Values (Structured.assignment F G) tys)
      (index : Nat) (value : Value F G) (sort : ValueSort),
      (encodeValues values)[index]? = some value → (tys.map ValueSort.data)[index]? = some sort →
        HasSort value sort
  | [], .nil, _, _, _, found, _ => by simp [encodeValues] at found
  | ty :: _, .cons head rest, 0, value, sort, found, sortFound => by
      simp only [encodeValues, List.getElem?_cons_zero, Option.some.injEq, List.map_cons] at found sortFound
      subst found sortFound
      exact ⟨head, rfl⟩
  | _ :: _, .cons _ rest, index + 1, value, sort, found, sortFound => by
      simp only [encodeValues, List.getElem?_cons_succ, List.map_cons] at found sortFound
      exact encodeValues_sorted rest index value sort found sortFound

theorem calculate_sorted [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    {calculation : Calculation} {arguments results : List (Value F G)}
    (computed : Zkc.Construction.calculate calculation arguments = .returned results) :
    ∀ (index : Nat) (value : Value F G) (sort : ValueSort), results[index]? = some value →
      (calculation.op.results.map ValueSort.data)[index]? = some sort → HasSort value sort := by
  unfold Zkc.Construction.calculate at computed
  split at computed
  · cases computed
  · split at computed
    · cases computed
      exact encodeValues_sorted _
    · cases computed

theorem evaluate_stopped [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (calculation : Calculation) {values : Values (Structured.assignment F G) calculation.op.arguments}
    {reason : PIR.Stop} (stopped : calculation.evaluate values = .stopped reason) : reason = .refused := by
  cases calculation with
  | boundedAt domain =>
      rcases values with _ | ⟨container, _ | ⟨index, _ | _⟩⟩
      simp only [Calculation.evaluate] at stopped
      split at stopped
      · cases stopped
      · cases stopped
        rfl
  | _ =>
      rcases values with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩
      simp [Calculation.evaluate] at stopped

/-- A calculation stops only by refusing. -/
theorem calculate_stopped [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    {calculation : Calculation} {arguments : List (Value F G)} {reason : PIR.Stop}
    (stopped : Zkc.Construction.calculate calculation arguments = .stopped reason) : reason = .refused := by
  unfold Zkc.Construction.calculate at stopped
  split at stopped
  · cases stopped
    rfl
  · split at stopped
    · cases stopped
    · rename_i stop evaluated
      cases stopped
      exact evaluate_stopped calculation evaluated

theorem readOperation_calculate (sorts : List ValueSort) (current : Nat) (site : String)
    (calculation : Calculation) (operands : List Nat) :
    readOperation sorts current site (.calculate calculation) operands =
      if operands.map (sorts[·]?) = calculation.op.arguments.map (some ∘ .data) then
        .ok (.calculate calculation, calculation.op.results.map .data, false)
      else .error (.operation site) := by
  rcases operands with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;> rfl

theorem Simulates.value {data : List (Value F G)} {R : Reading} {s : State F G} {env : List (Value F G)}
    (sim : Simulates data R s env) {index : Nat} {sort : ValueSort} (sortEq : R.sorts[index]? = some sort) :
    ∃ value, env[index]? = some value ∧ HasSort value sort := by
  have bound : index < env.length := by
    rw [sim.length]
    exact (List.getElem?_eq_some_iff.mp sortEq).1
  exact ⟨_, List.getElem?_eq_getElem bound,
    sim.sorted index _ sort (List.getElem?_eq_getElem bound) sortEq⟩

theorem not_sorted_transcript {history : History F G} {ty : Structured.Ty} :
    ¬ HasSort (.transcript history) (.data ty) := by
  rintro ⟨decoded, encoded⟩
  cases ty <;> simp [Value.encode] at encoded

theorem custody_of_read [DecidableEq F] [DecidableEq G] {data : List (Value F G)} {R : Reading}
    {s : State F G} {env : List (Value F G)} (sim : Simulates data R s env) :
    ∀ {references : List Nat} {results : List (Value F G)},
      references.mapM (fun reference => env[reference]?) = some results →
      custody R.sorts R.current references = true →
      custodyKept s.live results = true
  | [], results, found, _ => by
      change some [] = some results at found
      cases found
      rfl
  | reference :: references, results, found, checked => by
      simp only [List.mapM_cons] at found
      cases first : env[reference]? with
      | none => simp [first] at found
      | some value =>
          cases others : references.mapM (fun reference => env[reference]?) with
          | none => simp [first, others] at found
          | some rest =>
              simp [first, others] at found
              subst found
              simp only [custody, List.all_cons, Bool.and_eq_true] at checked
              have tail := custody_of_read sim others checked.2
              simp only [custodyKept, List.all_cons, Bool.and_eq_true] at tail ⊢
              refine ⟨?_, tail⟩
              cases value with
              | transcript history =>
                  have bound : reference < R.sorts.length := by
                    rw [← sim.length]
                    exact (List.getElem?_eq_some_iff.mp first).1
                  obtain ⟨sort, sortFound⟩ : ∃ sort, R.sorts[reference]? = some sort :=
                    ⟨_, List.getElem?_eq_getElem bound⟩
                  have sorted := sim.sorted reference _ sort first sortFound
                  cases sort with
                  | transcript suite =>
                      have current := checked.1
                      simp only [sortFound, beq_iff_eq] at current
                      subst current
                      rw [sim.live] at first
                      simp at first
                      simp [first]
                  | data => exact absurd sorted not_sorted_transcript
                  | indices => cases sorted
              | data => rfl
              | index => rfl
              | vector => rfl
              | indices => rfl

end Zkc.Executable
