module

public import Zkc.Executable.NativeLaws
public import Zkc.Executable.DomainSchema

@[expose] public section

/-! The native frame/scope invariant with nominal reached state. The partial
ABI must be proved at the actual reached environment. Suites and coordinate
values stay in that environment; scalar frames supply only its readback.
These laws do not assert that every raw artifact establishes the invariant. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G : Type}

private theorem mapM_get {A B : Type} (f : A → Option B) :
    ∀ {values : List A} {mapped : List B}, values.mapM f = some mapped →
      ∀ index : Nat, mapped[index]? = values[index]?.bind f
  | [], mapped, found, _ => by simp at found; subst mapped; rfl
  | value :: values, mapped, found, index => by
      simp only [List.mapM_cons] at found
      cases first : f value with
      | none => simp [first] at found
      | some head =>
          cases rest : values.mapM f with
          | none => simp [first, rest] at found
          | some tail =>
              simp [first, rest] at found
              subst mapped
              cases index with
              | zero => simp [first]
              | succ index => exact mapM_get f rest index

private theorem mapM_read {A B : Type} (f : A → Option B)
    {values : List A} {mapped : List B} (found : values.mapM f = some mapped) :
    ∀ references : List Nat,
      (references.mapM (values[·]?)).bind (List.mapM f) = references.mapM (mapped[·]?)
  | [] => rfl
  | reference :: references => by
      have head := mapM_get f found reference
      have tail := mapM_read f found references
      simp only [List.mapM_cons]
      cases first : values[reference]? with
      | none => simp only [first, Option.bind_none] at head; simp [head]
      | some value =>
          cases decoded : f value with
          | none =>
              simp only [first, Option.bind_some, decoded] at head
              cases rest : references.mapM (values[·]?) <;> simp [head, List.mapM_cons, decoded]
          | some scalar =>
              simp only [first, Option.bind_some, decoded] at head
              cases rest : references.mapM (values[·]?) <;>
                simp [rest] at tail <;> simp [head, List.mapM_cons, decoded, ← tail]

/-- Exact partial readback of the nominal environment, including the opaque
initial scalar history and the mapped suffix of every transcript. -/
def Erases (suite : String) (key : Origin → Origin) (initial : History F G)
    (nominal : Environment F G) (scalar : List (Value F G)) : Prop :=
  DomainAdapter.readbackValues suite key initial nominal = some scalar

theorem Erases.get {suite : String} {key : Origin → Origin} {initial : History F G}
    {nominal : Environment F G} {scalar : List (Value F G)}
    (erases : Erases suite key initial nominal scalar) (reference : Nat) :
    scalar[reference]? = nominal[reference]?.bind (DomainAdapter.readbackValue suite key initial) :=
  mapM_get _ erases reference

/-- Every reference list commutes with partial readback. Out-of-bounds access
and wrong scalar envelopes remain explicit failures. -/
theorem Erases.read {suite : String} {key : Origin → Origin} {initial : History F G}
    {nominal : Environment F G} {scalar : List (Value F G)}
    (erases : Erases suite key initial nominal scalar) (references : List Nat) :
    (Domain.read nominal references).bind (DomainAdapter.readbackValues suite key initial) =
      Construction.read scalar references := mapM_read _ erases references

/-- Reuse the native lookup theorem through the actual scalar frame, while
retaining the complete nominal schema in the shared state. -/
structure Reached (suite : String) (key : Origin → Origin) (initial : History F G)
    (data : List (Value F G)) (reading : Reading) (state : State F G)
    (nominal : Environment F G) (scalar : List (Value F G)) : Prop where
  erases : Erases suite key initial nominal scalar
  native : Executable.Simulates data reading state scalar
  schema : nominal.map Domain.Value.sort = reading.sorts

/-- Named native lookups resolve to exactly the same nominal operands, under
partial readback, for arbitrary selected reference lists. -/
theorem Reached.lookup {suite : String} {key : Origin → Origin} {initial : History F G}
    {data : List (Value F G)} {reading : Reading} {state : State F G} {nominal : Environment F G} {scalar : List (Value F G)}
    (reached : Reached suite key initial data reading state nominal scalar)
    {named : Env F G} {scope : List (String × Nat)}
    (agrees : EnvAgrees scalar named scope) {names : List String} {references : List Nat}
    (resolved : names.mapM (lookupName scope) = .ok references) :
    lookupAll named names =
      (Domain.read nominal references).bind (DomainAdapter.readbackValues suite key initial) := by
  rw [reached.erases.read]
  exact (lookupAll_eq agrees resolved).1

private theorem transcript_readback {suite : String} {key : Origin → Origin} {initial : History F G}
    {value : Domain.Value (Structured.uniformCarriers F G)} {live : History F G}
    (found : DomainAdapter.readbackValue suite key initial value = some (.transcript live)) :
    ∃ history suffix, value = .transcript suite history ∧
      DomainAdapter.readbackHistory key history = some suffix ∧ live = initial ++ suffix := by
  cases value with
  | transcript actual history =>
      simp only [DomainAdapter.readbackValue] at found
      split at found
      · rename_i suiteEq
        subst actual
        cases mapped : DomainAdapter.readbackHistory key history with
        | none => simp [mapped] at found
        | some suffix =>
            simp only [mapped, Option.map_some, Option.some.injEq, Value.transcript.injEq] at found
            exact ⟨history, suffix, rfl, mapped, found.symm⟩
      · cases found
  | indices => cases found
  | data payload =>
      rcases payload with ⟨ty, supported, contents⟩
      cases ty <;> simp [DomainAdapter.readbackValue, DomainAdapter.readbackData] at found

private theorem coordinates_readback {suite : String} {key : Origin → Origin} {initial : History F G}
    {value : Domain.Value (Structured.uniformCarriers F G)} {path : List Nat}
    (found : DomainAdapter.readbackValue suite key initial value = some (.indices path)) :
    value = .indices path := by
  cases value with
  | indices coordinates => cases found; rfl
  | transcript actual history =>
      simp only [DomainAdapter.readbackValue] at found
      split at found
      · cases mapped : DomainAdapter.readbackHistory key history <;> simp [mapped] at found
      · cases found
  | data payload =>
      rcases payload with ⟨ty, supported, contents⟩
      cases ty <;> simp [DomainAdapter.readbackValue, DomainAdapter.readbackData] at found

/-- The native live history is the opaque prefix followed by the mapped
nominal suffix, with the actual suite retained in the reached slot. -/
theorem Reached.live {suite : String} {key : Origin → Origin} {initial : History F G}
    {data scalar : List (Value F G)} {reading : Reading} {state : State F G} {nominal : Environment F G}
    (reached : Reached suite key initial data reading state nominal scalar) :
    ∃ history suffix, nominal[reading.current]? = some (.transcript suite history) ∧
      DomainAdapter.readbackHistory key history = some suffix ∧ state.live = initial ++ suffix := by
  have projected := (reached.erases.get reading.current).symm.trans reached.native.live
  cases looked : nominal[reading.current]? with
  | none => simp [looked] at projected
  | some value =>
      simp only [looked, Option.bind_some] at projected
      obtain ⟨history, suffix, rfl, mapped, live⟩ := transcript_readback projected
      exact ⟨history, suffix, rfl, mapped, live⟩

/-- Scalar occurrence coordinates are the exact reached nominal path. No
length or numeric value is recovered from a default scalar representation. -/
theorem Reached.coordinates {suite : String} {key : Origin → Origin} {initial : History F G}
    {data scalar : List (Value F G)} {reading : Reading} {state : State F G} {nominal : Environment F G}
    (reached : Reached suite key initial data reading state nominal scalar)
    {reference : Nat} {path : List Nat} (looked : scalar[reference]? = some (.indices path)) :
    nominal[reference]? = some (.indices path) := by
  have projected := (reached.erases.get reference).symm.trans looked
  cases found : nominal[reference]? with
  | none => simp [found] at projected
  | some value =>
      simp only [found, Option.bind_some] at projected
      exact congrArg some (coordinates_readback projected)

private theorem dataSort_embed (suite : String) (key : Origin → Origin) (initial : History F G)
    {value : Value F G} {sort : ValueSort} (reported : dataSort? value = some sort) :
    ∃ nominal : Domain.Value (Structured.uniformCarriers F G),
      DomainAdapter.embedData value = some nominal ∧ nominal.sort = sort ∧
        DomainAdapter.readbackValue suite key initial nominal = some value := by
  cases value with
  | data payload =>
      cases payload <;> cases reported <;> exact ⟨_, rfl, rfl, rfl⟩
  | index | vector => cases reported; exact ⟨_, rfl, rfl, rfl⟩
  | transcript | indices | unsupported => cases reported

private theorem embed_sorted_data (suite : String) (key : Origin → Origin) (initial : History F G) :
    ∀ (sorts : List ValueSort) (data : List (Value F G)),
      sorts.map some = data.map dataSort? →
        ∃ nominal : Environment F G, DomainAdapter.embedValues data = some nominal ∧
          nominal.map Domain.Value.sort = sorts ∧ Erases suite key initial nominal data
  | [], [], _ => ⟨[], rfl, rfl, rfl⟩
  | [], _ :: _, matched => by simp at matched
  | _ :: _, [], matched => by simp at matched
  | sort :: sorts, value :: data, matched => by
      simp only [List.map_cons, List.cons.injEq] at matched
      obtain ⟨nominal, embedded, sorted, readback⟩ := dataSort_embed suite key initial matched.1.symm
      obtain ⟨rest, restEmbedded, restSorted, restReadback⟩ :=
        embed_sorted_data suite key initial sorts data matched.2
      refine ⟨nominal :: rest, ?_, ?_, ?_⟩
      · simp [DomainAdapter.embedValues_cons, embedded, restEmbedded]
      · simp only [List.map_cons, sorted, restSorted]
      · simp only [Erases, DomainAdapter.readbackValues, List.mapM_cons] at restReadback ⊢
        simp [readback, restReadback]

/-- The actual native entry check supplies the nominal schema and partial ABI
for every admitted data tuple. The opaque initial history is retained as the
handler prefix; the nominal live transcript starts with an empty suffix.
Rejected tuples remain the native entry refusal case. -/
theorem Reached.initial (validator : Validator) (data : List (Value F G))
    (history : History F G) (bytes : List UInt8) (key : Origin → Origin)
    (admitted : validator.admits data = true) :
    ∃ suite nominal, DomainAdapter.embedValues data = some nominal ∧
      Reached suite key history data ⟨validator.inputs.map (·.2.sort), data.length⟩
        (Executable.initial validator data history bytes)
        (nominal ++ [.transcript suite []]) (data ++ [.transcript history]) := by
  obtain ⟨suite, sorts, sortsEq, reported⟩ := admits_sorts validator admitted
  obtain ⟨nominal, embedded, sorted, erased⟩ := embed_sorted_data suite key history sorts data reported
  refine ⟨suite, nominal, embedded, ?_⟩
  refine ⟨?_, initial_simulates validator data history bytes admitted, ?_⟩
  · simp only [Erases, DomainAdapter.readbackValues] at erased ⊢
    simp [List.mapM_append, erased, DomainAdapter.readbackValue, DomainAdapter.readbackHistory]
  · simp [List.map_append, sorted, sortsEq, Domain.Value.sort]

end Zkc.Executable.DomainVM
