module

public import Zkc.Executable.DomainNativeState
public import Zkc.Executable.DomainNativeHelpers

@[expose] public section

/-! Exact data ABI laws used at native operation boundaries. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G : Type}

theorem embed_readbackData (nominal : Domain.Value (Structured.uniformCarriers F G))
    (scalar : Value F G) (found : DomainAdapter.readbackData nominal = some scalar) :
    DomainAdapter.embedData scalar = some nominal := by
  cases nominal with
  | transcript => cases found
  | indices => cases found; rfl
  | data payload =>
      rcases payload with ⟨ty, supported, contents⟩
      cases ty <;> simp only [DomainAdapter.readbackData] at found
      all_goals cases found
      all_goals rfl

theorem readbackData_nontranscript (suite : String) (key : Origin → Origin) (initial : History F G)
    (nominal : Domain.Value (Structured.uniformCarriers F G))
    (notTranscript : ∀ actual, nominal.sort ≠ .transcript actual) :
    DomainAdapter.readbackValue suite key initial nominal = DomainAdapter.readbackData nominal := by
  cases nominal with
  | transcript actual => exact (notTranscript actual rfl).elim
  | data | indices => rfl

theorem readbackData_embed (suite : String) (key : Origin → Origin) (initial : History F G)
    (scalar : Value F G) (nominal : Domain.Value (Structured.uniformCarriers F G))
    (embedded : DomainAdapter.embedData scalar = some nominal) :
    DomainAdapter.readbackValue suite key initial nominal = some scalar := by
  cases scalar with
  | data payload => cases payload <;> cases embedded <;> rfl
  | index | vector | indices => cases embedded; rfl
  | transcript | unsupported => cases embedded

theorem embedValues_erases (suite : String) (key : Origin → Origin) (initial : History F G) :
    ∀ {scalar : List (Value F G)} {nominal : Environment F G},
      DomainAdapter.embedValues scalar = some nominal → Erases suite key initial nominal scalar
  | [], nominal, embedded => by cases embedded; rfl
  | value :: values, nominal, embedded => by
      simp only [DomainAdapter.embedValues_cons] at embedded
      cases head : DomainAdapter.embedData value with
      | none => simp [head] at embedded
      | some first =>
          cases tail : DomainAdapter.embedValues values with
          | none => simp [head, tail] at embedded
          | some rest =>
              simp [head, tail] at embedded
              subst nominal
              simp only [Erases, DomainAdapter.readbackValues, List.mapM_cons,
                readbackData_embed suite key initial value first head]
              change (do let rest ← DomainAdapter.readbackValues suite key initial rest
                         pure (value :: rest)) = some (value :: values)
              rw [show DomainAdapter.readbackValues suite key initial rest = some values from
                embedValues_erases suite key initial tail]
              rfl

/-- Reading data-only nominal slots gives the partial scalar embedding itself,
not merely an equality after a lossy projection. -/
theorem Erases.dataEmbedding {suite : String} {key : Origin → Origin} {initial : History F G}
    {nominal : Environment F G} {scalar : List (Value F G)}
    (erases : Erases suite key initial nominal scalar)
    (data : ∀ value ∈ nominal, ∀ actual, value.sort ≠ .transcript actual) :
    DomainAdapter.embedValues scalar = some nominal := by
  induction nominal generalizing scalar with
  | nil => simp [Erases, DomainAdapter.readbackValues] at erases; subst scalar; rfl
  | cons value values ih =>
      simp only [Erases, DomainAdapter.readbackValues, List.mapM_cons] at erases
      rw [readbackData_nontranscript suite key initial value (data value List.mem_cons_self)] at erases
      cases head : DomainAdapter.readbackData value with
      | none => simp [head] at erases
      | some first =>
          cases tail : values.mapM (DomainAdapter.readbackValue suite key initial) with
          | none => simp [head, tail] at erases
          | some rest =>
              simp [head, tail] at erases
              subst scalar
              have embedded := embed_readbackData value first head
              have others := ih tail (fun v member => data v (List.mem_cons_of_mem _ member))
              simp [DomainAdapter.embedValues_cons, embedded, others]

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem encodeValues_embeds {types : List Structured.Ty}
    (values : Values (Structured.assignment F G) types) (eligible : types.all dataType = true) :
    ∃ nominal : Environment F G,
      DomainAdapter.embedValues (encodeValues values) = some nominal ∧
        nominal.map Domain.Value.sort = types.map ValueSort.data := by
  have admitted : types.all Domain.dataType = true := by
    apply List.all_eq_true.mpr
    intro ty member
    have allowed := List.all_eq_true.mp eligible ty member
    cases ty <;> simp_all [dataType, Domain.dataType, Structured.Ty.isService]
  obtain ⟨encoded, found⟩ := Domain.encodeValues_exists values admitted
  exact ⟨encoded, (DomainAdapter.encodeValues_embed values eligible).trans found, encodeValues_sorts values found⟩

theorem calculate_returns_embeds (calculation : Calculation)
    (eligible : calculation.op.results.all dataType = true)
    {arguments results : List (Value F G)}
    (returned : Construction.calculate calculation arguments = .returned results) :
    ∃ nominal : Environment F G, DomainAdapter.embedValues results = some nominal ∧
      nominal.map Domain.Value.sort = calculation.op.results.map ValueSort.data := by
  unfold Construction.calculate at returned
  split at returned
  · cases returned
  · split at returned
    · rename_i values returnedValues computed
      cases returned
      exact encodeValues_embeds returnedValues eligible
    · cases returned

end Zkc.Executable.DomainVM
