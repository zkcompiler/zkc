module

public import Zkc.Subject.Coverage
public import ZkcFormal.Written.ArithmeticDraws
public import ZkcFormal.Written.ScalarField

@[expose] public section

namespace ZkcFormal.Written.StandardInterpretation
open Zkc.Core Zkc.Vocabulary Zkc.Subject ProbabilisticProcess
open scoped ScalarField

/-- The scalar field and the additive cyclic group of its order. -/
abbrev F := ScalarField
abbrev G := ScalarField
noncomputable abbrev D := ArithmeticModel.data F G
noncomputable abbrev model := ArithmeticModel.model F G
noncomputable abbrev draws := ArithmeticModel.draws F G
noncomputable abbrev samplers := lawSamplers model draws

theorem served : Served samplers (Permitted model) := ArithmeticModel.served F G
theorem large : Zkc.Vocabulary.Field.bls12381Fr.order ≤ Fintype.card F := ScalarField.card.ge

/-- Acceptance of a nominal sort requires an actual entry before totalization. -/
theorem coveredSort_iff_carrierEntry (k : Standard.TypeKey) :
    (Coverage.missingSort (.nominal k)).isNone = (StandardModel.carrierEntry D k).isSome := by
  cases k with
  | inr => rfl
  | inl k =>
    cases k with
    | field f | nonzero f => cases f <;> rfl
    | group g => cases g <;> rfl

/-- The compiler's row test describes precisely the arms of the semantic table. -/
theorem interpreted_iff_arm (k : Standard.RowKey) :
    Coverage.interpreted k = (StandardModel.arm D k).isSome := by
  cases k with
  | inr => rfl
  | inl k =>
    cases k with
    | field r f a => cases f <;> cases a <;> cases r <;> rfl
    | group r a =>
      cases a with
      | field => cases r <;> rfl
      | group g => cases g <;> cases r <;> rfl
    | seq r e size =>
      cases e with
      | sized => cases r <;> rfl
      | atom a =>
        cases a with
        | group => cases r <;> rfl
        | field f => cases f <;> cases r <;> cases size <;> rfl
    | hash | pair => rfl

/-- A covered draw has an actual distribution at the reply type in the program. -/
theorem sampled_iff_draws (t : Zkc.Vocabulary.Ty) (reply : Standard.Ty) :
    Coverage.sampledType t reply = (draws (.uniform t) [] .nil reply).isSome := by
  apply Eq.trans _ (ArithmeticModel.sampled_iff_draws F G (.uniform t) reply)
  change Coverage.sampledType t reply = ArithmeticModel.sampledType t reply
  unfold Coverage.sampledType ArithmeticModel.sampledType
  split <;> rfl

/-- A conservative syntactic bound on the row table. No nested collection row is implemented. -/
def respectsPointStructure : Standard.RowKey → Bool
  | .inl (.group .add (.group .g1)) | .inl (.group .scale (.group .g1)) |
    .inl (.group .equal (.group .g1)) => true
  | .inl (.group ..) | .inl (.seq _ (.atom (.group _)) _) |
    .inl (.seq _ (.sized ..) _) | .inl .pair | .inr _ => false
  | .inl (.field ..) | .inl (.hash _) | .inl (.seq _ (.atom (.field _)) _) => true

theorem row_respectsPointStructure (k : Standard.RowKey) : StandardModel.interprets k = true → respectsPointStructure k = true := by
  cases k with
  | inr j => intro h; contradiction
  | inl k =>
    cases k with
    | field | hash => exact fun _ => rfl
    | pair => intro h; contradiction
    | group r a =>
      cases r <;> cases a with
        | field f => cases f <;> decide
        | group g => cases g <;> decide
    | seq r item size =>
      cases item with
      | sized => cases r <;> intro h <;> contradiction
      | atom a =>
        cases a with
        | field f => exact fun _ => rfl
        | group g => cases r <;> intro h <;> contradiction


/-- Coverage belongs to the protocol and relation of one goal in the stored program. -/
def covers (p : NamedProgram Standard) (root relation : Key) : Bool :=
  (Coverage.missing (b := ⟨[], by decide⟩) p root relation).isNone

/-- For unambiguous stored keys, every row reached from either entry respects point structure. -/
theorem covered_rows {p : NamedProgram Standard} {root relation : Key}
    (covered : covers p root relation = true) (distinct : (p.definitions.map Definition.key).Nodup)
    {d : Definition Standard} (stored : d ∈ p.definitions) (path : Coverage.Reachable p root relation d.key)
    {k : Standard.RowKey} (row : k ∈ d.rows) : respectsPointStructure k = true := by
  have ok := Option.isNone_iff_eq_none.mp covered
  have member := (Coverage.closed_of_missing ok).mem_of_reachable
    (fun _ hd _ he => List.inj_on_of_nodup_map distinct hd he) stored path
  apply row_respectsPointStructure
  rw [StandardModel.interprets_iff_arm D, ← interpreted_iff_arm]
  exact Coverage.interpreted_of_missing ok k (List.mem_flatMap.mpr ⟨d, member, row⟩)

end ZkcFormal.Written.StandardInterpretation
