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

theorem covered_rows {p : NamedProgram Standard} {root relation : Key}
    (covered : covers p root relation = true) :
    ∀ k ∈ (NamedProgram.mk (Coverage.reach p root relation).2).rows, respectsPointStructure k = true := by
  intro k member
  apply row_respectsPointStructure
  rw [StandardModel.interprets_iff_arm D, ← interpreted_iff_arm]
  unfold covers Coverage.missing at covered
  generalize Coverage.reach p root relation = reached at *
  rcases reached with ⟨keys, defs⟩
  simp only at covered member
  split at covered
  · contradiction
  · split at covered
    · contradiction
    · rename_i absent
      have noRow : (NamedProgram.mk defs).rows.find? (!Coverage.interpreted ·) = none :=
        Option.eq_none_iff_forall_ne_some.mpr absent
      simpa using List.find?_eq_none.mp noRow k member

end ZkcFormal.Written.StandardInterpretation
