module

public import ZkcExamples.Structured.SumcheckReduceAssociations
public import ZkcExamples.Structured.SumcheckUnitContracts

@[expose] public section
namespace ZkcExamples.Structured.SumcheckReduceContracts
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary MapFirstLaws
open SumcheckHelperBodies SumcheckHelperLaws SumcheckReduceAssociations
open SumcheckReduceViews (unit)
open Zkc.Polynomial Zkc.Polynomial.Multilinear

/-! The shared Sumcheck helper contracts at this unit's own members. -/

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The closed-site fold of this complete original unit's own helper list. -/
abbrev helperMeanings : Meanings F G := closedMeanings unit.definitions

theorem bodies : SumcheckUnitContracts.Bodies unit.definitions :=
  ⟨⟨_, first_bodies⟩, sums_association, empty_association, append_association, values_association,
    width_association, variables_association⟩

theorem first_laws : MapFirstContracts.Laws (helperMeanings (F := F) (G := G)) :=
  SumcheckUnitContracts.first_laws unit.linked bodies

theorem sums_all (xs : List F) (dimension columns : Nat) :
    invoke (helperMeanings (G := G)) sumsHelper (inputs xs dimension columns) =
      if dimension < indexLimit then
        if 0 < dimension then
          if 0 < xs.length ∧ xs.length % 2 = 0 then
            .done (messageResult (xs.take (xs.length / 2)).sum (xs.drop (xs.length / 2)).sum)
          else .halt .refused
        else .halt .reject
      else .halt .refused :=
  SumcheckUnitContracts.sums_all unit.linked bodies xs dimension columns

theorem sums_honestMessage {n : Nat} (xs : List F) (table : Table F (n + 1))
    (columns : Nat) (decoded : ofList? (n + 1) xs = some table)
    (dimensionBound : n + 1 < indexLimit) :
    invoke (helperMeanings (G := G)) sumsHelper (inputs xs (n + 1) columns) =
      .done (messageResult (Zkc.Protocols.Sumcheck.Multilinear.honestMessage table).1
        (Zkc.Protocols.Sumcheck.Multilinear.honestMessage table).2) :=
  SumcheckUnitContracts.sums_honestMessage unit.linked bodies xs table columns decoded dimensionBound

end ZkcExamples.Structured.SumcheckReduceContracts
