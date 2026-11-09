module

public import Zkc.IR.Source.Structured.UnitViews
public import Zkc.Verification.Installations.Sumcheck.Source.HelperBridge
public import Zkc.Verification.Installations.Sumcheck.Source.MathematicalHelpers
public import Zkc.Verification.Installations.Multilinear.Source.MapPrefixContracts
import Zkc.IR.Source.Structured.CollectionReference

@[expose] public section
namespace ZkcExamples.Structured.SumcheckUnitContracts
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary MapFirstLaws MapPrefixBodies
open SumcheckHelperBodies SumcheckHelperLaws
open Zkc.Polynomial Zkc.Polynomial.Multilinear

/-! Helper contracts shared by the imported Sumcheck source and reduction
units. A unit supplies its own linked declaration list and the associations of
its actual members with the shared typed bodies; the laws below then hold for
that unit's own closed table. No unit's meanings are equated with another
unit's table. -/

/-- Associations of a unit's actual declarations with the shared helper bodies. -/
structure Bodies (definitions : List CheckedDefinition) : Prop where
  first : ∃ bindings, MapFirstContracts.Bodies definitions bindings
  sums : BodyIn definitions sumsHelper sumsBody
  empty : BodyIn definitions emptyHelper emptyBody
  append : BodyIn definitions appendHelper appendBody
  values : BodyIn definitions MapFirstBodies.valuesHelper MapFirstBodies.valuesBody
  width : BodyIn definitions MapFirstBodies.widthHelper MapFirstBodies.widthBody
  «variables» : BodyIn definitions MapFirstBodies.variablesHelper MapFirstBodies.variablesBody

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]
section Laws
variable {definitions : List CheckedDefinition} (linked : DeclarationsLinked [] definitions)
  (bodies : Bodies definitions)
include linked bodies

theorem first_laws : MapFirstContracts.Laws (closedMeanings (F := F) (G := G) definitions) :=
  bodies.first.elim fun bindings associations =>
    ⟨MapFirstContracts.less_all linked associations,
      MapFirstContracts.halves_equation linked associations,
      MapFirstContracts.shape_equation linked associations,
      MapFirstContracts.table_equation linked associations, by
        intro xs dimension columns challenge shape bound
        rw [(SumcheckMathematicalHelpers.firstLaw (F := F) (G := G) bindings).invokeUniform
          definitions linked associations.first (firstInputs xs dimension columns challenge)
          ⟨MapFirstContracts.halves_equation linked associations,
            MapFirstContracts.map_law linked associations, shape, bound⟩]
        exact SumcheckMathematicalHelpers.first_reference_eq bindings xs dimension columns challenge⟩

theorem halves_body : HalvesBodyLaw (closedMeanings (F := F) (G := G) definitions) :=
  bodies.first.elim fun _ associations =>
    fun xs dimension columns => associations.halves.invoke linked (inputs xs dimension columns)

theorem shape_body : ShapeBodyLaw (closedMeanings (F := F) (G := G) definitions) :=
  bodies.first.elim fun _ associations =>
    fun xs dimension columns => associations.shape.invoke linked (inputs xs dimension columns)

/-- Full raw-input contract, with no width or vector-length admission invented. -/
theorem sums_all (xs : List F) (dimension columns : Nat) :
    invoke (closedMeanings (G := G) definitions) sumsHelper (inputs xs dimension columns) =
      if dimension < indexLimit then
        if 0 < dimension then
          if 0 < xs.length ∧ xs.length % 2 = 0 then
            .done (messageResult (xs.take (xs.length / 2)).sum (xs.drop (xs.length / 2)).sum)
          else .halt .refused
        else .halt .reject
      else .halt .refused := by
  rw [(SumcheckMathematicalHelpers.sumsLaw (F := F) (G := G)).invokeUniform
    definitions linked bodies.sums (inputs xs dimension columns)
    ⟨(first_laws linked bodies).less, halves_body linked bodies⟩]
  exact SumcheckMathematicalHelpers.reference_eq xs dimension columns

theorem sums_honestMessage {n : Nat} (xs : List F) (table : Table F (n + 1))
    (columns : Nat) (decoded : ofList? (n + 1) xs = some table)
    (dimensionBound : n + 1 < indexLimit) :
    invoke (closedMeanings (G := G) definitions) sumsHelper (inputs xs (n + 1) columns) =
      .done (messageResult (Zkc.Protocols.Sumcheck.Multilinear.honestMessage table).1
        (Zkc.Protocols.Sumcheck.Multilinear.honestMessage table).2) := by
  rw [sums_all linked bodies xs (n + 1) columns]
  simp only [dimensionBound, Nat.zero_lt_succ,
    Zkc.Protocols.Sumcheck.Multilinear.decoded_split xs table decoded, ite_true]
  change PIR.Process.done (messageResult
    (Zkc.Protocols.Sumcheck.Multilinear.endpoints xs).1
    (Zkc.Protocols.Sumcheck.Multilinear.endpoints xs).2) = _
  rw [Zkc.Protocols.Sumcheck.Multilinear.endpoints_honestMessage xs table decoded]

theorem empty_equation :
    invoke (closedMeanings (F := F) (G := G) definitions) emptyHelper .nil = .done (.cons [] .nil) :=
  (bodies.empty.invoke linked .nil).trans (empty_body _)

theorem append_equation (xs : List F) (x : F) :
    invoke (closedMeanings (G := G) definitions) appendHelper (.cons xs (.cons x .nil)) =
      .done (.cons (xs ++ [x]) .nil) :=
  (bodies.append.invoke linked (.cons xs (.cons x .nil))).trans (append_body _ xs x)

theorem values_equation (xs : List F) (dimension columns : Nat) :
    invoke (closedMeanings (G := G) definitions) MapFirstBodies.valuesHelper
      (inputs xs dimension columns) = .done (.cons xs .nil) :=
  (bodies.values.invoke linked (inputs xs dimension columns)).trans
    (MapSourceExpansions.first_values _ xs dimension columns)

theorem width_equation (xs : List F) (dimension columns : Nat) :
    invoke (closedMeanings (G := G) definitions) MapFirstBodies.widthHelper
      (inputs xs dimension columns) = .done (.cons columns .nil) :=
  (bodies.width.invoke linked (inputs xs dimension columns)).trans
    (MapSourceExpansions.first_width _ xs dimension columns)

theorem variables_equation (xs : List F) (dimension columns : Nat) :
    invoke (closedMeanings (G := G) definitions) MapFirstBodies.variablesHelper
      (inputs xs dimension columns) = .done (.cons dimension .nil) :=
  (bodies.«variables».invoke linked (inputs xs dimension columns)).trans
    (MapSourceExpansions.first_variables _ xs dimension columns)

end Laws

/-- The projection preserves its selected optional component without demanding other operands. -/
theorem width_components {unit : UnitPayload} (bodies : Bodies unit.definitions)
    (xs : Option (List F)) (dimension : Option Nat) (columns : Option Nat) :
    invoke (unit.tables F G).components MapFirstBodies.widthHelper
      (.cons xs (.cons dimension (.cons columns .nil))) = .done (.cons columns .nil) :=
  (unit.component_body_of_bodyIn bodies.width _).trans (by rfl)

/-- The projection preserves its selected optional component without demanding other operands. -/
theorem variables_components {unit : UnitPayload} (bodies : Bodies unit.definitions)
    (xs : Option (List F)) (dimension : Option Nat) (columns : Option Nat) :
    invoke (unit.tables F G).components MapFirstBodies.variablesHelper
      (.cons xs (.cons dimension (.cons columns .nil))) = .done (.cons dimension .nil) :=
  (unit.component_body_of_bodyIn bodies.«variables» _).trans (by rfl)

/-- The projection preserves its selected optional component without demanding other operands. -/
theorem values_components {unit : UnitPayload} (bodies : Bodies unit.definitions)
    (xs : Option (List F)) (dimension : Option Nat) (columns : Option Nat) :
    invoke (unit.tables F G).components MapFirstBodies.valuesHelper
      (.cons xs (.cons dimension (.cons columns .nil))) = .done (.cons xs .nil) :=
  (unit.component_body_of_bodyIn bodies.values _).trans (by rfl)

theorem empty_plain {unit : UnitPayload} (bodies : Bodies unit.definitions) :
    (invoke (unit.tables F G).closed emptyHelper .nil).interpret forgetSites =
      .done (.cons [] .nil) := by
  rw [unit.closed_invoke_forgetSites, empty_equation unit.linked bodies]
  rfl

theorem append_plain {unit : UnitPayload} (bodies : Bodies unit.definitions) (xs : List F) (x : F) :
    (invoke (unit.tables F G).closed appendHelper (.cons xs (.cons x .nil))).interpret forgetSites =
      .done (.cons (xs ++ [x]) .nil) := by
  rw [unit.closed_invoke_forgetSites, append_equation unit.linked bodies]
  rfl

end ZkcExamples.Structured.SumcheckUnitContracts
