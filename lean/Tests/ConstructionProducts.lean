module

public import Zkc.Construction.ConnectionCalculations

@[expose] public section

/-! Nominal records use the existing structured product meaning. Field order
is observable even when every field has the same type; host carrier equality
cannot erase the nominal product identity. -/
namespace Tests.ConstructionProducts
open Zkc.Source Zkc.Source.Structured Zkc.Construction

/-- Construction uses the shared packing operation for every field tuple. -/
theorem make_fields (model : DomainModel) (identity constructor : String)
    (fields : ProductFields) (values : Values model.Value fields.toList) :
    ConnectionCalculations.closedCalculation model (.makeProduct identity constructor fields) values =
      .done (.cons (fields.pack values) .nil) := rfl

/-- One law covers every projection position and every heterogeneous record. -/
theorem get_made (model : DomainModel) (identity constructor : String)
    (fields : ProductFields) (ty : Ty) (field : Var fields.toList ty)
    (values : Values model.Value fields.toList) :
    ConnectionCalculations.closedCalculation model (.getProduct identity constructor fields ty field)
        (.cons (fields.pack values) .nil) = .done (.cons (values.get field) .nil) := by
  change (PIR.Process.done (Values.cons ((fields.unpack (fields.pack values)).get field) .nil) :
    PIR.Process closedInterface (Values model.Value [ty])) = _
  rw [ProductFields.unpack_pack]
  rfl

def fields : ProductFields := .cons .index (.cons .index .nil)

def recordValue (model : DomainModel) : Domain.Value model.toCarriers :=
  .data ⟨.product "reference" "Record" fields, rfl, (5, 9, PUnit.unit)⟩

theorem ordered_fields (model : DomainModel) :
    Domain.calculate model (.getProduct "reference" "Record" fields .index .here) [recordValue model] =
        .returned [.data (.index 5)] ∧
    Domain.calculate model (.getProduct "reference" "Record" fields .index (.there .here))
        [recordValue model] = .returned [.data (.index 9)] := by
  constructor <;> rfl

theorem other_nominal_product_refused (model : DomainModel) :
    Domain.calculate model (.getProduct "other-reference" "Record" fields .index .here)
        [recordValue model] = .stopped .refused := rfl

theorem other_constructor_refused (model : DomainModel) :
    Domain.calculate model (.getProduct "reference" "Other" fields .index .here)
        [recordValue model] = .stopped .refused := rfl

#print axioms get_made
#print axioms ordered_fields
#print axioms other_nominal_product_refused
end Tests.ConstructionProducts
