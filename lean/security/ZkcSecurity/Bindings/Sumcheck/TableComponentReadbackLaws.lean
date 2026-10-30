module

public import Zkc.Construction.DomainCalculations

@[expose] public section

/-! Pure calculation law used by table component readback. -/
namespace ZkcSecurity.Families.Sumcheck.TableComponent.Execution
open Zkc.Source.Structured Zkc.Construction

theorem booleanAnd {F G : Type} [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] (left right : Bool) :
    Domain.calculate (ringModel F G) .booleanAnd
      [.data (.boolean left), .data (.boolean right)] =
      .returned [.data (.boolean (left && right))] := rfl

end ZkcSecurity.Families.Sumcheck.TableComponent.Execution
