module

public import Zkc.Source.Structured.Vocabulary

@[expose] public section

/-! Structural type properties independent of source admission or evaluation.
These predicates classify complete nominal types; they grant no codec or provider. -/
namespace Zkc.Source.Structured

mutual
  def Ty.isService : Ty → Bool
    | .service _ => true
    | .sequence element => element.isService
    | .product _ _ fields => fields.hasService
    | _ => false
  def ProductFields.hasService : ProductFields → Bool
    | .nil => false
    | .cons type rest => type.isService || rest.hasService
end

mutual
  /-- Logical handles cannot acquire ordinary Math, message or codec rights
  through a type added to the wire vocabulary. A custody permission is not a
  payload either: it is never selected, packed, transmitted or encoded. -/
  def Ty.isHandle : Ty → Bool
    | .service _ | .oracle _ | .oracleSequence .. | .resourceUnit _ => true
    | .sequence element => element.isHandle
    | .product _ _ fields => fields.hasHandle
    | _ => false
  def ProductFields.hasHandle : ProductFields → Bool
    | .nil => false
    | .cons type rest => type.isHandle || rest.hasHandle
end

mutual
  /-- Polynomial values may be computed locally, but have no common-value wire codec. -/
  def Ty.containsPolynomial : Ty → Bool
    | .polynomial _ => true
    | .sequence element => element.containsPolynomial
    | .product _ _ fields => fields.containsPolynomial
    | _ => false
  def ProductFields.containsPolynomial : ProductFields → Bool
    | .nil => false
    | .cons type rest => type.containsPolynomial || rest.containsPolynomial
end

/-- A custody permission: a nominal resource unit of one exact slot. -/
def Ty.isCustody : Ty → Bool
  | .resourceUnit _ => true
  | _ => false

/-- A logical handle other than a custody permission. -/
def Ty.isForeignHandle (ty : Ty) : Bool := ty.isHandle && !ty.isCustody

/-- Logical protocol families have structural transport, independently of closed Math
values, services and affine custody. This predicate grants no wire codec. -/
def Ty.isOracleFamily : Ty → Bool
  | .oracle _ | .oracleSequence .. => true
  | _ => false

-- Materialize the type-property equations in their defining module. Lazy generation
-- in independent clients can produce different stored proofs for the same
-- equation name; declaration provenance must have a single checked owner.
section
attribute [local simp] Ty.isService ProductFields.hasService Ty.isHandle ProductFields.hasHandle Ty.isCustody Ty.containsPolynomial ProductFields.containsPolynomial
end

end Zkc.Source.Structured
