module

public import Zkc.Source.Structured.Format

@[expose] public section

/-! Exact type serialization shared by inspection, execution and discovery. -/
namespace ZkcTools.StructuredSource
open Lean Zkc.Source.Structured

mutual
  def wireType : Ty → Json
    | .boolean => .arr #[.str "bool"]
    | .index => .arr #[.str "index"]
    | .field domain => .arr #[.str "field", .str domain]
    | .vector domain => .arr #[.str "vector", .str domain]
    | .group domain => .arr #[.str "group", .str domain]
    | .service contract => .arr #[.str "service", .str contract]
    | .sequence element => .arr #[.str "sequence", wireType element]
    | .product identity constructor fields =>
      .arr #[.str "product", .str identity, .str constructor, .arr (wireFields fields).toArray]
  def wireFields : ProductFields → List Json
    | .nil => []
    | .cons type rest => wireType type :: wireFields rest
end

end ZkcTools.StructuredSource
