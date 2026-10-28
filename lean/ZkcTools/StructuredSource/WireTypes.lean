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
    | .indices => .arr #[.str "indices"]
    | .field domain => .arr #[.str "field", .str domain]
    | .vector domain => .arr #[.str "vector", .str domain]
    | .group domain => .arr #[.str "group", .str domain]
    | .groups domain => .arr #[.str "groups", .str domain]
    | .oracle kind => .arr #[.str "oracle", wireOracleKind kind]
    | .oracleSequence kind maximum =>
      .arr #[.str "oracle_sequence", wireOracleKind kind, .str (toString maximum)]
    | .service contract => .arr #[.str "service", .str contract]
    | .sequence element => .arr #[.str "sequence", wireType element]
    | .product identity constructor fields =>
      .arr #[.str "product", .str identity, .str constructor, .arr (wireFields fields).toArray]
  def wireOracleKind : OracleKind → Json
    | .table row rows =>
      .arr #[.str "table", .arr (#[.arr #[.str "type", wireType row]] ++
        match rows with
        | none => #[]
        | some count => #[.arr #[.str "nat", .str (toString count)]])]
  def wireFields : ProductFields → List Json
    | .nil => []
    | .cons type rest => wireType type :: wireFields rest
end

/-- Diagnostic logical identities only. They are not message codecs or
user-authorized constructors of oracle handles. -/
def wireOracleAnchor (value : OracleAnchor) : Json :=
  let nats := fun values : List Nat => .arr (values.map toJson).toArray
  let frames := value.invocation.frames.map fun frame => match frame with
    | .application caller position => .arr #[.str "application", toJson caller, nats position]
    | .iteration owner position index => .arr #[.str "iteration", toJson owner, nats position, toJson index]
  let site := match value.site with
    | .input port => .arr #[.str "input", toJson port]
    | .construction position => .arr #[.str "construction", nats position]
  .arr #[.str "oracle_anchor", toJson value.invocation.root, .arr frames.toArray, site]

end ZkcTools.StructuredSource
