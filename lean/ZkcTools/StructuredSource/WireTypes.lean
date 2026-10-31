module

public import Zkc.Source.Structured.Format

@[expose] public section

/-! Exact type serialization shared by inspection, execution and discovery. -/
namespace ZkcTools.StructuredSource
open Lean Zkc.Source Zkc.Source.Structured

/-- Invert the existing internal atom/string and tuple/array identity encoding.
Only the canonical encoding emitted by `LogicalFormat.identity` is representable;
malformed internal text must never become a newly invented nominal atom. -/
def wireIdentityAt : Nat → Json → Except String Json
  | 0, _ => .error "structured-identity-depth"
  | _ + 1, .str value => do
    discard <| LogicalFormat.text (.str value)
    return .arr #[.str "atom", .str value]
  | depth + 1, .arr children => do
    let children ← (← LogicalFormat.array (.arr children)).mapM (wireIdentityAt depth)
    return .arr #[.str "tuple", .arr children.toArray]
  | _, _ => .error "structured-identity"

def wireIdentity (value : String) : Except String Json := do
  discard <| Structured.Format.string (.str value)
  LogicalFormat.checkUnicodeEscapes value
  let json ← Json.parse value
  LogicalFormat.checkWork json
  let identity ← wireIdentityAt 64 json
  unless (← LogicalFormat.identity identity) == value do throw "structured-identity"
  return identity

def wireApplication (constructor : String) (arguments : Array Json := #[]) : Json :=
  .arr #[.str "apply", .str constructor, .arr arguments]

def wireDomainApplication (constructor sort domain : String) : Json :=
  wireApplication constructor #[.arr #[.str "domain", .str sort, .str domain]]

mutual
  def wireType : Ty → Json
    | .boolean => wireApplication "bool"
    | .index => wireApplication "index"
    | .indices => wireApplication "indices"
    | .field domain => wireDomainApplication "field" "Field" domain
    | .vector domain => wireDomainApplication "vector" "Field" domain
    | .group domain => wireDomainApplication "group" "Group" domain
    | .groups domain => wireDomainApplication "groups" "Group" domain
    | .oracle (.table row rows) => .arr #[.str "oracle", .str "table", wireOracleArguments row rows]
    | .oracleSequence (.table row rows) maximum =>
      .arr #[.str "oracle_sequence", .str "table", wireOracleArguments row rows, .str (toString maximum)]
    | .service contract => .arr #[.str "service", .str contract]
    | .sequence element => wireApplication "sequence" #[.arr #[.str "type", wireType element]]
    | .product identity constructor fields =>
      -- Null is deliberately not an identity: an invalid internal encoding
      -- produces a refused tree, never an alternate nominal interpretation.
      let nominal := match wireIdentity identity with | .ok value => value | .error _ => .null
      .arr #[.str "variant", nominal,
        .arr #[.arr #[.str constructor, .arr (wireFields fields).toArray]]]
  def wireOracleKind : OracleKind → Json
    | .table row rows => .arr #[.str "table", wireOracleArguments row rows]
  def wireOracleArguments (row : Ty) (rows : Option Nat) : Json :=
    .arr (#[.arr #[.str "type", wireType row]] ++
      match rows with
      | none => #[]
      | some count => #[.arr #[.str "nat", .str (toString count)]])
  def wireFields : ProductFields → List Json
    | .nil => []
    | .cons type rest => wireType type :: wireFields rest
end

end ZkcTools.StructuredSource
