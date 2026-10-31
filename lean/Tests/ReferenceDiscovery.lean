module

public import ZkcTools.StructuredSource.Discovery.Json

@[expose] public section

/-! Narrow controls for the untrusted search and exact kernel selection seam. -/

namespace Tests.ReferenceDiscovery
open Zkc.Source Zkc.Source.Structured ZkcTools.StructuredSource.Discovery

/-- Discovery preserves both table and prefix operands and the restricted table result. -/
example : opJson (.multilinearRestrictPrefix "bls12-381.fr") = Lean.Json.mkObj [
    ("constructor", Lean.toJson "multilinearRestrictPrefix"),
    ("arguments", Lean.toJson ([Lean.Json.arr #[.str "apply", .str "vector",
      .arr #[.arr #[.str "domain", .str "Field", .str "bls12-381.fr"]]],
      Lean.Json.arr #[.str "apply", .str "vector",
      .arr #[.arr #[.str "domain", .str "Field", .str "bls12-381.fr"]]]] : List Lean.Json)),
    ("results", Lean.toJson ([Lean.Json.arr #[.str "apply", .str "vector",
      .arr #[.arr #[.str "domain", .str "Field", .str "bls12-381.fr"]]]] : List Lean.Json)),
    ("helpers", Lean.toJson ([] : List String)), ("parameters", .null)] := by
  simp only [opJson, Op.arguments, Op.results, Op.helpers, List.map_cons, List.map_nil,
    ZkcTools.StructuredSource.wireType.eq_5, ZkcTools.StructuredSource.wireDomainApplication,
    ZkcTools.StructuredSource.wireApplication]

private def raw : RawRegion Ty Op :=
  .letOp (.fieldAdd "bls12-381.fr") [0, 1] [.field "bls12-381.fr"] .nil
    (.ret [0])

example : regionAt raw [] = some raw := rfl
example : regionAt raw [1] = some (.ret [0]) := rfl
example : regionAt raw [0] = none := rfl
example : regionAt raw [2, 0] = none := rfl
example : regionAt raw [1, 1] = none := rfl

private def source : Address := ⟨"sha256:source", "helper", [], .operand 0⟩
private def swapped : Address := { source with coordinate := .operand 1 }
example : source ≠ swapped := by decide
example : ({ source with region := [2, 0] } : Address) ≠ source := by decide
example : ({ source with snapshot := "sha256:changed" } : Address) ≠ source := by decide

private def emptyView : View := { snapshot := "sha256:source", entry := "root", arm := .verifier, role := 1 }
example : (discover emptyView).status = "unresolved" := rfl
example : (discover emptyView 0).reasons = ["search-timeout"] := rfl
example : (helperFeatures emptyView 32 "unknown").unknown = true := rfl
example : (helperFeatures emptyView 0 "unknown").unknown = true := rfl
example : allowed .verifier 1 [0] = false := rfl
example : allowed .verifier 1 [1] = true := rfl
example : allowed .joint 1 [0] = true := rfl
example : (manual []).status = "unresolved" := rfl
example : (proposeLoop emptyView { address := source, tag := "repeat" }).status =
    "unresolved" := rfl

/-- Same names and types cannot prove an operand permutation equation. -/
private def arguments : RawRegion Ty Op → List Nat
  | .letOp _ arguments _ _ _ => arguments
  | _ => []

example : arguments raw = [0, 1] := rfl

/-- A lookup equation is not permission to discard the supplied law. -/
example {program : Program} {address : Address} {expected : CheckedDefinition} {law : Prop}
    (association : HelperAssociation program address expected law) : law := association.checkedLaw

end Tests.ReferenceDiscovery
