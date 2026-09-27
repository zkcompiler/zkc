import Tools.Interactive.PhysicalLocal
import Tests.Checks

/-! Focused independent structural-type controls. Run with:
`lake build Tests.StructuralTypes`.
These are finite executable controls, not a cross-language adequacy proof. -/

set_option autoImplicit false
namespace Tests.StructuralTypes
open Tools.Interactive Zkc.Source.Requirements
open Lean (Json)

private def fixed (element : String) (n : Nat) : String :=
  s!"fixed_vector<{element},{n}>"

private def field (identity : String := Bindings.koalaBear) := "field:" ++ identity

private def wrapVariant (payload : List String) (nominal : String := "choice") : String :=
  (Variant.Descriptor.mk (.str nominal) [("item", payload)]).spelling

private def wrap (f : String → String) (count : Nat) (leaf : String) : String :=
  (List.range count).foldl (fun value _ => f value) leaf

private def code {α : Type} : Result α → Option String
  | .ok _ => none | .error error => some error

private def get {α : Type} (value : Result α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

private def binding (contract : String) (n : Nat) (identity : String := Bindings.koalaBear)
    (physical : Bool := false) : OperationBinding :=
  ⟨contract, contract, [identity, toString n], if physical then "plonky3/" ++ contract else ""⟩

private def function (n : Nat) (identity : String := Bindings.koalaBear) : Explicit.Function :=
  ⟨⟨"FixedVector", [("x", "vector:" ++ identity), ("y", "vector:" ++ identity)],
    ["vector:" ++ identity, "field:" ++ identity], some [
      .op "left" "fixed_vector.from_vector" [] ["x"] ["a"],
      .op "right" "fixed_vector.from_vector" [] ["y"] ["b"],
      .op "dot" "fixed_vector.dot" [] ["a", "b"] ["result"],
      .op "convert" "fixed_vector.to_vector" [] ["a"] ["restored"],
      .ret ["restored", "result"]]⟩, some ⟨"FixedVector", [("N", toString n)]⟩⟩

private def contracts : List String :=
  ["fixed_vector.from_vector", "fixed_vector.to_vector", "fixed_vector.dot"]

private def execute (n : Nat) (left right : List Nat)
    (domain : ScalarReference.Domain := .koalaBear) : Result Json := do
  let bindings := contracts.map fun contract => binding contract n domain.identity
  let function ← TypedLocal.elaborate bindings (function n domain.identity)
  let values := [left, right].map fun xs => Reference.Value.fromArithmetic domain
    (.vector (xs.map fun n => (n : ScalarReference.Scalar domain)))
  let (outcome, _) := (Reference.executeFunction (Reference.Location.plain "test" "root" "fixed" "P") function values).run {}
  match outcome with
  | .ok values => return Reference.valuesJson values
  | .error fault => throw fault.detail

private def expected (left : List Nat) (dot : Nat) : Json :=
  .arr #[.arr #[.str "vector:koala-bear", .arr (left.map fun n => Json.str (toString n)).toArray],
    .arr #[.str "field:koala-bear", .str (toString dot)]]

private def genericText := r#"[
  "generic_function", "Fixed", [["F","Field"],["N","Nat"]], [["Field",["F"]]],
  [["x","vector:F"],["y","vector:F"]], ["vector:F","field:F"], [
    ["op","left","fixed_vector.from_vector",["F","N"],[],["x"],["a"]],
    ["op","right","fixed_vector.from_vector",["F","N"],[],["y"],["b"]],
    ["op","dot","fixed_vector.dot",["F","N"],[],["a","b"],["result"]],
    ["op","convert","fixed_vector.to_vector",["F","N"],[],["a"],["restored"]],
    ["return",["restored","result"]]]]"#

def run : IO Unit := do
  let checks ← Tests.Checks.start
  let admitted := ["bool", "index", "indices", field, field Bindings.fr,
    "vector:koala-bear", "vector:bls12-381.fr", "transcript:" ++ Bindings.transcriptIdentity,
    fixed field 0, fixed field 4, fixed field Logical.naturalLimit,
    fixed (field Bindings.fr) 4, fixed "bool" 0, fixed (fixed field 4) 2,
    wrapVariant [fixed field 4, "bool"], fixed (wrapVariant [field]) 4]
  for text in admitted do
    let parsed := Bindings.valueType false text
    checks.holds ((parsed.toOption.map (·.spelling)) == some text) ("canonical roundtrip: " ++ (text.take 100).toString)
    checks.holds ((parsed.toOption.bind fun ty => (Bindings.valueType false ty.spelling).toOption) == parsed.toOption)
      "parse-print-parse structural identity"
  let malformed := ["bool:", "field<koala-bear>", "fixed_vector<field<koala-bear>,4>",
    "fixed_vector<field:koala-bear,04>", "fixed_vector<field:koala-bear,-1>",
    "fixed_vector<field:koala-bear,+1>", "fixed_vector<field:koala-bear,0x4>",
    "fixed_vector<field:koala-bear,1048577>", "fixed_vector<field:koala-bear,99999999999999999999>",
    "fixed_vector<field:koala-bear, 4>", "fixed_vector<field:koala-bear,4> ",
    "fixed_vector<field:koala-bear,4\n>", "fixed_vector<field:koala-bear,４>",
    "fixed_vector<field:koala-bear,>", "fixed_vector<,4>", "fixed_vector<field:koala-bear,4,5>",
    "fixed_vector<field:koala-bear,4", "fixed_vector<field:koala-bear,4>>", "fixed_vector<>",
    "fixed_vector:field:koala-bear,4", "fixed_vector<koala-bear,4>", "fixed_vector<field:unknown,4>",
    "fixed_vector<field:koala-bear@plonky3.koala-bear/1,4>",
    "unknown<field:koala-bear,4>", "fixed_vector<unknown:koala-bear,4>"]
  for text in malformed do
    checks.holds (!(Bindings.valueType false text).isOk) ("malformed: " ++ text)
    checks.holds (!(Logical.permissions text).copy && !(Logical.permissions text).isPublic)
      "malformed spelling grants no ground copy or codec"
  for text in ["0", "1", "1048576"] do
    checks.holds ((Logical.natural text).isOk) "canonical Nat boundary"
  for text in ["", "00", "01", "1048577", "1.0", "1e2", "-0", " 0"] do
    checks.holds (!(Logical.natural text).isOk) "malformed or oversized Nat"
  let a ← get (Bindings.valueType false (fixed field 4))
  let b ← get (Bindings.valueType false (fixed field 5))
  let c ← get (Bindings.valueType false (fixed (field Bindings.fr) 4))
  checks.holds (a != b && a != c && a.identity.isEmpty) "Nat and nested element identities are retained separately"
  checks.holds (a.arguments == [.type (.atom "field" Bindings.koalaBear), .natural 4]) "kinded ground arguments"
  checks.holds (!((Bindings.ValueType.mk "fixed_vector" "field:koala-bear,4").valid false)) "no fake domain identity"
  checks.holds (!((Bindings.ValueType.ofParts "fixed_vector" "" "" [.domain Bindings.koalaBear, .natural 4]).valid false))
    "constructed type must still satisfy installed kinds"
  checks.holds (duplicable a.spelling && discardable a.spelling && !affine a.spelling && !serializable a.spelling)
    "copyable element yields private immutable fixed vector"
  let affineElement := fixed ("nonce:" ++ Bindings.fr) 0
  checks.holds ((Bindings.valueType false affineElement).isOk && !duplicable affineElement &&
    !discardable affineElement && affine affineElement) "zero length does not erase element permissions"
  let droppableElement := fixed "resource_unit:Trace" 4
  checks.holds (!duplicable droppableElement && discardable droppableElement && affine droppableElement)
    "copy and drop are independently conjoined"
  let privateElement := fixed ("opening_state:" ++ Bindings.pcs) 4
  checks.holds (duplicable privateElement && discardable privateElement && !serializable privateElement)
    "private copyable element remains private"
  let alternatives := (Variant.Descriptor.mk (.str "either")
    [("copy", [field]), ("affine", ["nonce:" ++ Bindings.fr])]).spelling
  checks.holds (!duplicable (fixed alternatives 4) && !discardable (fixed alternatives 4))
    "every variant alternative contributes to nested permissions"
  checks.holds (Bindings.codec "fixed_vector" "" == "" && Bindings.codec "unknown" Bindings.koalaBear == "")
    "no constructor-prefix codec authority"
  checks.holds (code (Bindings.resolve false ⟨"observe", "transcript.observe.fixed_vector", [], ""⟩) == some "binding-contract")
    "fixed-vector transcript observation remains undeclared"
  checks.holds (code (Bindings.resolve false ⟨"unknown", "fixed_vector.unknown", [Bindings.koalaBear, "4"], ""⟩) == some "binding-contract")
    "unknown operation fails closed"
  let nested := wrap (fun s => fixed s 0) 8 field
  checks.holds ((Bindings.valueType false nested).isOk && !(Bindings.valueType false (fixed nested 0)).isOk)
    "eight application layers, not nine"
  let variants := wrap (fun s => wrapVariant [s]) 8 field
  checks.holds ((Bindings.valueType false variants).isOk && !(Bindings.valueType false (wrapVariant [variants])).isOk)
    "existing eight variant layers remain admitted"
  let mixed := wrapVariant [wrap (fun s => fixed s 0) 7 field]
  checks.holds ((Bindings.valueType false mixed).isOk && !(Bindings.valueType false (wrapVariant [mixed])).isOk)
    "variant and application nesting share one depth bound"
  let reverseMixed := fixed (wrap (fun s => wrapVariant [s]) 7 field) 0
  checks.holds ((Bindings.valueType false reverseMixed).isOk && !(Bindings.valueType false (fixed reverseMixed 0)).isOk)
    "depth bound also traverses variant arguments"
  checks.holds ((Logical.parseBudgeted 8 3 a.spelling).isOk &&
    code (Logical.parseBudgeted 8 2 a.spelling) == some "binding-type-nodes") "shared node budget without large workloads"
  let sized := fun n => fixed (wrapVariant [field] (String.ofList (List.replicate n 'x'))) 0
  let padding := 1 + (4096 - (sized 1).utf8ByteSize) / 2
  let atLimit := sized padding
  checks.holds (atLimit.utf8ByteSize == 4096 && (Bindings.valueType false atLimit).isOk)
    "4096-byte nonvariant spelling is admitted, including nested variant"
  checks.holds (code (Bindings.valueType false (sized (padding + 1))) == some "binding-type-limit")
    "nonvariant byte bound exceeded"
  checks.holds ((Bindings.valueType false (sized 300)).isOk && (sized 300).utf8ByteSize > 512)
    "no retained Lean 512-byte divergence"
  checks.holds (a.defaultRepresentation == "plonky3.fixed-vector/1" && c.defaultRepresentation.isEmpty)
    "realization selection uses full element identity"
  checks.holds ((Bindings.valueType true (a.spelling ++ "@plonky3.fixed-vector/1")).isOk)
    "KoalaBear fixed-vector physical spelling"
  checks.holds (code (Bindings.valueType true (c.spelling ++ "@plonky3.fixed-vector/1")) == some "binding-representation")
    "BLS formation succeeds but physical selection fails"
  checks.holds (code (Bindings.valueType true c.spelling) == some "binding-representation")
    "empty default is not physical support"
  checks.holds (!(Bindings.valueType true (a.spelling ++ "@plonky3.koala-bear-vector/1")).isOk)
    "fixed vectors do not reuse the dynamic-vector representation"
  checks.holds (!(Bindings.valueType true (a.spelling ++ "@plonky3.fixed-vector/1@extra")).isOk)
    "one outer representation only"
  for contract in contracts do
    checks.holds ((Bindings.resolve false (binding contract 4)).isOk) "logical operation signature"
    checks.holds ((Bindings.resolve false (binding contract 4 Bindings.fr)).isOk) "BLS logical operation signature"
    checks.holds ((Bindings.resolve true (binding contract 4 Bindings.koalaBear true)).isOk) "KoalaBear realization"
    checks.holds (PhysicalLocal.supported (binding contract 4 Bindings.koalaBear true) &&
      !PhysicalLocal.supported (binding contract 4 Bindings.fr true)) "physical interpreter uses exact installed realization"
    checks.holds (code (Bindings.resolve true (binding contract 4 Bindings.fr true)) == some "binding-implementation")
      "BLS implementation is unavailable"
    checks.holds (code (Bindings.attributes false contract ["4"]) == some "kernel-attributes") "no operation attributes"
  let sig ← get (Bindings.resolve false (binding "fixed_vector.from_vector" 4))
  let observation : Bindings.Declaration := ⟨"observe", "transcript.observe.field",
    [Bindings.extensionTranscript, Bindings.bn254Fr, Bindings.codec "field" Bindings.bn254Fr], ""⟩
  checks.holds ((Bindings.resolve false observation).isOk)
    "logical payload field is independent of transcript challenge field"
  checks.holds (!(Bindings.resolve false { observation with implementation :=
    "plonky3/transcript.observe.field" }).isOk)
    "explicit physical provider still checks its observation support"
  checks.holds (sig.inputs.map (·.spelling) == ["vector:koala-bear"] && sig.outputs.map (·.spelling) == [a.spelling])
    "one nominal bulk output port"
  checks.holds ((execute 2 [1, 2] [3, 4]).toOption == some (expected [1, 2] 11)) "hand-computed dot and reverse conversion"
  checks.holds ((execute 2 [Bindings.koalaBearModulus - 1, 2] [2, 3]).toOption ==
    some (expected [Bindings.koalaBearModulus - 1, 2] 4)) "modular dot independently computed"
  checks.holds ((execute 0 [] []).toOption == some (expected [] 0)) "zero-length conversion and empty dot"
  checks.holds (code (execute 2 [1] [3, 4]) == some "fixed-vector-length") "short input length refuses at execution"
  checks.holds (code (execute 2 [1, 2, 3] [3, 4]) == some "fixed-vector-length") "long input length refuses at execution"
  checks.holds (code (execute 0 [1] []) == some "fixed-vector-length") "zero-length exactness"
  checks.holds (code (execute 2 [1, 2] [3, 4] .bls) == some "reference-fixed-vector-not-supported")
    "known logical type refuses at interpretation, not formation"
  let value ← get (FixedVectorReference.admit (.atom "field" Bindings.koalaBear) 2 [1, 2])
  let privateValue := Reference.Value.fixedVector value
  checks.holds (privateValue.ty.spelling == fixed field 2 && !privateValue.public &&
    code privateValue.wire == some "nonserializable-message") "private value has full identity and no wire codec"
  checks.holds ((Reference.typedValues [value.ty] [privateValue]).isOk &&
    !(Reference.typedValues [a] [privateValue]).isOk) "runtime Nat identity is checked"
  let other ← get (FixedVectorReference.admit (.atom "field" Bindings.koalaBear) 1 [3])
  checks.holds (code (FixedVectorReference.dot value other) == some "reference-value-type") "dot never zip-truncates"
  let unsupported : FixedVectorReference.Data := ⟨.atom "field" Bindings.fr, 0, [], rfl⟩
  checks.holds (code (Reference.Value.fixedVector unsupported).validate == some "reference-fixed-vector-not-supported")
    "manually constructed unsupported carrier fails validation"
  let parameters : Generic.Parameters := [("F", .field), ("N", .natural), ("T", .type)]
  let genericTy ← get (Generic.valueType parameters "fixed_vector<fixed_vector<T,N>,0>")
  let specialized ← get (Generic.specializeType [("T", field), ("N", "4")] genericTy)
  checks.holds (specialized.spelling == fixed (fixed field 4) 0) "nested Type and Nat specialization"
  checks.holds (genericTy.affine) "unconstrained Type argument does not gain copy permission"
  checks.holds (!(← get (Generic.valueType parameters "fixed_vector<field:F,N>")).affine)
    "installed field constructor supplies element copy permission"
  checks.holds (Generic.termSort parameters (.apply "fixed_vector" [.apply "field" [.root "F"], .root "N"]) == .ok .type)
    "nested Type-valued applications use existing term DAG"
  checks.holds (!(Generic.termSort parameters (.apply "fixed_vector" [.root "F", .root "N"])).isOk)
    "Domain root cannot stand in for Type argument"
  checks.holds (!(Generic.valueType parameters "field<F>").isOk &&
    !(Generic.valueType parameters "fixed_vector<field:F,04>").isOk) "generic canonical grammar"
  checks.holds ((Generic.valueType parameters (wrap (fun s => fixed s 0) 8 "field:F")).isOk &&
    !(Generic.valueType parameters (wrap (fun s => fixed s 0) 9 "field:F")).isOk) "generic structural depth matches ground depth"
  let generic ← get (Generic.decodeDefinition (← get (Json.parse genericText)))
  let checked ← get (Generic.checkDefinition generic)
  checks.holds (!(Generic.checkDefinition {generic with requirements := []}).isOk) "Field capability is a required promise"
  let (specialized, selected) ← get (Generic.specialize
    ⟨"FixedAtTwo", "Fixed", [("F", Bindings.koalaBear), ("N", "2")], []⟩ checked)
  checks.holds (selected.all (fun b => b.arguments == [Bindings.koalaBear, "2"]) &&
    (TypedLocal.elaborate selected specialized).isOk) "generic scope constants specialize canonical static strings"
  checks.holds (!(Generic.consistent checked [("F", Bindings.koalaBear), ("N", "02")]).isOk)
    "configured Nat constants are canonical"
  checks.holds (!(Generic.consistent checked [("F", "2"), ("N", "2")]).isOk)
    "Nat constant cannot be installed as a fake Field identity"
  checks.holds ((Explicit.decodeOrigin (.arr #[.str "Fixed", .arr #[
    .arr #[.str "F", .str Bindings.koalaBear], .arr #[.str "N", .str "2"],
    .arr #[.str "T", .str (fixed field 2)]]])).isOk)
    "common local origins retain canonical Type and Nat values"
  checks.holds (!(Explicit.decodeOrigin (.arr #[.str "Fixed", .arr #[
    .arr #[.str "N", .str "02"]]])).isOk) "origin cannot smuggle noncanonical Nat spelling"
  let substitution : List (Name × Term) := [("F", .root "G"), ("N", .root "M")]
  let substituted ← get (Generic.applicationSignature generic substitution)
  checks.holds (substituted.inputs[0]?.map (·.term) == some (.apply "vector" [.root "G"]))
    "application substitution preserves symbolic scope terms"
  checks.holds ((Requirements.check [.equal (.root "N") (.root "M")]
    [.equal (.apply "fixed_vector" [.apply "field" [.root "F"], .root "N"])
      (.apply "fixed_vector" [.apply "field" [.root "F"], .root "M"])]).isOk)
    "unchanged checker proves application congruence"
  checks.holds (!(Requirements.check [] [.equal (.root "$2") (.root "$3")]).isOk)
    "no Nat arithmetic or equality solver is introduced"
  checks.finish "Lean structural type admission and fixed-vector reference"

end Tests.StructuralTypes

#eval Tests.StructuralTypes.run
