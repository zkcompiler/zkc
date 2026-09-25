import Tools.Artifact.Codec

/-! Canonical matrix content for the installed identity check. Lean derives the
ordered payload from its mathematical matrix; SHA256 remains an explicitly
requested trusted hash service. A digest is not a proof of relation adequacy. -/
set_option autoImplicit false

namespace Tools.Interactive.MatrixIdentity
open Lean (Json)

/-- Independently encode exact dimensions, ordered coordinates and coefficients. -/
def request {F : Type} [Zero F] [BEq F] (domain : String) (canonical : F → Nat)
    (value : ScalarReference.Data F) : Result Json := do
  let .matrix matrix := value | throw "matrix-identity-type"
  ensure matrix.valid "matrix-canonical"
  let natural := fun n => Json.str (toString n)
  let payload := Json.arr #[.str "zkc.matrix/1", .str domain,
    .arr #[natural matrix.rows, natural matrix.columns,
      .arr (matrix.entries.map fun e => Json.arr #[natural e.row, natural e.column,
        natural (canonical e.coefficient)]).toArray]]
  return .arr #[.str "zkc.hash/1", .str "sha256", .str (Tools.Artifact.hex payload.compress.toUTF8)]

/-- Prime-field content uses the canonical residue, not Montgomery bytes. -/
def prime (domain : ScalarReference.Domain) (value : ScalarReference.Data (ScalarReference.Scalar domain)) :
    Result Json := request domain.identity (fun x => x.val) value

/-- The installed extension's ascending coefficients encode sum(c_i * p^i). -/
def extension (value : ExtensionReference.Data) : Result Json :=
  request Bindings.koalaBearExt8 (fun x =>
    x.coordinates.toList.foldr (fun c acc => c.val + Bindings.koalaBearModulus * acc) 0) value

/-- Hash responses have the same canonical lowercase digest alphabet as attributes. -/
def acceptsDigest (attributes : List String) (response : Json) : Result Bool := do
  Bindings.attributes false "matrix.identity_check" attributes
  let digest ← Decode.string response
  Bindings.attributes false "matrix.identity_check" [digest]
  return attributes == [digest]

end Tools.Interactive.MatrixIdentity
