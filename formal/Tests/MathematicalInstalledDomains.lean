import Tools.Mathematical.InstalledDomains
import Tests.MathematicalTypeExpansion

set_option autoImplicit false
namespace Tests.MathematicalInstalledDomains
open Zkc.Source.Mathematical
open Tools.Mathematical.InstalledDomains

def shape (identity : String) (raw : Raw.TypeExpression) : Except TypeAdmission.Error (TypeExpansion.Shape 1 0) :=
  (do
    let table ← TypeAdmission.declarations MathematicalTypeExpansion.atomMeaning (check (fun _ => identity)) [⟨0, raw⟩]
    let result ← TypeAdmission.use MathematicalTypeExpansion.atomMeaning table 0 ⟨⟨0⟩, []⟩
    return result.expanded.shape).run' 1000000

def run : IO Unit := do
  let checks ← Checks.start
  checks.holds (shape "bls12-381.fr" (.nominal ⟨0⟩ "field" [])).isOk "installed field value"
  checks.holds (!(shape "bls12-381.fr" (.nominal ⟨0⟩ "group" [])).isOk) "nominal domain sort"
  checks.holds (!(shape "bls12-381.fr" (.nominal ⟨0⟩ "rng" [])).isOk) "affine RNG state excluded"
  checks.holds (!(shape "bls12-381.fr" (.nominal ⟨0⟩ "field" [.literal 1])).isOk) "closed unary constructor arity"
  checks.holds (shape "bls12-381.fr" (.polynomial ⟨0⟩ (.literal 3) (.literal 2) .total)).isOk
    "polynomial over an installed field"
  checks.holds (shape "bls12-381.fr" (.residual ⟨0⟩ (.literal 3) (.literal 2))).isOk
    "residual over an installed field"
  checks.holds (!(shape "bls12-381.g1" (.polynomial ⟨0⟩ (.literal 3) (.literal 2) .total)).isOk)
    "polynomial coefficient domain sort"
  checks.holds (!(shape "not-installed" (.nominal ⟨0⟩ "field" [])).isOk) "unknown catalog domain"
  checks.holds (!(shape "koala-bear" (.nominal ⟨0⟩ "table" [])).isOk) "matching sort cannot grant a missing type instance"
  checks.holds (!(shape "bls12-381.fr" (.nominal ⟨0⟩ "not-installed" [])).isOk) "unknown constructor"
  checks.holds (nominal "multilinear.kzg.bls12-381/1" "prover_key") "installed immutable private value"
  checks.finish "mathematical installed domain adapter"

#eval run
end Tests.MathematicalInstalledDomains
