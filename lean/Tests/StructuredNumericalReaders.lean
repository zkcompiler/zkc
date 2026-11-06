import ZkcTools.StructuredSource.OpenValues
import Zkc.Source.Structured.ProtocolAdmission

/-! Strict numerical wire boundaries and the explicit scalar tool model. -/
namespace Tests.StructuredNumericalReaders
open Lean Zkc.Source Zkc.Source.Structured
open ZkcTools.StructuredSource

def json (text : String) : Json := (Json.parse text).toOption.get!

def embedBinding (input : String) : Json := json
  ("[\"binding\",\"embed\",\"vector.embed\"," ++
   "[[\"domain\",\"Field\",\"koala-bear.ext8-binomial3\"]]," ++
   "\"\",[[\"apply\",\"vector\",[[\"domain\",\"Field\",\"" ++ input ++
   "\"]]]],[[\"apply\",\"vector\",[[\"domain\",\"Field\",\"koala-bear.ext8-binomial3\"]]]]]")

#guard (Format.bindingIn koalaBearCatalogue (embedBinding "koala-bear")).isOk
#guard !(Format.bindingIn koalaBearCatalogue (embedBinding "koala-bear.ext8-binomial3")).isOk
#guard !(Format.bindingIn admittedCatalogue (embedBinding "bls12-381.fr")).isOk
#guard (Structured.Format.type (json
    "[\"apply\",\"polynomial\",[[\"domain\",\"Field\",\"koala-bear\"]]]")) ==
      .ok (.polynomial "koala-bear")

#guard (input (.polynomial "koala-bear")
    (json "[\"polynomial\",\"koala-bear\",[\"1\",\"2\"]]")).isOk
#guard (input (.polynomial "koala-bear")
    (json "[\"polynomial\",\"koala-bear\",[]]")).isOk
#guard !(input (.polynomial "koala-bear")
    (json "[\"polynomial\",\"koala-bear\",[\"1\",\"0\"]]")).isOk
#guard !(input (.polynomial "koala-bear")
    (json "[\"polynomial\",\"koala-bear\",[\"0\"]]")).isOk
#guard !(input (.polynomial "koala-bear")
    (json "[\"polynomial\",\"koala-bear.ext8-binomial3\",[]]")).isOk
#guard !(input (.polynomial "koala-bear")
    (json "[\"vector\",\"koala-bear\",[]]")).isOk
#guard (wireInput (.polynomial "koala-bear") (json "[\"1\",\"2\"]")).isOk
#guard !(wireInput (.polynomial "koala-bear") (json "[\"1\",\"0\"]")).isOk
#guard ((output (.polynomial "koala-bear") (PolynomialValue.ofCoefficients 0 [1, 2])).map
    Json.compress) == .ok (json "[\"polynomial\",\"koala-bear\",[\"1\",\"2\"]]").compress
#guard !(output (.polynomial "koala-bear") (PolynomialValue.ofCoefficients 1 [2])).isOk

#guard (ProtocolInterface.resolve ⟨["P", "V"], [["P"]], [["P"]]⟩
    [.polynomial "koala-bear"] [.polynomial "koala-bear"]).isOk
#guard !(ProtocolInterface.resolve ⟨["P", "V"], [["P", "V"]], []⟩
    [.polynomial "koala-bear"] []).isOk
#guard !(ProtocolInterface.resolve ⟨["P", "V"], [], [["P", "V"]]⟩
    [] [.sequence (.polynomial "koala-bear")]).isOk

-- The observer's existing budgets apply independently of semantic u64 limits.
#guard !((Bounds.primitive (.numerical .vectorFill "F" "")
    [.atom, .index (Bounds.exact 4097)]).run {}).isOk
#guard ((Bounds.primitive (.numerical .polyEvaluateBatch "F" "")
    [.vector (Bounds.exact 0), .index (Bounds.exact 0), .index (Bounds.exact 0),
      .atom, .index (Bounds.exact (2^63))]).run {}).isOk

end Tests.StructuredNumericalReaders
