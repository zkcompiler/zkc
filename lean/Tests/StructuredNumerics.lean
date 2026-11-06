import Zkc.Source.Structured.NumericalLaws
import Zkc.Source.Structured.NumericalCapabilities
import Zkc.Source.Structured.PrimitiveEvaluation
import Zkc.Source.Structured.Admission
import Mathlib.Data.ZMod.Basic

/-! Focused numerical equations and strict admission controls. Small finite
fields exercise the equations independently of any native FFT or CPU adapter. -/
namespace Tests.StructuredNumerics
open Zkc.Source Zkc.Source.Structured

abbrev F := ZMod 17

def model : FieldModel where
  toCarriers := uniformCarriers F Unit
  fieldRing _ := inferInstance
  fieldDecEq _ := inferInstance
  inverse _ := some (fun x ↦ x ^ 15)
  embed _ _ x := x
  twoAdic _ := some ⟨"F", [1, 16, 4, 2, 6]⟩

-- Extraction observes complete returns/stops through the existing Outcome.
def vectorResult : PIR.Outcome (Values model.Value [.vector "F"]) → PIR.Outcome (List F)
  | .returned (.cons xs .nil) => .returned xs
  | .stopped stop => .stopped stop

def scalarResult : PIR.Outcome (Values model.Value [.field "F"]) → PIR.Outcome F
  | .returned (.cons x .nil) => .returned x
  | .stopped stop => .stopped stop

def indexResult : PIR.Outcome (Values model.Value [.index]) → PIR.Outcome Nat
  | .returned (.cons x .nil) => .returned x
  | .stopped stop => .stopped stop

def indicesResult : PIR.Outcome (Values model.Value [.indices]) → PIR.Outcome (List Nat)
  | .returned (.cons xs .nil) => .returned xs
  | .stopped stop => .stopped stop

def polynomialResult : PIR.Outcome (Values model.Value [.polynomial "F"]) →
    PIR.Outcome (List F)
  | .returned (.cons p .nil) => .returned p.coefficients
  | .stopped stop => .stopped stop

abbrev run (op : Numerical) := Numerical.checkedEvaluateOn model "F" "B" op

#guard (.polynomial "F" : Ty) != .vector "F"
#guard (.polynomial "F" : Ty) != .polynomial "B"
#guard (PolynomialValue.ofCoefficients (0 : F) [0, 0]).coefficients == []
#guard (PolynomialValue.ofCoefficients (0 : F) [2, 0, 3, 0, 0]).coefficients == [2, 0, 3]
#guard polynomialResult (run .polyFromCoefficients (.cons [2, 0, 0] .nil)) == .returned [2]
#guard polynomialResult (run .polyFromCoefficients (.cons [] .nil)) == .returned []
#guard scalarResult (run .polyEvaluate
    (.cons (PolynomialValue.ofCoefficients 0 [2, 3]) (.cons 4 .nil))) == .returned 14
#guard scalarResult (run .polyEvaluate
    (.cons (PolynomialValue.ofCoefficients 0 []) (.cons 4 .nil))) == .returned 0
#guard vectorResult (run .polyCoefficients
    (.cons (PolynomialValue.ofCoefficients 0 [2, 0, 0]) .nil)) == .returned [2]
-- A polynomial authored with another zero cannot cross the model boundary.
#guard vectorResult (run .polyCoefficients
    (.cons (PolynomialValue.ofCoefficients 1 [2]) .nil)) == .stopped .refused

#guard scalarResult (run .fieldInverse (.cons 2 .nil)) == .returned 9
#guard scalarResult (run .fieldInverse (.cons 0 .nil)) == .stopped .refused
#guard vectorResult (run .vectorInverse (.cons [] .nil)) == .returned []
#guard vectorResult (run .vectorInverse (.cons [2, 0] .nil)) == .stopped .refused
#guard vectorResult (run .vectorInverse (.cons [2, 4] .nil)) == .returned [9, 13]
#guard indicesResult (run .indicesEmpty .nil) == .returned []
#guard indicesResult (run .indicesAppend (.cons [2, 2] (.cons 2 .nil))) == .returned [2, 2, 2]
#guard indexResult (run .indicesAt (.cons [4, 4] (.cons 1 .nil))) == .returned 4
#guard indexResult (run .indicesAt (.cons [4] (.cons 1 .nil))) == .stopped .refused
#guard indexResult (run .indicesLength (.cons [4, 4] .nil)) == .returned 2
#guard indicesResult (run .indicesAppend (.cons [] (.cons indexLimit .nil))) == .stopped .refused
#guard indexResult (run .indicesAt (.cons [indexLimit] (.cons 0 .nil))) == .stopped .refused

#guard vectorResult (run .vectorFill (.cons 3 (.cons 0 .nil))) == .returned []
#guard vectorResult (run .vectorFill (.cons 3 (.cons 2 .nil))) == .returned [3, 3]
#guard vectorResult (run .vectorConcat (.cons [1, 2] (.cons [3] .nil))) == .returned [1, 2, 3]
#guard scalarResult (run .vectorGet (.cons [3] (.cons 1 .nil))) == .stopped .refused
#guard vectorResult (run .vectorAdd (.cons [1, 2] (.cons [3] .nil))) == .stopped .refused
#guard vectorResult (run .vectorAdd (.cons [1, 2] (.cons [3, 4] .nil))) == .returned [4, 6]
#guard vectorResult (run .vectorSub (.cons [1, 2] (.cons [3, 4] .nil))) == .returned [15, 15]
#guard vectorResult (run .vectorMul (.cons [1, 2] (.cons [3, 4] .nil))) == .returned [3, 8]
#guard vectorResult (run .vectorScale (.cons [1, 2] (.cons 3 .nil))) == .returned [3, 6]
#guard vectorResult (run .vectorGeometric (.cons 2 (.cons 4 .nil))) == .returned [1, 2, 4, 8]
#guard vectorResult (run .vectorGeometric (.cons 2 (.cons 0 .nil))) == .returned []
#guard vectorResult (run .vectorSlice (.cons [1, 2] (.cons 2 (.cons 0 .nil)))) == .returned []
#guard vectorResult (run .vectorSlice (.cons [1, 2] (.cons 3 (.cons 0 .nil)))) == .stopped .refused
#guard vectorResult (run .vectorSlice
    (.cons [] (.cons (indexLimit - 1) (.cons 1 .nil)))) == .stopped .refused
#guard vectorResult (run .vectorTranspose
    (.cons [1, 2, 3, 4, 5, 6] (.cons 2 (.cons 3 .nil)))) == .returned [1, 4, 2, 5, 3, 6]
#guard vectorResult (run .vectorTranspose
    (.cons [] (.cons 0 (.cons (indexLimit - 1) .nil)))) == .returned []
#guard vectorResult (run .vectorTranspose (.cons [1] (.cons 0 (.cons 1 .nil)))) == .stopped .refused
#guard vectorResult (run .vectorEmbed (.cons [1, 2] .nil)) == .returned [1, 2]
#guard vectorResult (run .vectorRotate (.cons [1, 2] (.cons 2 .nil))) == .stopped .refused
#guard vectorResult (run .vectorRotate (.cons [] (.cons 0 .nil))) == .stopped .refused
#guard vectorResult (run .vectorRotate (.cons [1, 2, 3] (.cons 1 .nil))) == .returned [2, 3, 1]
#guard vectorResult (run .vectorBitReverseRows
    (.cons [1, 2, 3, 4, 5, 6, 7, 8] (.cons 2 .nil))) == .returned [1, 2, 5, 6, 3, 4, 7, 8]
#guard vectorResult (run .vectorBitReverseRows (.cons [] (.cons 1 .nil))) == .stopped .refused
#guard vectorResult (run .vectorBitReverseRows (.cons [] (.cons 0 .nil))) == .stopped .refused
#guard vectorResult (run .vectorPrefixSum (.cons [1, 2, 3] .nil)) == .returned [1, 3, 6]
#guard vectorResult (run .vectorPrefixProduct (.cons [2, 3, 4] .nil)) == .returned [2, 6, 7]
#guard vectorResult (run .vectorPrefixProduct (.cons [] .nil)) == .returned []

#guard scalarResult (run .polyRoot (.cons 4 .nil)) == .returned 4
#guard scalarResult (run .polyRoot (.cons 3 .nil)) == .stopped .refused
#guard scalarResult (run .polyRoot (.cons 32 .nil)) == .stopped .refused
#guard scalarResult (run .polyPoint (.cons 3 (.cons 2 (.cons 1 .nil)))) == .returned 14
#guard scalarResult (run .polyPoint (.cons 3 (.cons 2 (.cons 2 .nil)))) == .stopped .refused
#guard vectorResult (run .polyPoints (.cons 3 (.cons 4 .nil))) == .returned [3, 12, 14, 5]
#guard vectorResult (run .polyPoints (.cons 0 (.cons 1 .nil))) == .stopped .refused
#guard polynomialResult (run .polyInterpolate (.cons [] (.cons 1 .nil))) == .stopped .refused
#guard polynomialResult (run .polyInterpolate (.cons [7] (.cons 3 .nil))) == .returned [7]
#guard polynomialResult (run .polyInterpolate (.cons [5, 16] (.cons 3 .nil))) == .returned [2, 1]
#guard vectorResult (run .polyFold (.cons [5, 16] (.cons 3 (.cons 4 .nil)))) == .returned [6]
#guard vectorResult (run .polyFold (.cons [7] (.cons 3 (.cons 4 .nil)))) == .stopped .refused

-- STARK coefficients and evaluations are column-major. Heights need not be powers of two.
#guard vectorResult (run .polyEvaluateBatch
    (.cons [1, 2, 3, 4] (.cons 2 (.cons 2 (.cons 1 (.cons 2 .nil)))))) == .returned [3, 16, 7, 16]
#guard vectorResult (run .polyEvaluateBatch
    (.cons [] (.cons 2 (.cons 0 (.cons 1 (.cons 2 .nil)))))) == .returned [0, 0, 0, 0]
#guard vectorResult (run .polyEvaluateBatch
    (.cons [1, 2, 3] (.cons 1 (.cons 3 (.cons 1 (.cons 4 .nil)))))) == .returned [6, 6, 2, 7]
#guard vectorResult (run .polyEvaluateBatch
    (.cons [1, 0, 2] (.cons 1 (.cons 3 (.cons 1 (.cons 2 .nil)))))) == .stopped .refused
#guard vectorResult (run .polyEvaluateBatch
    (.cons [1, 0, 0] (.cons 1 (.cons 3 (.cons 1 (.cons 2 .nil)))))) == .returned [1, 1]
#guard vectorResult (run .polyEvaluateAt
    (.cons [5, 16] (.cons 1 (.cons 2 (.cons 3 (.cons 3 .nil)))))) == .returned [5]
#guard vectorResult (run .polyExtend
    (.cons [5, 16] (.cons 1 (.cons 2 (.cons 3 (.cons 1 (.cons 4 .nil))))))) ==
      .returned [3, 6, 1, 15]
#guard vectorResult (run .polyExtend
    (.cons [5, 16] (.cons 1 (.cons 2 (.cons 3 (.cons 1 (.cons 1 .nil))))))) ==
      .stopped .refused
#guard vectorResult (run .polyExtend
    (.cons [5, 5] (.cons 1 (.cons 2 (.cons 3 (.cons 1 (.cons 1 .nil))))))) == .returned [5]

-- Width zero skips every unused domain, but never the supplied shape or u64 ingress.
#guard vectorResult (run .polyEvaluateBatch
    (.cons [] (.cons 0 (.cons 3 (.cons 0 (.cons 3 .nil)))))) == .returned []
#guard vectorResult (run .polyEvaluateAt
    (.cons [] (.cons 0 (.cons 0 (.cons 0 (.cons 0 .nil)))))) == .returned []
#guard vectorResult (run .polyExtend
    (.cons [] (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 .nil))))))) == .returned []
#guard vectorResult (run .polyExtend
    (.cons [1] (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 .nil))))))) == .stopped .refused
#guard vectorResult (run .polyEvaluateBatch
    (.cons [] (.cons 0 (.cons 0 (.cons 0 (.cons indexLimit .nil)))))) == .stopped .refused
#guard vectorResult (run .polyEvaluateBatch
    (.cons [] (.cons (2^32) (.cons (2^32) (.cons 1 (.cons 1 .nil)))))) == .stopped .exhausted

#guard vectorResult (run .polyOpeningSum
    (.cons [5, 16] (.cons 1 (.cons 2 (.cons 3 (.cons [0, 0] (.cons [0, 0]
      (.cons [2, 2] (.cons [1, 1] (.cons [0, 0] .nil)))))))))) == .returned [2, 2]
#guard vectorResult (run .polyOpeningSum
    (.cons [] (.cons 0 (.cons 0 (.cons 0 (.cons [] (.cons []
      (.cons [] (.cons [] (.cons [] .nil)))))))))) == .returned []
#guard vectorResult (run .polyOpeningSum
    (.cons [] (.cons 0 (.cons 3 (.cons 0 (.cons [] (.cons []
      (.cons [] (.cons [] (.cons [1, 2, 3] .nil)))))))))) == .returned [1, 2, 3]
-- An invalid column/point refuses even when its weight is zero.
#guard vectorResult (run .polyOpeningSum
    (.cons [5, 16] (.cons 1 (.cons 2 (.cons 3 (.cons [1] (.cons [0]
      (.cons [2] (.cons [0] (.cons [0, 0] .nil)))))))))) == .stopped .refused
#guard vectorResult (run .polyOpeningSum
    (.cons [5, 16] (.cons 1 (.cons 2 (.cons 3 (.cons [0] (.cons [3]
      (.cons [2] (.cons [0] (.cons [0, 0] .nil)))))))))) == .stopped .refused
#guard vectorResult (run .polyOpeningSum
    (.cons [5, 16] (.cons 1 (.cons 2 (.cons 3 (.cons [0] (.cons []
      (.cons [2] (.cons [1] (.cons [0, 0] .nil)))))))))) == .stopped .refused

-- Strict signatures, exact field literals and exact base-field embedding ports.
def binding (contract : String) (root : String) (inputs outputs : List Ty) : Binding :=
  ⟨"operation", contract, [root], "", some ⟨[.domain "Field" root], inputs, outputs⟩⟩

def extension := "koala-bear.ext8-binomial3"
#guard (binding "poly.from_coefficients" extension [.vector extension] [.polynomial extension]
    |>.resolveRoot koalaBearCatalogue).isOk
#guard !(binding "poly.from_coefficients" extension [.vector extension] [.vector extension]
    |>.resolveRoot koalaBearCatalogue).isOk
#guard (binding "vector.embed" extension [.vector "koala-bear"] [.vector extension]
    |>.resolveRoot koalaBearCatalogue).isOk
#guard !(binding "vector.embed" extension [.vector extension] [.vector extension]
    |>.resolveRoot koalaBearCatalogue).isOk
#guard !(binding "vector.embed" extension [.vector "bls12-381.fr"] [.vector extension]
    |>.resolveRoot admittedCatalogue).isOk
#guard Numerical.ofContract "poly.coset_evaluate" == none
#guard Numerical.ofContract "poly.opening_quotient" == none
#guard Numerical.ofContract "vector.bit_reverse" == none
#guard (Format.fieldLiteral koalaBearCatalogue "koala-bear"
    (.fieldLiteral "koala-bear" "natural" "2130706432")).isOk
#guard !(Format.fieldLiteral koalaBearCatalogue "koala-bear"
    (.fieldLiteral "koala-bear" "natural" "2130706433")).isOk
#guard !(Format.fieldLiteral koalaBearCatalogue extension
    (.fieldLiteral "koala-bear" "natural" "1")).isOk
#guard !(Format.fieldLiteral koalaBearCatalogue "koala-bear"
    (.fieldLiteral "koala-bear" "natural" "01")).isOk

-- These are kernel reductions, not executable-reader checks. A serialized
-- parameter would get stuck at the opaque JSON parser here.
example : Format.fieldLiteral koalaBearCatalogue "koala-bear"
    (.fieldLiteral "koala-bear" "natural" "0") = .ok (.natural 0) := rfl
example : Format.fieldLiteral koalaBearCatalogue "koala-bear"
    (.natural "0") = .error "structured-field-literal" := rfl

-- Binary patterns are retained at their full installed width.
def binaryField := "gf2-64.pentanomial-4-3-1"
def binaryExtension := "gf2-64.pentanomial-4-3-1.ext3-trinomial1"
#guard (Format.fieldLiteral binaryCatalogue binaryField
    (.fieldLiteral "gf2-64.pentanomial-4-3-1" "bits" "0x8000000000000000")).isOk
#guard !(Format.fieldLiteral binaryCatalogue binaryField
    (.fieldLiteral "gf2-64.pentanomial-4-3-1" "bits" "0x10000000000000000")).isOk
#guard !(Format.fieldLiteral binaryCatalogue binaryField
    (.fieldLiteral "gf2-64.pentanomial-4-3-1" "natural" "2")).isOk
#guard !(Format.fieldLiteral binaryCatalogue binaryField
    (.fieldLiteral "gf2-64.pentanomial-4-3-1" "bits" "0x02")).isOk
#guard !(Format.fieldLiteral binaryCatalogue binaryField
    (.fieldLiteral "gf2-64.pentanomial-4-3-1" "bits" "0xA")).isOk
#guard !(Format.fieldLiteral binaryCatalogue binaryField
    (.fieldLiteral "gf2-64.pentanomial-4-3-1" "bits" "0x1")).isOk
#guard (Format.fieldLiteral binaryCatalogue binaryExtension
    (.fieldLiteral binaryExtension "bits" "0x800000000000000000000000000000000000000000000000")).isOk
-- This raw test basis distinguishes bit selection from a parity/natural cast.
-- It is deliberately not claimed to satisfy BinaryPresentationLaw.
#guard Numerical.binaryBasisValue ([1, 2, 4] : List F) 6 == 6
#guard Numerical.binaryValue { model with binary := fun _ ↦ some ⟨[1, 2, 4]⟩ }
    "F" 8 == .error .refused
#guard Numerical.binaryValue model "F" 2 == .error .refused

end Tests.StructuredNumerics
