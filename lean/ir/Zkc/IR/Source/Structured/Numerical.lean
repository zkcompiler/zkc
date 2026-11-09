module

public import Zkc.IR.Source.Structured.Vocabulary

@[expose] public section

/-! Fixed numerical operations. Contract spelling selects this closed enum;
no unknown name or catalogue tag supplies an evaluator. -/
namespace Zkc.Source.Structured

inductive Numerical where
  | fieldInverse
  | indicesEmpty
  | indicesAppend
  | indicesAt
  | indicesLength
  | polyCoefficients
  | polyFromCoefficients
  | polyEvaluate
  | polyInterpolate
  | polyRoot
  | polyPoint
  | polyPoints
  | polyFold
  | vectorConcat
  | vectorFill
  | vectorGet
  | vectorAdd
  | vectorSub
  | vectorMul
  | vectorScale
  | vectorInverse
  | vectorGeometric
  | vectorSlice
  | vectorTranspose
  | vectorEmbed
  | vectorRotate
  | vectorBitReverseRows
  | vectorPrefixSum
  | vectorPrefixProduct
  | polyEvaluateBatch
  | polyEvaluateAt
  | polyExtend
  | polyOpeningSum
  deriving DecidableEq, Repr

def Numerical.contract : Numerical → String
  | .fieldInverse => "field.inverse"
  | .indicesEmpty => "indices.empty"
  | .indicesAppend => "indices.append"
  | .indicesAt => "indices.at"
  | .indicesLength => "indices.length"
  | .polyCoefficients => "poly.coefficients"
  | .polyFromCoefficients => "poly.from_coefficients"
  | .polyEvaluate => "poly.univariate_evaluate"
  | .polyInterpolate => "poly.coset_interpolate"
  | .polyRoot => "poly.domain_root"
  | .polyPoint => "poly.domain_point"
  | .polyPoints => "poly.domain_points"
  | .polyFold => "poly.even_odd_fold"
  | .vectorConcat => "vector.concat"
  | .vectorFill => "vector.fill"
  | .vectorGet => "vector.get"
  | .vectorAdd => "vector.add"
  | .vectorSub => "vector.sub"
  | .vectorMul => "vector.mul"
  | .vectorScale => "vector.scale"
  | .vectorInverse => "vector.inverse"
  | .vectorGeometric => "vector.geometric"
  | .vectorSlice => "vector.slice"
  | .vectorTranspose => "vector.transpose"
  | .vectorEmbed => "vector.embed"
  | .vectorRotate => "vector.rotate"
  | .vectorBitReverseRows => "vector.bit_reverse_rows"
  | .vectorPrefixSum => "vector.prefix_sum"
  | .vectorPrefixProduct => "vector.prefix_product"
  | .polyEvaluateBatch => "poly.coset_evaluate_batch"
  | .polyEvaluateAt => "poly.coset_evaluate_at"
  | .polyExtend => "poly.coset_extend"
  | .polyOpeningSum => "poly.opening_quotient_sum"

def Numerical.ofContract : String → Option Numerical
  | "field.inverse" => some .fieldInverse
  | "indices.empty" => some .indicesEmpty
  | "indices.append" => some .indicesAppend
  | "indices.at" => some .indicesAt
  | "indices.length" => some .indicesLength
  | "poly.coefficients" => some .polyCoefficients
  | "poly.from_coefficients" => some .polyFromCoefficients
  | "poly.univariate_evaluate" => some .polyEvaluate
  | "poly.coset_interpolate" => some .polyInterpolate
  | "poly.domain_root" => some .polyRoot
  | "poly.domain_point" => some .polyPoint
  | "poly.domain_points" => some .polyPoints
  | "poly.even_odd_fold" => some .polyFold
  | "vector.concat" => some .vectorConcat
  | "vector.fill" => some .vectorFill
  | "vector.get" => some .vectorGet
  | "vector.add" => some .vectorAdd
  | "vector.sub" => some .vectorSub
  | "vector.mul" => some .vectorMul
  | "vector.scale" => some .vectorScale
  | "vector.inverse" => some .vectorInverse
  | "vector.geometric" => some .vectorGeometric
  | "vector.slice" => some .vectorSlice
  | "vector.transpose" => some .vectorTranspose
  | "vector.embed" => some .vectorEmbed
  | "vector.rotate" => some .vectorRotate
  | "vector.bit_reverse_rows" => some .vectorBitReverseRows
  | "vector.prefix_sum" => some .vectorPrefixSum
  | "vector.prefix_product" => some .vectorPrefixProduct
  | "poly.coset_evaluate_batch" => some .polyEvaluateBatch
  | "poly.coset_evaluate_at" => some .polyEvaluateAt
  | "poly.coset_extend" => some .polyExtend
  | "poly.opening_quotient_sum" => some .polyOpeningSum
  | _ => none

def Numerical.root : Numerical → Option String
  | .fieldInverse => some "Field"
  | .indicesEmpty => none
  | .indicesAppend => none
  | .indicesAt => none
  | .indicesLength => none
  | .polyCoefficients => some "CommRing"
  | .polyFromCoefficients => some "CommRing"
  | .polyEvaluate => some "CommRing"
  | .polyInterpolate => some "TwoAdicField"
  | .polyRoot => some "TwoAdicField"
  | .polyPoint => some "TwoAdicField"
  | .polyPoints => some "TwoAdicField"
  | .polyFold => some "TwoAdicField"
  | .vectorConcat => some "Field"
  | .vectorFill => some "Field"
  | .vectorGet => some "Field"
  | .vectorAdd => some "Field"
  | .vectorSub => some "Field"
  | .vectorMul => some "Field"
  | .vectorScale => some "Field"
  | .vectorInverse => some "Field"
  | .vectorGeometric => some "Field"
  | .vectorSlice => some "Field"
  | .vectorTranspose => some "Field"
  | .vectorEmbed => some "ExtensionField"
  | .vectorRotate => some "Field"
  | .vectorBitReverseRows => some "Field"
  | .vectorPrefixSum => some "Field"
  | .vectorPrefixProduct => some "Field"
  | .polyEvaluateBatch => some "TwoAdicField"
  | .polyEvaluateAt => some "TwoAdicField"
  | .polyExtend => some "TwoAdicField"
  | .polyOpeningSum => some "TwoAdicField"

def Numerical.arguments (domain base : String) : Numerical → List Ty
  | .fieldInverse => [.field domain]
  | .indicesEmpty => []
  | .indicesAppend => [.indices, .index]
  | .indicesAt => [.indices, .index]
  | .indicesLength => [.indices]
  | .polyCoefficients => [.polynomial domain]
  | .polyFromCoefficients => [.vector domain]
  | .polyEvaluate => [.polynomial domain, .field domain]
  | .polyInterpolate => [.vector domain, .field domain]
  | .polyRoot => [.index]
  | .polyPoint => [.field domain, .index, .index]
  | .polyPoints => [.field domain, .index]
  | .polyFold => [.vector domain, .field domain, .field domain]
  | .vectorConcat => [.vector domain, .vector domain]
  | .vectorFill => [.field domain, .index]
  | .vectorGet => [.vector domain, .index]
  | .vectorAdd => [.vector domain, .vector domain]
  | .vectorSub => [.vector domain, .vector domain]
  | .vectorMul => [.vector domain, .vector domain]
  | .vectorScale => [.vector domain, .field domain]
  | .vectorInverse => [.vector domain]
  | .vectorGeometric => [.field domain, .index]
  | .vectorSlice => [.vector domain, .index, .index]
  | .vectorTranspose => [.vector domain, .index, .index]
  | .vectorEmbed => [.vector base]
  | .vectorRotate => [.vector domain, .index]
  | .vectorBitReverseRows => [.vector domain, .index]
  | .vectorPrefixSum => [.vector domain]
  | .vectorPrefixProduct => [.vector domain]
  | .polyEvaluateBatch => [.vector domain, .index, .index, .field domain, .index]
  | .polyEvaluateAt => [.vector domain, .index, .index, .field domain, .field domain]
  | .polyExtend => [.vector domain, .index, .index, .field domain, .field domain, .index]
  | .polyOpeningSum => [.vector domain, .index, .index, .field domain, .indices,
      .vector domain, .vector domain, .vector domain, .vector domain]

def Numerical.results (domain _base : String) : Numerical → List Ty
  | .fieldInverse => [.field domain]
  | .indicesEmpty => [.indices]
  | .indicesAppend => [.indices]
  | .indicesAt => [.index]
  | .indicesLength => [.index]
  | .polyCoefficients => [.vector domain]
  | .polyFromCoefficients => [.polynomial domain]
  | .polyEvaluate => [.field domain]
  | .polyInterpolate => [.polynomial domain]
  | .polyRoot => [.field domain]
  | .polyPoint => [.field domain]
  | .polyPoints => [.vector domain]
  | .polyFold => [.vector domain]
  | .vectorConcat => [.vector domain]
  | .vectorFill => [.vector domain]
  | .vectorGet => [.field domain]
  | .vectorAdd => [.vector domain]
  | .vectorSub => [.vector domain]
  | .vectorMul => [.vector domain]
  | .vectorScale => [.vector domain]
  | .vectorInverse => [.vector domain]
  | .vectorGeometric => [.vector domain]
  | .vectorSlice => [.vector domain]
  | .vectorTranspose => [.vector domain]
  | .vectorEmbed => [.vector domain]
  | .vectorRotate => [.vector domain]
  | .vectorBitReverseRows => [.vector domain]
  | .vectorPrefixSum => [.vector domain]
  | .vectorPrefixProduct => [.vector domain]
  | .polyEvaluateBatch => [.vector domain]
  | .polyEvaluateAt => [.vector domain]
  | .polyExtend => [.vector domain]
  | .polyOpeningSum => [.vector domain]

/-- Conservative dependency on optional inversion, including interpolation. -/
def Numerical.usesInverse : Numerical → Bool
  | .fieldInverse | .vectorInverse | .polyInterpolate | .polyFold |
    .polyEvaluateAt | .polyExtend | .polyOpeningSum => true
  | _ => false

end Zkc.Source.Structured
