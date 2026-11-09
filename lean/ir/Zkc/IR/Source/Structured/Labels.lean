module

@[expose] public section
namespace Zkc.Source.Structured

/-- The explicit-label case of the frontend's `nativeSiteName`: lowercase
UTF-8 hex. Unlabelled ordinal sites require an admitted source coordinate. -/
def encodedLabel (label : String) : String :=
  let digits := "0123456789abcdef".toList
  "label_" ++ String.ofList (label.toByteArray.data.toList.flatMap fun byte =>
    [digits[byte.toNat / 16]!, digits[byte.toNat % 16]!])

end Zkc.Source.Structured
