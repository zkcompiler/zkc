module
public import Zkc.Source.Structured.ApplicationMetadata

/-! Concrete checks deliberately use module visibility, like the complete source
admission proofs. Runtime-only checks cannot detect a hidden comparator body. -/

public section
namespace Tests.StructuredApplicationMetadata
open Zkc.Source.Structured.ApplicationMetadata

/-- Inserting several labels remains reducible in an importing module. -/
theorem distinct_labels :
    (((∅ : SiteSet).insert "s0").insert "s2").contains "s3" = false := by
  decide +kernel

/-- Duplicate membership is exact, including a previously inserted label. -/
theorem repeated_label :
    (((∅ : SiteSet).insert "s0").insert "s2").contains "s0" = true := by
  decide +kernel

/-- Collection equality compares whole labels rather than a hash or prefix. -/
theorem generated_labels :
    (((∅ : SiteSet).insert "apply_1_a_b").insert "apply_1_b_c").contains
      "apply_1_a_c" = false := by
  decide +kernel

/-- Logical string membership is exact even outside admission's ASCII profile. -/
theorem unicode_labels :
    (((∅ : SiteSet).insert "λ").insert "한").contains "λ" = true ∧
    (((∅ : SiteSet).insert "λ").insert "한").contains "가" = false := by
  decide +kernel

end Tests.StructuredApplicationMetadata
