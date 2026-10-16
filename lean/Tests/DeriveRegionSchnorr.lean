import Zkc.Source.DeriveRegion
import Zkc.Source.RegionView
import Zkc.Source.Structured.ProjectedBody
import Zkc.Source.Structured.EqualityDerivationRules
import ZkcExamples.Structured.SchnorrInteractive

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option smartUnfolding false
noncomputable section

namespace Tests.DeriveRegionSources
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured

/-- The protocol view is generated directly, with no manually restated operation. -/
def schnorrView := region_view% SchnorrInteractive.program.payload.entry.body

theorem schnorr_view_exact : schnorrView = SchnorrInteractive.program.payload.entry.body := rfl

/-- The actual admitted dormant relation helper, selected from the checked table. -/
def schnorrFormula := SchnorrInteractive.program.payload.definitions[0]'(by decide)

theorem schnorr_formula_identity : schnorrFormula.helper = SchnorrInteractive.formula := rfl

def schnorrFormulaView := region_view% schnorrFormula.body

theorem schnorr_formula_view_exact : schnorrFormulaView = schnorrFormula.body := rfl

theorem schnorr_formula_association :
    BodyIn SchnorrInteractive.program.payload.definitions schnorrFormula.helper schnorrFormula.body := by
  exact BodyIn.of_checked schnorrFormula (by structured_mem)

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Reuse equality orientation at the real group-equality occurrence. The
scalar-multiplication prefix is discovered from the admitted helper body. -/
theorem schnorr_formula_reversed (table : Meanings F G) (base key : G) (secret : F) :
    Region.Derivation (meaning F G table) (fun op => .call op .done) schnorrFormulaView
      (Values.cons base (.cons key (.cons secret .nil))).get
      (.done (.cons (decide (secret • base = key)) .nil)) := by
  derive_region using (first
    | exact groupEqual_reverse_law _ _ _ _ _
    | (apply RegionMeaning.OperationLaw.identity; rfl))

theorem schnorr_formula_sound (table : Meanings F G) (base key : G) (secret : F) :
    schnorrFormula.body.denote (meaning F G table)
      (Values.cons base (.cons key (.cons secret .nil))).get =
      .done (.cons (decide (secret • base = key)) .nil) := by
  rw [← schnorr_formula_view_exact]
  exact (schnorr_formula_reversed table base key secret).sound_identity

end Tests.DeriveRegionSources
