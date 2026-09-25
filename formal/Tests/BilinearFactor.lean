import Zkc.Compiler.Analysis.FactorReuse
import Zkc.Polynomial.Bilinear.Factor

set_option autoImplicit false

open Zkc.Compiler.FactorReuse

namespace Tests.BilinearFactor
open Zkc.Polynomial.Bilinear.Factor Zkc.Modules.Factor

def fixtureQuery : Query := ⟨originKey 100,[0,5]⟩
def fixtureFacts : List Fact := [Zkc.Source.FactorInputs.fact (source 100) 0]
-- The plan the inference above produces, run on the materialized factor: the
-- only place this fixture reaches runPlan, and what it evaluates to.
#guard runPlan (materialized 100 1 2 3 4 2) fixtureQuery (infer fixtureFacts [0,5] fixtureQuery) = 60

theorem residual_is_reused :
    infer fixtureFacts [0,5] fixtureQuery = .reuse (Zkc.Source.FactorInputs.fact (source 100) 0) [5] := by decide

end Tests.BilinearFactor
