module

public import Zkc.Core.Facts.Contracts.Typing

@[expose] public section

namespace Zkc.Core.BodyAnalysis

variable {D : Dialect} {Raw : Type} [DecidableEq D.Ty]

/-- Execute the walk only after structural checks succeed, including on semantic dead paths. -/
def analyseCheckedFrom [DecidableEq Raw] (cfg : Config D Raw) (notes : Annotations Raw)
    {ins outs : List D.Ty} (summary : Contract Raw) (inputs : Names ins)
    (body : Term D (Ctx.empty.extend inputs) outs) (start : Values Raw) :
    Except DefinitionCheckError (Exit D Raw cfg.domain.State outs) :=
  match checkDefinition cfg.assertions cfg.lemmas inputs body notes summary with
  | .error reason => .error reason
  | .ok () => .ok (analyseFrom cfg notes summary inputs body start)

end Zkc.Core.BodyAnalysis
