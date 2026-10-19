module

public import Zkc.Source.Structured.Association

@[expose] public section

namespace Zkc.Source.Structured

/-- The checked declaration already contains its typed view. Reusing that view
requires membership, but no duplicate symbol, ABI, operation tree or raw witness. -/
theorem BodyIn.of_checked {definitions : List CheckedDefinition}
    (definition : CheckedDefinition) (member : definition ∈ definitions) :
    BodyIn definitions definition.helper definition.body :=
  BodyIn.of_mem member rfl definition.exactBody.symm

end Zkc.Source.Structured
