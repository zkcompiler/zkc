module

public import ZkcTools.StructuredSource.ReferenceLaws

public meta section

/-! Selection is finite checked syntax work. It supplies only exact body
associations; dependency equations and mathematics are separate obligations. -/
namespace ZkcTools.StructuredSource

macro "select_reference_bodies" : tactic =>
  `(tactic| focus (constructor <;> bind_structured_bodies))

end ZkcTools.StructuredSource
