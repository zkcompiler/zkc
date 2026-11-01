module

public meta import Lean.Meta.Tactic.Simp.RegisterCommand

public meta section

/-! Named proof-rule sets use Lean's ordinary simp attributes. Registration
must precede the module that assigns rules to the attribute. No set is selected
implicitly by the source-reference elaborator. -/

/-- Structural equations for typed source presentations, excluding helper
mathematics and callee implementations. -/
register_simp_attr zkc_source_structure
