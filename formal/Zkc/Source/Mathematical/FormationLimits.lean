/-! Consumer bounds for mathematical formation. These are independent of
logical carrier depth and closed-call-chain depth. The native checker counts
one level for each step/node and another for its nested body/region.
Sibling steps never consume nesting depth; each pure region starts at zero.
-/

namespace Zkc.Source.Mathematical.FormationLimits

def bodyDepth : Nat := 64
def regionDepth : Nat := 64
/-- Root depth is zero; cached heights count a leaf as one. -/
def typeDepth : Nat := 64
/-- Expanded constructors, counting each occurrence of a shared child. -/
def typeNodes : Nat := 65536

end Zkc.Source.Mathematical.FormationLimits
