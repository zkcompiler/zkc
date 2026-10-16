import Lean

namespace Tests.DerivationCounter

/-- Counts local solver calls across tactic backtracking. Use with async disabled. -/
initialize solverCalls : IO.Ref Nat ← IO.mkRef 0

end Tests.DerivationCounter
