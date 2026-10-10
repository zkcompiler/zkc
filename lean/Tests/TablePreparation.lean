import Zkc.Polynomial.Bilinear.Preparation
import Zkc.Protocols.CommitmentSessions.Modular

set_option autoImplicit false

namespace Tests.TablePreparation
open Zkc.Modules.Preparation Zkc.Source.TablePreparation

def polyProgram (x y z : Nat) : Program Key (List Nat) Nat Nat :=
  .request (Zkc.Polynomial.Bilinear.key 100 1 2 3 4 x) fun t =>
  .emit (Zkc.Polynomial.Bilinear.consume t y) <|
  .request (Zkc.Polynomial.Bilinear.key 100 1 2 3 4 x) fun u =>
  .emit (Zkc.Polynomial.Bilinear.consume u z) (.done (Zkc.Polynomial.Bilinear.consume u z))

def groupProgram (h m0 r0 m1 r1 : Nat) : Program Key (List Nat) Nat Nat :=
  .request (Zkc.Protocols.CommitmentSessions.Modular.key h) fun t => .emit (Zkc.Protocols.CommitmentSessions.Modular.consume t m0 r0) <|
  .request (Zkc.Protocols.CommitmentSessions.Modular.key h) fun u => .emit (Zkc.Protocols.CommitmentSessions.Modular.consume u m1 r1) (.done (Zkc.Protocols.CommitmentSessions.Modular.consume u m1 r1))

/-- The exact same run/acquire/exec functions serve both source families. -/
theorem poly_observer (x y z : Nat) :
    (run provider prices .direct (polyProgram x y z) empty).trace =
    (run provider prices .memo (polyProgram x y z) empty).trace :=
  observer provider prices _ (fun _ tr => tr)
theorem group_observer (h m0 r0 m1 r1 : Nat) :
    (run provider prices .direct (groupProgram h m0 r0 m1 r1) empty).trace =
    (run provider prices .memo (groupProgram h m0 r0 m1 r1) empty).trace :=
  observer provider prices _ (fun _ tr => tr)

def fixture (p : Program Key (List Nat) Nat Nat) (mode : Mode) : List Nat :=
  let r := run provider prices mode p empty
  r.trace ++ [r.work,r.saved,r.overhead]
-- What each preparation mode costs on each program. Memoizing trades the
-- third column for the fourth and fifth, which is the whole claim.
#guard fixture (polyProgram 2 3 5) .direct = [38, 60, 8, 0, 0]
#guard fixture (polyProgram 2 3 5) .memo = [38, 60, 4, 4, 3]
#guard fixture (groupProgram 3 1 2 2 3) .direct = [0, 4, 24, 0, 0]
#guard fixture (groupProgram 3 1 2 2 3) .memo = [0, 4, 12, 12, 3]

theorem pure_cost_obstruction :
    (run provider prices .direct (polyProgram 2 3 5) empty).work ≠
    (run provider prices .memo (polyProgram 2 3 5) empty).work := by decide

def secretProbe (secret : Nat) : Program Key (List Nat) Nat Nat :=
  .request (Zkc.Protocols.CommitmentSessions.Modular.key 0) fun _ => .request (Zkc.Protocols.CommitmentSessions.Modular.key secret) fun _ => .emit 0 (.done 0)

theorem secret_hit_obstruction :
    (run provider prices .memo (secretProbe 0) empty).trace =
      (run provider prices .memo (secretProbe 1) empty).trace ∧
    (run provider prices .memo (secretProbe 0) empty).work ≠
      (run provider prices .memo (secretProbe 1) empty).work := by decide

/-- Exact-request memoization cannot promise even nonincrease of this priced
    total: a zero-arithmetic literal table costs three cache operations on reuse. -/
def cheap : Program Key (List Nat) Nat Nat :=
  .request ⟨1,900,[],[.lit 0]⟩ fun _ =>
  .request ⟨1,900,[],[.lit 0]⟩ fun _ => .done 0

theorem overhead_obstruction :
    (run provider prices .direct cheap empty).work +
      (run provider prices .direct cheap empty).overhead = 0 ∧
    (run provider prices .memo cheap empty).work +
      (run provider prices .memo cheap empty).overhead = 3 := by decide

end Tests.TablePreparation
