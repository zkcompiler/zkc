import ZkcArkLib.Mathematical.Execution
import ZkcArkLib.Mathematical.PolynomialQueries
import Zkc.Source.Mathematical.Meaning

set_option autoImplicit false
namespace TestsArkLib.Mathematical
open Zkc.Source Zkc.Source.Mathematical ZkcArkLib.Mathematical

abbrev language : Zkc.Source.Mathematical.Language := ⟨Unit, Empty, (fun op => nomatch op),
  (fun op => nomatch op), (fun _ => ()), (), (fun _ => Unit)⟩
abbrev counter : Capability Unit Unit := ⟨[()], [], ()⟩
abbrev meaning : Interpretation language where
  Value _ := Nat
  pure op := nomatch op
  condition n := n != 0
  index i := i.val

def source : Zkc.Source.Mathematical.Program [()] language [counter] [] [] [] :=
  .query 0 () .here (by decide) .nil (by decide)
    (.query 1 () .here (by decide) .nil (by decide) (.stop 2 () .reject))

def handler : PIR.Handler (interface () language [counter] meaning.Value) Nat Nat
  | .query location .here _ .nil, state => ⟨.returned state, state + 1, [location.site]⟩
  | .stop location reason, state => ⟨.stopped reason, state, [location.site]⟩
  | .send .., state => ⟨.returned (), state, []⟩
  | .receive .., state => ⟨.stopped .refused, state, []⟩

/-- The simulated computation comes from the actual typed mathematical source. -/
theorem actual_shared_service :
    simulate handler (encode (source.openMeaning meaning () (fun ref => nomatch ref))) 0 =
      ⟨.stopped .reject, 2, [0, 1, 2]⟩ := by
  rw [simulate_encode]
  rfl

example (point : ZMod 5) :
    OracleInterface.answer
      (Zkc.Protocols.Sumcheck.messagePolynomial (⟨1, 2, 2⟩ : Zkc.Protocols.AlgebraicRounds.Message (ZMod 5)))
      point = (1 + (2 * point + 2 * (point * point))) := by
  rw [round_query_answer]
  rfl

end TestsArkLib.Mathematical
