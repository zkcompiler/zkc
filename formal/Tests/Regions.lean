import Examples.TableProtocol.Invocation
import Zkc.Compiler.RegionArtifact
import Zkc.Source.RegionBounds

/-! Typed compact binding, profile separation, and continuation size controls. -/
set_option autoImplicit false
namespace Tests.Regions
open Lean Zkc.Source Zkc.Compiler TableProtocol

def declarations : List (InputDeclaration Ty) := [
  ⟨"x", .scalar .seven, .shared, .argument⟩,
  ⟨"y", .scalar .seven, .shared, .argument⟩]

def body : RawRegion Ty Protocol.Operation :=
  .bind .boolean (.letOp .equal [0, 1] (.ret 0)) (.branch 0 (.ret 1) (.ret 2))

def request : RegionArtifact.Request Ty Protocol.Operation :=
  ⟨⟨"trace", declarations, .scalar .seven, dependencies⟩, [], body⟩

def candidate : RegionArtifact.Candidate Ty Protocol.Operation :=
  ⟨⟨1, RegionArtifact.semanticsVersion, [], "direct-logical-plan", "direct-lowering",
    completeExecution, request.context, []⟩, body⟩

-- There is no Boolean input or artificial initial Boolean value.
example : (body.elaborate [.scalar .seven, .scalar .seven] (.scalar .seven)
    (language := Protocol.language)).isOk = true := by decide
example : (RegionArtifact.check request candidate (language := Protocol.language)).isOk = true := by decide
example : (RegionArtifact.check request { candidate with body := .ret 0 }
    (language := Protocol.language)).isOk = false := by decide
example : (RegionArtifact.check request
    { candidate with metadata := { candidate.metadata with semantics := "finite-source-1" } }
    (language := Protocol.language)).isOk = false := by decide
example : (RegionArtifact.check request
    { candidate with metadata := { candidate.metadata with requirements := [⟨"extra", "1"⟩] } }
    (language := Protocol.language)).isOk = false := by decide

-- A stopped body does not excuse a malformed suffix.
example : (RawRegion.bind .boolean (.stop .abort) (.ret 0) : RawRegion Ty Protocol.Operation).elaborate
    [.scalar .seven] (.scalar .seven) (language := Protocol.language) =
    .error (.invalidOperand 0 (.scalar .seven)) := by rfl
example : (RawRegion.bind (.scalar .seven) (.branch 0 (.ret 1) (.ret 99)) (.ret 0) :
    RawRegion Ty Protocol.Operation).elaborate [.boolean, .scalar .seven] (.scalar .seven)
    (language := Protocol.language) = .error (.invalidOperand 99 (.scalar .seven)) := by rfl

-- JSON round trips and profile rejection are executable integration controls.
-- The generic kernel-checked round trip is Region.elaborate_erase.

/-- A parametric family has one suffix per decision. Input positions track accumulated results. -/
def decisions : Nat → Nat → RawRegion Ty Protocol.Operation
  | 0, _ => .ret 0
  | n + 1, offset => .bind (.scalar .seven)
      (.branch (offset + 2)
        (.letOp (.base (.add .seven)) [0, offset + 1] (.ret 0))
        (.letOp (.base (.add .seven)) [0, 0] (.ret 0)))
      (decisions n (offset + 1))

theorem decisions_size (n offset : Nat) : (decisions n offset).nodeCount = 6 * n + 1 := by
  induction n generalizing offset with
  | zero => rfl
  | succ n ih => simp only [decisions, RawRegion.nodeCount, ih]; omega

example : (decisions 14 0).nodeCount = 85 := by decide

end Tests.Regions
