import Tools.RequirementChecker.Transport
import Tools.Interactive.Requirements

/-! Regression tests for the maintained requirement calculus and its carrier.
No parallel equality calculus: semantic examples use Derives.sound itself. -/
set_option autoImplicit false
namespace Tests.Requirements
open Zkc.Source.Requirements

private def a : Term := .root "F"
private def b : Term := .root "G"
private def s : Term := .root "S"
private def lhs : Term := .apply "Poly" [a, s]
private def rhs : Term := .apply "Poly" [b, s]
private def assumptions : List Predicate := [.equal a b]

/-- Equality of actuals shares projected members through a pure selection. -/
theorem member_sharing : Derives assumptions []
    (.equal (.project lhs "Commitment") (.project rhs "Commitment")) :=
  .projection _ (.application _ (.cons (.assumption (by simp [assumptions]))
    (.cons (.reflexivity s) .nil)))

theorem member_sharing_sound (model : Model)
    (provided : ∀ p ∈ assumptions, p.Holds model) :
    (Term.project lhs "Commitment").denote model = (Term.project rhs "Commitment").denote model :=
  member_sharing.sound model provided (by simp)

private def cert : List Step := [
  ⟨.equal a b, .assumption 0⟩,
  ⟨.equal s s, .reflexivity⟩,
  ⟨.equal lhs rhs, .application [0, 1]⟩,
  ⟨.equal (.project lhs "Commitment") (.project rhs "Commitment"), .projection 2⟩]
example : (check assumptions [] cert).isSome = true := by decide
example : (check assumptions [] (cert.take 2 ++ [⟨.equal lhs rhs, .application [1, 0]⟩])).isSome = false := by decide
example : (check assumptions [] (cert.take 2 ++ [⟨.equal lhs rhs, .application [0]⟩])).isSome = false := by decide
example : (check assumptions [] (cert.take 2 ++ [⟨.equal lhs rhs, .application [0, 2]⟩])).isSome = false := by decide
example : (check assumptions [] (cert.take 2 ++ [⟨.equal lhs (.apply "Other" [b,s]), .application [0,1]⟩])).isSome = false := by decide
example : (check assumptions [] [⟨.equal (.apply "Seal" []) (.apply "Seal" []), .application []⟩]).isSome = true := by decide

#guard ((Tools.Interactive.Requirements.check assumptions
    [.equal (.project lhs "Commitment") (.project rhs "Commitment")]).isOk == true)
#guard ((Tools.Interactive.Requirements.check assumptions
    [.equal lhs (.apply "Poly" [s,b])]).isOk == false)
#guard ((Tools.Interactive.Requirements.check assumptions
    [.equal lhs (.apply "Other" [b,s])]).isOk == false)
#guard ((Tools.Interactive.Requirements.check
    (assumptions ++ [.relation "Ready" [lhs,s]]) [.relation "Ready" [rhs,s]]).isOk == true)

-- Concrete models distinguish heads and ordered arguments. Congruence supplies
-- neither injectivity nor an assertion that arbitrary named roots are unequal.
private def orderedModel : Model where
  Identity := Nat
  root name := if name == "S" then 2 else 1
  project value _ := value
  relation _ _ := True
  apply head args := if head == "Poly" then args.headD 0 else 9
example : lhs.denote orderedModel ≠ (Term.apply "Poly" [s,b]).denote orderedModel := by simp [lhs, s, b, a, Term.denote, orderedModel]
example : lhs.denote orderedModel ≠ (Term.apply "Other" [b,s]).denote orderedModel := by simp [lhs, s, b, a, Term.denote, orderedModel]

private def accepted (input : String) : Bool := (Tools.RequirementChecker.dispatch input).isOk
private def refusal (input : String) : Option String :=
  match Tools.RequirementChecker.dispatch input with
  | .error code => some code
  | .ok _ => none
#guard (accepted "[[\"zkc.requirements/1\",[[null,\"X\"],[\"apply\",\"Seal\",[]]],[],[],[[\"=\",[1,1]]]],[\"zkc.requirements-certificate/1\",[[[\"=\",[1,1]],\"application\",[],0]],[0]]]" == true)
#guard (accepted "[[\"zkc.requirements/1\",[[\"apply\",\"Seal\",[0]]],[],[],[]],[\"zkc.requirements-certificate/1\",[],[]]]" == false)
#guard (accepted "[[\"zkc.requirements/1\",[[\"apply\",\"\",[]]],[],[],[]],[\"zkc.requirements-certificate/1\",[],[]]]" == false)
#guard (accepted "[[\"zkc.requirements/1\",[[\"apply\",\"Seal\",[]],[\"apply\",\"Seal\",[]]],[],[],[]],[\"zkc.requirements-certificate/1\",[],[]]]" == false)
#guard (accepted "[[\"zkc.requirements/1\",[[null,\"F\"]],[],[],[[\"=\",[0,0]]]],[\"zkc.requirements-certificate/1\",[[[\"=\",[0,0]],\"reflexivity\",[],0]],[0]]]" == true)
-- One request format and one certificate format; a raised version name is refused.
#guard (refusal "[[\"zkc.requirements/2\",[],[],[],[]],[\"zkc.requirements-certificate/1\",[],[]]]" == some "requirements-version")
#guard (refusal "[[\"zkc.requirements/1\",[],[],[],[]],[\"zkc.requirements-certificate/2\",[],[]]]" == some "requirements-version")
-- A step names the declaration it uses; one beyond the table is refused.
#guard (refusal "[[\"zkc.requirements/1\",[[null,\"F\"]],[],[],[[\"=\",[0,0]]]],[\"zkc.requirements-certificate/1\",[[[\"=\",[0,0]],\"reflexivity\",[],1]],[0]]]" == some "requirements-declaration")

#print axioms Derives.sound
#print axioms checked_sound
#print axioms member_sharing_sound
end Tests.Requirements
