import Zkc.Formal.ModelComparison
import Zkc.Formal.Written.Source
import Zkc.Tests.Formal.SourceProtocolRoots

open Zkc.Core Zkc.Formal Zkc.Formal.ModelComparison

namespace Zkc.Tests.Formal.ModelComparison

-- These tests compute the meaning of small programs by Lean's own reduction.
unseal Zkc.Core.fnMeaning Zkc.Core.roleMeaning Zkc.Core.protocolMeaning

variable {V : Vocabulary} (M N : Model V)

private def bitRelation : Values M N
  | .bool, x, y => x = y
  | _, _, _ => False

private def request (at_ : Occurrence) (argument : Bool) : GOp M :=
  .given (.request ⟨1⟩) 0 [1] at_ [.bool] (.cons argument .nil) .bool

private def echo (at_ : Occurrence) (argument : Bool) : Protocol M Bool :=
  .call (request M at_ argument) fun x => .done x

/-- Both answers of a Boolean service are covered in arbitrary models of the vocabulary. -/
theorem echo_related (at_ : Occurrence) (argument : Bool) :
    ProtocolSimulation (bitRelation M N) Eq (echo M at_ argument) (echo N at_ argument) := by
  apply SupportSimulation.call
  · exact .given (.cons rfl .nil)
  · intro y _
    exact ⟨y, trivial, rfl⟩
  · intro x y _ _ same
    exact .done same

-- A concrete true answer witnesses a returning abstract run with a related result.
example (at_ : Occurrence) :
    ∃ a, (echo M at_ false).CanReturn (permitted M) a ∧ a = true :=
  (echo_related M N at_ false).canReturn (.call _ true trivial (.done true))

-- Even identical replies cannot repair a changed request payload.
example (at_ : Occurrence) :
    ¬ JointOperations (bitRelation M N) (request M at_ false) (request N at_ true) Eq := by
  intro same
  cases same with
  | given payload =>
    cases payload with
    | cons equal _ => exact Bool.noConfusion equal

-- The path and instruction key are both part of the correspondence.
example {first second : Occurrence} (changed : first ≠ second) :
    ¬ JointOperations (bitRelation M N) (request M first false) (request N second false) Eq := by
  intro same
  cases same
  exact changed rfl

-- The echo heard by one role records the owner. Swapping it for another role is observable.
example (at_ : Occurrence) (owner other : Role) (different : owner ≠ other) :
    ¬ RoleOperations (bitRelation M N) (.hear (.request ⟨1⟩) owner at_ .bool)
      (.hear (.request ⟨1⟩) other at_ .bool) Eq := by
  intro same
  cases same
  exact different rfl

-- The return narrows the result to its declared holder, as emitted by the frontend.
private abbrev bitPort (V : Vocabulary) : LTy V := ⟨.bool, [0]⟩
private abbrev bitHeader (V : Vocabulary) : ProtocolHeader V := ⟨⟨0⟩, 2, [bitPort V], [bitPort V], .nil⟩
private abbrev bitNames (V : Vocabulary) : Names (bitHeader V).ins := .cons 0 .nil
private def identityBody (V : Vocabulary) : Prot V ⟨[], []⟩ (bitHeader V) (bitNames V) :=
  .op ⟨0⟩ (.narrow [0] (fun _ h => h)) (.cons ⟨0, rfl⟩ .nil) (.cons 1 .nil)
    (.ret (.cons ⟨1, rfl⟩ .nil))
private def identityProtocol (V : Vocabulary) : Typed V :=
  Written.singletonProgram (bitHeader V) (bitNames V) (identityBody V)
    (by
      exact {
        within := @of_decide_eq_true _ (decideWithin (List.range 2) (identityBody V)) rfl
        located := by simp [bitPort]
        enclosed := @of_decide_eq_true _ (decideEnclosed (identityBody V)) rfl
        distinct := (Term.repeatedAddress_eq_none _).mp rfl
        shaped := rfl
        linear := rfl
        armed := rfl
        once := (Term.rebound_eq_none _ _).mp rfl })

private theorem identity_related (r : Values M N) (role : Fin 2) (path : List Frame) :
    atRole r (identityProtocol V) (hdr := bitHeader V) .head role path := by
  intro a b _ _ args
  cases a with
  | cons x rem =>
    cases rem
    cases b with
    | cons y rem =>
      cases rem
      obtain ⟨_ | _ | k, h⟩ := role
      · exact .done args
      · exact .done args
      · omega

-- Transfer the member and the role theorem together to the program returned by admission.
private def hasIdentityRoles (program : Typed V) : Prop :=
  ∃ member : Member program.headers.protocols (bitHeader V),
    ∀ (M N : Model V) (r : Values M N) (role : Fin 2) (path : List Frame),
      atRole r program member role path

private def certifyIdentity {a : Admitted V} {named : NamedProgram V} {assoc : Association}
    (accepted : admit named assoc = .ok a) : Option (PLift (hasIdentityRoles a.program)) :=
  letI := identifyAdmitted accepted (identityProtocol V)
  if same : a.program = identityProtocol V then
    some ⟨same ▸ ⟨.head, identity_related⟩⟩
  else none

private def checkIdentitySource : IO Unit := do
  let file := "role_identity.zkc"
  let text := "module role_identity\npub protocol Identity roles(P, V)(bit: bool @P) -> answer: bool @P:\n    return bit\n"
  for (sourceText, expected) in [(text, true), (text.replace "@P" "@V", false)] do
    let source := Zkc.Frontend.Syntax.parseString file sourceText
    let root ← SourceProtocolRoots.admitRoot ⟨file, source⟩ (fun _ => pure none)
    unless (certifyIdentity root.evidence.accepted).isSome == expected do
      throw (IO.userError "cross-model role simulation control failed for the admitted identity protocol")

#eval checkIdentitySource

-- The abstract service can return false, whereas the concrete service can return true too.
-- Its extra answer violates an every-path property of the abstract process.
private abbrev bits : Sig := ⟨Unit, fun _ => Bool⟩
private def readBit : Process bits Unit Bool := .call () .done

example (relation : EffectRelation bits bits) :
    ¬ SupportSimulation relation (fun _ x => x = false) (fun _ _ => True) Eq readBit readBit := by
  intro sim
  have all := sim.every (first := (· = false)) (second := (· = false)) (stop := fun _ => False)
    (fun _ _ h hx => h ▸ hx) (fun _ h => h)
  exact Bool.noConfusion (all true trivial)

end Zkc.Tests.Formal.ModelComparison
