module

public import Zkc.Claims.Wire

@[expose] public section

/-! Typed versioned exports. Registration never interprets a declaration name.
An absent definition is different from an unregistered name or version. -/

set_option autoImplicit false
namespace Zkc.Claims
universe u

structure Export (α : Type u) where
  identifier : Identifier
  schema : String
  definition : Option α

structure Registry (α : Type u) where
  exports : List (Export α) := []

/-- Duplicate keys are refused even when their printed schemas happen to agree. -/
def Registry.register {α : Type u} (registry : Registry α) (entry : Export α) :
    Except ResolutionError (Registry α) :=
  if registry.exports.any (fun existing => existing.identifier == entry.identifier) then
    .error (.conflict entry.identifier)
  else .ok ⟨registry.exports ++ [entry]⟩

/-- Also check conflicts in externally assembled registry lists. -/
def Registry.lookup {α : Type u} (registry : Registry α) (identifier : Identifier) :
    Except ResolutionError (Export α) :=
  match registry.exports.filter (fun entry => entry.identifier == identifier) with
  | [] => .error (.unknownIdentifier identifier)
  | [entry] => .ok entry
  | _ :: _ :: _ => .error (.conflict identifier)

/-- A property is extended only by publishing an elaborator and a typed meaning
function. Evidence routes have no access to replace that function. -/
structure PropertyExport (Subject : Type u) where
  Arguments : Subject → Type
  elaborate : (request : Wire.Request) → (subject : Subject) → Except ResolutionError (Arguments subject)
  meaning : (subject : Subject) → Arguments subject → Except Incomplete Prop
  requiredLinks : (subject : Subject) → Arguments subject → List Obligation := fun _ _ => []

/-- The index pins the exact wire request, admitted subject and registered
export. The lookup and elaboration equations are kernel checked. -/
structure Resolved {Subject : Type u} (registry : Registry (PropertyExport Subject))
    (reference : Subject → SubjectRef) (subject : Subject) (request : Wire.Request) where
  subjectMatched : request.subject = reference subject
  entry : Export (PropertyExport Subject)
  registered : registry.lookup request.property = .ok entry
  property : PropertyExport Subject
  defined : entry.definition = some property
  arguments : property.Arguments subject
  elaborated : property.elaborate request subject = .ok arguments

def Resolved.meaning {Subject : Type u} {registry : Registry (PropertyExport Subject)}
    {reference : Subject → SubjectRef} {subject : Subject} {request : Wire.Request}
    (resolved : Resolved registry reference subject request) : Except Incomplete Prop :=
  resolved.property.meaning subject resolved.arguments

def Resolved.requiredLinks {Subject : Type u} {registry : Registry (PropertyExport Subject)}
    {reference : Subject → SubjectRef} {subject : Subject} {request : Wire.Request}
    (resolved : Resolved registry reference subject request) : List Obligation :=
  resolved.property.requiredLinks subject resolved.arguments

/-- Unknown versions fail resolution. A known entry whose definition is absent
returns the explicit missing-definition state before any proof is sought. -/
def resolve {Subject : Type u} (registry : Registry (PropertyExport Subject))
    (reference : Subject → SubjectRef) (subject : Subject) (request : Wire.Request) :
    Except ResolutionError (Except Incomplete (Resolved registry reference subject request)) := do
  if matched : request.subject = reference subject then
    match registered : registry.lookup request.property with
    | .error error => .error error
    | .ok entry =>
      match found : entry.definition with
      | none => return .error ⟨[entry.identifier.name ++ "@" ++ toString entry.identifier.version]⟩
      | some property =>
        match elaborated : property.elaborate request subject with
        | .error error => .error error
        | .ok arguments => return .ok ⟨matched, entry, registered, property, found, arguments, elaborated⟩
  else .error .subjectMismatch

/-- A checked resolved record is exactly the result of the resolver. This lets
generated consumers reuse lookup/elaboration equations without unfolding a
recursive expression interpreter or substituting their own proposition. -/
theorem Resolved.resolve_eq {Subject : Type u} {registry : Registry (PropertyExport Subject)}
    {reference : Subject → SubjectRef} {subject : Subject} {request : Wire.Request}
    (resolved : Resolved registry reference subject request) :
    resolve registry reference subject request = .ok (.ok resolved) := by
  rcases resolved with ⟨matched, entry, registered, property, defined, arguments, elaborated⟩
  simp only [resolve, dite_eq_left matched]
  split
  next error same => simp_all
  next actual same =>
    have equal : actual = entry := Except.ok.inj (same.symm.trans registered)
    subst actual
    split
    next missing => simp_all
    next actual same =>
      have equal : actual = property := Option.some.inj (same.symm.trans defined)
      subst actual
      split
      next error same => simp_all
      next actual same =>
        have equal : actual = arguments := Except.ok.inj (same.symm.trans elaborated)
        subst actual
        rfl

end Zkc.Claims
