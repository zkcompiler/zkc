module

public import Mathlib.Data.Rat.Defs

@[expose] public section

/-! Probability-free claim envelopes. Digests are audit identities supplied by
admission tooling; the typed subject and kernel proof, rather than a hash, are
authoritative. Attachments and proposed proof methods never enter a request. -/

set_option autoImplicit false
namespace Zkc.Claims

inductive Stage where
  | interactive | compiledIdeal | executableBytes
  deriving DecidableEq, Repr

structure ArtifactDigest where
  role : String
  digest : String
  deriving DecidableEq, Repr

structure SubjectRef where
  unitDigest : String
  entry : String
  stage : Stage
  artifacts : List ArtifactDigest
  deriving DecidableEq, Repr

structure Identifier where
  name : String
  version : Nat
  deriving DecidableEq, Repr

namespace Wire

inductive Binary where
  | add | sub | mul | div | pow
  deriving DecidableEq, Repr

/-- A finite wire tree, never a Lean term or a proposition. -/
inductive Expr where
  | natural (value : Nat)
  | reference (name : String)
  | application (identifier : String) (version : Option Nat) (arguments : List (Option String × Expr))
  | binary (operator : Binary) (left right : Expr)
  | neg (operand : Expr)
  | list (items : List Expr)
  deriving Repr

structure Application where
  identifier : Identifier
  arguments : List (Option String × Expr) := []
  deriving Repr

inductive TargetRef where
  | retained (protocol : String) (clause : Nat) (name : String)
  | importedLanguage (protocol : String) (application : Application)
  deriving Repr

/-- Version zero imports a closed typed language export. Preserve the complete
wire application and refuse its unsupported parameters instead of dropping them. -/
def TargetRef.matches : TargetRef → TargetRef → Bool
  | .retained protocol index name, .retained expectedProtocol expectedIndex expectedName =>
      protocol == expectedProtocol && index == expectedIndex && name == expectedName
  | .importedLanguage protocol application, .importedLanguage expectedProtocol expected =>
      protocol == expectedProtocol && application.identifier == expected.identifier &&
        application.arguments.isEmpty && expected.arguments.isEmpty
  | .retained .., .importedLanguage .. | .importedLanguage .., .retained .. => false

/-- A successful supported-schema comparison pins the complete target value. -/
theorem TargetRef.eq_of_matches (actual expected : TargetRef)
    (matched : actual.matches expected = true) : actual = expected := by
  cases actual <;> cases expected
  · simp only [TargetRef.matches, Bool.and_eq_true, beq_iff_eq] at matched
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := matched
    rfl
  · cases matched
  · cases matched
  · rename_i protocol application expectedProtocol expectedApplication
    rcases application with ⟨identifier, arguments⟩
    rcases expectedApplication with ⟨expectedIdentifier, expectedArguments⟩
    simp only [TargetRef.matches, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at matched
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := matched
    rfl

structure Acceptance where
  output : Bool := true
  port : Nat
  role : Nat
  path : List Nat := []
  deriving DecidableEq, Repr

inductive Quantity where
  | scalar (expression : Expr)
  | charged (charges : List (String × Expr))
  | guarantee (form : Application)
  deriving Repr

/-- The frontend envelope enriched with the exact admission/stage identity. -/
structure Request where
  subject : SubjectRef
  property : Identifier
  parameters : Option Expr := none
  model : Application
  target : TargetRef
  accept : Acceptance
  quantity : Quantity
  capabilities : List Application := []
  deriving Repr

end Wire

structure Attachment where
  moduleName : String
  declaration : String
  label : String
  owner : String
  block : Nat
  claim : Nat
  sourceBegin : Nat
  sourceEnd : Nat
  deriving DecidableEq, Repr

inductive ResolutionError where
  | subjectMismatch
  | unknownIdentifier (identifier : Identifier)
  | conflict (identifier : Identifier)
  | schema (message : String)
  | targetMismatch
  | acceptanceMismatch
  | siteMismatch (site : String)
  | stageMismatch
  deriving DecidableEq, Repr

structure Incomplete where
  definitions : List String
  deriving DecidableEq, Repr

/-- Evaluation responsibility layers: protocol, mathematics, domain
installation, infrastructure glue, system extension and external dependency. -/
inductive Responsibility where
  | protocol | mathematics | domain | infrastructure | system | external
  deriving DecidableEq, Repr

def Responsibility.tag : Responsibility → String
  | .protocol => "P"
  | .mathematics => "M"
  | .domain => "D"
  | .infrastructure => "I"
  | .system => "S"
  | .external => "X"

/-- The goal can be a dependent telescope over parameters, reading, checkpoint
and path conditions. Those hypotheses remain part of the kernel statement. -/
structure Obligation where
  identifier : String
  context : String
  goal : Prop
  responsibility : Responsibility

inductive Status where
  | incomplete | open | certified
  deriving DecidableEq, Repr

end Zkc.Claims
