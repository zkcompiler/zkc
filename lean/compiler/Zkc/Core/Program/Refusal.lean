module

public import Zkc.Core.Program.Annotations
public import Zkc.Core.Program.Requirement

@[expose] public section

/-!
Refusals: the rules of the core, what a rule found, and the place of a program where it found
it, as data. Elaboration, the conditions of a body and the check of facts refuse in this one
form. The core words nothing: a frontend words a refusal from its rule, its place and what was
found, with its own map from places to source. What a rule found has the types and the written
operations of a dialect as parameters, so nothing here is about a dialect or the vocabulary; a
refusal of a program of functions (`ProgramRefusal`) is in `Program/NamedProgram.lean`.
-/

namespace Zkc.Core

/-- The rules of refusal of the core: each names what a program satisfies. -/
inductive Rule where
  /-- A name is in scope. -/
  | scope
  /-- The operands of an operation have the types that it takes. -/
  | operands
  /-- An instruction names each of its results. -/
  | results
  /-- A region or a function names each of its inputs. -/
  | inputs
  /-- An operation is a row of the vocabulary: its key names one. -/
  | row
  /-- An operation that the core owns is named with its types and its numbers. -/
  | owned
  /-- The data of a literal reads as its type. -/
  | literal
  /-- One definition before the caller has the key of the callee. -/
  | callee
  /-- Those who guard or choose may do so on the type of the condition. -/
  | condition
  /-- The regions of a choice give the same types. -/
  | regions
  /-- Those who perform a form of control may give what it gives. -/
  | gives
  /-- The subject of a case analysis is a variant that they may choose on. -/
  | variant
  /-- A case analysis has an arm for each alternative. -/
  | arms
  /-- The arms of a case analysis give the same types. -/
  | armTypes
  /-- The body of a loop gives back the carried values. -/
  | carried
  /-- A loop repeats as often as a count that they may repeat by. -/
  | count
  /-- Who performs an attempt may own one. -/
  | attempt
  /-- The body of a definition gives the results of its header. -/
  | outputs
  /-- The instructions of a body have their own addresses. -/
  | distinct
  /-- A definition binds each of its names at one place. -/
  | assignment
  /-- Every value of a linear type is used once. -/
  | linear
  /-- The header of a function says whether it can stop with a reason, as its body does. -/
  | stops
  /-- No definition before a definition has its key. -/
  | key
  /-- Admission requires a checked protocol projection. -/
  | protocol
  /-- Each participant in the body belongs to the enclosing protocol. -/
  | participants
  /-- Every holder of a protocol port is a declared role. -/
  | portHolders
  /-- Participants in the alternatives and iterations belong to that control. -/
  | enclosed
  /-- The association of a program names definitions of the program. -/
  | association
  /-- An application of an operation with a domain is inside it, by what is known there. -/
  | domain
  /-- A definition establishes each guarantee of its summary, by what is known where it
  returns. -/
  | guarantee
  /-- The summary of a function names, by their positions, its inputs in a requirement and its
  inputs followed by its results in a guarantee, and nothing else. -/
  | summary
  /-- A body annotation resolves and is well typed at its lexical site. -/
  | annotation
  /-- A supplied fact has evidence at its lexical site. -/
  | factEvidence
  /-- A lemma used by a step has established premises. -/
  | lemmaPremise
  /-- A loop establishes and preserves its invariant. -/
  | loopInvariant
deriving DecidableEq, Repr

/-- What a rule found, with the types `T` of a dialect and its written operations `Raw` as
values. -/
inductive Detail (T Raw : Type) where
  /-- A name: one that is not in scope, or one that is bound a second time. -/
  | name (name : Name)
  /-- The types expected and the types found. -/
  | types (expected found : List T)
  /-- A type that the rule does not allow there. -/
  | type (found : T)
  /-- The number expected and the number found. -/
  | number (expected found : Nat)
  /-- A written operation that names no operation. -/
  | operation (written : Raw)
  /-- The key of a callee, and the number of definitions before the caller that have it. -/
  | callee (key : Key) (found : Nat)
  /-- Types of values of which one may not be given. -/
  | given (types : List T)
  /-- The key of a definition. -/
  | key (key : Key)
  /-- Whether the header says that the function can stop, and whether its body can. -/
  | stops (header body : Bool)
  /-- A value bound at the place, by its name, and how often it is used. -/
  | uses (name : Name) (found : Nat)
  /-- A value from around the place, by its name, with a count of its uses: in the second
  region of a choice, in the first arm of a case analysis that differs from the first, in the
  body of a loop. -/
  | around (name : Name) (found : Nat)
  /-- An application that is not known to be inside its operation's domain: the written
  operation, the requirement that is not known, and what is known of the values that the
  requirement names, in the order in which it names them. -/
  | unjustified (operation : Raw) (requirement : Requirement Raw) (known : List (Option Range))
  /-- A guarantee of a summary that is not known where the definition returns: the guarantee, and
  what is known of the values that it names, in the order in which it names them. -/
  | unestablished (guarantee : Requirement Raw) (known : List (Option Range))
  /-- A requirement or a guarantee that the rule does not allow there. -/
  | requirement (requirement : Requirement Raw)
  | contractAssertion (clause : BodyAnalysis.ContractClause Raw)
  | unjustifiedAssertion (operation : Raw) (clause : BodyAnalysis.ContractClause Raw)
  | annotationSite (site : BodyAnalysis.AnnotationSite)
  | premise (site : BodyAnalysis.AnnotationSite) (index : Nat)
  | invariant (site : BodyAnalysis.AnnotationSite) (index : Nat) (preservation : Bool)
  /-- Nothing beyond the rule and the place. -/
  | nothing
deriving DecidableEq

/-- What a rule found, before it is at a place: what the rules of a dialect answer. -/
structure Finding (T Raw : Type) where
  rule : Rule
  detail : Detail T Raw
deriving DecidableEq

/-- A refusal: a rule, the place of a program that breaks it, and what the rule found there. -/
structure Refusal (T Raw : Type) where
  rule : Rule
  place : Place
  detail : Detail T Raw
deriving DecidableEq

section
variable {T Raw : Type}

/-- A refusal at an instruction of a definition, inside the blocks given. -/
def refuseAt (definition : Key) (blocks : List (Key × Nat)) (instruction : Key) (rule : Rule)
    (detail : Detail T Raw) : Refusal T Raw :=
  ⟨rule, ⟨definition, blocks, some instruction, none⟩, detail⟩

/-- A refusal of a definition as a whole. -/
def refuseWhole (definition : Key) (rule : Rule) (detail : Detail T Raw) : Refusal T Raw :=
  ⟨rule, ⟨definition, [], none, none⟩, detail⟩

/-- What the rules of a dialect answered, at an instruction of a definition. -/
def Finding.refuseAt (finding : Finding T Raw) (definition : Key) (blocks : List (Key × Nat))
    (instruction : Key) : Refusal T Raw :=
  Zkc.Core.refuseAt definition blocks instruction finding.rule finding.detail

end

end Zkc.Core
