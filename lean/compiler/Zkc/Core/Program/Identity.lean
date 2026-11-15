module


@[expose] public section

/-!
Identity: keys, roles, labels, occurrences, sites, places, reasons.

A key identifies a definition, an event or a block; a number is a position and nothing else.
An occurrence is where an event happened in a run: the path of applications, iterations and
attempts that reached it, then its key.
-/

namespace Zkc.Core

/-- The key of a definition or of an instruction: of the event, the block, the loop, the
choice, the guard or the application that the instruction is. The producer gives it, by the
reference's rule (a definition by its declaration and its static arguments, an instruction by
its site), so that it does not change when something else is inserted. The meaning of an
interactive protocol does not depend on which keys are chosen; the identity of a deployed
scheme and its transcript do. The instructions of a definition's body have different keys,
except that the blocks of one stepped loop repeat them, each under its number; the keys of the
definitions of a program are different. -/
structure Key where
  number : Nat
deriving DecidableEq, Repr, Hashable

abbrev Role := Nat

/-- The roles that hold a value: strictly increasing, so that equal sets are equal. Every
operation below keeps the order. -/
abbrev Holders := List Role

namespace Holders

def insert (r : Role) : Holders → Holders
  | [] => [r]
  | h :: rest => if r < h then r :: h :: rest else if r = h then h :: rest else h :: insert r rest

def ofList (roles : List Role) : Holders := roles.foldr insert []

def map (ρ : Role → Role) (holders : Holders) : Holders := ofList (List.map ρ holders)

end Holders

/-- One step of the path to an event. An iteration is reached by the key of its loop and its
number, so that it is not confused with an application or with another loop. An attempt is
the key of the attempt and its number: the retry of a deployed role puts it in front of every
private coin that the role owns in the body of that attempt, so that a coin asked again in a
later attempt is asked at another occurrence. Nothing between roles is under it, and neither
is a request to a service. -/
inductive Frame where
  | application (key : Key)
  | iteration (loop : Key) (number : Nat)
  | attempt (key : Key) (number : Nat)
deriving DecidableEq, Repr

/-- What names an instruction, a field of the record of a run, or a block: a key, or the key
of a loop and the number of one of its iterations, which a block of a stepped loop is and
whose frame is `Frame.iteration loop number`. -/
inductive Label where
  | key (key : Key)
  | step (loop : Key) (number : Nat)
deriving DecidableEq, Repr

structure Occurrence where
  path : List Frame
  key : Key
deriving DecidableEq, Repr

/-- A site: the keys of the applications that reach an instruction from the entry, then its
key. Under a loop or in the blocks of a stepped loop it stands for every occurrence. -/
structure Site where
  through : List Key
  key : Key
deriving DecidableEq, Repr

/-- A place in a program: the key of the definition, the blocks around the instruction (each
the key of its loop and its number, the outermost first), the key of the instruction, and the
role when it is about a role program. A place names one instruction of a definition. -/
structure Place where
  definition : Key
  blocks : List (Key × Nat)
  instruction : Option Key
  role : Option Role
deriving DecidableEq, Repr

/-- The keys of the applications on a path; iterations and attempts are dropped. -/
def Frame.applications : List Frame → List Key
  | [] => []
  | .application key :: rest => key :: Frame.applications rest
  | .iteration _ _ :: rest => Frame.applications rest
  | .attempt _ _ :: rest => Frame.applications rest

/-- The site of an occurrence. -/
def Occurrence.site (at_ : Occurrence) : Site := ⟨Frame.applications at_.path, at_.key⟩

/-- The reasons that a program names. -/
inductive Reason where
  | reject
  | abort
  | exhausted
  | refused
deriving DecidableEq, Repr

/-- How a process stops: with a reason at the occurrence of a guard or of an attempt, or
outside the domain of an operation. An admitted program never stops `undefined`. -/
inductive Stop where
  | declared (why : Reason) (at_ : Occurrence)
  | undefined
deriving DecidableEq, Repr

/-- Whether a stop is the reason `abort`. -/
def Stop.isAbort : Stop → Bool
  | .declared .abort _ => true
  | _ => false

end Zkc.Core
