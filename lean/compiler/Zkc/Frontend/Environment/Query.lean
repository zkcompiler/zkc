module

public import Std.Data.HashMap
public import Zkc.Frontend.Basic.Diagnostic

@[expose] public section

set_option autoImplicit false

/-!
# Tables of requests

Everything that depends on static values is computed on request, once, and remembered by what
was asked: the closed signature of a declaration at values, the typed body of an instance, what
the passes make of it, where it is in the emitted package. Each kind of request has a table.
An entry is entered as in progress when it is first asked for, so a request that reaches itself
is seen (NL1); it keeps who first asked for it and from where, which is the chain of a
diagnostic (SP7); and it keeps the requests that its own computation made, from which what an
instance reaches is read, and from which a later run could tell what a change invalidates.

Every request is about an instance, so a request is named by its kind and its instance.
-/

namespace Zkc.Frontend

inductive QueryKind where
  /-- The closed signature of a declaration at static values. -/
  | signature
  /-- What the body of an instance came to, with what is kept of it beside its tree. -/
  | body
  /-- The typed tree of an instance. -/
  | tree
  /-- The body after the passes of roles, linearity and sites. -/
  | checked
  deriving Inhabited, BEq, Hashable, Repr

/-- A request: its kind and the instance it is about. -/
structure QueryRef where
  kind : QueryKind
  «instance» : Nat
  deriving Inhabited, BEq, Hashable, Repr

inductive QueryState (ρ : Type) where
  | inProgress
  | done (result : ρ)
  /-- Refused; the diagnostic is logged. A later request finds it failed and reports nothing. -/
  | failed
  /-- A default instance whose `where` does not hold (SP7): it is not an instance, nothing is
  refused and nothing is logged. A later request for it as a default instance skips it again;
  a request that the program makes computes it, and is refused where the `where` fails (SP4). -/
  | skipped
  /-- Not computed here: it needs a form of a later layer. -/
  | waiting (reason : String)
  /-- Not checked to the end: a budget of the compiler ran out, here or in a request it made.
  It is not refused: a later request finds it exhausted, never failed (SP10). -/
  | exhausted (exhaustion : Exhaustion)
  deriving Inhabited

structure QueryEntry (κ ρ : Type) where
  key : κ
  state : QueryState ρ
  /-- What was asked, as a chain line names it, and the place of the first request. -/
  requested : ChainFrame
  /-- The request during whose computation this one was first made; none for a root. -/
  requestedBy : Option QueryRef := none
  /-- The requests that the computation of this one made, each once, in order. -/
  requests : Array QueryRef := #[]

instance {κ ρ : Type} [Inhabited κ] : Inhabited (QueryEntry κ ρ) :=
  ⟨{ key := default, state := .failed, requested := default }⟩

structure QueryTable (κ ρ : Type) [BEq κ] [Hashable κ] where
  entries : Array (QueryEntry κ ρ) := #[]
  index : Std.HashMap κ Nat := {}

namespace QueryTable

variable {κ ρ : Type} [BEq κ] [Hashable κ]

instance : Inhabited (QueryTable κ ρ) := ⟨{}⟩

def find? (table : QueryTable κ ρ) (key : κ) : Option Nat := table.index[key]?

def entry? (table : QueryTable κ ρ) (key : κ) : Option (QueryEntry κ ρ) :=
  (table.index[key]?).bind (table.entries[·]?)

/-- The result of a request that is done. -/
def result? (table : QueryTable κ ρ) (key : κ) : Option ρ :=
  match table.entry? key with
  | some { state := .done result, .. } => some result
  | _ => none

/-- The number of a key, entering it as in progress when it is new. The flag says whether it
is new. The table is taken apart before it grows, so that a table that no one else holds grows
in place. -/
def intern (table : QueryTable κ ρ) (key : κ) (requested : ChainFrame)
    (requestedBy : Option QueryRef) : QueryTable κ ρ × Nat × Bool :=
  match table.index[key]? with
  | some id => (table, id, false)
  | none =>
    let ⟨entries, index⟩ := table
    let id := entries.size
    ({ entries := entries.push { key, state := .inProgress, requested, requestedBy }
       index := index.insert key id }, id, true)

def setState (table : QueryTable κ ρ) (id : Nat) (state : QueryState ρ) : QueryTable κ ρ :=
  let ⟨entries, index⟩ := table
  { entries := entries.modify id fun entry => { entry with state }, index }

/-- An entry that is computed again for a request other than its first: in progress, with what
asks for it now and from where. -/
def reenter (table : QueryTable κ ρ) (id : Nat) (requested : ChainFrame)
    (requestedBy : Option QueryRef) : QueryTable κ ρ :=
  let ⟨entries, index⟩ := table
  { entries := entries.modify id fun entry =>
      { entry with state := .inProgress, requested, requestedBy }
    index }

/-- The entry of a key in a state. -/
def setStateOf (table : QueryTable κ ρ) (key : κ) (state : QueryState ρ) : QueryTable κ ρ :=
  match table.index[key]? with
  | some id => table.setState id state
  | none => table

/-- One more request made by the computation of an entry. -/
def addRequest (table : QueryTable κ ρ) (key : κ) (request : QueryRef) : QueryTable κ ρ :=
  match table.index[key]? with
  | some id =>
    let ⟨entries, index⟩ := table
    { entries := entries.modify id fun entry =>
        if entry.requests.contains request then entry
        else { entry with requests := entry.requests.push request }
      index }
  | none => table

/-- An entry with its result replaced: for a result that a later pass refines. -/
def setResult (table : QueryTable κ ρ) (key : κ) (result : ρ) : QueryTable κ ρ :=
  match table.index[key]? with
  | some id => table.setState id (.done result)
  | none => table

end QueryTable

end Zkc.Frontend
