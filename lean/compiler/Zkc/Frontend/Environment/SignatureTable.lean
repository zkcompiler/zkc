module

public import Zkc.Frontend.Environment.Intern
public import Zkc.Frontend.Environment.Query

public section

set_option autoImplicit false

namespace Zkc.Frontend

/-- Signature numbers include keys allocated by isolated checks. Request history includes only
actual requests in this state, in the order in which they were first made. Lookups use hash
tables or array indexing, and visiting the order takes time proportional to the requests. -/
structure SignatureTable (κ ρ : Type) [BEq κ] [Hashable κ] where
  private keys : Interner κ
  private requests : Std.HashMap Nat (QueryEntry κ ρ)
  private order : Array Nat

namespace SignatureTable

variable {κ ρ : Type} [BEq κ] [Hashable κ]

@[no_expose] instance : Inhabited (SignatureTable κ ρ) := ⟨⟨{}, {}, #[]⟩⟩

/-- The number of allocated keys, including those kept from discarded trials. -/
def allocatedCount (table : SignatureTable κ ρ) : Nat := table.keys.size

/-- The key for an allocated number, even before its first request. -/
def allocatedKey? (table : SignatureTable κ ρ) (id : Nat) : Option κ := table.keys.get? id

def requestedIds (table : SignatureTable κ ρ) : Array Nat := table.order

def entryAt? (table : SignatureTable κ ρ) (id : Nat) : Option (QueryEntry κ ρ) :=
  table.requests[id]?

def allocatedKey! [Inhabited κ] (table : SignatureTable κ ρ) (id : Nat) : κ :=
  (table.allocatedKey? id).get!

def entryAt! [Inhabited κ] (table : SignatureTable κ ρ) (id : Nat) : QueryEntry κ ρ :=
  (table.entryAt? id).get!

def find? (table : SignatureTable κ ρ) (key : κ) : Option Nat := do
  let id ← table.keys.find? key
  guard (table.requests.contains id)
  return id

def entry? (table : SignatureTable κ ρ) (key : κ) : Option (QueryEntry κ ρ) :=
  (table.keys.find? key).bind table.entryAt?

def result? (table : SignatureTable κ ρ) (key : κ) : Option ρ :=
  match table.entry? key with
  | some { state := .done result, .. } => some result
  | _ => none

/-- Enter the first request for a key, reusing its number if already allocated. -/
def intern (table : SignatureTable κ ρ) (key : κ) (requested : ChainFrame)
    (requestedBy : Option QueryRef) : SignatureTable κ ρ × Nat × Bool :=
  let ⟨keys, requests, order⟩ := table
  let (keys, id, _) := keys.intern key
  if requests.contains id then (⟨keys, requests, order⟩, id, false)
  else
    (⟨keys, requests.insert id { key, state := .inProgress, requested, requestedBy },
      order.push id⟩, id, true)

/-- Adopt the key allocation of a trial descended from this table. Both parts of the interner
are shared with the trial, so adopting them takes constant time. Request entries and their
order stay in the original state. -/
def reserveNewKeys (table trial : SignatureTable κ ρ) : SignatureTable κ ρ :=
  if table.allocatedCount < trial.allocatedCount then { table with keys := trial.keys }
  else table

def setState (table : SignatureTable κ ρ) (id : Nat) (state : QueryState ρ) : SignatureTable κ ρ :=
  let ⟨keys, requests, order⟩ := table
  ⟨keys, requests.modify id fun entry => { entry with state }, order⟩

/-- Resume computation with the frame of the current request, keeping its place in request order. -/
def reenter (table : SignatureTable κ ρ) (id : Nat) (requested : ChainFrame)
    (requestedBy : Option QueryRef) : SignatureTable κ ρ :=
  let ⟨keys, requests, order⟩ := table
  ⟨keys, requests.modify id fun entry => { entry with state := .inProgress, requested, requestedBy },
    order⟩

def addRequest (table : SignatureTable κ ρ) (id : Nat) (request : QueryRef) : SignatureTable κ ρ :=
  let ⟨keys, requests, order⟩ := table
  ⟨keys, requests.modify id fun entry =>
    if entry.requests.contains request then entry
    else { entry with requests := entry.requests.push request }, order⟩

end SignatureTable

end Zkc.Frontend
