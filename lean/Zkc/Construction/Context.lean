module

public import Zkc.Construction.Participant

@[expose] public section

/-! Common source identity and the explicit plain or single-service profile.
Plain contexts contain no replacement service and no transcript configuration.
Private capability ports are independently owned by the actual source ABI. -/
set_option autoImplicit false
namespace Zkc.Construction
open Zkc.Source

/-- Source and application identity shared by both construction profiles. -/
structure ContextIdentity where
  entry : String
  roles : List String
  producer : Nat
  validator : Nat
  deriving DecidableEq, Repr

/-- The one selected public challenge service. Private services are owned by
separate ports and are never represented by this record. -/
structure Replacement where
  service : Nat
  contract : String
  request : Option Request
  suite : String
  draws : List (String × String)
  deriving DecidableEq, Repr

/-- A plain participant has no replacement service or transcript capability. -/
inductive Profile where
  | plain
  | fiatShamir (replacement : Replacement)
  deriving DecidableEq, Repr

structure Context extends ContextIdentity where
  profile : Profile
  deriving DecidableEq, Repr

namespace Context

/-- Constructor for the existing single-service profile. -/
def fiatShamir (entry : String) (roles : List String) (producer validator service : Nat)
    (contract : String) (request : Option Request) (suite : String)
    (draws : List (String × String)) : Context :=
  ⟨⟨entry, roles, producer, validator⟩, .fiatShamir ⟨service, contract, request, suite, draws⟩⟩

-- Realize this shared constructor equation at its definition. Otherwise a
-- client using simp can become its apparent owner in a merged audit.
section
attribute [local simp] fiatShamir
end

def plain (entry : String) (roles : List String) (producer validator : Nat) : Context :=
  ⟨⟨entry, roles, producer, validator⟩, .plain⟩

def replacement? (context : Context) : Option Replacement :=
  match context.profile with | .plain => none | .fiatShamir replacement => some replacement

def service (context : Context) : Option Nat := context.replacement?.map (·.service)
def request (context : Context) : Option Request := context.replacement? >>= (·.request)
def suite (context : Context) : String := (context.replacement?.map (·.suite)).getD ""
def contract (context : Context) : String := (context.replacement?.map (·.contract)).getD ""
def draws (context : Context) : List (String × String) :=
  (context.replacement?.map (·.draws)).getD []

def mapReplacement (context : Context) (change : Replacement → Replacement) : Context :=
  { context with profile := match context.profile with
    | .plain => .plain | .fiatShamir replacement => .fiatShamir (change replacement) }

/-- Data ports are the entire plain ABI; only Fiat–Shamir appends a capability. -/
def dataPorts {α : Type} (context : Context) (ports : List α) : List α :=
  match context.profile with | .plain => ports | .fiatShamir _ => ports.dropLast

end Context

/-- One decimal digit; larger arguments spell `9`. -/
def decimalDigit : Nat → String
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"

-- Materialize shared equation proofs at the definition's owner. Otherwise
-- independent clients can realize different private matcher proofs under the
-- same public equation name. The scoped attribute exports no global simp rule.
section
attribute [local simp] decimalDigit
end

/-- The canonical decimal spelling of an index below `10000`, as used in native
service port names. It is built from literals so that kernel evaluation reduces
it. -/
def decimal (index : Nat) : String :=
  if index < 10 then decimalDigit index
  else if index < 100 then decimalDigit (index / 10) ++ decimalDigit (index % 10)
  else if index < 1000 then
    decimalDigit (index / 100) ++ decimalDigit (index / 10 % 10) ++ decimalDigit (index % 10)
  else
    decimalDigit (index / 1000 % 10) ++ decimalDigit (index / 100 % 10) ++
      decimalDigit (index / 10 % 10) ++ decimalDigit (index % 10)

namespace Context

def role (context : Context) (index : Nat) : String := context.roles.getD index ""

def message (context : Context) (site : String) (sender receiver : Nat) : Origin :=
  .message context.entry site (context.role sender) (context.role receiver)

/-- The selected query's occurrence names the replaced service's original port
and contract, which the original export fixes, and carries the query's typed
request. -/
def query? (context : Context) (site : String) (request : Request) : Option Origin :=
  context.replacement?.map fun replacement =>
    .query context.entry site ("input_" ++ decimal replacement.service) replacement.contract
      (context.role context.validator) request

/-- A candidate query identity, used by legacy uniform proofs. Without a
replacement the port is absent (the empty spelling), so it cannot be an admitted
source occurrence. Nominal execution additionally checks `replacement?` and the
request before issuing any challenge. -/
def query (context : Context) (site : String) (request : Request) : Origin :=
  .query context.entry site ((context.service.map (fun service => "input_" ++ decimal service)).getD "")
    context.contract (context.role context.validator) request

/-- The old single-service occurrence construction is preserved exactly by its
canonical inclusion into the explicit profile. This is an identity law, not a
probabilistic game or native realization theorem. -/
theorem fiatShamir_query (entry : String) (roles : List String)
    (producer validator service : Nat) (contract : String) (request : Option Request)
    (suite : String) (draws : List (String × String)) (site : String) (asked : Request) :
    (fiatShamir entry roles producer validator service contract request suite draws).query site asked =
      Origin.query entry site ("input_" ++ decimal service) contract (roles.getD validator "") asked := rfl

theorem plain_no_query (entry : String) (roles : List String) (producer validator : Nat)
    (site : String) (request : Request) :
    (plain entry roles producer validator).query? site request = none := rfl

end Context


namespace Template

/-- The model occurrence of a template, as `transform` names it: a message by
its qualified site and its roles; a selected draw challenge by its qualified
query site under the context's replaced service, with that service's typed
request. -/
def origin (context : Context) (template : Template) : Option Origin :=
  match template.event with
  | ["message", _, site, schema, sender, receiver] =>
      if schema = site then some (Origin.message context.entry (template.qualify site) sender receiver)
      else none
  | ["query", _, site, _, _, "draw", _] => context.request.map (context.query (template.qualify site))
  | _ => none

end Template

end Zkc.Construction
