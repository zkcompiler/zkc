module

public import Zkc.Core.Program.Identity

@[expose] public section

/-!
The declaration of a scheme, as a record.
-/

namespace Zkc.Core

/-! ## Schemes -/

inductive RoleKind where
  /-- A role that runs when a proof is made or checked. Which online role proves and which
  verifies is computed from the shape. -/
  | online
  /-- A role whose messages were published before. -/
  | offline
  /-- A role that an ideal service plays. -/
  | service
deriving DecidableEq, Repr

/-- A module of the source at its static arguments, as a scheme names one (a suite, a
layout, a commitment scheme): the definition of each member that a handler applies, by the
key of the member in its interface. The definitions are functions of the admitted program. -/
structure ModuleRef where
  members : List (Key × Key)

/-- How a scheme is made from its protocol: run as it is, between online roles, or derived
with a suite. -/
inductive Construction where
  | interactive
  | derived (suite : ModuleRef)
  /-- A primitive suite selected by its catalogue identity. Its members have no source bodies. -/
  | catalogue (suite : String)

/-- The layout of a proof: its module, the sites whose values the proof carries, and the
sites whose values are recovered, each by a member of the module. -/
structure Layout where
  module : ModuleRef
  carry : List Site
  recover : List (Site × Key)

/-- A grind: the number of bits, at the sites that it guards. -/
structure Grind where
  bits : Nat
  sites : List Site

/-- A commitment: its kind, its scheme, and the sites of the keys of the prover and of the
verifier when they are values of the run. -/
structure Commitment where
  kind : Key
  scheme : ModuleRef
  proverKey : Option Site
  verifierKey : Option Site

/-- A value pinned at a site: the hash and its digest. -/
structure Pin where
  site : Site
  hash : Key
  digest : List Nat

/-- The declaration of a scheme: the entry, the kind of each role, the construction (one), the
prover when it is written, the layout, the retry (its bound and the site of its attempt), the
definition that derives the samples, the parts of the context, and the grinds, commitments and
pins. A role that an ideal service plays is a role of that kind. -/
structure Declaration where
  key : Key
  entry : Key
  kinds : List RoleKind
  construction : Construction
  prover : Option Role
  layout : Option Layout
  retry : Option (Nat × Site)
  samples : Option Key
  context : List Key
  grinds : List Grind
  commits : List Commitment
  pins : List Pin

end Zkc.Core
