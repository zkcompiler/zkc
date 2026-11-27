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
key of the member in its interface. The definitions are functions of the admitted program.
Optional `lawMembers` entries bind `(slot, canonicalLawKeyBytes, defKey)` so overloaded
distribution slots such as `SuiteSlot.derive` can select distinct decoders for distinct
sampling laws that share one Core signature. -/
structure ModuleRef where
  members : List (Key × Key)
  lawMembers : List (Key × List Nat × Key) := []
deriving DecidableEq, Repr

/- Standard member slot keys for a Fiat–Shamir `Suite` module reference.
Each slot identifies a role in the `Suite` interface; overloaded slots (`encode`, `derive`) are
disambiguated by their admitted function header signatures, and `derive` may additionally be
disambiguated per sampling law via `ModuleRef.lawMembers`. -/
namespace SuiteSlot
  /-- `[.seq (.fin 256) none] → [stateTy]` -/
  def start : Key := ⟨0⟩
  /-- `[stateTy, .seq (.fin 256) none, .seq unitTy none] → [stateTy]` -/
  def absorb : Key := ⟨1⟩
  /-- `[τ] → [.seq unitTy none]` (one per absorbed statement or message type `τ`) -/
  def encode : Key := ⟨2⟩
  /-- `[stateTy, .seq (.fin 256) none] ++ drawIns → [τ, stateTy]` (one per drawn type `τ`) -/
  def derive : Key := ⟨3⟩
end SuiteSlot

/- Standard member slot keys for a proof `Layout` module reference.
Overloaded slots (`write`, `read`, `equal`) are disambiguated by their admitted header types. -/
namespace LayoutSlot
  /-- `[τ] → [.seq unitTy none]` (one per serialized type `τ`) -/
  def write : Key := ⟨0⟩
  /-- `[.seq unitTy none, .nat] → [τ, .nat]` (one per deserialized type `τ`; may reject) -/
  def read : Key := ⟨1⟩
  /-- `[τ, τ] → [.bool]` (equality predicate for carried draw comparison) -/
  def equal : Key := ⟨2⟩
end LayoutSlot

/-- How a scheme is made from its protocol: run as it is between online roles, derived
with a Fiat–Shamir suite module (and an optional published session tag), or authored in source. -/
inductive Construction where
  | interactive
  | derived (suite : ModuleRef) (sessionTag : Option (List Nat) := none)
  | authored
deriving DecidableEq, Repr

/-- The layout of a proof: its module, the sites whose values the proof carries, and the
sites whose values are recovered, each by a member of the module. -/
structure Layout where
  module : ModuleRef
  carry : List Site
  recover : List (Site × Key)
deriving DecidableEq, Repr

/-- A grind: the number of bits, at the sites that it guards. -/
structure Grind where
  bits : Nat
  sites : List Site
deriving DecidableEq, Repr

/-- A commitment: its kind, its scheme, and the sites of the keys of the prover and of the
verifier when they are values of the run. -/
structure Commitment where
  kind : Key
  scheme : ModuleRef
  proverKey : Option Site
  verifierKey : Option Site
deriving DecidableEq, Repr

/-- A value pinned at a site: the hash and its digest. -/
structure Pin where
  site : Site
  hash : Key
  digest : List Nat
deriving DecidableEq, Repr

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
  /-- Optional application context bytes bound into the deployment identity. -/
  application : List Nat := []
deriving DecidableEq, Repr

end Zkc.Core
