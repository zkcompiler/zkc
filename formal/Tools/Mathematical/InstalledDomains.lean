import Tools.Interactive.LogicalTypes
import Zkc.Source.Mathematical.TypeExpansion

/-! Conservative mathematical type formation using the independent installed
logical vocabulary. The package resolver supplies an explicit nominal catalog
identity for each manifest slot. This adapter supplies no operation totality,
wire semantics, cryptographic law, or legacy-program lifting theorem.
-/

set_option autoImplicit false
namespace Tools.Mathematical.InstalledDomains
open Zkc.Source.Mathematical
open Tools.Interactive

/-- Closed unary nominal value constructors reuse the old formation and
permission checker. Capability state and affine resources are excluded. -/
def nominal (identity constructor : String) : Bool :=
  match Logical.parameterKinds constructor with
  | .ok [.domain _] =>
      let spelling := constructor ++ ":" ++ identity
      let permissions := Logical.permissions spelling
      (Logical.parse spelling).isOk && permissions.copy && permissions.drop
  | _ => false

/-- Polynomial and residual indices stay in the mathematical carrier. Only
coefficient-domain registration is borrowed from the installed field catalog. -/
def check {domains : Nat} (identity : Fin domains → String) : TypeExpansion.DomainCheck domains
  | _, .nominal domain constructor arguments => arguments.isEmpty && nominal (identity domain) constructor
  | _, .polynomial domain _ _ _ | _, .residual domain _ _ => Bindings.scalarDomain (identity domain)

end Tools.Mathematical.InstalledDomains
