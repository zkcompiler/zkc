module

public import Zkc.Core.Admission
public import Zkc.Core.Serialize

public section

/-! Construction on an admitted package, admitted at each step.

`constructAdmitted` is the one way from an admitted package and a declaration to a constructed
scheme: the Fiat–Shamir step, then the serialize step, with admission run on the package of
what each returns. A consumer takes the `Construction` and assembles nothing.

What is checked of what a step returns: it elaborates (its residual conditions hold); the
normal form of every body passes the check of facts; its sites are in the order of its bodies;
its rows and the data of its literals are the vocabulary's, when that was stated of the
package. The steps are proved to keep the conditions of a definition; the rest is this check.

What is not checked of it is the check of copies. The Fiat–Shamir step threads two transcript
states, the prover's and the verifier's, and does not declare them copies of one value, so a
protocol that derives a coin at both roles and returns it under an agreement does not pass
(the derived Sumcheck). After serialization the prover and the verifier do not interact: the
verifier reads from a proof that is its input, and what relates its values to the prover's
is the theorem of the step, not a class of copies. A side of one role has at most one
participant of a choice or a loop, so the program of a role does not depend on the check.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- The raw package of what a step returns: the tables and the functions of the package it
was applied to, with the protocols after the step, without names. -/
def Stepped.package (typed : Typed)
    (stepped : Stepped typed.typeTable (typed.table.map (·.signature)) typed.functions) :
    Raw.Package :=
  { unelaborate typed with
    protocols := unelaborateProtocols typed.functions.length stepped.headers.length
      stepped.protocols []
    names := none }

/-- Why a construction on an admitted package has no admitted result. -/
inductive ConstructionRefusal where
  /-- A step refuses the declaration. -/
  | step (refusal : StepRefusal)
  /-- What the Fiat–Shamir step returns is not admitted. -/
  | derived (refusals : List Admission.Refusal)
  /-- What the serialize step returns is not admitted. -/
  | serialized (refusals : List Admission.Refusal)
  deriving Repr

/-- What is stated beside the package of what a step returns: that it is not a program as
written; the vocabulary of the rows and of the literal data that was stated beside the package
the step was applied to; and which functions can stop, since a step leaves the functions as
they are. The keys of the sites are those of the written program and are not stated of the
steps' events. -/
def Admission.Claims.afterStep (claims : Admission.Claims) : Admission.Claims :=
  { claims with keys := none, written := false }

/-- A construction on an admitted package: what each of the two steps returns, with the
admission of its package. -/
structure Construction (source : Admitted) (declaration : Raw.Declaration) where
  derived : Stepped source.typed.typeTable (source.typed.table.map (·.signature))
    source.typed.functions
  derives : fiatShamir source.typed declaration = .ok derived
  derivedAdmitted : Admitted
  derivedPackage : derivedAdmitted.package = derived.package source.typed
  serialized : Stepped source.typed.typeTable (source.typed.table.map (·.signature))
    source.typed.functions
  serializes : serializeProtocols declaration derived.identities derived.protocols =
    .ok serialized
  admitted : Admitted
  package : admitted.package = serialized.package source.typed

/-- The construction of a declaration on an admitted package: the Fiat–Shamir step, then the
serialize step, with what each returns admitted; or the first refusal. -/
def constructAdmitted (source : Admitted) (declaration : Raw.Declaration) :
    Except ConstructionRefusal (Construction source declaration) :=
  match derives : fiatShamir source.typed declaration with
  | .error refusal => .error (.step refusal)
  | .ok derived =>
      match derivedAdmits : admit (derived.package source.typed) source.claims.afterStep with
      | .error refusals => .error (.derived refusals)
      | .ok derivedAdmitted =>
          match serializes : serializeProtocols declaration derived.identities
              derived.protocols with
          | .error refusal => .error (.step refusal)
          | .ok serialized =>
              match admits : admit (serialized.package source.typed)
                  source.claims.afterStep with
              | .error refusals => .error (.serialized refusals)
              | .ok admitted =>
                  .ok ⟨derived, derives, derivedAdmitted, admit_package derivedAdmits, serialized,
                    serializes, admitted, admit_package admits⟩

/-- A construction is the pipeline of its declaration: `construct` returns what its serialize
step returned. -/
theorem Construction.constructs {source : Admitted} {declaration : Raw.Declaration}
    (construction : Construction source declaration) :
    construct source.typed declaration = .ok construction.serialized := by
  unfold construct
  rw [construction.derives]
  exact construction.serializes

end Zkc.Core
