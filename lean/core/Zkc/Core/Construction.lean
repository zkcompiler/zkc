module

public import Zkc.Core.Admission
public import Zkc.Core.Serialize
public import Zkc.Core.Pipeline

public section

/-! Construction on an admitted package, admitted at each step.

`constructAdmitted` is the one way from an admitted package and a declaration to a constructed
scheme: the Fiat–Shamir step, then the serialize step, with admission run on the package of
what each returns. A consumer takes the `Construction` and assembles nothing. `compile` is the
one way from a raw package to role programs: admission as written, the construction when a
scheme is declared, and projection. A tool calls it and assembles nothing either.

A construction starts from a package admitted as written, and says so: the theorems about a
program as written hold of its source. What was stated beside the source, other than the keys
of its sites, is stated of what each step returns, and the construction records that too, so a
consumer reads the vocabulary of the rows of a constructed package from the construction.

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
  /-- The package was not admitted as a program as written: it is what a step returned. -/
  | stepped
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

/-- A construction on a package admitted as written: what each of the two steps returns, with
the admission of its package under what was stated beside the source. -/
structure Construction (source : Admitted) (declaration : Raw.Declaration) where
  written : source.claims.written = true
  derived : Stepped source.typed.typeTable (source.typed.table.map (·.signature))
    source.typed.functions
  derives : fiatShamir source.typed declaration = .ok derived
  derivedAdmitted : Admitted
  derivedPackage : derivedAdmitted.package = derived.package source.typed
  derivedClaims : derivedAdmitted.claims = source.claims.afterStep
  serialized : Stepped source.typed.typeTable (source.typed.table.map (·.signature))
    source.typed.functions
  serializes : serializeProtocols declaration derived.identities derived.protocols =
    .ok serialized
  admitted : Admitted
  package : admitted.package = serialized.package source.typed
  claims : admitted.claims = source.claims.afterStep

/-- The construction of a declaration on a package admitted as written: the Fiat–Shamir step,
then the serialize step, with what each returns admitted; or the first refusal. A package that
was admitted as what a step returned is refused: a construction is not applied twice. -/
def constructAdmitted (source : Admitted) (declaration : Raw.Declaration) :
    Except ConstructionRefusal (Construction source declaration) :=
  if written : source.claims.written = true then
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
                    .ok ⟨written, derived, derives, derivedAdmitted, admit_package derivedAdmits,
                      admit_claims derivedAdmits, serialized, serializes, admitted,
                      admit_package admits, admit_claims admits⟩
  else .error .stepped

namespace Construction

variable {source : Admitted} {declaration : Raw.Declaration}

/-- A construction is the pipeline of its declaration: `construct` returns what its serialize
step returned. -/
theorem constructs (construction : Construction source declaration) :
    construct source.typed declaration = .ok construction.serialized := by
  unfold construct
  rw [construction.derives]
  exact construction.serializes

/-- The vocabulary that was stated of the rows of the source is stated of the rows of the
constructed package. -/
theorem claims_rows (construction : Construction source declaration) :
    construction.admitted.claims.rows = source.claims.rows := by
  rw [construction.claims]
  rfl

/-- The vocabulary that was stated of the literal data of the source is stated of the
constructed package. -/
theorem claims_literals (construction : Construction source declaration) :
    construction.admitted.claims.literals = source.claims.literals := by
  rw [construction.claims]
  rfl

/-- Which functions can stop, as stated beside the source, is stated of the constructed
package. -/
theorem claims_stops (construction : Construction source declaration) :
    construction.admitted.claims.stops = source.claims.stops := by
  rw [construction.claims]
  rfl

/-- When the rows of the source were checked against a vocabulary, the rows of the constructed
package under the names of that vocabulary are its rows: the steps add the rows of a suite and
of a layout, and admission after the step checked them. -/
theorem rows_stated (construction : Construction source declaration) {table : Vocabulary.Table}
    (claimed : source.claims.rows = some table) :
    Vocabulary.misstated table construction.admitted.package = [] :=
  construction.admitted.rows_stated (construction.claims_rows.trans claimed)

end Construction

/-! ## From a raw package to role programs -/

/-- Why a raw package has no role programs. -/
inductive CompileRefusal where
  /-- The package is not admitted as a program as written. -/
  | admission (refusals : List Admission.Refusal)
  /-- The scheme of the declaration is not constructed on the admitted package. -/
  | construction (refusal : ConstructionRefusal)
  /-- A protocol has no program for one of its roles. -/
  | projection (refusal : ProjectionRefusal)
  deriving Repr

/-- The role programs of the protocols of a typed package after a step, with applications
kept as calls. -/
def Stepped.roles (typed : Typed)
    (stepped : Stepped typed.typeTable (typed.table.map (·.signature)) typed.functions) :
    Except CompileRefusal (List Raw.RoleProgram) :=
  match projectProtocols stepped.protocols with
  | .error refusal => .error (.projection refusal)
  | .ok projected =>
      .ok (unelaborateRolePrograms typed.functions.length projected.headers.length
        projected.programs [])

/-- The role programs of every protocol of an admitted package, with applications kept as
calls. -/
def Admitted.roles (source : Admitted) : Except CompileRefusal (List Raw.RoleProgram) :=
  match projectProtocols source.typed.program.protocols with
  | .error refusal => .error (.projection refusal)
  | .ok projected =>
      .ok (unelaborateRolePrograms source.typed.functions.length projected.headers.length
        projected.programs [])

/-- The role programs of a constructed scheme: those of what its serialize step returned. -/
def Construction.roles {source : Admitted} {declaration : Raw.Declaration}
    (construction : Construction source declaration) :
    Except CompileRefusal (List Raw.RoleProgram) :=
  construction.serialized.roles source.typed

/-- What is stated beside a package that is compiled: what the producer states, of a program
as written. Whether a package is a program as written is not the producer's to state here. -/
def Admission.Claims.asWritten (claims : Admission.Claims) : Admission.Claims :=
  { claims with written := true }

/-- The compilation of a raw package to role programs: the package is admitted as a program as
written, with what the producer states beside it; when a scheme is declared it is constructed
on the admitted package, admitted after each step; and the protocols of the result are
projected. Without a declaration the role programs are those of the written protocols. -/
def compile (package : Raw.Package) (claims : Admission.Claims := {})
    (declaration : Option Raw.Declaration := none) :
    Except CompileRefusal (List Raw.RoleProgram) :=
  match admit package claims.asWritten with
  | .error refusals => .error (.admission refusals)
  | .ok source =>
      match declaration with
      | none => source.roles
      | some declaration =>
          match constructAdmitted source declaration with
          | .error refusal => .error (.construction refusal)
          | .ok construction => construction.roles

/-- A package that compiles was admitted as a program as written, and its role programs are
those of the admitted package, or of a construction of the declared scheme on it. No role
program comes from a package that admission refuses. -/
theorem compile_checked {package : Raw.Package} {claims : Admission.Claims}
    {declaration : Option Raw.Declaration} {roles : List Raw.RoleProgram}
    (compiles : compile package claims declaration = .ok roles) :
    ∃ source : Admitted, admit package claims.asWritten = .ok source ∧
      match declaration with
      | none => source.roles = .ok roles
      | some declaration =>
          ∃ construction : Construction source declaration, construction.roles = .ok roles := by
  unfold compile at compiles
  split at compiles
  · cases compiles
  · rename_i source admits
    refine ⟨source, admits, ?_⟩
    split at compiles
    · exact compiles
    · split at compiles
      · cases compiles
      · rename_i construction _
        exact ⟨construction, compiles⟩

end Zkc.Core
