module

public import Zkc.Core.Declaration
public import Zkc.Core.Concrete
public import Zkc.Core.Closure

public section

/-! The proof identity of a package (`docs/spec/core/package.md`, *Identities*): the SHA-256
of the canonical encoding of `["zkc.core.proof/0", original, proof, parameters]`.

- `original` is the original program as the package prints it,
  `["original", types, records, variants, oracles, operations, definitions]`, with the rows of
  the suite and of the layout that the declaration names.
- `proof` is the declaration in its JSON form (`Zkc.Core.Declaration`), always with its list of
  online roles. The catalogue suite of a declaration carries the proof identity itself, so the
  identity is computed over the declaration whose suite carries none (`[]`), and then written
  into it.
- `parameters` are the stage parameters that the declaration does not hold: the commitment
  scheme of each oracle row. A package with no oracle row has none, `[]`; the suite and the
  layout are in the declaration.

The canonical encoding is the JSON printer's (`Json.render`): no whitespace, integers in
decimal.

`proofIdentity` is the identity of a package and a declaration as they are given.
`schemeIdentity` is the proof identity of a scheme: `proofIdentity` over its scheme closure
(`schemeClosure`), the original program restricted to what the entry and the declaration
reach (`Zkc.Core.Closure`), with the declaration numbered over it. Definitions and rows that
neither reaches do not change it.
-/

set_option autoImplicit false

namespace Zkc.Core.Raw

open Zkc (Json)

def printSiteRow (row : SiteRow) : Json :=
  match row.roles with
  | none => .arr #[row.site, row.row]
  | some (prover, verifier) => .arr #[row.site, row.row, prover, verifier]

def printPairs (pairs : List (Nat × Nat)) : Json :=
  .arr (pairs.map fun (law, row) => Json.arr #[law, row]).toArray

def printSuite : Option Suite → Json
  | none => .null
  | some (.catalogue state label start absorbing deriving_ identity) =>
      .arr #["catalogue", printType state, label, start, nats absorbing, printPairs deriving_,
        nats identity]
  | some (.source state start absorbing deriving_ sites) =>
      .arr #["source", printType state, start, nats absorbing, printPairs deriving_,
        .arr (sites.map fun rows => Json.arr (rows.map printSiteRow).toArray).toArray]

def printLayout : Option Layout → Json
  | none => .null
  | some layout =>
      .arr #["canonical", printType layout.writer, printType layout.reader, printType layout.proof,
        layout.start, layout.close, layout.read, layout.exhausted, nats layout.putting,
        nats layout.taking]

/-- A declaration in its JSON form, with its online roles. -/
def printDeclaration (declaration : Declaration) : Json :=
  .arr #["declaration", declaration.entry, declaration.prover, declaration.verifier,
    printSuite declaration.suite, printLayout declaration.layout, nats declaration.online]

/-- The declaration with a catalogue suite that carries the given identity. -/
def Declaration.withIdentity (declaration : Declaration) (identity : List Nat) : Declaration :=
  match declaration.suite with
  | some (.catalogue state label start absorbing deriving_ _) =>
      { declaration with suite := some (.catalogue state label start absorbing deriving_ identity) }
  | _ => declaration

/-- The original program of a package as the package prints it. -/
def originalProgram (package : Package) : Json :=
  match printPackage package with
  | .arr #[_, .arr #[program], _, _, _, _] => program
  | other => other

/-- The text whose SHA-256 is the proof identity. -/
def proofIdentityText (package : Package) (declaration : Declaration) : String :=
  (Json.arr #["zkc.core.proof/0", originalProgram package,
    printDeclaration (declaration.withIdentity []), .arr #[]]).render

/-- The proof identity of a package with its declaration: 32 bytes. -/
def proofIdentity (package : Package) (declaration : Declaration) : List Nat :=
  Concrete.bytesOf (Concrete.Sha256.digest (proofIdentityText package declaration).toUTF8)

/-! ## The scheme closure

A declaration names items of the package. A catalogue suite names the nominal row of its
labels and operation rows: the start row, the absorbing rows, and per law the law's row and
the deriving row. A source suite names functions: the start function, the absorbing
functions, per law the law's operation row and the deriving function, and the function of
each site row. The site rows are listed per protocol, so only those of the protocols that
the entry reaches count, in the closure's order of protocols. A layout names operation rows.
The types of the state, the writer, the reader and the proof name what they name. No item
that a declaration names reaches a protocol: the protocols of the scheme closure are those
that the entry reaches. -/

/-- The items a suite names, in the order of its fields. `protocols` lists the protocols
whose site rows count, in their order. -/
@[expose] def Suite.references (protocols : List Nat) : Suite → List Reference
  | .catalogue state label start absorbing deriving_ _ =>
      state.references ++ (.typeRow label :: .operation start :: absorbing.map .operation ++
        deriving_.flatMap fun pair => [.operation pair.1, .operation pair.2])
  | .source state start absorbing deriving_ sites =>
      state.references ++ (.function start :: absorbing.map .function ++
        (deriving_.flatMap (fun pair => [.operation pair.1, .function pair.2]) ++
          protocols.flatMap fun protocol =>
            (sites.getD protocol []).map fun row => .function row.row))

/-- The items a layout names, in the order of its fields. -/
@[expose] def Layout.references (layout : Layout) : List Reference :=
  layout.writer.references ++ (layout.reader.references ++ (layout.proof.references ++
    ([.operation layout.start, .operation layout.close, .operation layout.read,
        .operation layout.exhausted] ++
      (layout.putting.map .operation ++ layout.taking.map .operation))))

/-- The items a declaration names besides its entry: those of its suite, then those of its
layout. `protocols` lists the protocols whose site rows count, in their order. -/
@[expose] def Declaration.references (declaration : Declaration) (protocols : List Nat) :
    List Reference :=
  (match declaration.suite with
    | some suite => suite.references protocols
    | none => []) ++
  (match declaration.layout with
    | some layout => layout.references
    | none => [])

@[expose] def SiteRow.renumber (renumbering : Renumbering) (row : SiteRow) : SiteRow :=
  ⟨row.site, positionIn renumbering.functions row.row, row.roles⟩

/-- A suite with its rows, functions and types renumbered. The site rows of a source suite
are those of the renumbered protocols, in their new order. -/
@[expose] def Suite.renumber (renumbering : Renumbering) : Suite → Suite
  | .catalogue state label start absorbing deriving_ identity =>
      .catalogue (state.renumber renumbering) (positionIn renumbering.typeRows label)
        (positionIn renumbering.operations start)
        (absorbing.map (positionIn renumbering.operations))
        (deriving_.map fun pair =>
          (positionIn renumbering.operations pair.1, positionIn renumbering.operations pair.2))
        identity
  | .source state start absorbing deriving_ sites =>
      .source (state.renumber renumbering) (positionIn renumbering.functions start)
        (absorbing.map (positionIn renumbering.functions))
        (deriving_.map fun pair =>
          (positionIn renumbering.operations pair.1, positionIn renumbering.functions pair.2))
        (renumbering.protocols.map fun protocol =>
          (sites.getD protocol []).map (SiteRow.renumber renumbering))

@[expose] def Layout.renumber (renumbering : Renumbering) (layout : Layout) : Layout :=
  ⟨layout.writer.renumber renumbering, layout.reader.renumber renumbering,
    layout.proof.renumber renumbering, positionIn renumbering.operations layout.start,
    positionIn renumbering.operations layout.close, positionIn renumbering.operations layout.read,
    positionIn renumbering.operations layout.exhausted,
    layout.putting.map (positionIn renumbering.operations),
    layout.taking.map (positionIn renumbering.operations)⟩

/-- A declaration over a renumbered package: its entry, suite and layout renumbered; the
roles are those of the entry and keep their numbers. -/
@[expose] def Declaration.renumber (renumbering : Renumbering) (declaration : Declaration) :
    Declaration :=
  ⟨positionIn renumbering.protocols declaration.entry, declaration.prover, declaration.verifier,
    declaration.online, declaration.suite.map (Suite.renumber renumbering),
    declaration.layout.map (Layout.renumber renumbering)⟩

/-- The scheme closure of a package and its declaration: the closure of the roots that are
the entry followed by what the declaration names (`Package.closureOfRoots`), with the
declaration renumbered over it. The site rows that count are those of the protocols that
the entry reaches; the entry is the last protocol. -/
@[expose] def Package.schemeClosure (package : Package) (declaration : Declaration) :
    Package × Declaration :=
  let protocols := (package.renumberingOf [.protocol declaration.entry]).protocols
  let renumbering := package.renumberingOf
    (.protocol declaration.entry :: declaration.references protocols)
  (package.renumber renumbering, declaration.renumber renumbering)

/-- The proof identity of a scheme: the proof identity of its scheme closure. -/
@[expose] def schemeIdentity (package : Package) (declaration : Declaration) : List Nat :=
  proofIdentity (package.schemeClosure declaration).1 (package.schemeClosure declaration).2

/-- Two packages with their declarations that have one scheme closure have one scheme
identity. -/
theorem schemeIdentity_eq_of_schemeClosure_eq {package other : Package}
    {declaration otherDeclaration : Declaration}
    (same : package.schemeClosure declaration = other.schemeClosure otherDeclaration) :
    schemeIdentity package declaration = schemeIdentity other otherDeclaration :=
  congrArg (fun (scheme : Package × Declaration) => proofIdentity scheme.1 scheme.2) same

end Zkc.Core.Raw
