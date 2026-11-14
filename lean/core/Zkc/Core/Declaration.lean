module

public import Zkc.Core.Package

public section

/-! The part of a declaration that the construction steps read, as plain data.

A declaration names the entry among the protocols, its prover and verifier, the suite
and the wire layout. A suite and a layout are rows of the package: every reference here
is the number of a row of the operation table or of a function. The steps resolve a
number to a typed reference when they use it, so a number that names a row of another
signature is a refusal of the step.

A catalogue suite gives the nominal type of labels, a start row that takes the proof
identity, the rows that absorb (one per message type) and the rows that derive (one per
law). Labels and the proof identity are literals that the step writes; no row names a
label. A source suite gives a start
function and one handler per rewritten site; for a site without a handler of its own it
gives functions that absorb, chosen by the message type, and functions that derive,
chosen by the law.

JSON form, positional:

    ["declaration", entry, prover, verifier, suite, layout]
    ["declaration", entry, prover, verifier, suite, layout, [online role…]]
    suite  = null
           | ["catalogue", state type, label type row, start row, [absorbing row…],
              [[law row, deriving row]…], [proof identity number…]]
           | ["source", state type, start function, [absorbing function…],
              [[law row, deriving function]…], [[site row…]…]]
    site row = [site, row] | [site, row, prover, verifier]
    layout = null
           | ["canonical", writer type, reader type, proof type, open row, close row,
              read row, exhausted row, [putting row…], [taking row…]]

The site rows are listed per protocol, in program order. A site row with roles is the
one of the image of the definition for those transcript roles. Without a list of online
roles, the online roles of the entry are its prover and its verifier.
-/

set_option autoImplicit false

namespace Zkc.Core.Raw

open Zkc (Json)

/-- The row or function of one site of a definition: for every image of the
definition, or for the image with the given transcript roles. -/
structure SiteRow where
  site : Nat
  row : Nat
  roles : Option (Nat × Nat)
  deriving Repr, DecidableEq

inductive Suite where
  | catalogue (state : Ty) (label : Nat) (start : Nat) (absorbing : List Nat)
      (deriving_ : List (Nat × Nat)) (identity : List Nat)
  | source (state : Ty) (start : Nat) (absorbing : List Nat) (deriving_ : List (Nat × Nat))
      (sites : List (List SiteRow))
  deriving Repr

structure Layout where
  writer : Ty
  reader : Ty
  proof : Ty
  start : Nat
  close : Nat
  read : Nat
  exhausted : Nat
  putting : List Nat
  taking : List Nat
  deriving Repr

structure Declaration where
  entry : Nat
  prover : Nat
  verifier : Nat
  /-- The roles of the entry that are online. -/
  online : List Nat
  suite : Option Suite
  layout : Option Layout
  deriving Repr

def readSiteRow : Json → Read SiteRow
  | .arr #[site, row] => return ⟨← readNat "site" site, ← readNat "row" row, none⟩
  | .arr #[site, row, prover, verifier] =>
      return ⟨← readNat "site" site, ← readNat "row" row,
        some (← readNat "prover" prover, ← readNat "verifier" verifier)⟩
  | other => throw s!"malformed site row {other.render}"

def readSites (json : Json) : Read (List (List SiteRow)) := do
  (← readArray "sites" json).toList.mapM fun definition => do
    (← readArray "site rows" definition).toList.mapM readSiteRow

def readPairs (json : Json) : Read (List (Nat × Nat)) := do
  (← readArray "deriving rows" json).toList.mapM fun
    | .arr #[law, row] => return (← readNat "law" law, ← readNat "row" row)
    | other => throw s!"malformed deriving row {other.render}"

def readSuite : Json → Read (Option Suite)
  | .null => pure none
  | .arr #[.str "catalogue", state, label, start, absorbing, deriving_, identity] =>
      return some (.catalogue (← readType state) (← readNat "label type" label)
        (← readNat "start" start) (← readNats "absorbing rows" absorbing) (← readPairs deriving_)
        (← readNats "proof identity" identity))
  | .arr #[.str "source", state, start, absorbing, deriving_, sites] =>
      return some (.source (← readType state) (← readNat "start" start)
        (← readNats "absorbing functions" absorbing) (← readPairs deriving_) (← readSites sites))
  | other => throw s!"malformed suite {(other.render.take 80).toString}"

def readLayout : Json → Read (Option Layout)
  | .null => pure none
  | .arr #[.str "canonical", writer, reader, proof, start, close, read, exhausted, putting,
      taking] =>
      return some ⟨← readType writer, ← readType reader, ← readType proof,
        ← readNat "open" start, ← readNat "close" close, ← readNat "read" read,
        ← readNat "exhausted" exhausted, ← readNats "putting rows" putting,
        ← readNats "taking rows" taking⟩
  | other => throw s!"malformed layout {(other.render.take 80).toString}"

def readDeclaration : Json → Read Declaration
  | .arr #[.str "declaration", entry, prover, verifier, suite, layout] => do
      let prover ← readNat "prover" prover
      let verifier ← readNat "verifier" verifier
      return ⟨← readNat "entry" entry, prover, verifier, [prover, verifier],
        ← readSuite suite, ← readLayout layout⟩
  | .arr #[.str "declaration", entry, prover, verifier, suite, layout, online] =>
      return ⟨← readNat "entry" entry, ← readNat "prover" prover, ← readNat "verifier" verifier,
        ← readNats "online roles" online, ← readSuite suite, ← readLayout layout⟩
  | _ => throw "malformed declaration"

def parseDeclaration (source : String) : Read Declaration := do
  readDeclaration (← Json.parse source)

end Zkc.Core.Raw
