module

public import Zkc.Core.Json

@[expose] public section

/-! Receipts: what a theorem about a subject states, as data.

A receipt is read from the theorem, not written beside it:

- **what was proved**: the theorem by its name, its conclusion, the values it ranges over and
  the conditions it puts on them;
- **what is left open**: the hypotheses it takes, each a closed proposition with a name, and
  the axioms of Lean that its proof uses;
- **what was decided by evaluation**: the executable checks of the hypotheses, each with what
  was evaluated and whether it held. A check is an observation at the points it names, and
  never a proof of the hypothesis.

A receipt also names its subject and the texts the subject was read from, so that a reader can
identify them by their digests. `Zkc.Tools.Formal.Receipt` reads the statement of a theorem;
a tool prints receipts as JSON.
-/

set_option autoImplicit false

namespace Zkc.Formal

/-- What a theorem states, read from the theorem. -/
structure Statement where
  /-- The name of the theorem. -/
  name : String
  /-- What it concludes. -/
  conclusion : String
  /-- The values it ranges over, each with its type. -/
  ranges : List String
  /-- The conditions it puts on those values. -/
  conditions : List String
  /-- The hypotheses it takes: closed propositions, which it does not prove. -/
  hypotheses : List String
  /-- The axioms of Lean that its proof uses. -/
  axioms : List String
  deriving Repr, Inhabited

/-- An executable check of a hypothesis. -/
structure Check where
  /-- The hypothesis that it checks. -/
  hypothesis : String
  /-- What is evaluated. -/
  evaluated : String
  /-- Whether it holds, when evaluated. -/
  holds : Unit → Bool

/-- A receipt of a theorem about a subject. -/
structure Receipt where
  /-- What the theorem is about. -/
  subject : String
  /-- The texts that the subject was read from, each by a name. -/
  texts : List String
  proved : Statement
  checks : List Check

namespace Receipt

def text (value : String) : String := (Json.str value).render

def list (items : List String) : String := "[" ++ ", ".intercalate items ++ "]"

def object (fields : List (String × String)) : String :=
  "{" ++ ", ".intercalate (fields.map fun (name, value) => text name ++ ": " ++ value) ++ "}"

/-- A receipt as JSON, with the digest of each text and the result of each check. -/
def render (receipt : Receipt) (digests : List String) : String :=
  object [
    ("subject", text receipt.subject),
    ("texts", list ((receipt.texts.zip digests).map fun (file, digest) =>
      object [("text", text file), ("sha256", text digest)])),
    ("proved", object [
      ("theorem", text receipt.proved.name),
      ("conclusion", text receipt.proved.conclusion),
      ("ranges over", list (receipt.proved.ranges.map text)),
      ("conditions", list (receipt.proved.conditions.map text))]),
    ("left open", object [
      ("hypotheses", list (receipt.proved.hypotheses.map text)),
      ("axioms", list (receipt.proved.axioms.map text))]),
    ("evaluated", list (receipt.checks.map fun check =>
      object [("hypothesis", text check.hypothesis), ("evaluated", text check.evaluated),
        ("holds", if check.holds () then "true" else "false")]))]

/-- Every check of the receipt holds. -/
def checked (receipt : Receipt) : Bool := receipt.checks.all fun check => check.holds ()

end Receipt

end Zkc.Formal
