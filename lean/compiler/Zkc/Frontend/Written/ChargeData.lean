module

public import Zkc.Core.Program.Identity
public import Zkc.Core.Program.Links

@[expose] public section
namespace Zkc.Frontend.Written

/-- A normalized nonnegative source ceiling and the ordered, definition-relative locations of its draw.
The model supplies the challenge alphabet and the formal consumer checks the locations. -/
structure DrawCharge where
  owner : Core.Key
  numerator : Nat
  denominator : Nat
  draws : List (List (Core.Key × Nat) × Core.Key)
  deriving DecidableEq, Repr

/-- The cap of a charged draw of a definition: what each occurrence of the draw may be charged
at most, as a numerator over a denominator, and how often the draw can occur in one run of the
definition. -/
structure DrawCap where
  key : Core.Key
  numerator : Nat
  denominator : Nat
  count : Nat
  deriving DecidableEq, Repr

/-- A call in a definition: the key of the application, how often it can run in one run of the
definition, and the use of the callee, by its place in the table. -/
structure CallCap where
  key : Core.Key
  count : Nat
  callee : Nat
  deriving DecidableEq, Repr

/-- A use of a definition: the definition at the proof arguments of one of its uses, with the
caps of its charged draws and with its calls. Two applications that give a callee the same proof
arguments are calls of one use. -/
structure UseCaps where
  definition : Core.Key
  draws : List DrawCap
  calls : List CallCap
  deriving DecidableEq, Repr

/-- The table of caps of a root: the uses that the root reaches, each after the uses that it
calls; the root's own use is the last. The charge of an application is computed from the
callee's charges and the counts of the loops around them (SX8), so the table has one entry for a
use and not one for every way from the root to it. A draw without a cap is allowed nothing. -/
structure CapTable where
  uses : List UseCaps
  deriving DecidableEq, Repr

namespace CapTable
open Core

/-- The use at the root of a table: the last. -/
def root (table : CapTable) : Nat := table.uses.length - 1

/-- **The counts of a use are those of its definition.** In the stored program, every charged
draw of the use is a coin of the definition with the count that the kept loops around it give,
and no draw is listed twice; the calls of the use are the applications of the definition, in
their order, each with its count and with the use of the definition that it applies, which
stands earlier in the table. A coin or an application under a loop whose count is read at run
time, or in an attempt, has no count and meets no entry. -/
def countedUse {V : Vocabulary} (p : NamedProgram V) (table : CapTable) (place : Nat)
    (use : UseCaps) : Bool :=
  match p.definitions.find? (·.key == use.definition) with
  | some (.protocol _ _ _ _ body) =>
    let found := body.counted (some 1)
    let coins := found.filterMap fun (key, operation, count) =>
      match operation with
      | .event (.given (.coin _) _ _) _ => some (key, count)
      | _ => none
    let applications := found.filterMap fun (key, operation, count) =>
      match operation with
      | .apply callee _ => some (key, callee, count)
      | _ => none
    use.draws.all (fun draw => coins.contains (draw.key, some draw.count)) &&
      decide (use.draws.map (·.key)).Nodup &&
      applications == (use.calls.filterMap fun call =>
        (table.uses[call.callee]?).map fun callee => (call.key, callee.definition, some call.count)) &&
      use.calls.all (fun call => call.callee < place)
  | _ => false

/-- **The counts of a table are those of the program.** Every use has the counts of its
definition, and the last use is of the root. The caps are the source's and are not checked
here: the stored program has no charges. -/
def counted {V : Vocabulary} (table : CapTable) (p : NamedProgram V) (root : Key) : Bool :=
  (table.uses.zipIdx.all fun (use, place) => table.countedUse p place use) &&
    (table.uses.getLast?.map (·.definition)) == some root

/-- The charged draws below a use by the applications that reach them, each with its cap and
how often it can occur in one run of the use: the table as a list of sites. Two calls of one
use give its draws twice, so the list can be far longer than the table; it is the view that a
test compares with `NamedProgram.occurrences`. `depth` bounds the applications entered. -/
def sitesFrom (table : CapTable) : Nat → Nat → List Key → Nat → List (Site × Nat × Nat × Nat)
  | 0, _, _, _ => []
  | depth + 1, place, through, times =>
    match table.uses[place]? with
    | none => []
    | some use =>
      (use.draws.map fun draw => (⟨through, draw.key⟩, draw.numerator, draw.denominator, times * draw.count)) ++
        use.calls.flatMap fun call =>
          table.sitesFrom depth call.callee (through ++ [call.key]) (times * call.count)

/-- The charged draws of the root by site: the site, the numerator and the denominator of its
cap, and its count. -/
def sites (table : CapTable) : List (Site × Nat × Nat × Nat) :=
  table.sitesFrom table.uses.length table.root [] 1

end CapTable

end Zkc.Frontend.Written
