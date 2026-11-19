module

public import Zkc.Frontend.Typed.Checked
public import Zkc.Frontend.Static.Basic

@[expose] public section

set_option autoImplicit false

/-!
# The events of a protocol body

The occurrences of the events of a typed body (EV3): one per event statement of the tree, with
the number of the event in the text and the iteration of each loop in sequence around it. An
event of an arm that a static condition does not take has its number and no occurrence at the
instance.

The names of the sites are a matter of the text of the declaration, the same at every instance:
each explicit `#[site(n)]` provides its stable name, a single binder supplies the default, and
two events of one definition may not share a name.
-/

namespace Zkc.Frontend.Passes

open Typed

namespace Events

mutual
  /-- The occurrences of the events of statements, in the order of the tree, under the
  iterations of the loops in sequence around them. -/
  partial def occurrencesOf (nested realized : Bool) (iteration : Array Nat) (found : Array CheckedEvent)
      (statements : Array Stmt) : Array CheckedEvent :=
    statements.foldl (occurrencesOfStmt nested realized iteration) found

  partial def occurrencesOfStmt (nested realized : Bool) (iteration : Array Nat) (found : Array CheckedEvent) :
      Stmt → Array CheckedEvent
    | .event mark event what => found.push (.event mark.id event what iteration nested realized)
    | .if _ _ onTrue onFalse _ => occurrencesOf true realized iteration (occurrencesOf true realized iteration found onTrue) onFalse
    | .match _ _ _ _ cases _ => cases.foldl (init := found) fun found (.case _ _ _ body) =>
        occurrencesOf true realized iteration found body
    | .for mark (.loop _ _ _ body) _ =>
      match body with
      | .uniform statements _ => occurrencesOf true realized iteration found statements
      | .empty statements _ =>
        if statements.isEmpty then found.push (.untypedLoop mark.span)
        else occurrencesOf true false iteration found statements
      | .stepped #[] => found.push (.untypedLoop mark.span)
      | .stepped iterations => iterations.foldl (init := found) fun found (.iteration index statements _) =>
          occurrencesOf true realized (iteration.push index) found statements
    | .scope _ body => occurrencesOf nested realized iteration found body
    | .bind .. | .unpack .. | .update .. | .guard .. | .error .. => found
end

end Events

/-- The occurrences of the events of a protocol body. -/
def occurrences (body : ProtocolBody) : Array CheckedEvent := Events.occurrencesOf false true #[] #[] body.statements

abbrev siteName := Syntax.eventSiteName

/-- The events of statements as the text has them, in its order, depth first: the place, the
`#[site(…)]` and the pattern of each. -/
partial def writtenEvents (statements : Array Syntax.Stmt) :
    Array (Syntax.Span × Option Syntax.SiteAttr × Option Syntax.Pattern) :=
  statements.foldl (init := #[]) fun found statement => found ++ match statement with
    | .eventStmt (.bound span site pattern _ _ _) => #[(span, site, some pattern)]
    | .eventStmt (.application span site _) | .«open» span site _ => #[(span, site, none)]
    | .«if» _ _ thenSuite elseBranch =>
      writtenEvents thenSuite ++ match elseBranch with
        | some (.suite _ statements) => writtenEvents statements
        | some (.elseIf statement) => writtenEvents #[statement]
        | none => #[]
    | .«match» _ _ cases => cases.foldl (init := #[]) fun found (.«case» _ _ body) => found ++ writtenEvents body
    | .«for» _ _ _ _ body => writtenEvents body
    | _ => #[]

/-- The places of the loops of statements as the text has them, in its order, depth first. The
number of a loop of a definition is its place in this list, the same at every instance. -/
partial def writtenLoops (statements : Array Syntax.Stmt) : Array Syntax.Span :=
  statements.foldl (init := #[]) fun found statement => found ++ match statement with
    | .«if» _ _ thenSuite elseBranch =>
      writtenLoops thenSuite ++ match elseBranch with
        | some (.suite _ statements) => writtenLoops statements
        | some (.elseIf statement) => writtenLoops #[statement]
        | none => #[]
    | .«match» _ _ cases => cases.foldl (init := #[]) fun found (.«case» _ _ body) => found ++ writtenLoops body
    | .«for» span _ _ _ body => #[span] ++ writtenLoops body
    | _ => #[]

/-- The names of the sites of a protocol (EV3): `#[site(n)]` names a site independently of its binder,
and two events do not share a name. Every refusal is reported. -/
def checkSiteNames (node : Syntax.Protocol) : CompileM Unit := do
  let mut named : Array (String × Syntax.Span) := #[]
  for (span, site, pattern) in writtenEvents node.body do
    if let some text := siteName site pattern then
      match named.find? (·.1 == text) with
      | some (_, earlier) =>
        logError "EV3" span
          (.ofText s!"two events are named `{text}` (lines {earlier.startLine}, {span.startLine})")
      | none => named := named.push (text, span)

end Zkc.Frontend.Passes
