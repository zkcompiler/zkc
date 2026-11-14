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
two events of one definition do not share a name, and `#[site(n)]` does not name an event whose
binder already names it.
-/

namespace Zkc.Frontend.Passes

open Typed

namespace Events

mutual
  /-- The occurrences of the events of statements, in the order of the tree, under the
  iterations of the loops in sequence around them. -/
  partial def occurrencesOf (iteration : Array Nat) (found : Array Occurrence)
      (statements : Array Stmt) : Array Occurrence :=
    statements.foldl (occurrencesOfStmt iteration) found

  partial def occurrencesOfStmt (iteration : Array Nat) (found : Array Occurrence) :
      Stmt → Array Occurrence
    | .event mark event _ => found.push { node := mark.id, event, iteration }
    | .if _ _ onTrue onFalse _ => occurrencesOf iteration (occurrencesOf iteration found onTrue) onFalse
    | .match _ _ _ _ cases _ => cases.foldl (init := found) fun found (.case _ _ _ body) =>
        occurrencesOf iteration found body
    | .for _ (.loop _ _ _ body) _ =>
      match body with
      | .uniform statements _ => occurrencesOf iteration found statements
      | .empty .. => found
      | .stepped iterations => iterations.foldl (init := found) fun found (.iteration index statements _) =>
          occurrencesOf (iteration.push index) found statements
    | .scope _ body => occurrencesOf iteration found body
    | .bind .. | .unpack .. | .update .. | .guard .. | .error .. => found
end

end Events

/-- The occurrences of the events of a protocol body. -/
def occurrences (body : ProtocolBody) : Array Occurrence := Events.occurrencesOf #[] #[] body.statements

/-- The name of the site of an event: its binder when it is one name, otherwise the name of
`#[site(…)]`. -/
def siteName (site : Option Syntax.SiteAttr) (pattern : Option Syntax.Pattern) : Option String :=
  match pattern, site with
  | some (.name name), _ => some name.text
  | _, some siteAttribute => some siteAttribute.name.text
  | _, _ => none

/-- The events of statements as the text has them, in its order, depth first: the place, the
`#[site(…)]` and the pattern of each. -/
partial def writtenEvents (statements : Array Syntax.Stmt) :
    Array (Syntax.Span × Option Syntax.SiteAttr × Option Syntax.Pattern) :=
  statements.foldl (init := #[]) fun found statement => found ++ match statement with
    | .eventStmt (.bound span site pattern _ _ _) => #[(span, site, some pattern)]
    | .eventStmt (.application span site _) => #[(span, site, none)]
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

/-- The names of the sites of a protocol (EV3): `#[site(n)]` names a site only when its binder
does not, and two events do not share a name. Every refusal is reported. -/
def checkSiteNames (node : Syntax.Protocol) : CompileM Unit := do
  let mut named : Array (String × Syntax.Span) := #[]
  for (span, site, pattern) in writtenEvents node.body do
    if let (some (.name binder), some siteAttribute) := (pattern, site) then
      unless siteAttribute.name.text == binder.text do
        logError "EV3" siteAttribute.span
          (.ofText s!"the site of `{binder.text} <- …` is named `{binder.text}`; `#[site({binder.text})]` names it otherwise")
    if let some text := siteName site pattern then
      match named.find? (·.1 == text) with
      | some (_, earlier) =>
        logError "EV3" span
          (.ofText s!"two events are named `{text}` (lines {earlier.startLine}, {span.startLine})")
      | none => named := named.push (text, span)

end Zkc.Frontend.Passes
