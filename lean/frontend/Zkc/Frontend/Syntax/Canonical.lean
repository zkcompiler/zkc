module

public import Zkc.Frontend.Syntax.Tree

@[expose] public section

set_option autoImplicit false

/-!
# The canonical tree (FM1, FM2)

The changes that the formatter makes to a tree, apart from layout. Each is decided from the
text alone:

- FM1: one role in `@( … )` is written without parentheses, and the roles of `@( … )` stand in
  the order of the roster of the enclosing protocol; a role that is not in the roster keeps its
  place after those that are. Outside a protocol the order is kept.
- FM1: a body that is one expression is printed as an expression body: a `def` body of only
  `return e` becomes the suite form with the expression alone.
- FM2: `else reject` on a guard is removed; `-> ()` on a `def` and on a function member of an
  interface is removed; `#[site(x)]` on an event whose binder is the single name `x` is removed;
  a role-map entry `O = O` is removed, and the map with it when it is left empty.

The other rows of FM2 (`@S` on a binder, `from p` on a send or a query, `@R` on `reduces` and
`proves`, `_ <-` on an application) compare an annotation with what the checker computes, and
are kept here.
-/

namespace Zkc.Frontend.Syntax.Canonical

def orderRoles (roster : Option (Array Name)) (roles : Array Name) : Array Name :=
  match roster with
  | none => roles
  | some names =>
    let inRoster := names.filterMap fun rosterName => roles.find? (·.text == rosterName.text)
    let others := roles.filter fun role => !names.any (·.text == role.text)
    if inRoster.size + others.size == roles.size then inRoster ++ others else roles

def holders (roster : Option (Array Name)) : Holders → Holders
  | .role role => .role role
  | .roles span roles =>
    match orderRoles roster roles with
    | #[role] => .role role
    | ordered => .roles span ordered

def placement (roster : Option (Array Name)) (value : Placement) : Placement :=
  { value with holders := holders roster value.holders
               readers := value.readers.map (holders roster) }

def isUnitType : TypeExpr → Bool
  | .tuple _ #[] => true
  | _ => false

def roleMap (value : Option RoleMap) : Option RoleMap :=
  match value with
  | none => none
  | some map =>
    let entries := map.entries.filter fun entry => entry.callee.text != entry.caller.text
    if entries.isEmpty then none else some { map with entries }

def application (value : Application) : Application :=
  { value with roleMap := roleMap value.roleMap }

def event : Event → Event
  | .application value => .application (application value)
  | other => other

def siteIsBinder (site : Option SiteAttr) (pattern : Pattern) : Bool :=
  match site, pattern with
  | some siteAttribute, .name binder => siteAttribute.name.text == binder.text
  | _, _ => false

mutual
  partial def stmt (roster : Option (Array Name)) : Stmt → Stmt
    | .binding span pattern type h value => .binding span pattern type (h.map (holders roster)) value
    | .mutDecl span name type p value =>
      .mutDecl span name type (p.map (placement roster)) value
    | .eventStmt (.bound span site pattern type h e) =>
      let site := if siteIsBinder site pattern then none else site
      .eventStmt (.bound span site pattern type (h.map (holders roster)) (event e))
    | .eventStmt (.application span site value) =>
      .eventStmt (.application span site (application value))
    | .guard span h condition reason =>
      let reason := match reason with
        | some (.reject _) => none
        | other => other
      .guard span (h.map (holders roster)) condition reason
    | .«if» span condition thenSuite elseBranch =>
      .«if» span condition (thenSuite.map (stmt roster)) (elseBranch.map (elseNode roster))
    | .«match» span scrutinee cases => .«match» span scrutinee (cases.map (caseNode roster))
    | .«for» span pattern domain collected body =>
      .«for» span pattern domain collected (body.map (stmt roster))
    | other => other

  partial def elseNode (roster : Option (Array Name)) : ElseBranch → ElseBranch
    | .suite span statements => .suite span (statements.map (stmt roster))
    | .elseIf statement => .elseIf (stmt roster statement)

  partial def caseNode (roster : Option (Array Name)) : Case → Case
    | .«case» span pattern body => .«case» span pattern (body.map (stmt roster))
end

def body : Body → Body
  | .statements span #[] result => .suiteExpression span result
  | .statements span statements result => .statements span (statements.map (stmt none)) result
  | other => other

def defBinding : DefBinding → DefBinding
  | .body value => .body (body value)
  | other => other

def defNode (value : Def) : Def :=
  { value with
    result := if value.result.any isUnitType then none else value.result
    binding := defBinding value.binding }

def protocolHead (value : ProtocolHead) : ProtocolHead :=
  let roster := some value.roles
  let port : Port → Port
    | .port span name type p isPrivate => .port span name type (placement roster p) isPrivate
    | other => other
  let result (r : Result) : Result := { r with placement := placement roster r.placement }
  { value with
    ports := value.ports.map port
    results := value.results.map fun
      | .one r => .one (result r)
      | .several span rs => .several span (rs.map result) }

def protocol (value : Protocol) : Protocol :=
  let roster := some value.head.roles
  { value with head := protocolHead value.head, body := value.body.map (stmt roster) }

def law (value : Law) : Law := { value with body := body value.body }

def member : Member → Member
  | .defMember span modifier name sp params result w =>
    .defMember span modifier name sp params (if result.any isUnitType then none else result) w
  | .protocolMember head => .protocolMember (protocolHead head)
  | .lawMember value => .lawMember (law value)
  | other => other

mutual
  partial def item : Item → Item
    | .«section» (.«section» span sp w items) => .«section» (.«section» span sp w (items.map item))
    | .«module» (.«module» span pub name sp b w moduleBody) =>
      let moduleBody := match moduleBody with
        | .suite items => .suite (items.map moduleItem)
        | other => other
      .«module» (.«module» span pub name sp b w moduleBody)
    | .interface value => .interface { value with members := value.members.map (·.map member) }
    | .«def» value => .«def» (defNode value)
    | .protocol value => .protocol (protocol value)
    | .relation value =>
      .relation { value with
        binding := match value.binding with
          | .body b => .body (body b)
          | other => other }
    | .law value => .law (law value)
    | other => other

  partial def moduleItem : ModuleItem → ModuleItem
    | .item value => .item (item value)
    | .memberDef value => .memberDef { value with binding := defBinding value.binding }
    | other => other
end

end Canonical

/-- The tree that the formatter prints for `tree` (FM1, FM2). -/
def canonicalize (tree : File) : File :=
  { tree with items := tree.items.map Canonical.item }

end Zkc.Frontend.Syntax
