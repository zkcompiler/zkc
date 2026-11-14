module

public import Zkc.Core.RoundTrip

public section

/-! The link between a raw package and its typed term, one definition at a time.

A link of a definition is the typed definition, its raw syntax, and two facts that the
kernel decides by evaluating functions on the typed term: its raw syntax is the given
one, and it has no residual violation. Both facts mention the headers of the earlier
definitions and not their bodies, so the kernel checks a definition without looking at
another one.

The links of a package compose without evaluation. `LinkedFunctions.snoc` and
`LinkedProtocols.snoc` add one link to the links before it, and `LinkedPackage` states
the result: `unelaborate typed = raw`, and from the round-trip theorem
`elaborate raw = .ok typed`.

A long body is linked in pieces. A `LocalPrefixLink` or `ProtocolPrefixLink` is a run of
instructions as a function of the region that follows it, with the two facts stated for
every such region; `followedBy` joins it to the link of the rest.

The counts of functions and protocols are indices of the links. A fact would otherwise
mention the length of a list of headers, and the kernel would walk that list once per
definition.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-! ## Local regions -/

/-- A local region with its raw syntax. -/
structure LocalRegionLink (typeTable : TypeTable) (operations : List OperationSignature)
    (functions : List FunctionHeader) (deployed : Bool) (functionCount : Nat)
    (Γ out : List Ty) (depth : Nat) where
  typed : Region (LocalDialect operations functions deployed) Γ out
  raw : Raw.LocalRegion
  linked : unelaborateLocalRegion functionCount depth typed = raw
  wellFormed : localRegionViolation typeTable typed = none

/-- A run of local instructions before a region in the context `Δ`. -/
structure LocalPrefixLink (typeTable : TypeTable) (operations : List OperationSignature)
    (functions : List FunctionHeader) (deployed : Bool) (functionCount : Nat)
    (Γ Δ out : List Ty) (depth depthAfter : Nat) where
  typed : Region (LocalDialect operations functions deployed) Δ out →
    Region (LocalDialect operations functions deployed) Γ out
  raw : Raw.LocalRegion → Raw.LocalRegion
  linked : ∀ rest, unelaborateLocalRegion functionCount depth (typed rest) =
    raw (unelaborateLocalRegion functionCount depthAfter rest)
  wellFormed : ∀ rest, localRegionViolation typeTable (typed rest) =
    localRegionViolation typeTable rest

/-- A run of instructions followed by the rest of its region. -/
def LocalPrefixLink.followedBy {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} {deployed : Bool} {functionCount : Nat}
    {Γ Δ out : List Ty} {depth depthAfter : Nat}
    (first : LocalPrefixLink typeTable operations functions deployed functionCount Γ Δ out depth
      depthAfter)
    (rest : LocalRegionLink typeTable operations functions deployed functionCount Δ out depthAfter) :
    LocalRegionLink typeTable operations functions deployed functionCount Γ out depth :=
  ⟨first.typed rest.typed, first.raw rest.raw,
    (first.linked rest.typed).trans (congrArg first.raw rest.linked),
    (first.wellFormed rest.typed).trans rest.wellFormed⟩

/-! ## Functions -/

/-- A function typed over the headers of the functions before it, with its raw syntax.
`functionCount` is the number of those functions. -/
structure FunctionLink (typeTable : TypeTable) (operations : List OperationSignature)
    (functions : List FunctionHeader) (functionCount : Nat) (header : FunctionHeader) where
  definition : FunctionDefinition operations functions header
  raw : Raw.Function
  linked : unelaborateFunction functionCount definition = raw
  wellFormed : definition.violation typeTable = none

/-- The link of a function from the link of its body. -/
def FunctionLink.ofBody {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} {functionCount : Nat} (header : FunctionHeader)
    (depth : Nat) (counted : header.inputs.length = depth)
    (named : (Ty.allNamed typeTable header.inputs && Ty.allNamed typeTable header.outputs) = true)
    (body : LocalRegionLink typeTable operations functions (!header.specificationOnly) functionCount
      (bindAll [] header.inputs) header.outputs depth) :
    FunctionLink typeTable operations functions functionCount header :=
  ⟨⟨body.typed⟩,
    ⟨header.specificationOnly, Ty.stripAll header.inputs, Ty.stripAll header.outputs, body.raw⟩,
    by
      show Raw.Function.mk _ _ _ (unelaborateLocalRegion functionCount header.inputs.length body.typed)
        = _
      rw [counted, body.linked],
    by
      show cond _ (localRegionViolation typeTable body.typed) _ = none
      rw [named, body.wellFormed]
      rfl⟩

/-- The functions of a program up to some point, with their raw syntax, the most recent
first. -/
structure LinkedFunctions (typeTable : TypeTable) (operations : List OperationSignature)
    (count : Nat) (headers : List FunctionHeader) where
  typed : Functions typeTable operations headers
  raws : List Raw.Function
  counted : headers.length = count
  linked : ∀ later, unelaborateFunctions count typed later = raws.reverseAux later

def LinkedFunctions.empty {typeTable : TypeTable} {operations : List OperationSignature} :
    LinkedFunctions typeTable operations 0 [] :=
  ⟨.nil, [], rfl, fun _ => rfl⟩

/-- One more function. No fact about the earlier functions or about the new one is
decided again. -/
def LinkedFunctions.snoc {typeTable : TypeTable} {operations : List OperationSignature} {count : Nat}
    {headers : List FunctionHeader} {header : FunctionHeader}
    (earlier : LinkedFunctions typeTable operations count headers)
    (link : FunctionLink typeTable operations headers count header) :
    LinkedFunctions typeTable operations (count + 1) (header :: headers) :=
  ⟨.snoc earlier.typed link.definition link.wellFormed, link.raw :: earlier.raws,
    by rw [List.length_cons, earlier.counted],
    fun later => by
      show unelaborateFunctions (count + 1 - 1) earlier.typed
        (unelaborateFunction (count + 1 - 1) link.definition :: later) = _
      rw [Nat.add_sub_cancel, link.linked, earlier.linked]
      rfl⟩

/-- The link of a function known by its header only: the one fact elaboration decides of
it. -/
structure OpaqueLink (typeTable : TypeTable) (header : FunctionHeader) where
  named : (Ty.allNamed typeTable header.inputs && Ty.allNamed typeTable header.outputs) = true

/-- The raw syntax of a function known by its header only. -/
def OpaqueLink.raw {typeTable : TypeTable} {header : FunctionHeader} (_ : OpaqueLink typeTable header) :
    Raw.Function :=
  unelaborateOpaque header

/-- One more function, known by its header only. -/
def LinkedFunctions.snocOpaque {typeTable : TypeTable} {operations : List OperationSignature}
    {count : Nat} {headers : List FunctionHeader} {header : FunctionHeader}
    (earlier : LinkedFunctions typeTable operations count headers)
    (link : OpaqueLink typeTable header) :
    LinkedFunctions typeTable operations (count + 1) (header :: headers) :=
  ⟨.opaque earlier.typed header link.named, link.raw :: earlier.raws,
    by rw [List.length_cons, earlier.counted],
    fun later => by
      show unelaborateFunctions (count + 1 - 1) earlier.typed (unelaborateOpaque header :: later) = _
      rw [Nat.add_sub_cancel, earlier.linked]
      rfl⟩

/-! ## Protocol regions -/

/-- A protocol region with its raw syntax and the sites it uses: `sites before` lists
them before the sites met earlier. `enclosing` lists the participants of the `repeat` or
`choose` the region belongs to, if there is one. -/
structure ProtocolRegionLink (typeTable : TypeTable) (operations : List OperationSignature)
    (functions : List FunctionHeader) (protocols : List ProtocolHeader) (deployed : Bool)
    (functionCount protocolCount roles : Nat) (enclosing : Option (List Nat))
    (Γ out : List Located) (depth : Nat) where
  typed : Region (ProtocolDialect operations functions protocols deployed) Γ out
  raw : Raw.ProtocolRegion
  sites : List Nat → List Nat
  linked : unelaborateProtocolRegion functionCount protocolCount depth typed = raw
  collected : ∀ before,
    protocolRegionSites typeTable roles enclosing typed before = .ok (sites before)

/-- A run of protocol instructions before a region in the context `Δ`. -/
structure ProtocolPrefixLink (typeTable : TypeTable) (operations : List OperationSignature)
    (functions : List FunctionHeader) (protocols : List ProtocolHeader) (deployed : Bool)
    (functionCount protocolCount roles : Nat) (enclosing : Option (List Nat))
    (Γ Δ out : List Located) (depth depthAfter : Nat) where
  typed : Region (ProtocolDialect operations functions protocols deployed) Δ out →
    Region (ProtocolDialect operations functions protocols deployed) Γ out
  raw : Raw.ProtocolRegion → Raw.ProtocolRegion
  sites : List Nat → List Nat
  linked : ∀ rest, unelaborateProtocolRegion functionCount protocolCount depth (typed rest) =
    raw (unelaborateProtocolRegion functionCount protocolCount depthAfter rest)
  collected : ∀ rest before, protocolRegionSites typeTable roles enclosing (typed rest) before =
    protocolRegionSites typeTable roles enclosing rest (sites before)

def ProtocolPrefixLink.followedBy {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} {protocols : List ProtocolHeader} {deployed : Bool}
    {functionCount protocolCount roles : Nat} {enclosing : Option (List Nat)}
    {Γ Δ out : List Located} {depth depthAfter : Nat}
    (first : ProtocolPrefixLink typeTable operations functions protocols deployed functionCount
      protocolCount roles enclosing Γ Δ out depth depthAfter)
    (rest : ProtocolRegionLink typeTable operations functions protocols deployed functionCount
      protocolCount roles enclosing Δ out depthAfter) :
    ProtocolRegionLink typeTable operations functions protocols deployed functionCount protocolCount
      roles enclosing Γ out depth :=
  ⟨first.typed rest.typed, first.raw rest.raw, fun before => rest.sites (first.sites before),
    (first.linked rest.typed).trans (congrArg first.raw rest.linked),
    fun before => (first.collected rest.typed before).trans (rest.collected (first.sites before))⟩

/-! ## Protocols -/

/-- A protocol typed over the headers of every function and of the protocols before it,
with its raw syntax. When `written` holds its sites are also numbered without gaps. -/
structure ProtocolLink (written : Bool) (typeTable : TypeTable) (operations : List OperationSignature)
    (functions : List FunctionHeader) (protocols : List ProtocolHeader)
    (functionCount protocolCount : Nat) (header : ProtocolHeader) where
  definition : ProtocolDefinition operations functions protocols header
  raw : Raw.Protocol
  linked : unelaborateProtocol functionCount protocolCount definition = raw
  wellFormed : definition.violation typeTable = none
  dense : written = true → definition.dense typeTable = true

/-- The link of a protocol from the link of its body. The conditions on the signature
and on the sites of the whole body are decided here, once. -/
def ProtocolLink.ofBody {written : Bool} {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} {protocols : List ProtocolHeader}
    {functionCount protocolCount : Nat} (header : ProtocolHeader) (depth : Nat)
    (agreements : List Raw.Agreement)
    (body : ProtocolRegionLink typeTable operations functions protocols (!header.specificationOnly)
      functionCount protocolCount header.roles none (bindAll [] header.inputs) header.outputs depth)
    (counted : header.inputs.length = depth)
    (agreed : unelaborateAgreements header.agreements = agreements)
    (signature : firstViolation
      (portConditions typeTable header.roles (header.inputs ++ header.outputs) ++
        (agreementConditions header.agreements.inputs ++
          agreementConditions header.agreements.outputs)) = none)
    (unused : sitesViolation (body.sites []) = none)
    (dense : written = true → sitesDense (body.sites []) = true) :
    ProtocolLink written typeTable operations functions protocols functionCount protocolCount header :=
  ⟨⟨body.typed⟩,
    ⟨header.specificationOnly, header.roles, Located.stripAll header.inputs,
      Located.stripAll header.outputs, agreements, body.raw⟩,
    by
      show Raw.Protocol.mk _ _ _ _ (unelaborateAgreements header.agreements)
        (unelaborateProtocolRegion functionCount protocolCount header.inputs.length body.typed) = _
      rw [counted, agreed, body.linked],
    by
      show earlierViolation _ (match protocolRegionSites typeTable header.roles none body.typed [] with
        | .error violation => some violation
        | .ok sites => sitesViolation sites) = none
      rw [signature, body.collected]
      exact unused,
    fun isWritten => by
      show (match protocolRegionSites typeTable header.roles none body.typed [] with
        | .error _ => true
        | .ok sites => sitesDense sites) = true
      rw [body.collected]
      exact dense isWritten⟩

/-- The protocols of a program up to some point, with their raw syntax, the most recent
first. -/
structure LinkedProtocols (written : Bool) (typeTable : TypeTable) (operations : List OperationSignature)
    (functions : List FunctionHeader) (functionCount count : Nat)
    (headers : List ProtocolHeader) where
  typed : Protocols typeTable operations functions headers
  raws : List Raw.Protocol
  counted : headers.length = count
  linked : ∀ later, unelaborateProtocols functionCount count typed later = raws.reverseAux later
  dense : written = true → typed.dense = true

def LinkedProtocols.empty {written : Bool} {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} {functionCount : Nat} :
    LinkedProtocols written typeTable operations functions functionCount 0 [] :=
  ⟨.nil, [], rfl, fun _ => rfl, fun _ => rfl⟩

def LinkedProtocols.snoc {written : Bool} {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} {functionCount count : Nat} {headers : List ProtocolHeader}
    {header : ProtocolHeader}
    (earlier : LinkedProtocols written typeTable operations functions functionCount count headers)
    (link : ProtocolLink written typeTable operations functions headers functionCount count header) :
    LinkedProtocols written typeTable operations functions functionCount (count + 1)
      (header :: headers) :=
  ⟨.snoc earlier.typed link.definition link.wellFormed, link.raw :: earlier.raws,
    by rw [List.length_cons, earlier.counted],
    fun later => by
      show unelaborateProtocols functionCount (count + 1 - 1) earlier.typed
        (unelaborateProtocol functionCount (count + 1 - 1) link.definition :: later) = _
      rw [Nat.add_sub_cancel, link.linked, earlier.linked]
      rfl,
    fun isWritten => by
      show (earlier.typed.dense && link.definition.dense typeTable) = true
      rw [earlier.dense isWritten, link.dense isWritten]
      rfl⟩

/-! ## Packages -/

/-- A package assembled from the links of its definitions. -/
structure LinkedPackage (written : Bool) where
  types : List CatalogueRow
  records : List RecordDeclaration
  variants : List VariantDeclaration
  table : List Operation
  names : Option Raw.Names
  functionCount : Nat
  protocolCount : Nat
  functionHeaders : List FunctionHeader
  protocolHeaders : List ProtocolHeader
  functions : LinkedFunctions (typeTableOf types records variants) (table.map (·.signature))
    functionCount functionHeaders
  protocols : LinkedProtocols written (typeTableOf types records variants)
    (table.map (·.signature)) functionHeaders functionCount protocolCount protocolHeaders
  tablesFormed : tablesViolation types records variants table = none
  namesFormed : namesViolation names functionHeaders.length (roleCounts protocolHeaders) = none

namespace LinkedPackage

variable {written : Bool} (package : LinkedPackage written)

/-- The typed package. -/
def typed : Typed :=
  ⟨package.types, package.records, package.variants, package.table, package.functionHeaders,
    package.protocolHeaders,
    ⟨package.functions.typed, package.protocols.typed⟩, package.names, package.tablesFormed,
    package.namesFormed⟩

/-- The raw package: the raw definitions in program order. -/
def raw : Raw.Package :=
  ⟨package.types.map CatalogueRow.strip, package.records, package.variants,
    package.table.map Operation.strip, package.functions.raws.reverse,
    package.protocols.raws.reverse, package.names⟩

/-- The raw syntax of the typed package is the raw package. This is the composition of
the per-definition facts; nothing is evaluated. -/
theorem unelaborates : unelaborate package.typed = package.raw := by
  show Raw.Package.mk _ _ _ _
    (unelaborateFunctions package.functionHeaders.length package.functions.typed [])
    (unelaborateProtocols package.functionHeaders.length package.protocolHeaders.length
      package.protocols.typed []) _ = _
  rw [package.functions.counted, package.protocols.counted, package.functions.linked,
    package.protocols.linked]
  rfl

/-- The typed package is the elaboration of the raw package. -/
theorem elaborates : elaborate package.raw = .ok package.typed :=
  package.unelaborates ▸ elaborate_unelaborate package.typed

/-- The typed package is the elaboration of the raw package as written: its sites are
also numbered without gaps. -/
theorem elaboratesWritten (isWritten : written = true) :
    elaborateWritten package.raw = .ok package.typed := by
  have dense : package.typed.program.dense = true := package.protocols.dense isWritten
  unfold elaborateWritten
  rw [package.elaborates]
  show cond package.typed.program.dense _ _ = _
  rw [dense]
  rfl

end LinkedPackage

/-! ## References through a skipped block of bindings

A reference to a value bound long ago would make the kernel walk the context to its
position. `Skips Γ Δ count` says that `Δ` is `Γ` without its `count` most recent values,
so a position of `Δ` is a position of `Γ`. Skips compose, and a skip over a whole piece
of a body is decided once, so the kernel reaches an old value in a number of steps that
is logarithmic in the number of pieces. -/

/-- `Δ` is `Γ` without its `count` most recent values. -/
def Skips {α : Type} (Γ Δ : List α) (count : Nat) : Prop :=
  ∀ index, Γ[index + count]? = Δ[index]?

namespace Skips

variable {α : Type}

/-- The kernel decides a skip by dropping the values. -/
theorem drop (Γ Δ : List α) (count : Nat) (dropped : Γ.drop count = Δ) : Skips Γ Δ count := by
  intro index
  rw [← dropped, List.getElem?_drop, Nat.add_comm]

theorem trans {Γ Δ Ε : List α} {first second : Nat} (total : Nat) (outer : Skips Γ Δ first)
    (inner : Skips Δ Ε second) (sum : second + first = total) : Skips Γ Ε total := by
  intro index
  rw [← sum, ← Nat.add_assoc, outer, inner]

/-- A value of the shorter context, found in the longer one. -/
theorem lookup {Γ Δ : List α} {count : Nat} (skips : Skips Γ Δ count) (index position : Nat)
    (entry : α) (placed : index + count = position) (found : Δ[index]? = some entry) :
    Γ[position]? = some entry := by
  rw [← placed, skips index, found]

end Skips

end Zkc.Core
