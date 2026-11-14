module

public import Zkc.Frontend.Lowered.Basic

@[expose] public section

set_option autoImplicit false

/-!
# The lowered form of bodies

The lowered form is what is known of a declaration before any instance of it exists. It is
computed once per declaration, from the syntax tree and the names in scope, and elaboration at
an instance reads it instead of the syntax tree.

- **Names are resolved in place.** A use of a local name is `local` with the number of its
  binder; a path to anything else is a `Reference` whose segments are the steps of resolution,
  with the static arguments written on them lowered. No table is consulted afterwards.
- **A derived form that needs no type is already its kernel form**: `else if` is an `if` in the
  `else`, an absent `else` is the empty suite, `T{f}` is `T{f = f}`, a call alone on a protocol
  line is an application without a binder, a pattern is one `unpack` per level with binders that
  lowering makes, `and` and `or` are conditionals that remember how they were written, the two
  spellings of a mathematical form are one node, a role is its place in the roster.
- **A static term is kept as a term.** A size, a static argument, a type: each is evaluated at
  the instance. `Stmt.staticName` and the flag of a static `if` say where a term is static by
  its form (TY2, TY9), so that the instance evaluates and does not type it.
- **What depends on a type stays unresolved, as a node that says so**: an operator, an index, a
  slice, a field, a dot call, a number (TY6), a bare alternative, a record update, a
  comprehension and a fold. Elaboration replaces each by typed kernel forms.

A name that resolution refused is `Expr.error`: what depends on it is not elaborated, and the
rest of the declaration is.
-/

namespace Zkc.Frontend.Lowered

open Syntax

/-- A local binder. Its number is its place among the binders of its declaration. -/
structure Binder where
  id : LocalId
  /-- The name as written; for a binder that lowering made, a name no source can write. -/
  name : String
  span : Span
  origin : BinderOrigin := .written
  /-- Declared with `mut`. -/
  mutable : Bool := false
  deriving Inhabited

mutual
  /-- A written path, resolved: one segment per step. -/
  inductive Reference where
    | reference (span : Span) (segments : Array Segment)

  /-- A step and the static arguments written on it. Arguments that an import fixed are those
  of the import's path, evaluated under the scopes of the import. -/
  inductive Segment where
    | segment (step : PathStep) (arguments : Option (Array StaticArgument))
        (fixedBy : Option ImportId)

  inductive StaticArgument where
    | term (span : Span) (name : Option String) (term : Expr)
    | inferred (span : Span) (name : Option String)
    | spec (span : Span) (name : String) (term : Expr)

  /-- A type as written, to evaluate at an instance: its sizes are terms. -/
  inductive TypeTerm where
    | bool (span : Span)
    | nat (span : Span)
    | rational (span : Span)
    | index (span : Span) (size : Expr)
    | nonzero (span : Span) (type : TypeTerm)
    | sequence (span : Span) (element : TypeTerm) (size : Option Expr)
    | tuple (span : Span) (fields : Array TypeTerm) (names : Array (Option String))
    | reference (reference : Reference)
    /-- A local name where a type stands: no type, which elaboration refuses (TY1). -/
    | «local» (span : Span) (binder : LocalId)
    /-- A path that resolution refused stood here. -/
    | error (span : Span)

  inductive Expr where
    /-- A number; its type is that of the place it stands in (TY6). -/
    | number (span : Span) (value : Nat)
    | bytes (span : Span) (data : List Nat)
    | bool (span : Span) (value : Bool)
    | «local» (span : Span) (binder : LocalId)
    /-- A path alone: a static parameter, a static name, an alternative without a payload, a
    declaration that a static term names. -/
    | reference (reference : Reference)
    /-- `Path(args)`: a call of a function, an alternative with its payload, a fixed function.
    In a relation's call the arguments after `;` are the witnesses. -/
    | call (span : Span) (callee : Reference) (arguments : Array Argument)
        (witnesses : Option (Array Argument))
    /-- Unresolved: an operator on its operands, in the order written. -/
    | operator (span : Span) (operator : Operator) (operands : Array Expr)
    /-- Unresolved: `xs[a..b]`. -/
    | slice (span : Span) (target : Expr) (lower upper : Option Expr)
    /-- Unresolved: `e.name` is a field of a record, a named component, or a result of an
    application. -/
    | field (span : Span) (target : Expr) (name : Name)
    /-- Unresolved: `e.m<σ>(a)` is `H::m<σ>(e, a)` for the home module `H` of the type of `e`. -/
    | method (span : Span) (target : Expr) (name : Name)
        (staticArguments : Option (Array StaticArgument)) (arguments : Array Argument)
    | position (span : Span) (target : Expr) (position : Nat)
    | conditional (span : Span) (form : ConditionalForm) (condition onTrue onFalse : Expr)
    | tuple (span : Span) (components : Array Expr) (names : Array (Option String))
    | list (span : Span) (elements : Array Expr)
    /-- `[v; n]` -/
    | repetition (span : Span) (element count : Expr)
    /-- `T{f = e, …}`; a field written bare is already `f = f`. -/
    | record (span : Span) (type : Reference) (fields : Array FieldValue)
    /-- Unresolved: `{r with f = v}` needs the record type of `r`. -/
    | recordUpdate (span : Span) (record : Expr) (fields : Array FieldValue)
    /-- Unresolved: `[e for p in D if c]`. What it becomes depends on the domain and on whether
    the elements are typed one by one (TY11). -/
    | comprehension (span : Span) (element : Expr) (generator : Generator) (filter : Option Expr)
    /-- Unresolved: `∑ ∏ ∀ ∃` over a domain, in either spelling. A row on elements of a sort, a
    loop that carries the accumulator otherwise. -/
    | fold (span : Span) (fold : Fold) (generator : Generator) (body : Expr)
    /-- Unresolved: `⟪a, b⟫`, in either spelling. -/
    | inner (span : Span) (left right : Expr)
    /-- Statements, then a value: the body of a function, and an expression whose pattern
    lowering took apart. -/
    | block (span : Span) (statements : Array Stmt) (result : Expr)
    /-- A type where a static term stands (GR5). -/
    | type (type : TypeTerm)
    /-- A name that resolution refused stood here. -/
    | error (span : Span)

  inductive Argument where
    | positional (span : Span) (value : Expr)
    | named (span : Span) (name : Name) (value : Expr)
    | spec (span : Span) (name : Name) (value : Expr)

  inductive FieldValue where
    | field (span : Span) (name : Name) (value : Expr)

  /-- What a loop, a comprehension or a fold ranges over, and the binder of each item. -/
  inductive Generator where
    /-- `for i in a..b`. `staticIndex` says that the index stands in the body in a size, in a
    static argument or in a bound of a slice (TY10): each iteration is typed on its own. An
    index that stands as the position of a tuple is found at the instance. -/
    | range (index : Binder) (start stop : Expr) (staticIndex : Bool)
    /-- `for x in xs`: the collection is evaluated once; `iteration` is the binder of the
    iteration number, which lowering made. -/
    | collection (item : Binder) (iteration : Binder) (source : Expr)

  inductive Stmt where
    /-- `x = e`, `x: T = e`, `x @S = e`, `mut x = e`. -/
    | bind (span : Span) (binder : Binder) (type : Option TypeTerm) (roles : Option RoleSet)
        (value : Expr)
    /-- `x = e` with `e` a static term: `x` stands for a number (TY2). -/
    | staticName (span : Span) (binder : Binder) (value : Expr)
    /-- One level of a pattern: every component at once. `_` is a binder that lowering makes,
    with the origin `discarded`, at the place of the `_`. -/
    | unpack (span : Span) (shape : UnpackShape) (binders : Array (Option Binder))
        (roles : Option RoleSet) (value : Expr)
    /-- `x := e`: the target is the local name as resolved, or an error node when it is not
    bound. -/
    | update (span : Span) (target : Expr) (value : Expr)
    | guard (span : Span) (roles : Option RoleSet) (condition : Expr) (reason : Zkc.Core.Reason)
    /-- `isStatic`: the condition is a comparison of sizes or built from such (TY9); the
    instance takes one arm and does not type the other. -/
    | «if» (span : Span) (isStatic : Bool) (condition : Expr) (onTrue onFalse : Array Stmt)
    | «match» (span : Span) (scrutinee : Expr) (cases : Array Case)
    | «for» (span : Span) (generator : Generator) (collected : Array Collected)
        (body : Array Stmt)
    /-- An event with its number in the text, the binder of its result when it has one name,
    and the role written on the binder (`s @P <- sample T`). -/
    | event (span : Span) (event : EventId) (binder : Option Binder) (type : Option TypeTerm)
        (roles : Option RoleSet) (what : Event)
    /-- A statement of a layer that is not elaborated yet: the body waits for it. Its names are
    kept resolved, as terms. -/
    | waiting (span : Span) (reason : String) (names : Array Expr)

  inductive Collected where
    | collected (span : Span) (binder : Binder) (value : Expr)

  inductive Case where
    | «case» (span : Span) (pattern : CasePattern) (body : Array Stmt)

  /-- What follows `case`. Which alternative a name stands for is decided against the type of
  the matched value. -/
  inductive CasePattern where
    /-- A name that is no alternative, or `_`: it covers every value. -/
    | any (span : Span) (binder : Option Binder)
    | alternative (span : Span) (alternative : Reference) (payload : Array CasePattern)
    | tuple (span : Span) (items : Array CasePattern)
    /-- A number or a literal of `bool`: one value of its type. -/
    | literal (span : Span) (value : Expr)
    /-- `T{f = p, …}`: a record taken apart, a pattern per field written. -/
    | record (span : Span) (type : Reference) (fields : Array (Name × CasePattern))

  inductive Event where
    /-- `send e from p to R`: the sender when written, the receivers in the order written. -/
    | send (payload : Expr) (sender : Option Nat) (receivers : Array Nat)
    | draw (law : TypeTerm) (sender : Nat) (receivers : Array Nat)
    | sample (law : TypeTerm)
    | attempt
    /-- An application of a protocol. The role map as written: the callee's role by name, the
    caller's by its place. It is completed by name against the callee's roster at the
    instance (RM1). -/
    | apply (callee : Reference) (arguments : Array Argument) (roleMap : Array (Name × Nat))

  /-- What a pattern of one level takes apart. -/
  inductive UnpackShape where
    /-- A tuple of this many components. -/
    | tuple (size : Nat)
    /-- A record, by its declaration and the path that names it: binder `k` takes the field
    written `fields[k]`, with the place of the field as written. Which field of the record that
    is, is decided at the instance: an alias names its record only there. -/
    | record (type : Reference) (declaration : DeclarationId) (fields : Array (Span × String))
    /-- The results of an application, in the order of the callee's head. -/
    | results
end

instance : Inhabited Reference := ⟨.reference default #[]⟩
instance : Inhabited Segment := ⟨.segment .«local» none none⟩
instance : Inhabited StaticArgument := ⟨.inferred default none⟩
instance : Inhabited Expr := ⟨.error default⟩
instance : Inhabited Argument := ⟨.positional default default⟩
instance : Inhabited FieldValue := ⟨.field default default default⟩
instance : Inhabited CasePattern := ⟨.any default none⟩
instance : Inhabited Case := ⟨.«case» default default #[]⟩
instance : Inhabited Collected := ⟨.collected default default default⟩
instance : Inhabited Event := ⟨.attempt⟩
instance : Inhabited UnpackShape := ⟨.results⟩
instance : Inhabited TypeTerm := ⟨.bool default⟩
instance : Inhabited Stmt := ⟨.waiting default "" #[]⟩
instance : Inhabited Generator := ⟨.range default default default false⟩

namespace Expr

/-- The place of an expression. -/
def span : Expr → Span
  | .number span _ | .bytes span _ | .bool span _ | .local span _ | .call span .. | .operator span ..
  | .slice span .. | .field span .. | .method span .. | .position span .. | .conditional span ..
  | .tuple span .. | .list span _ | .repetition span .. | .record span .. | .recordUpdate span ..
  | .comprehension span .. | .fold span .. | .inner span .. | .block span .. | .error span => span
  | .reference (.reference span _) => span
  | .type written =>
    match written with
    | .bool span | .nat span | .rational span | .index span _ | .nonzero span _
    | .sequence span .. | .tuple span .. | .error span | .local span _ => span
    | .reference (.reference span _) => span

end Expr

/-! ## The references of a term

One fold over the lowered form: every reference that a term, a type or a statement holds, in the
order of the text, each followed by the references in its static arguments. It is what every
question of which parameters, static names or declarations a term mentions reads. -/

mutual
  partial def Reference.collect (acc : Array Reference) (reference : Reference) : Array Reference :=
    match reference with
    | .reference _ segments =>
      segments.foldl (init := acc.push reference) fun acc (.segment _ arguments _) =>
        (arguments.getD #[]).foldl (init := acc) StaticArgument.collect

  partial def StaticArgument.collect (acc : Array Reference) : StaticArgument → Array Reference
    | .term _ _ term | .spec _ _ term => term.collect acc
    | .inferred .. => acc

  partial def TypeTerm.collect (acc : Array Reference) : TypeTerm → Array Reference
    | .index _ size => size.collect acc
    | .nonzero _ type => type.collect acc
    | .sequence _ element size =>
      let acc := element.collect acc
      match size with
      | some size => size.collect acc
      | none => acc
    | .tuple _ fields _ => fields.foldl TypeTerm.collect acc
    | .reference reference => reference.collect acc
    | .bool _ | .nat _ | .rational _ | .local .. | .error _ => acc

  partial def Expr.collect (acc : Array Reference) : Expr → Array Reference
    | .reference reference => reference.collect acc
    | .call _ callee arguments witnesses =>
      (arguments ++ witnesses.getD #[]).foldl Argument.collect (callee.collect acc)
    | .operator _ _ operands => operands.foldl Expr.collect acc
    | .slice _ target lower upper =>
      let acc := target.collect acc
      let acc := match lower with
        | some lower => lower.collect acc
        | none => acc
      match upper with
      | some upper => upper.collect acc
      | none => acc
    | .field _ target _ | .position _ target _ => target.collect acc
    | .method _ target _ staticArguments arguments =>
      let acc := (staticArguments.getD #[]).foldl StaticArgument.collect (target.collect acc)
      arguments.foldl Argument.collect acc
    | .conditional _ _ a b c => c.collect (b.collect (a.collect acc))
    | .tuple _ items _ | .list _ items => items.foldl Expr.collect acc
    | .repetition _ a b | .inner _ a b => b.collect (a.collect acc)
    | .record _ type fields =>
      fields.foldl (fun acc (.field _ _ value) => value.collect acc) (type.collect acc)
    | .recordUpdate _ value fields =>
      fields.foldl (fun acc (.field _ _ value) => value.collect acc) (value.collect acc)
    | .comprehension _ element domain filter =>
      let acc := element.collect (domain.collect acc)
      match filter with
      | some filter => filter.collect acc
      | none => acc
    | .fold _ _ domain body => body.collect (domain.collect acc)
    | .block _ statements result => result.collect (statements.foldl Stmt.collect acc)
    | .type type => type.collect acc
    | .number .. | .bytes .. | .bool .. | .local .. | .error _ => acc

  partial def Argument.collect (acc : Array Reference) : Argument → Array Reference
    | .positional _ value | .named _ _ value | .spec _ _ value => value.collect acc

  partial def Generator.collect (acc : Array Reference) : Generator → Array Reference
    | .range _ start stop _ => stop.collect (start.collect acc)
    | .collection _ _ source => source.collect acc

  partial def Stmt.collect (acc : Array Reference) : Stmt → Array Reference
    | .bind _ _ type _ value =>
      value.collect (match type with
        | some type => type.collect acc
        | none => acc)
    | .staticName _ _ value => value.collect acc
    | .unpack _ shape _ _ value =>
      value.collect (match shape with
        | .record type _ _ => type.collect acc
        | .tuple _ | .results => acc)
    | .update _ target value => value.collect (target.collect acc)
    | .guard _ _ condition _ => condition.collect acc
    | .«if» _ _ condition onTrue onFalse =>
      onFalse.foldl Stmt.collect (onTrue.foldl Stmt.collect (condition.collect acc))
    | .«match» _ scrutinee cases =>
      cases.foldl (fun acc (.«case» _ pattern body) => body.foldl Stmt.collect (pattern.collect acc))
        (scrutinee.collect acc)
    | .«for» _ domain collected body =>
      let acc := body.foldl Stmt.collect (domain.collect acc)
      collected.foldl (fun acc (.collected _ _ value) => value.collect acc) acc
    | .event _ _ _ type _ what =>
      what.collect (match type with
        | some type => type.collect acc
        | none => acc)
    | .waiting _ _ names => names.foldl Expr.collect acc

  partial def CasePattern.collect (acc : Array Reference) : CasePattern → Array Reference
    | .alternative _ alternative payload => payload.foldl CasePattern.collect (alternative.collect acc)
    | .tuple _ items => items.foldl CasePattern.collect acc
    | .record _ type fields => fields.foldl (fun acc (_, item) => item.collect acc) (type.collect acc)
    | .literal _ value => value.collect acc
    | .any .. => acc

  partial def Event.collect (acc : Array Reference) : Event → Array Reference
    | .send payload _ _ => payload.collect acc
    | .draw law _ _ | .sample law => law.collect acc
    | .attempt => acc
    | .apply callee arguments _ => arguments.foldl Argument.collect (callee.collect acc)
end

/-- The local names that a term reads, by their binders, in the order of the text: those in the
static arguments of its references included. -/
partial def Expr.locals (expr : Expr) : Array LocalId :=
  let fromArguments (arguments : Array StaticArgument) : Array LocalId :=
    arguments.foldl (init := #[]) fun acc argument =>
      match argument with
      | .term _ _ term | .spec _ _ term => acc ++ term.locals
      | .inferred .. => acc
  let fromReference : Reference → Array LocalId
    | .reference _ segments => segments.foldl (init := #[]) fun acc (.segment _ arguments _) =>
        acc ++ fromArguments (arguments.getD #[])
  let rec fromType : TypeTerm → Array LocalId
    | .index _ size => size.locals
    | .nonzero _ widened => fromType widened
    | .sequence _ element size => fromType element ++ ((size.map (·.locals)).getD #[])
    | .tuple _ fields _ => fields.foldl (init := #[]) fun acc field => acc ++ fromType field
    | .reference written => fromReference written
    | .local _ binder => #[binder]
    | .bool _ | .nat _ | .rational _ | .error _ => #[]
  let fromArgument : Argument → Array LocalId
    | .positional _ value | .named _ _ value | .spec _ _ value => value.locals
  match expr with
  | .local _ binder => #[binder]
  | .reference written => fromReference written
  | .call _ callee arguments witnesses =>
    (arguments ++ witnesses.getD #[]).foldl (init := fromReference callee) fun acc argument =>
      acc ++ fromArgument argument
  | .operator _ _ operands => operands.foldl (init := #[]) fun acc operand => acc ++ operand.locals
  | .slice _ target lower upper =>
    target.locals ++ ((lower.map (·.locals)).getD #[]) ++ ((upper.map (·.locals)).getD #[])
  | .field _ target _ | .position _ target _ => target.locals
  | .method _ target _ staticArguments arguments =>
    arguments.foldl (init := target.locals ++ fromArguments (staticArguments.getD #[])) fun acc argument =>
      acc ++ fromArgument argument
  | .conditional _ _ a b c => a.locals ++ b.locals ++ c.locals
  | .tuple _ items _ | .list _ items => items.foldl (init := #[]) fun acc item => acc ++ item.locals
  | .repetition _ a b | .inner _ a b => a.locals ++ b.locals
  | .record _ named fields =>
    fields.foldl (init := fromReference named) fun acc (.field _ _ value) => acc ++ value.locals
  | .recordUpdate _ value fields =>
    fields.foldl (init := value.locals) fun acc (.field _ _ value) => acc ++ value.locals
  | .comprehension _ element domain filter =>
    let fromDomain := match domain with
      | .range _ start stop _ => start.locals ++ stop.locals
      | .collection _ _ source => source.locals
    fromDomain ++ element.locals ++ ((filter.map (·.locals)).getD #[])
  | .fold _ _ domain body =>
    let fromDomain := match domain with
      | .range _ start stop _ => start.locals ++ stop.locals
      | .collection _ _ source => source.locals
    fromDomain ++ body.locals
  | .block _ _ result => result.locals
  | .type written => fromType written
  | .number .. | .bytes .. | .bool .. | .error _ => #[]

/-- The references of a term, in the order of the text, those of its static arguments
included. -/
def Expr.references (expr : Expr) : Array Reference := expr.collect #[]

/-- The references of a type, in the order of the text. -/
def TypeTerm.references (type : TypeTerm) : Array Reference := type.collect #[]

/-- The parameter that a reference names alone: one step that is a static parameter. -/
def Reference.parameter? : Reference → Option ParameterRef
  | .reference _ #[.segment (.parameter parameter) _ _] => some parameter
  | _ => none

/-- The parameter that a reference starts with. -/
def Reference.firstParameter? : Reference → Option ParameterRef
  | .reference _ segments =>
    match (segments[0]? : Option Segment) with
    | some (.segment (.parameter parameter) _ _) => some parameter
    | _ => none

end Zkc.Frontend.Lowered
