module

public import Zkc.Frontend.Elab.Family

@[expose] public section

set_option autoImplicit false

/-!
# The elaboration of expressions

`elabExpr` types a lowered expression at an instance, against the type its context gives when
it gives one, and returns its typed node.

- A literal expression is checked as a whole against the type that its context gives: the
  expected type, or its sibling typed first (TY6).
- A local name is its binder at the type it has; a static name, a static parameter and a size
  stand for their numbers.
- A value is brought to an expected type by a conversion node: a widening, or a conversion that
  a fact must justify, which emission decides (TY5).
-/

namespace Zkc.Frontend.Elab

open Syntax
open Static

/-- The information of a node. -/
def info (span : Span) (type : ClosedType) : Typed.Info := { span, type }

/-- The number that a typed node stands for when it is a static natural or a numeral, through
the operands bound to keep the order of evaluation. -/
partial def staticOf? (expr : Typed.Expr) : ElabM (Option Nat) := do
  match expr with
  | .staticValue _ value _ => return some value
  | .literal _ (.nat value) | .literal _ (.index value) => return some value
  | .literal _ (.nominal [value]) => return some value
  | .local _ binder =>
    match (← get).operands[binder]? with
    | some bound => staticOf? bound
    | none => return none
  | _ => return none

/-! ## Sizes -/

/-- A literal expression (TY6): numbers under the arithmetic operators, and sequence literals of
them. -/
partial def isLiteralExpr : Lowered.Expr → Bool
  | .number .. => true
  | .operator _ .negate #[inner] => isLiteralExpr inner
  | .operator _ operator #[a, b] =>
    (operator == .add || operator == .subtract || operator == .multiply || operator == .divide ||
      operator == .remainder || operator == .power) && isLiteralExpr a && isLiteralExpr b
  | .list _ elements => !elements.isEmpty && elements.all isLiteralExpr
  | .repetition _ element _ => isLiteralExpr element
  | _ => false

/-- Whether an expression is written as a size: numerals and static naturals under the
operators of sizes and `log2( )` (TY2). A local name is a size when it is a static name, or, with
`indices`, the index of an iteration that may be typed on its own. -/
partial def sizeSyntax (expr : Lowered.Expr) (indices : Bool := true) : ElabM Bool := do
  match expr with
  | .number .. => return true
  | .operator _ operator #[a, b] =>
    if operator == .add || operator == .subtract || operator == .multiply ||
        operator == .divide || operator == .power then
      return (← sizeSyntax a indices) && (← sizeSyntax b indices)
    return false
  | .call _ (.reference _ segments) #[.positional _ argument] none =>
    if segments.any fun (.segment step _ _) => step == .sizeOperator then sizeSyntax argument indices
    else return false
  | .local _ binder =>
    let state ← get
    if indices && state.indices.contains binder then return true
    return ((state.locals[binder]?).bind (·.static?)).isSome
  | .reference (.reference _ segments) =>
    if segments.isEmpty then return false
    return !segments.any fun (.segment step _ _) => match step with
      | .alternative .. | .bareAlternative _ | .fixed _ => true
      | _ => false
  | _ => return false

/-- Runs `action`; a refusal or a wait leaves no refusal behind and gives nothing. A run-time
index in a static position still asks for the body to be typed per iteration, a budget that ran
out leaves the body not checked, and a defect goes on. -/
def speculate {α : Type} (action : ElabM α) : ElabM (Option α) := do
  let saved ← getThe Compile.State
  recover (some <$> action) (skipped := true) (waits := true) do
    modifyThe Compile.State fun state => { state with log := saved.log, stack := saved.stack }
    return none

/-- The value of an expression written as a size, when it evaluates to a natural. With
`inCondition`, an index typed as a run-time natural is no size. With `operand`, the expression
is an operand of a condition, where the index of an iteration typed on its own is no size
either. -/
def staticNat? (expr : Lowered.Expr) (inCondition : Bool := false) (operand : Bool := false) :
    ElabM (Option Nat) := do
  unless ← sizeSyntax expr do
    -- an index typed as a run-time natural, in a static position
    if !inCondition then
      if let .local _ binder := expr then
        if (← get).indices.contains binder then
          let name := (((← get).locals[binder]?).map (·.binder.name)).getD ""
          throw (.staticIndex name)
    return none
  -- the index of a loop is no size in a condition, also where its iteration is typed on its
  -- own; a static name computed from it is one (TY9)
  if operand && expr.locals.any (← get).iterationIndices.contains then return none
  let env ← staticEnv
  let env := if inCondition then { env with indices := {} } else env
  speculate (liftM (evalSize env expr : CompileM Nat))

/-- The value of an expression written as a size. One that cannot be evaluated is refused
(TY2); an index typed as a run-time natural asks for the body to be typed per iteration. -/
def staticSize (expr : Lowered.Expr) : ElabM Nat := do
  for binder in expr.locals do
    if (← get).indices.contains binder then
      let name := (((← get).locals[binder]?).map (·.binder.name)).getD ""
      throw (.staticIndex name)
  liftM (evalSize (← staticEnv) expr : CompileM Nat)

/-- The value of a static condition (TY9): comparisons of two sizes, and `not`, `and`, `or` of
static conditions. -/
partial def staticCondition? (condition : Lowered.Expr) : ElabM (Option Bool) := do
  match condition with
  | .operator _ .not #[inner] => return (← staticCondition? inner).map (!·)
  | .conditional _ .and a b _ =>
    let some x ← staticCondition? a | return none
    let some y ← staticCondition? b | return none
    return some (x && y)
  | .conditional _ .or a _ b =>
    let some x ← staticCondition? a | return none
    let some y ← staticCondition? b | return none
    return some (x || y)
  | .operator _ operator #[a, b] =>
    let compare : Option (Nat → Nat → Bool) := match operator with
      | .equal => some (· == ·) | .notEqual => some (· != ·) | .less => some (· < ·)
      | .lessEqual => some (· ≤ ·) | .greater => some (· > ·) | .greaterEqual => some (· ≥ ·)
      | _ => none
    let some compare := compare | return none
    let some x ← staticNat? a (inCondition := true) (operand := true) | return none
    let some y ← staticNat? b (inCondition := true) (operand := true) | return none
    return some (compare x y)
  | _ => return none

/-- A literal expression (TY6), a static natural standing for the number it evaluates to (TY2):
a size over static parameters, static names and natural members. -/
partial def isLiteral (expr : Lowered.Expr) : ElabM Bool := do
  if isLiteralExpr expr then return true
  match expr with
  | .operator _ .negate #[inner] => isLiteral inner
  | .operator _ operator #[a, b] =>
    if operator == .add || operator == .subtract || operator == .multiply || operator == .divide ||
        operator == .remainder || operator == .power then
      return (← isLiteral a) && (← isLiteral b)
    return false
  | .reference .. | .call .. | .local .. =>
    if !(← sizeSyntax expr (indices := false)) then return false
    return (← staticNat? expr (inCondition := true)).isSome
  | .list _ elements =>
    if elements.isEmpty then return false
    elements.allM isLiteral
  | .repetition _ element _ => isLiteral element
  | _ => return false

/-! ## Conversion -/

mutual
  /-- How a value of one type is brought to another (TY5): unchanged (`none`), widened, or
  converted by a fact. `place` and `quote` are where a refusal is made and what it quotes. -/
  partial def conversionTo (source target : ClosedType) (place : Span) (quote : Typed.Quote) :
      ElabM (Option Typed.Conversion) := do
    if typeEq source target then return none
    -- `[]` checks against every collection of size 0 and every unsized collection (TY6)
    if isEmptyCollection source then
      match target with
      | .seq _ (some 0) | .seq _ none => return some .empty
      | _ => pure ()
    match source, target with
    | .index _, .nat => return some .indexToNat
    | .index bound, .index wider =>
      if bound ≤ wider then return some .widenIndex
      return some .bounded
    | .nat, .index _ => return some .bounded
    | .seq element (some size), .seq other none =>
      if typeEq element other then return some .unsized
      let inner ← elementConversion element other place quote
      return some (.andThen (.elements inner) (.seq other (some size)) .unsized)
    | .seq element none, .seq other (some size) =>
      if typeEq element other then return some .sized
      let inner ← elementConversion element other place quote
      return some (.andThen .sized (.seq element (some size)) (.elements inner))
    | .seq element (some m), .seq other (some n) =>
      if m == n then return some (.elements (← elementConversion element other place quote))
      mismatch source target place quote ""
    | .seq element none, .seq other none =>
      return some (.elements (← elementConversion element other place quote))
    | .tuple components _, .tuple targets _ =>
      if components.size != targets.size then return ← mismatch source target place quote ""
      let mut inner := #[]
      for index in [0:components.size] do
        inner := inner.push (← conversionTo components[index]! targets[index]! place quote)
      return some (.components inner)
    | .nonzero field, other =>
      if typeEq field other then return some .fromNonzero
      mismatch source target place quote ""
    | other, .nonzero field =>
      unless typeEq other field do return ← mismatch source target place quote ""
      return some .nonzero
    | source, target =>
      -- a type member of a module parameter is opaque in a generic definition (SP12)
      if let some fresh := (match source, target with
          | .«opaque» .., _ => some source
          | _, .«opaque» .. => some target
          | _, _ => none) then
        let .«opaque» «module» _ _ _ := fresh | mismatch source target place quote ""
        let state ← getThe Compile.State
        let parameter : Option String := ((state.table.entries[«module»]?).bind (·.key.opaqueFor)).bind
          fun (entry : ParameterRef × Array String) =>
            ((state.program.scopes[entry.1.scope]?).bind (·.parameters[entry.1.index]?)).map (·.name.text)
        let interface : Option String := match state.table.content? «module» with
          | some (.«module» interfaces _) =>
            (interfaces[0]?).map fun (entry : DeclarationId × Array StaticValue) =>
              state.program.nameOf entry.1
          | _ => none
        refuseHere "SP12" place
          s!"`{← renderTypeE source}` is not `{← renderTypeE target}`: in a definition generic over `{parameter.getD "?"}` the type member is opaque; its values come from the members of `{interface.getD "?"}`"
      mismatch source target place quote ""

  /-- The conversion of the elements of a collection. -/
  partial def elementConversion (element target : ClosedType) (place : Span) (quote : Typed.Quote) :
      ElabM Typed.Conversion := do
    match ← conversionTo element target place quote with
    | some conversion => return conversion
    | none => throw (.defect "the elements of two collection types that differ are equal")

  /-- A type mismatch at a conversion. -/
  partial def mismatch {α : Type} (source target : ClosedType) (place : Span) (quote : Typed.Quote)
      (hint : String) : ElabM α := do
    let text ← match quote with
      | .span span => textOf span
      | .text text => pure text
    refuseHere "TY5" place
      s!"`{text}` is a `{← renderTypeE source}`; `{← renderTypeE target}` is expected{hint}"
end

/-- A typed node at a type: unchanged when the types are equal, otherwise converted (TY5). -/
def convertTo (expr : Typed.Expr) (target : ClosedType) (place : Span) (quote : Typed.Quote) :
    ElabM Typed.Expr := do
  match ← conversionTo expr.type target place quote with
  | none => return expr
  | some conversion => return .convert (info place target) conversion expr quote

/-! ## Expressions -/

/-- The attributes of a control statement that elaboration makes around one name it updates:
the name, at the type it was made with. -/
def carrying (binder : Typed.Binder) : Typed.Control :=
  { updates := #[binder.id], carried := #[binder.type] }

/-- A static natural as a value. -/
def staticNode (span : Span) (value : Nat) (source : Typed.StaticSource) : Typed.Expr :=
  .staticValue (info span .nat) value source

/-- A row of the vocabulary as a callee. -/
def rowCallee (request : Typing.RowRequest) : Typed.Callee :=
  .row { name := request.name, statics := request.statics.map fun
    | .type type => StaticValue.type type
    | .nat value => .natural value }

/-- An application of a row of the vocabulary. -/
def applyRowNode (span : Span) (type : ClosedType) (request : Typing.RowRequest)
    (arguments : Array Typed.Expr) : Typed.Expr :=
  .apply (info span type) (rowCallee request) arguments

/-- An application of an operation of the core. -/
def operationNode (span : Span) (type : ClosedType) (operation : Typed.CoreOperation)
    (arguments : Array Typed.Expr) : Typed.Expr :=
  .apply (info span type) (.operation operation) arguments

/-- Binds an operand so that it is evaluated where it stands, before what follows it: the
binder, and its use. -/
def operandBinder (expr : Typed.Expr) : ElabM (Typed.Binder × Typed.Expr) := do
  let binder ← freshBinder "%operand" expr.span expr.type .operand
  modify fun state => { state with operands := state.operands.insert binder.id expr }
  return (binder, .local (info expr.span expr.type) binder.id)

/-- A node over operands bound before it, in order. -/
def afterOperands (span : Span) (bound : Array (Typed.Binder × Typed.Expr)) (node : Typed.Expr) :
    Typed.Expr :=
  if bound.isEmpty then node
  else .block (info span node.type) (bound.map fun (binder, expr) => .bind expr.span binder expr {}) node

/-- The two operands of an operator, each bound in the order written when the node would
otherwise not evaluate them first and in that order: when it takes them exchanged, or when the
first is converted before the second is evaluated. -/
def sequenceOperands (span : Span) (x y : Typed.Expr) (bind : Bool)
    (build : Typed.Expr → Typed.Expr → ElabM Typed.Expr) : ElabM Typed.Expr := do
  if !bind then return ← build x y
  let (xBinder, xUse) ← operandBinder x
  let (yBinder, yUse) ← operandBinder y
  return afterOperands span #[(xBinder, x), (yBinder, y)] (← build xUse yUse)

/-- Whether a typed node is a conversion. -/
def isConverted : Typed.Expr → Bool
  | .convert .. => true
  | _ => false

/-- The family of operators of a type (NL6). -/
def family (type : ClosedType) : ElabM Family := liftM (familyOf type : CompileM Family)

/-- The type a literal sibling of an operand of this type takes: a natural for a natural, `F`
for a `nonzero<F>`, none beside the collection of no elements, which joins any collection
(TY6), and the type itself otherwise. -/
def sameSibling (type : ClosedType) : ElabM (Option ClosedType) :=
  return match type with
    | .nat | .index _ => none
    | .nonzero field => some field
    | other => if isEmptyCollection other then none else some other

/-- A `nonzero<F>` operand of an operation on `F`, widened. -/
def widenNonzero (expr : Typed.Expr) : Typed.Expr :=
  match expr.type with
  | .nonzero field => .convert (info expr.span field) .fromNonzero expr (.span expr.span)
  | _ => expr

/-- The record or the variant whose home functions give operators. -/
def isDeclared : ClosedType → Bool
  | .record _ | .«variant» _ => true
  | _ => false

/-- Why the signature of an instance is not evaluated here: what the instance itself waits for
(a constraint of its `where`, a form of a later layer), or the reason of the first of its types
that is not evaluated (a generated member, a specification-only parameter). -/
def signatureWait (inst : InstanceId) : CompileM String := do
  let state ← get
  let some entry := state.table.entries[inst]? | return "a signature that is not evaluated here"
  if let some (.waits reason) := state.table.content? inst then return reason
  let some lowered := (← getModules).lowered? entry.key.declaration
    | return "a signature that is not evaluated here"
  let types : Array Lowered.TypeTerm := match lowered.content with
    | .function head _ => head.parameters.map (·.type) ++ head.result.toArray
    | .unlowered names => names.filterMap fun
      | .type type => some type
      | _ => none
    | _ => #[]
  let found ← declaration entry.key.declaration
  let env := instanceEnv state.program found entry.key.arguments entry.key.specification
  for type in types do
    let waits ← recoverWith (do discard (evalType env type); pure none)
      (fun | .waiting reason => pure (some reason) | _ => pure none) (waits := true)
    if let some reason := waits then
      return s!"a type of the signature that is not evaluated here: {reason}"
  return "a signature that is not evaluated here"

/-- A written argument that needs an expected type to be typed (SP6 step 2): a literal
expression, `[]`, a bare alternative. -/
def needsExpected (expr : Lowered.Expr) : Bool :=
  isLiteralExpr expr || match expr with
    | .list _ elements => elements.isEmpty
    | .reference (.reference _ segments) | .call _ (.reference _ segments) .. =>
      segments.any fun (.segment step _ _) => (step matches .bareAlternative _)
    | _ => false

/-- Whether a typed node is a term as a message names one (TY4): a name that is not `mut`, a
field of one, a length, or arithmetic over such terms and static naturals. -/
partial def isTerm (expr : Typed.Expr) : ElabM Bool := do
  match expr with
  | .staticValue .. | .literal _ (.index _) => return true
  | .local _ binder =>
    match (← get).operands[binder]? with
    | some bound => isTerm bound
    | none => return ((← get).locals[binder]?).any fun entry => !entry.binder.mutable
  | .convert _ .indexToNat inner _ => isTerm inner
  | .apply _ (.operation operation) arguments =>
    match operation, arguments with
    | .natAdd, #[x, y] | .natSub, #[x, y] | .natMul, #[x, y] | .natDiv, #[x, y]
    | .natRem, #[x, y] | .natPow, #[x, y] => return (← isTerm x) && (← isTerm y)
    | .seqLength, #[xs] => isTerm xs
    | _, _ => return false
  | .project _ target _ (some _) => isTerm target
  | _ => return false


/-- An argument of a call: written, or a value typed already (an operand of an operator, the
receiver of a dot call), with the place and the quote of a refusal of its conversion. -/
inductive Arg where
  | written (expr : Lowered.Expr)
  | typed (expr : Typed.Expr) (place : Span) (quote : Typed.Quote)
  deriving Inhabited

def Arg.span : Arg → Span
  | .written expr => expr.span
  | .typed _ place _ => place

def Arg.quote : Arg → Typed.Quote
  | .written expr => .span expr.span
  | .typed _ _ quote => quote

/-- An argument after inference: typed, or left for its parameter's type. -/
inductive ArgState where
  | typed (expr : Typed.Expr)
  | deferred
  deriving Inhabited

/-- What a callee path names. -/
inductive CalleeOf where
  | declaration (steps : Array (DeclarationId × Option (Array Lowered.StaticArgument)))
      (scopes : Std.HashMap ScopeId (Array StaticValue))
  /-- A function member of a module instance defined in source. -/
  | member («module» : InstanceId) (definition : DeclarationId) (name : String)
      (args : Option (Array Lowered.StaticArgument))
  /-- A function member of a sort: a row of §7.4. -/
  | sortMember (type : ClosedType) (name : String)
  /-- A function member of a module bound to a row of the vocabulary. -/
  | moduleRow («module» : InstanceId) (row : String) (name : String)
      (args : Option (Array Lowered.StaticArgument))
  | alternative (steps : Array (DeclarationId × Option (Array Lowered.StaticArgument)))
      (scopes : Std.HashMap ScopeId (Array StaticValue)) («variant» : DeclarationId) (index : Nat)
  | bare (name : String)
  | fixed (function : FixedFunction)
  | sizeOperator
  deriving Inhabited

/-- The fields of a record instance. -/
def recordFields (inst : InstanceId) : ElabM (Array (String × ClosedType)) := do
  match (← getThe Compile.State).table.content? inst with
  | some (.record _ fields) => return fields
  | some (.waits reason) => waitFor reason
  | _ => waitFor "a record whose fields are not evaluated"

/-- The alternatives of a variant instance. -/
def variantAlternatives (inst : InstanceId) : ElabM (Array (String × Array ClosedType)) := do
  match (← getThe Compile.State).table.content? inst with
  | some (.«variant» alternatives) => return alternatives
  | some (.waits reason) => waitFor reason
  | _ => waitFor "a variant whose alternatives are not evaluated"

/-- The lowered form of a declaration. -/
def loweredOf (id : DeclarationId) : ElabM Lowered.Declaration := do
  let some lowered := (← getModules).lowered? id | throw .abandoned
  return lowered

/-- The parameters of a function or a relation that a call gives values to, with their types
as written, and the result type as written. -/
def signatureOf (id : DeclarationId) :
    ElabM (Array (String × Lowered.TypeTerm) × Option Lowered.TypeTerm) := do
  let found ← liftM (declaration id : CompileM Declaration)
  match found.node, (← loweredOf id).content with
  | .«def» _, .function head _ | .relation _, .function head _ =>
    return (head.parameters.map fun parameter => (parameter.binder.name, parameter.type), head.result)
  | _, _ => waitFor s!"a call of {Names.kindWord found.kind}"

/-- The parameters of a function member of an interface, with their types as written, and the
result type as written. -/
def memberSignatureOf (id : DeclarationId) :
    ElabM (Array (String × Lowered.TypeTerm) × Option Lowered.TypeTerm) := do
  let .function head _ := (← loweredOf id).content | throw .abandoned
  return (head.parameters.map fun parameter => (parameter.binder.name, parameter.type), head.result)

/-- Whether a parameter type mentions a parameter that inference has not solved. -/
def mentionsUnknown (problem : Static.Infer.Problem) (type : Lowered.TypeTerm) : Bool :=
  (Static.Infer.typeParameters type).any problem.isUnknown

/-- A type found twice for one parameter agrees when one of the two widens to the other: the
parameter takes their join, to which the arguments are converted (TY5). -/
def widenFound (problem : Static.Infer.Problem) (before : Nat) : Static.Infer.Problem := Id.run do
  let mut problem := problem
  let mut kept := problem.conflicts.extract 0 before
  for (reference, earlier, found) in problem.conflicts.extract before problem.conflicts.size do
    match earlier, found with
    | .type a, .type b =>
      match join a b with
      | some joined =>
        if typeEq joined a || typeEq joined b then
          problem := { problem with known := problem.known.insert reference (.type joined) }
        else kept := kept.push (reference, earlier, found)
      | none => kept := kept.push (reference, earlier, found)
    | _, _ => kept := kept.push (reference, earlier, found)
  return { problem with conflicts := kept }

/-- Whether a declaration is a specification function: a `spec def` or a relation (SX1). -/
def isSpecificationFunction (found : Declaration) : Bool :=
  match found.node with
  | .«def» node => (node.modifier matches some (.spec _))
  | .relation _ => true
  | _ => false

/-- The home module of a type: the namespace of the declaration of a record or a variant, or of
the first declaration that binds a type of the vocabulary (NL5, NL6). -/
def homeOf (type : ClosedType) : ElabM (Option (NamespaceId × String)) := do
  let state ← getThe Compile.State
  let program := state.program
  match type with
  | .record inst | .variant inst =>
    let some entry := state.table.entries[inst]? | return none
    let some declaration := program.declarations[entry.key.declaration]? | return none
    let owner := (program.namespaces[declaration.namespace]?).map (·.owner)
    return some (declaration.namespace, (owner.map program.nameOf).getD "")
  | .nominal row _ =>
    for declaration in program.declarations do
      if let .typeDecl (.type _ _ _ _ (.primitive primitive)) := declaration.node then
        if primitive.row.content == row then
          let owner := (program.namespaces[declaration.namespace]?).map (·.owner)
          return some (declaration.namespace, (owner.map program.nameOf).getD "")
    return none
  | _ => return none

/-- The function of a name in a namespace, when there is one. -/
def functionIn (ns : NamespaceId) (name : String) : ElabM (Option DeclarationId) := do
  let program := (← getThe Compile.State).program
  match (program.namespaces[ns]?).bind (·.names[name]?) with
  | some (.declaration id) =>
    if (program.declarations[id]?).any (·.kind == .function) then return some id
    return none
  | _ => return none

/-- Whether a declaration is visible from the body being elaborated (NL7): it is `pub`, or the
body is in its module. -/
def visibleHere (declaration : Declaration) : ElabM Bool := do
  if declaration.pub then return true
  let state ← getThe Compile.State
  let here := ((state.table.entries[(← getContext).instance]?).bind fun entry =>
    state.program.declarations[entry.key.declaration]?).map (·.namespace)
  return (here.map (state.program.within · declaration.namespace)).getD true

/-- The declaration of a record instance. -/
def recordDeclaration (inst : InstanceId) : ElabM (Option Declaration) := do
  let state ← getThe Compile.State
  return (state.table.entries[inst]?).bind fun entry => state.program.declarations[entry.key.declaration]?

/-- The interface of a module instance that declares a member, the member and its number, and
the interface's static arguments. -/
def interfaceMember (inst : InstanceId) (name : String) :
    ElabM (DeclarationId × DeclarationId × Declaration × Array StaticValue) := do
  let state ← getThe Compile.State
  let some (.«module» interfaces _) := state.table.content? inst
    | waitFor "a module whose members are not evaluated"
  for (interface, args) in interfaces do
    let some inner := (state.program.declarations[interface]?).bind (·.inner) | continue
    if let some (.declaration member) := (state.program.namespaces[inner]?).bind (·.names[name]?) then
      if let some found := state.program.declarations[member]? then
        return (interface, member, found, args)
  refuseHere "SP3" default s!"`{renderInstance state inst}` has no member `{name}`"

/-- The parameters of a function member of a module, from the interface that declares it. -/
def memberParameters (inst : InstanceId) (name : String) : ElabM (Array String) := do
  let (_, _, member, _) ← interfaceMember inst name
  match member.node with
  | .member (.defMember _ _ _ _ params _ _) => return params.map (·.name.text)
  | _ => throw .abandoned

/-- A static argument of deployed code reads no specification-only parameter: one is given only
in a specification argument (SP11). -/
def deployedStaticArguments (steps : Array (DeclarationId × Option (Array Lowered.StaticArgument))) :
    ElabM Unit := do
  if (← getContext).specification then return
  let program := (← getThe Compile.State).program
  for (_, args?) in steps do
    let some args := args? | continue
    for arg in args do
      let .term _ _ term := arg | continue
      for reference@(.reference span _) in term.references do
        let some reference := reference.firstParameter? | continue
        let some parameter := (program.scopes[reference.scope]?).bind (·.parameters[reference.index]?)
          | continue
        if parameter.spec then
          refuseHere "SP11" span
            s!"`{parameter.name.text}` is a specification-only static parameter; deployed code gives it only in a specification argument, `spec … = {parameter.name.text}`"

/-- Pairs the arguments of a call with the parameters: positional first, then named (FN6). -/
def pairArguments (name : String) (parameters : Array String) (arguments : Array Lowered.Argument)
    (witnesses : Option (Array Lowered.Argument)) (place : Span) : ElabM (Array Arg) := do
  if let some witnesses := witnesses then
    unless witnesses.isEmpty do
      refuseHere "SX3" place s!"`;` stands only in the arguments of a relation"
  let mut paired : Array (Option Arg) := parameters.map fun _ => none
  let mut position := 0
  for argument in arguments do
    match argument with
    | .positional span value =>
      if position ≥ parameters.size then
        refuseHere "FN6" span s!"`{name}` takes {parameters.size} arguments"
      paired := paired.set! position (some (.written value))
      position := position + 1
    | .named span argName value =>
      match parameters.findIdx? (· == argName.text) with
      | some index =>
        if paired[index]!.isSome then
          refuseHere "FN6" span s!"`{name}` is given `{argName.text}` twice"
        paired := paired.set! index (some (.written value))
      | none => refuseHere "FN6" span s!"`{name}` has no parameter `{argName.text}`"
    | .spec .. => pure ()
  let mut result := #[]
  for index in [0:parameters.size] do
    match paired[index]! with
    | some arg => result := result.push arg
    | none => refuseHere "FN6" place s!"`{name}` is not given `{parameters[index]!}`"
  return result

/-- Pairs the arguments of an application of a relation: the statement before `;`, the witness
after it, each side as many as the definition has (SX3). -/
def pairRelationArguments (name : String) (statement witness : Array String)
    (arguments : Array Lowered.Argument) (witnesses : Option (Array Lowered.Argument)) (place : Span) :
    ElabM (Array Arg) := do
  let given := witnesses.getD #[]
  let count (n : Nat) (word : String) := if n == 1 then s!"1 {word} argument" else s!"{n} {word} arguments"
  unless arguments.size == statement.size && given.size == witness.size do
    refuseHere "SX3" place
      s!"`{name}` takes {count statement.size "statement"} and {count witness.size "witness"}"
  let statementArgs ← pairArguments name statement arguments none place
  let witnessArgs ← pairArguments name witness given none place
  return statementArgs ++ witnessArgs

/-- The application over the arguments of a call, each converted to its target where it is
evaluated, at its place and with its quote. -/
def applyAfterArguments (args : Array Typed.Expr) (targets : Array (ClosedType × Span × Typed.Quote))
    (node : Array Typed.Expr → Typed.Expr) : ElabM Typed.Expr := do
  let places := targets.map (·.2.1.startByte)
  if places.toList.Pairwise (· ≤ ·) then
    return node (← (args.zip targets).mapM fun (use, (target, place, quote)) => convertTo use target place quote)
  -- named arguments written out of the order of the parameters are evaluated in the order
  -- written (HO4): each is converted and bound where it is written
  let order := (List.range args.size).toArray.qsort fun i j => places[i]! < places[j]!
  let mut uses := args
  let mut bound := #[]
  for index in order do
    let (target, place, quote) := targets[index]!
    let value ← convertTo args[index]! target place quote
    let (binder, use) ← operandBinder value
    bound := bound.push (binder, value)
    uses := uses.set! index use
  let applied := node uses
  return afterOperands applied.span bound applied

/-- What a loop, a comprehension or a fold ranges over, typed (TY10, TY11). -/
structure LoopDomain where
  /-- The index of a range, or the iteration number of a collection. -/
  index : Lowered.Binder
  /-- The bounds of a range. -/
  range : Option (Typed.Expr × Typed.Expr) := none
  /-- A collection, and the binder of its element. -/
  source : Option Typed.Expr := none
  item : Option Lowered.Binder := none
  element : ClosedType := default
  /-- The number of iterations, when it is static. -/
  count : Option Nat := none
  /-- The start of a range, when it is static. -/
  start : Option Nat := none
  span : Span
  deriving Inhabited

/-- What a fold of terms of a type is (TY11): an accumulator from a start, that each iteration
combines with its term, or the terms collected for the row of the form. -/
inductive FoldKind (m : Type → Type) where
  /-- `start` is elaborated after the terms. -/
  | carried (accumulation : Accumulation) (type : ClosedType) (start : m Typed.Expr)
  | collected (type : ClosedType)

/-- The place of `a..b`, from the start of `a` to the end of `b`. -/
def spanOver (first last : Span) : Span :=
  { first with stopLine := last.stopLine, stopColumn := last.stopColumn, stopByte := last.stopByte }

/-- The typed domain of a loop, with the binder of its item. -/
def LoopDomain.typed (domain : LoopDomain) (item : Option Typed.Binder) : Typed.Domain :=
  match domain.range, domain.source, item with
  | some (start, stop), _, _ => .range start stop domain.count
  | _, some source, some item => .collection source item domain.count
  | _, _, _ => .range default default none

/-- Whether statements begin by taking a binder apart: a pattern that is no name. -/
def takesApart (binder : LocalId) (statements : Array Lowered.Stmt) : Bool :=
  match (statements[0]? : Option Lowered.Stmt) with
  | some (.unpack _ _ _ _ (.local _ taken)) => taken == binder
  | _ => false

/-- The fields of a record converted in the order written and made in the order of the
declaration (TY13): when the two differ, each converted field is bound in the order written. -/
def constructInOrder (span : Span) (args : Array Typed.Expr)
    (targets : Array (ClosedType × Span × Typed.Quote)) (positions : Array Nat)
    (node : Array Typed.Expr → Typed.Expr) : ElabM Typed.Expr := do
  let converted ← (args.zip targets).mapM fun (use, (target, place, quote)) => convertTo use target place quote
  if positions == (List.range positions.size).toArray then return node (positions.map (converted[·]!))
  let mut bound := #[]
  let mut uses := #[]
  for value in converted do
    let (binder, use) ← operandBinder value
    bound := bound.push (binder, value)
    uses := uses.push use
  return afterOperands span bound (node (positions.map (uses[·]!)))

mutual
  /-- Types an expression. `expected` is the type its context gives, when one does; the result
  is converted by the caller. -/
  partial def elabExpr (expr : Lowered.Expr) (expected : Option ClosedType) : ElabM Typed.Expr := do
    if expected == some .rational then return ← elabRational expr
    if let some target := expected then
      unless isNatural target do
        if ← isLiteral expr then return ← elabLiteral expr target
    match expr with
    | .number span value => elabNumber span value expected
    | .bool span value => return .literal (info span .bool) (.bool value)
    | .bytes span data =>
      return .literal (info span (.seq (.index 256) (some data.length))) (.bytes data)
    | .tuple span #[] _ => return .construct (info span ClosedType.unit) .tuple #[]
    | .local span binder => localPath span binder
    | .reference reference => elabPath reference expected
    | .type type =>
      let span := Lowered.Expr.span (.type type)
      refuseHere "TY1" span s!"`{← textOf span}` is a type; a value is expected here"
    | .error _ => throw .abandoned
    | .tuple span components _ => elabTuple span components expected
    | .field span target name => elabField span target name
    | .position span target position => elabPosition span target position
    | .operator span .index #[target, index] => elabIndex span target index
    | .slice span target lower upper => elabSlice span target lower upper
    | .record span type fields => elabRecord span type fields expected
    | .recordUpdate span value fields => elabRecordUpdate span value fields
    | .list span elements => elabList span elements expected
    | .repetition span element count => elabRepetition span element count expected
    | .call span callee arguments witnesses => elabCall span callee arguments witnesses expected
    | .comprehension span element generator filter =>
      elabComprehension span element generator filter expected
    | .fold span form generator body => elabFold span form generator (some body) expected
    | .inner span a b => elabInner span a b
    | .conditional span .and a b _ => elabLogic span true a b
    | .conditional span .or a _ b => elabLogic span false a b
    | .conditional span .ifThenElse condition onTrue onFalse =>
      elabIf span condition onTrue onFalse expected
    | .block span statements result =>
      inSuite do
        let typed ← elabStmtsR statements
        let value ← elabExpr result expected
        return .block (info span value.type) typed value
    | .method span target name staticArguments arguments =>
      elabMethod span target name staticArguments arguments expected
    | .operator span .negate #[operand] => elabNeg span operand expected
    | .operator span .not #[operand] =>
      return operationNode span .bool .boolNot #[← elabBool operand]
    | .operator span operator #[a, b] =>
      match operator with
      | .add | .subtract | .concatenate => elabSum span operator a b expected
      | .multiply | .divide | .remainder => elabProduct span operator a b expected
      | .power => elabPower span a b expected
      | .equal | .notEqual | .less | .lessEqual | .greater | .greaterEqual => elabCompare span operator a b
      | _ => unexpected s!"the expression {constructorName expr}"
    | other => unexpected s!"the expression {constructorName other}"

  /-- The name of the form of a lowered expression, for what is not elaborated yet. -/
  partial def constructorName : Lowered.Expr → String
    | .number .. => "number" | .bytes .. => "bytes" | .bool .. => "bool" | .local .. => "local"
    | .reference .. => "reference" | .call .. => "call" | .operator _ operator _ => s!"operator {reprStr operator}"
    | .slice .. => "slice" | .field .. => "field" | .method .. => "method"
    | .position .. => "position" | .conditional _ form .. => s!"conditional {reprStr form}"
    | .tuple .. => "tuple" | .list .. => "list" | .repetition .. => "repetition"
    | .record .. => "record" | .recordUpdate .. => "record update"
    | .comprehension .. => "comprehension" | .fold .. => "fold" | .inner .. => "inner"
    | .block .. => "block" | .type .. => "type" | .error .. => "error"

  /-- An expression at a type: typed with it expected, and converted to it. -/
  partial def elabAt (expr : Lowered.Expr) (target : ClosedType) : ElabM Typed.Expr := do
    let typed ← elabExpr expr (some target)
    convertTo typed target expr.span (.span expr.span)

  partial def elabBool (expr : Lowered.Expr) : ElabM Typed.Expr := elabAt expr .bool

  /-- A natural expression. -/
  partial def elabNatural (expr : Lowered.Expr) : ElabM Typed.Expr := do
    let typed ← elabExpr expr (some .nat)
    unless isNatural typed.type do
      refuseHere "TY5" expr.span
        s!"`{← textOf expr.span}` is a `{← renderTypeE typed.type}`; a natural is expected here"
    return typed

  /-- A number at the type its context gives (TY6). -/
  partial def elabNumber (span : Span) (n : Nat) (target : Option ClosedType) : ElabM Typed.Expr := do
    -- a number does not check against a type member of a module parameter (TY6, NL6)
    if let some (.«opaque» ..) := target then return ← numberMismatch span n target.get!
    match target with
    | none | some .nat => return staticNode span n .number
    | some (.index bound) =>
      if n < bound then return .literal (info span (.index bound)) (.index n)
      refuseHere "TY8" span s!"`{n}` can be as large as {n}; `index<{bound}>` is expected"
    | some (.nonzero field) =>
      let characteristic := (← liftM (naturalMember? field "Characteristic" : CompileM _)).getD 0
      unless (← family field) matches .field do return ← numberMismatch span n (.nonzero field)
      if n == 0 then
        refuseHere "TY6" span s!"`0` is not a `nonzero` value of `{← renderTypeE field}`"
      unless n < characteristic do
        refuseHere "TY6" span s!"`{n}` is not below the characteristic of `{← renderTypeE field}`"
      return .literal (info span (.nonzero field)) (.nominal [n])
    | some type =>
      match ← family type with
      | .field | .ring =>
        let characteristic := (← liftM (naturalMember? type "Characteristic" : CompileM _)).getD 0
        unless n < characteristic do
          refuseHere "TY6" span s!"`{n}` is not below the characteristic of `{← renderTypeE type}`"
        return .literal (info span type) (.nominal [n])
      | .group =>
        unless n == 0 do
          refuseHere "TY6" span s!"the only literal of a group is `0`; `{n}` is not a `{← renderTypeE type}`"
        return .apply (info span type) (.row { name := "group.zero", statics := #[.type type] }) #[]
      | .points element size =>
        unless n == 0 do
          refuseHere "TY6" span s!"the only literal of a group is `0`; `{n}` is not a `{← renderTypeE type}`"
        let identity : Typed.Expr :=
          .apply (info span element) (.row { name := "group.zero", statics := #[.type element] }) #[]
        return .apply (info span (.seq element (some size))) (.operation .seqFill) #[identity]
      | _ => numberMismatch span n type

  partial def numberMismatch {α : Type} (span : Span) (n : Nat) (type : ClosedType) : ElabM α := do
    match type with
    | .«opaque» .. =>
      refuseHere "TY6" span
        s!"`{n}` does not check against `{← renderTypeE type}`: a type member has no literals; apply the function that its interface declares for constants"
    | _ =>
      refuseHere "TY6" span
        s!"`{n}` does not check against `{← renderTypeE type}`: a number checks against a ring, a group, a natural or `rational`"

  /-- A literal expression checked as a whole against a type that is not a natural (TY6). -/
  partial def elabLiteral (expr : Lowered.Expr) (target : ClosedType) : ElabM Typed.Expr := do
    match expr with
    | .number span value => elabNumber span value (some target)
    | .reference (.reference span _) | .call span .. | .local span _ =>
      -- a static natural is the number it evaluates to (TY2)
      match ← staticNat? expr (inCondition := true) with
      | some value => elabNumber span value (some target)
      | none => elabExpr expr (some target)
    | .operator span .negate #[operand] =>
      let typed ← elabLiteral operand target
      applyNeg span typed
    | .operator span operator #[a, b] =>
      if operator == .add || operator == .subtract || operator == .concatenate then
        let x ← elabLiteral a (literalBase target)
        let y ← elabLiteral b (literalBase target)
        return ← applySum span operator x y
      if operator == .multiply || operator == .divide || operator == .remainder then
        -- a product of units is a unit; a `%` is of naturals, refused below
        let base := literalBase target
        let left := if (target matches .nonzero _) && operator != .remainder then target else base
        let x ← elabLiteral a left
        let right := (← liftM (rightOperandType operator left : CompileM _)).getD base
        let y ← elabLiteral b right
        return ← applyProduct span operator x y
      if operator == .power then
        let x ← elabLiteral a target
        let y ← elabNatural b
        return ← applyPower span x y
      elabExpr expr (some target)
    | .list span elements => elabList span elements (some target)
    | .repetition span element count => elabRepetition span element count (some target)
    | other => elabExpr other (some target)

  /-- The two operands of an operator, and whether the second was typed first: a literal
  expression is typed after its sibling, at the type that `leftOf` or `rightOf` gives from the
  sibling's type (TY6). -/
  partial def operands (a b : Lowered.Expr) (expected : Option ClosedType)
      (rightOf : ClosedType → ElabM (Option ClosedType))
      (leftOf : ClosedType → ElabM (Option ClosedType)) : ElabM (Typed.Expr × Typed.Expr) := do
    -- a literal, and a form that needs an expected type (a bare alternative), takes its type from
    -- its sibling: typed after it, it is still evaluated first when it is written first
    let aLiteral := (← isLiteral a) || needsExpected a
    let bLiteral := (← isLiteral b) || needsExpected b
    if aLiteral && !bLiteral then
      let y ← elabExpr b none
      let x ← elabExpr a (← leftOf y.type)
      return (x, y)
    if bLiteral && !aLiteral then
      let x ← elabExpr a none
      let y ← elabExpr b (← rightOf x.type)
      return (x, y)
    let operandExpected := match expected with
      | some type => if isNatural type then none else some type
      | none => none
    let x ← elabExpr a (if aLiteral then operandExpected else none)
    let y ← elabExpr b (if bLiteral then operandExpected else none)
    return (x, y)

  partial def elabSum (span : Span) (operator : Operator) (a b : Lowered.Expr)
      (expected : Option ClosedType) : ElabM Typed.Expr := do
    let (x, y) ← operands a b expected sameSibling sameSibling
    applySum span operator x y

  /-- `+`, `-` and `++` on typed operands. -/
  partial def applySum (span : Span) (operator : Operator) (x y : Typed.Expr) :
      ElabM Typed.Expr := do
    let symbol := match operator with
      | .add => "+" | .subtract => "-" | _ => "++"
    let undefined {α : Type} : ElabM α := do
      refuseHere "NL6" span
        s!"`{symbol}` is not defined for `{← renderTypeE x.type}` and `{← renderTypeE y.type}`"
    -- a `spec type` has no operator (NL6)
    if x.type matches .specification _ || y.type matches .specification _ then undefined
    -- a member of the interface of a module parameter (NL6, SP12)
    if operator != .concatenate then
      let function := if operator == .add then "add" else "sub"
      if let some typed ← memberOperator? span x.type function
          #[.typed x span (.span x.span), .typed y span (.span y.span)] none then
        return typed
    match operator with
    | .concatenate =>
      let (.seq a m, .seq b n) := (x.type, y.type) | undefined
      -- `[]` takes the element type of the other operand (TY6)
      let element? := if isEmptyCollection x.type then some b
        else if isEmptyCollection y.type then some a
        else join a b
      let some element := element? | do
        refuseHere "TY5" span
          s!"the elements of `{← textOf span}` are a `{← renderTypeE a}` and a `{← renderTypeE b}`, which have no join"
      let size := match m, n with
        | some p, some q => some (p + q)
        | _, _ => none
      let left ← convertTo x (.seq element m) span (.span x.span)
      let right ← convertTo y (.seq element n) span (.span y.span)
      return operationNode span (.seq element size) .seqConcat #[left, right]
    | _ =>
    -- a sum of units is no unit
    let wx := widenNonzero x
    let name := if operator == .add then "add" else "sub"
    let sort ← family wx.type
    match sort with
    | .natural =>
      unless isNatural y.type do undefined
      return operationNode span .nat (if operator == .add then .natAdd else .natSub) #[x, y]
    | .declared =>
      return ← homeCall span wx.type name symbol
        #[.typed x span (.span x.span), .typed y span (.span y.span)] none
    | _ =>
      let some row := sort.sumRow? wx.type name | undefined
      let right ← convertTo (widenNonzero y) wx.type span (.span y.span)
      return applyRowNode span wx.type row #[wx, right]

  partial def elabProduct (span : Span) (operator : Operator) (a b : Lowered.Expr)
      (expected : Option ClosedType) : ElabM Typed.Expr := do
    let rightOf (type : ClosedType) : ElabM (Option ClosedType) :=
      liftM (rightOperandType operator type : CompileM _)
    -- the literal sibling of a unit in a product is a unit
    let leftOf (type : ClosedType) : ElabM (Option ClosedType) := do
      match type with
      | .nonzero _ => return some type
      | other => sameSibling other
    let (x, y) ← operands a b expected rightOf leftOf
    applyProduct span operator x y

  /-- `*`, `/` and `%` on typed operands. -/
  partial def applyProduct (span : Span) (operator : Operator) (x y : Typed.Expr) :
      ElabM Typed.Expr := do
    let symbol := match operator with
      | .multiply => "*" | .divide => "/" | _ => "%"
    let undefined {α : Type} : ElabM α := do
      refuseHere "NL6" span
        s!"`{symbol}` is not defined for `{← renderTypeE x.type}` and `{← renderTypeE y.type}`"
    -- a `spec type` has no operator (NL6)
    if x.type matches .specification _ || y.type matches .specification _ then undefined
    -- a member of the interface of a module parameter (NL6, SP12)
    let function := match operator with
      | .multiply => "mul" | .divide => "div" | _ => "rem"
    if let some typed ← memberOperator? span x.type function
        #[.typed x span (.span x.span), .typed y span (.span y.span)] none then
      return typed
    let sort ← family x.type
    if sort matches .natural then
      unless isNatural y.type do undefined
      let operation : Typed.CoreOperation := match operator with
        | .multiply => .natMul | .divide => .natDiv | _ => .natRem
      return operationNode span .nat operation #[x, y]
    if operator == .remainder then
      refuseHere "NL6" span s!"`%` is defined on naturals, not on `{← renderTypeE x.type}`"
    -- the scalar stands on the right of the point
    if (← family (literalBase x.type)).hasProduct && (← family y.type).isScaled then
      refuseHere "NL6" span
        s!"`{← textOf span}`: the scalar stands on the right of the point: write `{← textOf y.span} * {← textOf x.span}`"
    let type := x.type
    match sort with
    | .unit field =>
      if operator == .multiply then
        if let .nonzero _ := y.type then
          return applyRowNode span type (Typing.Rows.unitMul field) #[x, y]
      if operator == .divide then
        let divisor ← convertTo y (.nonzero field) span (.span y.span)
        let inverse := applyRowNode span (.nonzero field) (Typing.Rows.fieldInverse field) #[divisor]
        -- `1 / y` is the inverse
        if (← staticOf? x) == some 1 then return inverse
        return applyRowNode span (.nonzero field) (Typing.Rows.unitMul field) #[x, inverse]
      applyProduct span operator (widenNonzero x) y
    | .field =>
      match operator with
      | .multiply =>
        let right ← convertTo y type span (.span y.span)
        return applyRowNode span type (Typing.Rows.fieldBinary "mul" type) #[x, right]
      | _ =>
        let divisor ← convertTo y (.nonzero type) span (.span y.span)
        let inverse := applyRowNode span (.nonzero type) (Typing.Rows.fieldInverse type) #[divisor]
        let widened := applyRowNode span type (Typing.Rows.fieldFromNonzero type) #[inverse]
        return applyRowNode span type (Typing.Rows.fieldBinary "mul" type) #[x, widened]
    | .ring =>
      unless operator == .multiply do undefined
      let right ← convertTo y type span (.span y.span)
      return applyRowNode span type (Typing.Rows.ringMul type) #[x, right]
    | .group | .points .. =>
      unless operator == .multiply do undefined
      let some scalar ← liftM (scalarOf type : CompileM _) | undefined
      unless join y.type scalar == some scalar do undefined
      let right ← convertTo y scalar span (.span y.span)
      let some row := sort.scaleRow? type | undefined
      return applyRowNode span type row #[x, right]
    | .declared =>
      return ← homeCall span type function symbol
        #[.typed x span (.span x.span), .typed y span (.span y.span)] none
    | _ => undefined

  partial def elabPower (span : Span) (a b : Lowered.Expr) (expected : Option ClosedType) :
      ElabM Typed.Expr := do
    let x ← if ← isLiteral a then elabExpr a (match expected with
        | some type => if isNatural type then none else some type
        | none => none)
      else elabExpr a none
    if (← family (literalBase x.type)) matches .group then
      refuseHere "NL6" span
        s!"`^` is not defined for the group `{← renderTypeE x.type}`: group notation is additive; write `g * r`"
    let y ← elabNatural b
    applyPower span x y

  partial def applyPower (span : Span) (x y : Typed.Expr) : ElabM Typed.Expr := do
    -- a member of the interface of a module parameter (NL6, SP12)
    if let some typed ← memberOperator? span x.type "pow"
        #[.typed x span (.span x.span), .typed y span (.span y.span)] none then
      return typed
    -- a power of a unit is a unit
    let sort ← family x.type
    match sort with
    | .natural => return operationNode span .nat .natPow #[x, y]
    | .group =>
      refuseHere "NL6" span
        s!"`^` is not defined for the group `{← renderTypeE x.type}`: group notation is additive; write `g * r`"
    | .declared =>
      return ← homeCall span x.type "pow" "^"
        #[.typed x span (.span x.span), .typed y span (.span y.span)] none
    | _ =>
      let some row := sort.powerRow? x.type
        | refuseHere "NL6" span s!"`^` is not defined for `{← renderTypeE x.type}`"
      return applyRowNode span x.type row #[x, naturalView y]

  partial def elabNeg (span : Span) (operand : Lowered.Expr) (expected : Option ClosedType) :
      ElabM Typed.Expr := do
    let x ← elabExpr operand (if ← isLiteral operand then expected else none)
    applyNeg span x

  partial def applyNeg (span : Span) (x : Typed.Expr) : ElabM Typed.Expr := do
    -- a member of the interface of a module parameter (NL6, SP12)
    if let some typed ← memberOperator? span x.type "neg" #[.typed x span (.span x.span)] none then
      return typed
    -- the negation of a unit is a unit
    let sort ← family x.type
    if sort matches .declared then
      return ← homeCall span x.type "neg" "-" #[.typed x span (.span span)] none
    let some row := sort.negRow? x.type
      | refuseHere "NL6" span s!"prefix `-` is not defined for `{← renderTypeE x.type}`"
    return applyRowNode span x.type row #[x]

  /-- A comparison (TY12): `==` and `!=` on every data type with a join, the order on
  naturals. -/
  partial def elabCompare (span : Span) (operator : Operator) (a b : Lowered.Expr) :
      ElabM Typed.Expr := do
    let isZero (side : Lowered.Expr) : Bool := match side with
      | .number _ 0 => true
      | _ => false
    -- a field element against the literal `0`: the domain row
    if operator == .equal || operator == .notEqual then
      let other := if isZero b && !isZero a then some a else if isZero a && !isZero b then some b else none
      if let some other := other then
        let element := widenNonzero (← elabExpr other none)
        if (← family element.type) matches .field then
          let isNonzero := applyRowNode span .bool (Typing.Rows.fieldIsNonzero element.type) #[element]
          return if operator == .notEqual then isNonzero else operationNode span .bool .boolNot #[isNonzero]
        let zero ← elabExpr (if isZero b then b else a) (← sameSibling element.type)
        let (x, y) := if isZero b then (element, zero) else (zero, element)
        let equal ← equality span x y
        return if operator == .equal then equal else operationNode span .bool .boolNot #[equal]
    let (x, y) ← operands a b none sameSibling sameSibling
    -- a `rational` is compared with `<`, `<=`, `>`, `>=` and `==` (TY8)
    if x.type == .rational || y.type == .rational then
      return .apply (info span .bool) (.specification "a comparison of `rational`s")
        #[← toRational x a, ← toRational y b]
    match operator with
    | .equal | .notEqual =>
      let equal ← equality span x y
      if operator == .equal then return equal
      return operationNode span .bool .boolNot #[equal]
    | _ =>
      unless isNatural x.type && isNatural y.type do
        let leftIsField := (← family (literalBase x.type)) matches .field
        let rightIsField := (← family (literalBase y.type)) matches .field
        let ordered? := if leftIsField then some (literalBase x.type)
          else if rightIsField then some (literalBase y.type) else none
        if let some field := ordered? then
          refuseHere "TY12" span
            s!"field elements are not ordered; compare `{← renderTypeE field}::to_nat({← textOf x.span})`"
        refuseHere "TY12" span
          s!"`{← textOf span}` orders a `{← renderTypeE x.type}` and a `{← renderTypeE y.type}`: the order is defined on naturals"
      let exchanged := operator == .greater || operator == .lessEqual
      sequenceOperands span x y exchanged fun x y => do
        match operator with
        | .less => return operationNode span .bool .natLess #[x, y]
        | .greaterEqual =>
          return operationNode span .bool .boolNot #[operationNode span .bool .natLess #[x, y]]
        | _ =>
          -- `a > b` is `b < a`, and `a <= b` is `not (b < a)`, the operands evaluated in the order
          -- written
          let less := operationNode span .bool .natLess #[y, x]
          return if operator == .greater then less else operationNode span .bool .boolNot #[less]

  /-- A natural as a `nat`: an `index<s>` is viewed through `fin.to_nat`. -/
  partial def naturalView (expr : Typed.Expr) : Typed.Expr :=
    match expr.type with
    | .index _ => .convert (info expr.span .nat) .indexToNat expr (.span expr.span)
    | _ => expr

  /-- `==` on two typed values of types with a join (TY12). -/
  partial def equality (span : Span) (x y : Typed.Expr) : ElabM Typed.Expr := do
    -- a member of the interface of a module parameter (NL6, SP12)
    if let some typed ← memberOperator? span x.type "equal"
        #[.typed x span (.span x.span), .typed y span (.span y.span)] (some .bool) then
      return typed
    if isNatural x.type && isNatural y.type then
      return operationNode span .bool .natEqual #[x, y]
    if let (.seq _ (some m), .seq _ (some n)) := (x.type, y.type) then
      if m != n then
        refuseHere "TY12" span s!"`{← textOf span}` compares collections of {m} and {n} elements"
    let some joined := join x.type y.type
      | refuseHere "TY5" span
          s!"`{← textOf span}`: `{← renderTypeE x.type}` and `{← renderTypeE y.type}` have no join"
    equalValues span joined (← convertTo x joined span (.span x.span)) (← convertTo y joined span (.span y.span))

  /-- Equality of two values of one type: the operation or the row of the type, the home
  function `equal`, or component by component (TY12). -/
  partial def equalValues (span : Span) (type : ClosedType) (x y : Typed.Expr) (path : String := "") :
      ElabM Typed.Expr := do
    -- a member of the interface of a module parameter (NL6, SP12)
    if let some typed ← memberOperator? span type "equal"
        #[.typed x span (.span span), .typed y span (.span span)] (some .bool) path then
      return typed
    -- each value evaluated once, when it is taken apart
    let componentwise (compare : Typed.Expr → Typed.Expr → ElabM Typed.Expr) : ElabM Typed.Expr := do
      let (xBinder, xUse) ← operandBinder x
      let (yBinder, yUse) ← operandBinder y
      return afterOperands span #[(xBinder, x), (yBinder, y)] (← compare xUse yUse)
    let chain (parts : Array (Typed.Expr × Typed.Expr × ClosedType)) : ElabM Typed.Expr := do
      let mut result : Typed.Expr := .literal (info span .bool) (.bool true)
      for index in [0:parts.size] do
        let (a, b, component) := parts[index]!
        result := operationNode span .bool .boolAnd #[result, ← equalValues span component a b s!"{path}.{index}"]
      return result
    let home : ElabM (Option Typed.Expr) := do
      let some (home, _) ← homeOf type | return none
      let some _ ← functionIn home "equal" | return none
      return some (← homeCall span type "equal" "==" #[.typed x span (.span span), .typed y span (.span span)] (some .bool))
    match type with
    | .nat | .index _ => return operationNode span .bool .natEqual #[x, y]
    | .bool => return operationNode span .bool .boolEqual #[x, y]
    -- two values of a `spec type` in a specification: a proposition of the formal library
    | .specification _ =>
      return .apply (info span .bool) (.specification "the equality of values of a `spec type`") #[x, y]
    | .nonzero field =>
      return applyRowNode span .bool (Typing.Rows.fieldEqual field) #[widenNonzero x, widenNonzero y]
    | .tuple components _ =>
      componentwise fun x y => chain ((List.range components.size).toArray.map fun index =>
        (.project (info span components[index]!) x index none,
         .project (info span components[index]!) y index none, components[index]!))
    | .record inst =>
      if let some call ← home then return call
      if isLinear (← getThe Compile.State) type then
        refuseHere "TY12" span s!"`{← textOf span}` compares linear values"
      let fields ← recordFields inst
      componentwise fun x y => chain ((List.range fields.size).toArray.map fun index =>
        (.project (info span fields[index]!.2) x index none,
         .project (info span fields[index]!.2) y index none, fields[index]!.2))
    | .«variant» inst =>
      if let some call ← home then return call
      -- the same alternative on both sides, with equal payloads, part by part
      let alternatives ← variantAlternatives inst
      componentwise fun x y => do
        let result ← freshBinder "%equal" span .bool (.accumulator .equality) (mutable := true)
        let control : Typed.Control := carrying result
        let mut outer := #[]
        for index in [0:alternatives.size] do
          let payload := alternatives[index]!.2
          let lefts ← payload.mapM fun type => freshBinder "%payload" span type .operand
          let rights ← payload.mapM fun type => freshBinder "%payload" span type .operand
          let mut equal : Typed.Expr := .literal (info span .bool) (.bool true)
          for k in [0:payload.size] do
            let part ← equalValues span payload[k]! (.local (info span payload[k]!) lefts[k]!.id)
              (.local (info span payload[k]!) rights[k]!.id) s!"{path}:{index}.{k}"
            equal := operationNode span .bool .boolAnd #[equal, part]
          let others := (List.range alternatives.size).toArray.filter (· != index)
          let mut inner := #[Typed.Case.case span #[index] (rights.map some) #[.update span result.id equal {}]]
          unless others.isEmpty do inner := inner.push (.case span others #[] #[])
          outer := outer.push (Typed.Case.case span #[index] (lefts.map some)
            #[.match span y none inst inner control])
        return .block (info span .bool)
          #[.bind span result (.literal (info span .bool) (.bool false)) {}, .match span x none inst outer control]
          (.local (info span .bool) result.id)
    | .seq element size =>
      if (← family element).isElement then
        return applyRowNode span .bool (Typing.Rows.seqEqual element size) #[x, y]
      -- element by element: of the same length, and equal at each index of the first
      componentwise fun x y => do
        let index ← madeBinder "%index" span .written
        let result ← freshBinder "%equal" span .bool (.accumulator .equality) (mutable := true)
        let use : Typed.Expr := .local (info span .bool) result.id
        let lengthOf (xs : Typed.Expr) : Typed.Expr := operationNode span .nat .seqLength #[xs]
        let typedIndex ← bindLocal index .nat
        let elementAt (xs : Typed.Expr) : Typed.Expr := operationNode span element .seqAt #[xs, .local (info span .nat) index.id]
        let control : Typed.Control := carrying result
        let (start, count) : Typed.Expr × Option Nat := match size with
          | some n => (staticNode span n .number, some n)
          | none => (lengthOf x, none)
        let body ← match size with
          | some _ => pure #[Typed.Stmt.update span result.id
              (operationNode span .bool .boolAnd #[use, ← equalValues span element (elementAt x) (elementAt y) s!"{path}[]"]) {}]
          | none => pure #[Typed.Stmt.«if» span (operationNode span .bool .natLess #[.local (info span .nat) index.id, lengthOf y])
              #[.update span result.id (operationNode span .bool .boolAnd #[use, ← equalValues span element (elementAt x) (elementAt y) s!"{path}[]"]) {}]
              #[.update span result.id (.literal (info span .bool) (.bool false)) {}] control]
        let loop : Typed.Loop := .loop typedIndex (.range (staticNode span 0 .number) start count) #[] (.uniform body #[])
        let (sameBinder, same) ← operandBinder (operationNode span .bool .natEqual #[lengthOf x, lengthOf y])
        let statements : Array Typed.Stmt := match size with
          | some _ => #[.bind span result (.literal (info span .bool) (.bool true)) {}, .for span loop control]
          | none => #[.bind span sameBinder (operationNode span .bool .natEqual #[lengthOf x, lengthOf y]) {},
              .bind span result (.literal (info span .bool) (.bool true)) {}, .for span loop control]
        let value := match size with
          | some _ => use
          | none => operationNode span .bool .boolAnd #[same, use]
        return .block (info span .bool) statements value
    | other =>
      let some row := (← family other).equalRow? other
        | refuseHere "TY12" span s!"`==` is not defined for `{← renderTypeE other}`"
      return applyRowNode span .bool row #[x, y]

  /-- What a callee path names, step by step. -/
  partial def calleeOf (callee : Lowered.Reference) : ElabM CalleeOf := do
    let env ← staticEnv
    let .reference span segments := callee
    let some (.segment lastStep lastArgs _) := segments.back? | throw .abandoned
    match lastStep with
    | .fixed function => return .fixed function
    | .sizeOperator => return .sizeOperator
    | .bareAlternative name => return .bare name
    | .generated name => waitFor s!"the generated member `{name}` (§8)"
    | _ => pure ()
    let text ← textOf span
    let prefixThing ← if segments.size == 1 then pure (Thing.declarations #[] {})
      else liftM (evalSegments env segments.pop span : CompileM Thing)
    match lastStep with
    | .declaration id =>
      let found ← liftM (declaration id : CompileM Declaration)
      if found.kind == .functionDefinition then
        -- a member definition named through its module
        match ← liftM (thingValue env prefixThing (some .«module») span (pure text) : CompileM StaticValue) with
        | .«module» inst => return .member inst id ((found.name.map (·.text)).getD "") lastArgs
        | _ => refuseHere "GR5" span s!"`{text}` names no function"
      match prefixThing with
      | .declarations previous scopes => return .declaration (previous.push (id, lastArgs)) scopes
      | _ => refuseHere "GR5" span s!"`{text}` is reached through a value"
    | .alternative «variant» index =>
      match prefixThing with
      | .declarations previous scopes => return .alternative previous scopes «variant» index
      | _ => refuseHere "GR5" span s!"`{text}` is reached through a value"
    | .member name _ =>
      let value ← match prefixThing with
        | .value value => pure value
        | .declarations previous _ =>
          if previous.isEmpty then throw .abandoned
          liftM (thingValue env prefixThing none span (pure text) : CompileM StaticValue)
        | _ => refuseHere "GR5" span s!"`{text}` names no function"
      match value with
      | .«module» inst =>
        let members ← match (← getThe Compile.State).table.content? inst with
          | some (.«module» _ members) => pure members
          | _ => waitFor "a member of a module whose members are not evaluated"
        let found : Option MemberValue := (members.find? (·.1 == name)).map (·.2)
        match found with
        | some (.definition id) => return .member inst id name lastArgs
        | some (.row row) => return .moduleRow inst row name lastArgs
        | _ => refuseHere "SP3" span s!"`{text}` is no function"
      | .type type => return .sortMember type name
      | .natural _ => refuseHere "SP3" span s!"`{text}` is no function"
    | _ => refuseHere "TY1" span s!"`{text}` is no function"

  /-- A call. -/
  partial def elabCall (span : Span) (callee : Lowered.Reference) (arguments : Array Lowered.Argument)
      (witnesses : Option (Array Lowered.Argument)) (expected : Option ClosedType) : ElabM Typed.Expr := do
    let written := arguments.map fun
      | .positional _ value | .named _ _ value | .spec _ _ value => Arg.written value
    match ← calleeOf callee with
    | .fixed function => elabFixed span function arguments expected
    | .sizeOperator =>
      match ← staticNat? (.call span callee arguments witnesses) with
      | some value => return staticNode span value (.declared (← textOf span))
      | none => refuseHere "TY2" span s!"`log2` stands in a size"
    | .bare name => elabBare span name written expected
    | .alternative steps scopes «variant» index => elabAlternative span steps scopes «variant» index written expected
    | .declaration steps scopes =>
      let some (id, _) := steps.back? | throw .abandoned
      let env ← staticEnv
      deployedStaticArguments steps
      let assigned ← liftM (assignArguments env steps scopes span : CompileM _)
      let (parameters, _) ← signatureOf id
      let name ← liftM (nameOf id : CompileM String)
      let paired ← match (← liftM (declaration id : CompileM Declaration)).node with
        | .relation node =>
          pairRelationArguments name (node.statement.map (·.name.text))
            ((node.witness.getD #[]).map (·.name.text)) arguments witnesses span
        | _ => pairArguments name (parameters.map (·.1)) arguments witnesses span
      callDeclaration id assigned paired expected span
    | .member inst definition name staticArgs =>
      let parameters ← memberParameters inst name
      let paired ← pairArguments name parameters arguments witnesses span
      callMember inst definition name staticArgs paired expected span
    | .sortMember type name =>
      let (parameters, _) ← sortSignature type name span
      let paired ← pairArguments name (parameters.map (·.1)) arguments witnesses span
      callSortMember type name paired span
    | .moduleRow inst row name staticArgs =>
      let parameters ← memberParameters inst name
      let paired ← pairArguments name parameters arguments witnesses span
      callModuleRow inst row name staticArgs paired span

  /-- `length(t)` of a collection. -/
  partial def lengthNode (span : Span) (xs : Typed.Expr) : ElabM Typed.Expr := do
    let .seq _ _ := xs.type | waitFor "the length of a value that is no collection"
    return operationNode span .nat .seqLength #[xs]

  /-- A call of a declaration with its arguments paired with its parameters. -/
  partial def callDeclaration (id : DeclarationId) (assigned : StaticEnvironment) (args : Array Arg)
      (expected : Option ClosedType) (place : Span) : ElabM Typed.Expr := do
    let found ← liftM (declaration id : CompileM Declaration)
    let name := (← getThe Compile.State).program.nameOf id
    -- a specification function is called only from specifications (SX2)
    if isSpecificationFunction found && !(← getContext).specification then
      refuseHere "SX2" place s!"`{name}` is a specification function; deployed code cannot call it"
    -- `length` is the operation the core owns on any collection
    if let .«def» node := found.node then
      if let .primitive primitive := node.binding then
        if primitive.row.content == "seq.length" then
          let some arg := args[0]? | throw .abandoned
          let xs ← match arg with
            | .written expr => elabExpr expr none
            | .typed value _ _ => pure value
          unless xs.type matches .seq .. do
            let text ← match arg.quote with
              | .span span => textOf span
              | .text text => pure text
            refuseHere "TY5" arg.span s!"`{text}` is a `{← renderTypeE xs.type}`; `length` takes a collection"
          return ← lengthNode place xs
    else if found.kind != .relation then
      unless found.kind == .function do
        refuseHere "FN1" place s!"`{name}` is {Names.kindWord found.kind}: an application stands only in a protocol body; a `def` runs inside one role"
    let (parameters, result) ← signatureOf id
    let (values, states) ← inferArguments id assigned found.file parameters result args expected place
    let description ← liftM (describeInstance id values : CompileM String)
    let inst ← liftM (instantiate id values { description, span := place } : CompileM InstanceId)
    let (parameterTypes, resultType) ← match (← getThe Compile.State).table.content? inst with
      | some (.signature parameterTypes (some resultType)) =>
        if parameterTypes.all (·.2.isSome) then
          pure (parameterTypes.map fun (_, type) => type.getD default, resultType)
        else waitFor (← liftM (signatureWait inst : CompileM String))
      | _ => waitFor (← liftM (signatureWait inst : CompileM String))
    let typed ← finishArguments args states parameterTypes
    let node ← applyAfterArguments typed (targetsOf args parameterTypes) fun operands =>
      .apply (info place resultType) (.instance inst) operands
    reachCallee inst place
    return node

  /-- The targets of the conversions of arguments. -/
  partial def targetsOf (args : Array Arg) (types : Array ClosedType) :
      Array (ClosedType × Span × Typed.Quote) :=
    (args.zip types).map fun (arg, type) => (type, arg.span, arg.quote)

  /-- The body of a callee, typed before its result is used: a body that waits or is not checked
to the end makes the caller wait or not checked; a refused body abandons the caller. -/
  partial def reachCallee (inst : InstanceId) (place : Span) : ElabM Unit := do
    liftM ((← getContext).typeBody inst place)
    match (← getThe Compile.State).results.body? inst with
    | some (.row _) | some (.done _) => pure ()
    | some (.waiting reason) => waitFor reason
    | some (.exhausted exhaustion) => throw (.exhausted exhaustion)
    | _ => throw .abandoned

  /-- SP6 over written parameter types: the values of the callee's parameters, and the arguments
  typed so far (`deferred` for those that wait for their parameter's type). -/
  partial def inferArguments (callee : DeclarationId) (assigned : StaticEnvironment) (file : FileId)
      (parameters : Array (String × Lowered.TypeTerm)) (result : Option Lowered.TypeTerm) (args : Array Arg)
      (expected : Option ClosedType) (place : Span) (self? : Option InstanceId := none) :
      ElabM (Array StaticValue × Array ArgState) := do
    let state ← getThe Compile.State
    let found ← liftM (declaration callee : CompileM Declaration)
    let mut problem ← liftM (Static.Infer.startProblem callee assigned : CompileM Static.Infer.Problem)
    problem := { problem with self? }
    let context : Static.Infer.Context := .context file []
    let mut typed : Array ArgState := #[]
    for ((_, type), arg) in parameters.zip args do
      match arg with
      | .typed value _ quote =>
        let before := problem.conflicts.size
        problem ← liftM (Static.Infer.matchType problem context type value.type : CompileM _)
        problem := widenFound problem before
        if problem.conflicts.size > before then conflict arg.span quote value.type
        typed := typed.push (.typed value)
      | .written expr =>
        if needsExpected expr then
          -- `[]` is a collection of no elements of any type (TY6): against `[T; s]` it gives the
          -- size 0 and nothing of the element
          if let .list _ elements := expr then
            if let .sequence _ _ (some size) := type then
              if elements.isEmpty then
                problem ← liftM (Static.Infer.matchTerm problem context size (.natural 0) : CompileM _)
          if mentionsUnknown problem type then
            typed := typed.push .deferred
          else
            let target ← liftM (evalType { file, values := problem.known } type : CompileM ClosedType)
            typed := typed.push (.typed (← elabExpr expr (some target)))
        else
          let value ← elabExpr expr none
          let before := problem.conflicts.size
          problem ← liftM (Static.Infer.matchType problem context type value.type : CompileM _)
          problem := widenFound problem before
          if problem.conflicts.size > before then conflict expr.span (.span expr.span) value.type
          typed := typed.push (.typed value)
    problem ← liftM (Static.Infer.retry problem : CompileM _)
    if !problem.remaining.isEmpty then
      if let (some resultType, some expectedType) := (result, expected) then
        problem ← liftM (Static.Infer.matchType problem context resultType expectedType : CompileM _)
        problem ← liftM (Static.Infer.retry problem : CompileM _)
    let known ← liftM (Static.Infer.finish problem place : CompileM StaticEnvironment)
    let values := (deployedParameters state.program found).map fun (reference, _) =>
      known.getD reference default
    return (values, typed)

  /-- A value found twice that disagrees, at an argument (SP6 step 7). -/
  partial def conflict {α : Type} (span : Span) (quote : Typed.Quote) (type : ClosedType) : ElabM α := do
    let text ← match quote with
      | .span place => textOf place
      | .text text => pure text
    refuseHere "TY5" span
      s!"`{text}` is a `{← renderTypeE type}`, which disagrees with the static arguments the other arguments give"

  /-- The arguments after inference at their parameters' types: those left for their type are
  typed now. -/
  partial def finishArguments (args : Array Arg) (states : Array ArgState)
      (targets : Array ClosedType) : ElabM (Array Typed.Expr) := do
    let mut typed : Array Typed.Expr := #[]
    for index in [0:args.size] do
      let target := targets[index]!
      match states[index]!, args[index]! with
      | .typed value, _ => typed := typed.push value
      | .deferred, .written expr => typed := typed.push (← elabExpr expr (some target))
      | .deferred, .typed value _ _ => typed := typed.push value
    return typed

  /-- An argument at a type, converted where it stands. -/
  partial def argumentAt (arg : Arg) (type : ClosedType) : ElabM Typed.Expr := do
    match arg with
    | .written expr => elabAt expr type
    | .typed expr place quote => convertTo expr type place quote

  /-- The types of a function member of a module at the module: the interface's member read with
  `Self` the module (SP8). -/
  partial def memberSignature (inst : InstanceId) (name : String) (own : Array StaticValue := #[]) :
      ElabM (Array ClosedType × ClosedType) := do
    let (interface, memberId, member, args) ← interfaceMember inst name
    let program := (← getThe Compile.State).program
    let interfaceDeclaration ← liftM (declaration interface : CompileM Declaration)
    let (parameters, result) ← memberSignatureOf memberId
    let base : Env := { instanceEnv program interfaceDeclaration args with
      file := member.file, self? := some (.«module» inst) }
    let ownValues := ((ownParameters program member).zip own).foldl (init := base.values)
      fun map (reference, value) => map.insert reference value
    let env : Env := { base with values := ownValues }
    let types ← parameters.mapM fun (_, type) => liftM (evalType env type : CompileM ClosedType)
    let resultType ← match result with
      | some type => liftM (evalType env type : CompileM ClosedType)
      | none => pure ClosedType.unit
    return (types, resultType)

  /-- An operator, a form or a dot call that is a member of the interface of a module parameter
  (NL6, SP12): in the opaque elaboration, on a value of a type member of the parameter, recorded
  by its place; at the instance, at the places the opaque elaboration recorded. -/
  partial def memberOperator? (span : Span) (type : ClosedType) (function : String) (args : Array Arg)
      (expected : Option ClosedType) (path : String := "") : ElabM (Option Typed.Expr) := do
    let key := resolvedPlace span (function ++ path)
    if let some reference := (← getContext).resolutions[key]? then
      let some (.«module» inst) := (← getContext).env.values[reference]? | throw .abandoned
      return some (← callModuleMember inst function args expected span)
    let .«opaque» «module» _ _ sorts := type | return none
    if let some sort := sortOfFunction function then
      if sorts.contains sort then return none
    -- `*` on a type of sort `Group` is its scaling by a scalar, a row of the sort (§7.4): it
    -- is no member of the interface either
    if function == "mul" && sorts.contains "Group" then return none
    let state ← getThe Compile.State
    let some (reference, _) := (state.table.entries[«module»]?).bind (·.key.opaqueFor) | return none
    let some (.«module» interfaces _) := state.table.content? «module» | return none
    let program := state.program
    let declared := interfaces.any fun (interface, _) =>
      (((program.declarations[interface]?).bind (·.inner)).bind fun inner =>
        (program.namespaces[inner]?).bind (·.names[function]?)).any fun
          | .declaration id => (program.declarations[id]?).any (·.kind == .functionMember)
          | _ => false
    unless declared do
      let interface := ((interfaces[0]?).map fun (id, _) => program.nameOf id).getD "?"
      let parameter := ((program.scopes[reference.scope]?).bind (·.parameters[reference.index]?)).map
        (·.name.text)
      let typeText ← renderTypeE type
      if function == "equal" then
        refuseHere "SP12" span
          s!"`==` is not defined for `{typeText}` in a definition generic over `{parameter.getD "?"}: {interface}`: `{interface}` declares no `equal` for its type member"
      refuseHere "NL6" span
        s!"`{interface}` declares no `{function}`: an operator on its type member `{typeText}` is a member of the interface"
    modify fun builder => { builder with resolved := builder.resolved.push (key, reference) }
    return some (← callModuleMember «module» function args expected span)

  /-- A call of the function member `name` of a module instance, in source or bound to a row. -/
  partial def callModuleMember (inst : InstanceId) (name : String) (args : Array Arg)
      (expected : Option ClosedType) (place : Span) : ElabM Typed.Expr := do
    match (← getThe Compile.State).table.content? inst with
    | some (.«module» _ members) =>
      match (members.find? (·.1 == name)).map (·.2) with
      | some (MemberValue.definition id) => callMember inst id name none args expected place
      | some (MemberValue.row row) => callModuleRow inst row name none args place
      | _ => refuseHere "SP3" place s!"`{renderInstance (← getThe Compile.State) inst}` has no function `{name}`"
    | _ => waitFor "a module whose members are not evaluated"

  /-- A call of a function member of a module defined in source. -/
  partial def callMember (inst : InstanceId) (definition : DeclarationId) (name : String)
      (staticArgs : Option (Array Lowered.StaticArgument)) (args : Array Arg)
      (expected : Option ClosedType) (place : Span) : ElabM Typed.Expr := do
    -- a member that its interface declares `spec` is called only from specifications (SX2)
    let (interface, memberId, member, interfaceArgs) ← interfaceMember inst name
    if let .member (.defMember _ (some (.spec _)) ..) := member.node then
      unless (← getContext).specification do
        refuseHere "SX2" place s!"`{name}` is a specification function; deployed code cannot call it"
    let state ← getThe Compile.State
    let program := state.program
    let some entry := state.table.entries[inst]? | throw .abandoned
    let own := ownParameters program member
    -- the member's own static parameters: written, or inferred from the arguments (SP6, SP8)
    let (ownValues, states) ← if own.isEmpty then pure (#[], none) else do
      let interfaceDeclaration ← liftM (declaration interface : CompileM Declaration)
      let mut assigned : StaticEnvironment := ((deployedParameters program interfaceDeclaration).zip
        interfaceArgs).foldl (init := {}) fun map ((reference, _), value) => map.insert reference value
      let written := staticArgs.getD #[]
      let env ← staticEnv
      for index in [0:min own.size written.size] do
        if let some (.term _ _ term) := written[index]? then
          let cls ← liftM (parameterClass own[index]! : CompileM Class)
          assigned := assigned.insert own[index]! (← liftM (evalTerm env term cls : CompileM StaticValue))
      let (parameters, result) ← memberSignatureOf memberId
      let (values, states) ← inferArguments memberId assigned member.file parameters result args
        expected place (some inst)
      let interfaceCount := (deployedParameters program interfaceDeclaration).size
      pure (values.extract interfaceCount values.size, some states)
    let (types, resultType) ← memberSignature inst name ownValues
    let values := entry.key.arguments ++ ownValues
    let ownText := ((own.zip ownValues).map fun (reference, value) =>
      let parameterName := ((program.scopes[reference.scope]?).bind (·.parameters[reference.index]?)).map
        (·.name.text)
      s!"{parameterName.getD "?"} = {renderValue state value}").toList
    let description := if ownText.isEmpty then name else s!"{name}<{", ".intercalate ownText}>"
    let callee ← liftM (instantiate definition values { description, span := place } : CompileM InstanceId)
    let node ← match states with
      | some states =>
        let typed ← finishArguments args states types
        applyAfterArguments typed (targetsOf args types) fun operands =>
          .apply (info place resultType) (.instance callee) operands
      | none =>
        let operands ← (args.zip types).mapM fun (arg, type) => argumentAt arg type
        pure (.apply (info place resultType) (.instance callee) operands)
    reachCallee callee place
    return node

  /-- The signature of a function member of a sort at a type: its member in `zkc::algebra`
  read with `Self` the type. -/
  partial def sortSignature (type : ClosedType) (name : String) (place : Span) :
      ElabM (Array (String × ClosedType) × ClosedType) := do
    let state ← getThe Compile.State
    for (id, sort) in state.sortNames.toList do
      unless hasSort (← getVocabulary) type sort do continue
      let some inner := (state.program.declarations[id]?).bind (·.inner) | continue
      let some (.declaration member) := (state.program.namespaces[inner]?).bind (·.names[name]?) | continue
      let some found := state.program.declarations[member]? | continue
      let .member (.defMember ..) := found.node | continue
      let (parameters, result) ← memberSignatureOf member
      let env : Env := { file := found.file, self? := some (.type type) }
      let types ← parameters.mapM fun (parameter, written) => do
        return (parameter, ← liftM (evalType env written : CompileM ClosedType))
      let resultType ← match result with
        | some written => liftM (evalType env written : CompileM ClosedType)
        | none => pure ClosedType.unit
      return (types, resultType)
    refuseHere "SP3" place s!"`{← renderTypeE type}` has no function `{name}`"

  /-- A function member of a sort: the row of §7.4 at the type. -/
  partial def callSortMember (type : ClosedType) (name : String) (args : Array Arg) (place : Span) :
      ElabM Typed.Expr := do
    let (parameters, result) ← sortSignature type name place
    let some rowName := Typing.sortMemberRow name
      | refuseHere "SP3" place s!"`{name}` of a sort has no row"
    -- the interface states the member's type and the vocabulary the row's: they must agree
    let request := Typing.rowAt rowName type
    let row ← liftM (vocabularyRow request : CompileM Typing.Row)
    unless row.inputs == parameters.map (·.2) && row.outputs == #[result] do
      waitFor s!"the row `{rowName}` at `{← renderTypeE type}`, whose type in the vocabulary is not that of `{name}` in its sort"
    let mut operands := #[]
    for (arg, input) in args.zip row.inputs do
      operands := operands.push (← argumentAt arg input)
    let some resultType := row.outputs[0]? | throw .abandoned
    return applyRowNode place resultType request operands

  /-- A function member of a module bound to a row: the module's row, at the member's own static
  arguments. -/
  partial def callModuleRow (inst : InstanceId) (row : String) (name : String)
      (staticArgs : Option (Array Lowered.StaticArgument)) (args : Array Arg) (place : Span) :
      ElabM Typed.Expr := do
    let (interface, memberId, member, interfaceArgs) ← interfaceMember inst name
    let program := (← getThe Compile.State).program
    let interfaceDeclaration ← liftM (declaration interface : CompileM Declaration)
    let (parameters, result) ← memberSignatureOf memberId
    let env ← staticEnv
    let mut memberEnv : Env := { instanceEnv program interfaceDeclaration interfaceArgs with
      file := member.file, self? := some (.«module» inst) }
    let mut statics : Array Typing.RowStatic := #[]
    let ownParameters := ((member.ownScope.bind fun scope => program.scopes[scope]?).map
      fun scope => scope.parameters).getD #[]
    let written := staticArgs.getD #[]
    for index in [0:ownParameters.size] do
      let reference : ParameterRef := ⟨member.ownScope.getD 0, index⟩
      let some (.term _ _ term) := written[index]?
        | refuseHere "SP6" place
            s!"cannot infer `{ownParameters[index]!.name.text}` of `{name}`; write `{name}<{ownParameters[index]!.name.text} = …>`"
      let cls ← liftM (parameterClass reference : CompileM Class)
      let value ← liftM (evalTerm env term cls : CompileM StaticValue)
      memberEnv := { memberEnv with values := memberEnv.values.insert reference value }
      match value with
      | .natural n => statics := statics.push (.nat n)
      | .type type => statics := statics.push (.type type)
      | .«module» _ => waitFor "a row at a module argument"
    let types ← parameters.mapM fun (_, type) => liftM (evalType memberEnv type : CompileM ClosedType)
    let resultType ← match result with
      | some type => liftM (evalType memberEnv type : CompileM ClosedType)
      | none => pure ClosedType.unit
    let functionMembers := (((program.declarations[interface]?).bind (·.inner)).map fun inner =>
      (program.declarations.filter fun d => d.namespace == inner && d.kind == .functionMember).size).getD 1
    let rowName := if functionMembers ≤ 1 then row else s!"{row}.{name}"
    -- a row of the vocabulary has its type there; a row that a project binds, the interface's
    let entry : Typing.Row := match Typing.rowOf? { name := rowName, statics } with
      | some found => found
      | none => { key := { name := rowName, statics }, kind := .pure, inputs := types,
                  outputs := #[resultType] }
    let mut operands := #[]
    for (arg, type) in args.zip entry.inputs do operands := operands.push (← argumentAt arg type)
    let some resultType := entry.outputs[0]? | throw .abandoned
    return .apply (info place resultType) (.boundRow entry) operands

  /-- A dot call (NL5): `e.m(a…)` is `H::m(e, a…)` with `H` the home module of the type of `e`. -/
  partial def elabMethod (span : Span) (target : Lowered.Expr) (name : Name)
      (staticArgs : Option (Array Lowered.StaticArgument)) (arguments : Array Lowered.Argument)
      (expected : Option ClosedType) : ElabM Typed.Expr := do
    let receiver ← elabExpr target none
    -- a dot call that is a member of the interface of a module parameter (NL6, SP12)
    let first := Arg.typed receiver target.span (.span receiver.span)
    let memberModule : Option InstanceId ← do
      match (← getContext).resolutions[resolvedPlace span name.text]? with
      | some reference =>
        match (← getContext).env.values[reference]? with
        | some (.«module» inst) => pure (some inst)
        | _ => pure none
      | none =>
        match receiver.type with
        | .«opaque» «module» .. => pure (some «module»)
        | _ => pure none
    if let some inst := memberModule then
      let parameters ← memberParameters inst name.text
      let rest ← pairArguments name.text (parameters.extract 1 parameters.size) arguments none span
      if let some typed ← memberOperator? span receiver.type name.text (#[first] ++ rest) expected then
        return typed
    let typeText ← renderTypeE receiver.type
    let some (home, homeName) ← homeOf receiver.type
      | refuseHere "NL5" span s!"`{typeText}` has no function `{name.text}` in its home module: it has none"
    let some id ← functionIn home name.text
      | refuseHere "NL5" span s!"`{typeText}` has no function `{name.text}` in its home module `{homeName}`"
    -- a function without `pub` is called in its module only (NL7)
    if let some declaration := (← getThe Compile.State).program.declarations[id]? then
      unless ← visibleHere declaration do
        refuseHere "NL7" name.span
          s!"`{name.text}` is not `pub` in `{homeName}`; a declaration without `pub` is visible in its module only"
    let env ← staticEnv
    let assigned ← liftM (assignArguments env #[(id, staticArgs)] {} span : CompileM _)
    let (parameters, _) ← signatureOf id
    let rest ← pairArguments name.text ((parameters.extract 1 parameters.size).map (·.1)) arguments none span
    callDeclaration id assigned (#[first] ++ rest) expected span

  /-- An operator on a record or a variant: the function of its fixed name in the home module of
  the type (NL6). -/
  partial def homeCall (span : Span) (type : ClosedType) (function : String) (operator : String)
      (args : Array Arg) (expected : Option ClosedType) : ElabM Typed.Expr := do
    let typeText ← renderTypeE type
    let some (home, homeName) ← homeOf type
      | refuseHere "NL6" span s!"`{operator}` is not defined for `{typeText}`"
    let some id ← functionIn home function
      | refuseHere "NL6" span s!"`{typeText}` has no function `{function}` in its home module `{homeName}`"
    let env ← staticEnv
    let assigned ← liftM (assignArguments env #[(id, none)] {} span : CompileM _)
    callDeclaration id assigned args expected span

  /-- A bare alternative, completed with the expected type (NL3). -/
  partial def elabBare (span : Span) (name : String) (args : Array Arg)
      (expected : Option ClosedType) : ElabM Typed.Expr := do
    match expected with
    | some (.«variant» inst) =>
      let alternatives ← variantAlternatives inst
      match alternatives.findIdx? (·.1 == name) with
      | some index => makeAlternative span inst index alternatives[index]!.2 args
      | none =>
        refuseHere "NL3" span
          s!"`{name}` is not an alternative of `{← renderTypeE (.«variant» inst)}`, the type expected here"
    | some other =>
      refuseHere "NL3" span s!"`{name}` stands where a `{← renderTypeE other}` is expected; it is an alternative of no such type"
    | none =>
      refuseHere "NL3" span s!"`{name}` stands where no variant type is expected: write it with the path of its variant"

  /-- The value of an alternative of a variant instance from its payload. -/
  partial def makeAlternative (span : Span) (inst : InstanceId) (index : Nat)
      (payload : Array ClosedType) (args : Array Arg) : ElabM Typed.Expr := do
    unless args.size == payload.size do
      refuseHere "TY13" span s!"the alternative takes {payload.size} values; {args.size} are given"
    let mut values := #[]
    for (arg, type) in args.zip payload do
      values := values.push (← argumentAt arg type)
    return .construct (info span (.«variant» inst)) (.alternative inst index) values

  /-- `Enum::Name(e…)`: the static arguments of the enum from its path, the expected type or
  inference over the payload (SP6). -/
  partial def elabAlternative (span : Span) (steps : Array (DeclarationId × Option (Array Lowered.StaticArgument)))
      (scopes : Std.HashMap ScopeId (Array StaticValue)) («variant» : DeclarationId) (index : Nat)
      (args : Array Arg) (expected : Option ClosedType) : ElabM Typed.Expr := do
    let env ← staticEnv
    let mut assigned ← liftM (assignArguments env (steps.push («variant», none)) scopes span : CompileM _)
    let found ← liftM (declaration «variant» : CompileM Declaration)
    let program := (← getThe Compile.State).program
    if let some (.«variant» inst) := expected then
      if let some entry := (← getThe Compile.State).table.entries[inst]? then
        if entry.key.declaration == «variant» then
          for ((reference, _), value) in (deployedParameters program found).zip entry.key.arguments do
            unless assigned.contains reference do assigned := assigned.insert reference value
    let .«variant» alternatives := (← loweredOf «variant»).content | throw .abandoned
    let some (_, payload) := alternatives[index]? | throw .abandoned
    let parameters := payload.map fun type => ("", type)
    unless args.size == parameters.size do
      refuseHere "TY13" span s!"the alternative takes {parameters.size} values; {args.size} are given"
    let (values, states) ← inferArguments «variant» assigned found.file parameters none args expected span
    let inst ← liftM (instantiate «variant» values
      { description := ← liftM (describeInstance «variant» values : CompileM String), span } : CompileM InstanceId)
    let alternatives ← variantAlternatives inst
    let payload := alternatives[index]!.2
    let typed ← finishArguments args states payload
    applyAfterArguments typed (targetsOf args payload) fun operands =>
      .construct (info span (.«variant» inst)) (.alternative inst index) operands

  /-- A tuple: each component at the type expected of it, when the expected type is a tuple of
  as many components, and converted where it stands. -/
  partial def elabTuple (span : Span) (components : Array Lowered.Expr) (expected : Option ClosedType) :
      ElabM Typed.Expr := do
    let targets := match expected with
      | some (.tuple types _) => if types.size == components.size then types.map some else components.map fun _ => none
      | _ => components.map fun _ => none
    let mut parts := #[]
    let mut types := #[]
    for (component, target) in components.zip targets do
      let typed ← elabExpr component target
      let converted ← match target with
        | some target => convertTo typed target component.span (.span component.span)
        | none => pure typed
      parts := parts.push converted
      types := types.push (target.getD typed.type)
    return .construct (info span (.tuple types (types.map fun _ => none))) .tuple parts

  /-- `.f` of a record, or of a tuple with named components. -/
  partial def elabField (span : Span) (target : Lowered.Expr) (name : Name) : ElabM Typed.Expr := do
    -- `y.r` of a name bound to the results of an application: the result `r` (RM3)
    if let .local _ binder := target then
      if let some results := (← get).results[binder]? then
        if (← get).refused.contains binder then throw .abandoned
        match results.find? (·.1 == name.text) with
        | some (_, result) => return .local (info span result.type) result.id
        | none =>
          refuseHere "RM3" name.span
            s!"`{← textOf target.span}` has no result `{name.text}`; its results are {", ".intercalate (results.map (·.1)).toList}"
    let record ← elabExpr target none
    match record.type with
    | .record inst =>
      let fields ← recordFields inst
      -- a field without `pub` is read in the module of its record only (NL7)
      if let some declaration ← recordDeclaration inst then
        if let .struct node := declaration.node then
          if node.fields.any (fun field => field.name.text == name.text && !field.pub) then
            unless ← visibleHere { declaration with pub := false } do
              refuseHere "NL7" name.span
                s!"`{name.text}` is not `pub` in `{← renderTypeE record.type}`; a field without `pub` is visible in its module only"
      match fields.findIdx? (·.1 == name.text) with
      | some index => return .project (info span fields[index]!.2) record index (some name.text)
      | none => refuseHere "TY13" name.span s!"`{← renderTypeE record.type}` has no field `{name.text}`"
    | .tuple components names =>
      match names.findIdx? (· == some name.text) with
      | some index => return .project (info span components[index]!) record index (some name.text)
      | none => refuseHere "TY13" name.span s!"`{← renderTypeE record.type}` has no component `{name.text}`"
    | other =>
      refuseHere "TY13" span s!"`{← textOf target.span}` is a `{← renderTypeE other}`; it has no field `{name.text}`"

  /-- `.n` of a tuple. -/
  partial def elabPosition (span : Span) (target : Lowered.Expr) (position : Nat) : ElabM Typed.Expr := do
    let tuple ← elabExpr target none
    let .tuple components _ := tuple.type
      | refuseHere "TY7" span s!"`{← textOf target.span}` is a `{← renderTypeE tuple.type}`; a position reads a tuple"
    let some type := components[position]?
      | refuseHere "TY7" span s!"`{← textOf target.span}` has {components.size} components"
    return .project (info span type) tuple position (some (toString position))

  /-- `xs[i]` (TY7). -/
  partial def elabIndex (span : Span) (target index : Lowered.Expr) : ElabM Typed.Expr := do
    let xs ← elabExpr target none
    match xs.type with
    | .tuple components _ =>
      match ← staticNat? index with
      | some position =>
        let some type := components[position]?
          | refuseHere "TY7" span s!"`{← textOf (← xsPlace xs target)}` has {components.size} components; `{← textOf index.span}` is {position}"
        return .project (info span type) xs position none
      | none =>
        refuseHere "TY7" span
          s!"`{← textOf (← xsPlace xs target)}` is a tuple; a tuple is indexed by a static natural, and `{← textOf index.span}` is a run-time value"
    | .seq element _ =>
      let i ← elabNatural index
      return operationNode span element .seqAt #[xs, i]
    | other =>
      if isDeclared other then
        return ← homeCall span other "at" "[ ]"
          #[.typed xs span (.span xs.span), .written index] none
      refuseHere "TY7" span s!"`{← textOf (← xsPlace xs target)}` is a `{← renderTypeE other}`; it is not indexed"

  /-- What a message about an indexed value quotes: the value when it is a term, its expression
  otherwise. -/
  partial def xsPlace (xs : Typed.Expr) (target : Lowered.Expr) : ElabM Span := do
    return if ← isTerm xs then xs.span else target.span

  /-- Whether a bound of a slice mentions an index of a static range typed as a run-time natural:
  the body is then typed per iteration (TY10). -/
  partial def mentionsIndex (expr : Lowered.Expr) : ElabM (Option String) := do
    let state ← get
    for binder in expr.locals do
      if state.indices.contains binder then
        return ((state.locals[binder]?).map (·.binder.name)).getD ""
    return none

  /-- `xs[a..b]` (TY7): the size of the result when both bounds are static, or when `b` is written
  `a + c` with `c` static. -/
  partial def elabSlice (span : Span) (target : Lowered.Expr) (lower upper : Option Lowered.Expr) :
      ElabM Typed.Expr := do
    for bound in [lower, upper] do
      if let some bound := bound then
        if let some index ← mentionsIndex bound then throw (.staticIndex index)
    let xs ← elabExpr target none
    let .seq element size := xs.type
      | refuseHere "TY7" span s!"`{← textOf (← xsPlace xs target)}` is a `{← renderTypeE xs.type}`; a slice reads a collection"
    let lowerExpr : Lowered.Expr := lower.getD (.number span 0)
    let a ← elabNatural lowerExpr
    let b ← upper.mapM elabNatural
    -- the size of the result: both bounds static, or `a + c` with `c` static
    let resultSize ← do
      let aStatic ← staticNat? lowerExpr (inCondition := true)
      let bStatic ← match upper with
        | some upper => staticNat? upper (inCondition := true)
        | none => pure size
      match aStatic, bStatic with
      | some x, some y => pure (some (y - x))
      | _, _ =>
        match upper with
        | some (.operator _ .add #[left, right]) =>
          let lowerText ← textOf lowerExpr.span
          if (← textOf left.span) == lowerText then staticNat? right (inCondition := true)
          else if (← textOf right.span) == lowerText then staticNat? left (inCondition := true)
          else pure none
        | _ => pure none
    let operands := match b with
      | some b => #[xs, a, b]
      | none => #[xs, a]
    return operationNode span (.seq element resultSize) .seqSlice operands

  /-- `T{f = e, g}` (TY13): the static arguments from the path, the expected type, or inference
  from the fields (SP6). Evaluated in the order written, made in the order of the declaration. -/
  partial def elabRecord (span : Span) (type : Lowered.Reference) (fields : Array Lowered.FieldValue)
      (expected : Option ClosedType) : ElabM Typed.Expr := do
    let env ← staticEnv
    let .reference typeSpan segments := type
    let text ← textOf typeSpan
    let thing ← liftM (evalSegments env segments typeSpan : CompileM Thing)
    let fieldName : Lowered.FieldValue → Name := fun (.field _ name _) => name
    let fieldSpan : Lowered.FieldValue → Span := fun (.field span _ _) => span
    -- the fields given, each once
    let mut given : Array String := #[]
    for field in fields do
      if given.contains (fieldName field).text then
        refuseHere "TY13" (fieldSpan field) s!"`{text}\{…}` gives `{(fieldName field).text}` twice"
      given := given.push (fieldName field).text
    let args := fields.map fun (.field _ _ value) => Arg.written value
    -- the instance: from the path, the expected type or inference over the fields written (SP6)
    let (inst, states) ← match thing with
      | .declarations steps scopes =>
        let some (id, _) := steps.back? | throw .abandoned
        let found ← liftM (declaration id : CompileM Declaration)
        match found.node with
        | .struct _ =>
          let program := (← getThe Compile.State).program
          let mut assigned ← liftM (assignArguments env steps scopes typeSpan : CompileM _)
          if let some (.record inst) := expected then
            if let some entry := (← getThe Compile.State).table.entries[inst]? then
              if entry.key.declaration == id then
                for ((reference, _), value) in (deployedParameters program found).zip entry.key.arguments do
                  unless assigned.contains reference do assigned := assigned.insert reference value
          let .record _ declaredFields := (← loweredOf id).content | throw .abandoned
          let mut parameters := #[]
          for field in fields do
            let name := (fieldName field).text
            let some (_, declared) := declaredFields.find? (·.1.text == name)
              | refuseHere "TY13" (fieldSpan field) s!"`{text}` has no field `{name}`"
            parameters := parameters.push (name, declared)
          let (values, states) ← inferArguments id assigned found.file parameters none args expected span
          let description ← liftM (describeInstance id values : CompileM String)
          let inst ← liftM (instantiate id values { description, span } : CompileM InstanceId)
          pure (inst, states)
        | _ =>
          match ← liftM (thingValue env thing (some .type) typeSpan (pure text) : CompileM StaticValue) with
          | .type (.record inst) => pure (inst, args.map fun _ => ArgState.deferred)
          | _ => refuseHere "TY13" span s!"`{text}` is no record"
      | _ => refuseHere "TY13" span s!"`{text}` is no record"
    let declared ← recordFields inst
    let mut targets := #[]
    for field in fields do
      let name := (fieldName field).text
      let some (_, type) := declared.find? (·.1 == name)
        | refuseHere "TY13" (fieldSpan field) s!"`{text}` has no field `{name}`"
      targets := targets.push type
    for (name, _) in declared do
      unless given.contains name do
        refuseHere "TY13" span s!"`{text}\{…}` does not give the field `{name}`"
    let typed ← finishArguments args states targets
    -- converted in the order written, made in the order of the declaration
    let positions ← declared.mapM fun (name, _) => do
      let some index := given.findIdx? (· == name) | throw .abandoned
      pure index
    constructInOrder span typed (targetsOf args targets) positions fun parts =>
      .construct (info span (.record inst)) (.record inst) parts

  /-- `{r with f = e}` (TY13). -/
  partial def elabRecordUpdate (span : Span) (record : Lowered.Expr) (fields : Array Lowered.FieldValue) :
      ElabM Typed.Expr := do
    let typed ← elabExpr record none
    let .record inst := typed.type
      | refuseHere "TY13" span s!"`{← textOf record.span}` is a `{← renderTypeE typed.type}`; `with` updates a record"
    if isLinear (← getThe Compile.State) typed.type then
      refuseHere "TY13" span s!"`{← textOf record.span}` is linear; `with` needs a record of freely copied data"
    -- a record with a field that is not `pub` is built in its module only (NL7)
    if let some declaration ← recordDeclaration inst then
      if let .struct node := declaration.node then
        if node.fields.any (!·.pub) then
          unless ← visibleHere { declaration with pub := false } do
            refuseHere "NL7" span
              s!"`{← renderTypeE typed.type}` has a field that is not `pub`; it is built only in its module"
    let declared ← recordFields inst
    let (binder, use) ← operandBinder typed
    -- the fields given, in the order written: each names a field of the record, once
    let mut given : Array (Nat × Typed.Expr) := #[]
    for field in fields do
      let .field fieldSpan name value := field
      let some position := declared.findIdx? (·.1 == name.text)
        | refuseHere "TY13" fieldSpan s!"`{← renderTypeE typed.type}` has no field `{name.text}`"
      if given.any (·.1 == position) then
        refuseHere "TY13" fieldSpan s!"`{name.text}` is given twice"
      given := given.push (position, ← elabAt value declared[position]!.2)
    -- they are evaluated in the order written (HO4): where that is not the order of the
    -- declaration, each is bound where it is written
    let ordered := (given.map (·.1)).toList.Pairwise (· < ·)
    let mut bound := #[(binder, typed)]
    let mut values : Array (Nat × Typed.Expr) := #[]
    for (position, value) in given do
      if ordered then values := values.push (position, value)
      else
        let (valueBinder, valueUse) ← operandBinder value
        bound := bound.push (valueBinder, value)
        values := values.push (position, valueUse)
    let parts := (List.range declared.size).toArray.map fun index =>
      match values.find? (·.1 == index) with
      | some (_, value) => value
      | none => .project (info span declared[index]!.2) use index none
    return afterOperands span bound (.construct (info span typed.type) (.record inst) parts)

  /-- `[e₁, …, eₖ]`: a `[T; k]`, `T` the join of the elements, or the element type expected. -/
  partial def elabList (span : Span) (elements : Array Lowered.Expr) (expected : Option ClosedType) :
      ElabM Typed.Expr := do
    let elementExpected := match expected with
      | some (.seq element _) => some element
      | _ => none
    match elementExpected with
    | some element =>
      let mut parts := #[]
      for item in elements do parts := parts.push (← elabAt item element)
      return .construct (info span (.seq element (some elements.size))) .sequence parts
    | none =>
      if elements.isEmpty then
        return .construct (info span (.seq ClosedType.unit (some 0))) .sequence #[]
      let mut typed : Array Typed.Expr := #[]
      for item in elements do typed := typed.push (← elabExpr item none)
      let mut joined := typed[0]!.type
      for item in typed do
        match join joined item.type with
        | some type => joined := type
        | none =>
          refuseHere "TY5" span
            s!"the elements of the collection are a `{← renderTypeE joined}` and a `{← renderTypeE item.type}`, which have no join"
      let targets := (typed.zip elements).map fun (_, source) => (joined, source.span, Typed.Quote.span source.span)
      applyAfterArguments typed targets fun parts =>
        .construct (info span (.seq joined (some elements.size))) .sequence parts

  /-- `[v; n]`. -/
  partial def elabRepetition (span : Span) (element count : Lowered.Expr) (expected : Option ClosedType) :
      ElabM Typed.Expr := do
    let some n ← staticNat? count
      | refuseHere "TY2" span s!"`{← textOf count.span}` is not a size; `[v; n]` takes a size"
    let elementExpected := match expected with
      | some (.seq element _) => some element
      | _ => none
    let typed ← elabExpr element elementExpected
    let type := elementExpected.getD typed.type
    let value ← convertTo typed type element.span (.span element.span)
    return operationNode span (.seq type (some n)) .seqFill #[value]

  /-- The domain of a loop, a comprehension or a fold (TY10, TY11): a range, static when both its
  bounds are, or a collection, evaluated once. -/
  partial def elabDomain (generator : Lowered.Generator) : ElabM LoopDomain := do
    match generator with
    | .range index start stop _ =>
      let span := spanOver start.span stop.span
      let aStatic ← staticNat? start (inCondition := true)
      let bStatic ← staticNat? stop (inCondition := true)
      if let (some x, some y) := (aStatic, bStatic) then
        if y < x then
          refuseHere "CT6" span
            s!"the range `{← textOf start.span}..{← textOf stop.span}` is `{x}..{y}` here: a range `a..b` needs `a <= b`"
        return { index, range := some (staticNode start.span x .number, staticNode stop.span y .number)
                 count := some (y - x), start := some x, span }
      let a ← elabNatural start
      let b ← elabNatural stop
      return { index, range := some (a, b), start := aStatic, span }
    | .collection item iteration source =>
      let xs ← elabExpr source none
      match xs.type with
      | .seq element size =>
        return { index := iteration, source := some xs, item := some item, element, count := size
                 span := source.span }
      | other =>
        refuseHere "TY10" source.span
          s!"`{← textOf source.span}` is a `{← renderTypeE other}`; a loop runs over a range or a collection"

  /-- Binds the item of an iteration: the index of a range, static in an iteration typed on its
  own (`fixed`), or the element of a collection. Gives the binder of the index or of the
  iteration number, and of the element. -/
  partial def bindItem (domain : LoopDomain) (fixed : Option Nat) :
      ElabM (Typed.Binder × Option Typed.Binder) := do
    match domain.item with
    | none =>
      match fixed with
      | some k =>
        modify fun state => { state with iterationIndices := state.iterationIndices.insert domain.index.id }
        return (← bindLocal domain.index .nat (static? := some ((domain.start.getD 0) + k)), none)
      | none =>
        let index ← bindLocal domain.index .nat
        -- an index of a static range stands where it is static only when each iteration is typed
        -- on its own
        if domain.count.isSome && domain.index.origin == .written then
          modify fun state => { state with indices := state.indices.insert domain.index.id }
        return (index, none)
    | some item =>
      let iteration ← bindLocal domain.index .nat
      return (iteration, some (← bindLocal item domain.element))

  /-- The index of a range is a name (TY10): a pattern that is no name takes it apart in the
  statements that begin the body. -/
  partial def checkRangeIndex (domain : LoopDomain) (statements : Array Lowered.Stmt) (span : Span) :
      ElabM Unit := do
    if domain.item.isNone && domain.index.origin == .patternValue && takesApart domain.index.id statements then
      refuseHere "TY10" span "the index of a range is a name"

  /-- The statements that begin the body of a comprehension or a fold: the levels of its pattern. -/
  partial def levelsOf : Lowered.Expr → Array Lowered.Stmt
    | .block _ statements _ => statements
    | _ => #[]

  /-- The name of the index of a range, when a static position of it asks for the iterations to
  be typed one by one. -/
  partial def indexName (domain : LoopDomain) : Option String :=
    if domain.item.isNone && domain.index.origin == .written then some domain.index.name else none

  /-- The terms of a fold or the elements of a comprehension typed one by one, the index a static
  natural in each (TY10, TY11). -/
  partial def perIteration {α : Type} (domain : LoopDomain) (count : Nat) (body : ElabM α) :
      ElabM (Array α) := do
    let mut results := #[]
    for k in [0:count] do
      results := results.push (← inSuite do
        discard <| bindItem domain (some k)
        body)
    return results

  /-- A loop over a domain typed one iteration at a time, the index a static natural in each
  (TY10, TY11): its index and item binders and its iterations. -/
  partial def steppedLoop (domain : LoopDomain) (iterations : Array (Array Typed.Stmt × Array Typed.Expr)) :
      ElabM (Typed.Binder × Option Typed.Binder × Array Typed.Iteration) := do
    let (index, item) ← inSuite (bindItem domain none)
    let mut typed := #[]
    for k in [0:iterations.size] do
      let (statements, values) := iterations[k]!
      typed := typed.push (Typed.Iteration.iteration k statements values)
    return (index, item, typed)

  /-- A body over a domain, typed once with the index a run-time natural; when the index of the
  domain stands where a number is needed, the body is typed per iteration instead, the index
  that number in each (TY10, TY11). `once` types it once; `each` is given the count and types it
  per iteration. Every derived form that types a body over a domain goes through this. -/
  partial def onceOrPerIteration {α : Type} (domain : LoopDomain) (span : Span) (once : ElabM α)
      (each : Nat → ElabM α) : ElabM α := do
    try once
    catch failure =>
      let .staticIndex name := failure | throw failure
      unless some name == indexName domain do throw failure
      let some count := domain.count | throw failure
      checkStepped count span
      each count

  /-- `[e for p in D]` and `[e for p in D if c]` (TY11): a loop that collects, or a `mut`
  collection that a loop appends to where the filter holds. -/
  partial def elabComprehension (span : Span) (element : Lowered.Expr) (generator : Lowered.Generator)
      (filter : Option Lowered.Expr) (expected : Option ClosedType) : ElabM Typed.Expr := do
    let elementExpected := match expected with
      | some (.seq type _) => some type
      | _ => none
    let domain ← elabDomain generator
    checkRangeIndex domain (levelsOf element) span
    let typeElement (target : Option ClosedType) : ElabM Typed.Expr := do
      let typed ← elabExpr element target
      match target with
      | some type => convertTo typed type element.span (.span element.span)
      | none => return typed
    match filter with
    | none =>
      onceOrPerIteration domain span (do
        let (index, item, typed) ← inSuite do
          let (index, item) ← bindItem domain none
          return (index, item, ← typeElement elementExpected)
        let type : ClosedType := .seq typed.type domain.count
        let collected ← freshBinder "%collected" span type (.accumulator .comprehension)
        let loop : Typed.Loop := .loop index (domain.typed item) #[collected] (.uniform #[] #[typed])
        return .block (info span type) #[.for span loop {}] (.local (info span type) collected.id)) fun n => do
        -- typed per element (TY11): the elements at their join, each converted in its iteration
        let items ← perIteration domain n (typeElement elementExpected)
        let mut joined := elementExpected.getD ((items[0]?.map (·.type)).getD ClosedType.unit)
        for item in items do
          match join joined item.type with
          | some type => joined := type
          | none =>
            refuseHere "TY5" span
              s!"the elements of the comprehension are a `{← renderTypeE joined}` and a `{← renderTypeE item.type}`, which have no join"
        let mut values := #[]
        for item in items do
          values := values.push (#[], #[← convertTo item joined span (.span element.span)])
        let (index, item, iterations) ← steppedLoop domain values
        let type : ClosedType := .seq joined (some n)
        let collected ← freshBinder "%collected" span type (.accumulator .comprehension)
        let loop : Typed.Loop := .loop index (domain.typed item) #[collected] (.stepped iterations)
        return .block (info span type) #[.for span loop {}] (.local (info span type) collected.id)
    | some condition =>
      -- the statements of one iteration: where the filter holds, the element is appended
      let appending (collected : Typed.Binder) (type element : ClosedType) (test typed : Typed.Expr) :
          Array Typed.Stmt :=
        let use : Typed.Expr := .local (info span type) collected.id
        let single : Typed.Expr := .construct (info span (.seq element (some 1))) .sequence #[typed]
        let appended := operationNode span type .seqConcat #[use, single]
        #[Typed.Stmt.«if» span test #[.update span collected.id appended {}] #[] (carrying collected)]
      let starting (type element : ClosedType) : Typed.Expr :=
        .convert (info span type) .unsized
          (.construct (info span (.seq element (some 0))) .sequence #[]) (.span span)
      onceOrPerIteration domain span (do
        let (index, item, test, typed) ← inSuite do
          let (index, item) ← bindItem domain none
          let test ← elabBool condition
          return (index, item, test, ← typeElement elementExpected)
        let type : ClosedType := .seq typed.type none
        let collected ← freshBinder "%collected" span type (.accumulator .comprehension) (mutable := true)
        let use : Typed.Expr := .local (info span type) collected.id
        let loop : Typed.Loop :=
          .loop index (domain.typed item) #[] (.uniform (appending collected type typed.type test typed) #[])
        return .block (info span type)
          #[.bind span collected (starting type typed.type) {}, .for span loop (carrying collected)] use)
        fun n => do
        -- typed per element (TY11), with the filter: the elements at their join
        let items ← perIteration domain n do
          let test ← elabBool condition
          return (test, ← typeElement elementExpected)
        let mut joined := elementExpected.getD ((items[0]?.map (·.2.type)).getD ClosedType.unit)
        for (_, item) in items do
          match join joined item.type with
          | some type => joined := type
          | none =>
            refuseHere "TY5" span
              s!"the elements of the comprehension are a `{← renderTypeE joined}` and a `{← renderTypeE item.type}`, which have no join"
        let type : ClosedType := .seq joined none
        let collected ← freshBinder "%collected" span type (.accumulator .comprehension) (mutable := true)
        let use : Typed.Expr := .local (info span type) collected.id
        let mut bodies := #[]
        for (test, item) in items do
          let converted ← convertTo item joined span (.span element.span)
          bodies := bodies.push (appending collected type joined test converted, #[])
        let (index, item, iterations) ← steppedLoop domain bodies
        let loop : Typed.Loop := .loop index (domain.typed item) #[] (.stepped iterations)
        return .block (info span type)
          #[.bind span collected (starting type joined) {}, .for span loop (carrying collected)] use

  /-- `∑`, `∏`, `∀`, `∃` over a domain (TY11): on a type of a sort the row of the form, applied
  to the collection itself or to the collected terms; on naturals, `bool` and a declared type a
  `mut` accumulator from the start of the form, which each iteration combines with its term. A
  sum of naturals over a static range whose term mentions the index is written one term at a
  time, up to 4,096 terms (TY8); so is every fold whose index stands where it is static. `body`
  is absent for the function of the fixed table applied to a collection: the term is the
  element. -/
  partial def elabFold (span : Span) (form : Fold) (generator : Lowered.Generator)
      (body : Option Lowered.Expr) (expected : Option ClosedType) : ElabM Typed.Expr := do
    let symbol := match form with
      | .sum => "∑" | .product => "∏" | .all => "∀" | .any => "∃"
    let quote : Typed.Quote := match body with
      | some body => .span body.span
      | none => .text "item"
    let elementExpected : Option ClosedType := match form, expected with
      | .all, _ | .any, _ => some .bool
      | _, some type => if isNatural type then none else some type
      | _, none => none
    let domain ← elabDomain generator
    if let some body := body then checkRangeIndex domain (levelsOf body) span
    -- the collection itself, when the term is the element
    if let (some xs, some item) := (domain.source, domain.item) then
      let identity := match body with
        | none => true
        | some (.local _ binder) => binder == item.id
        | _ => false
      if identity && (form == .sum || form == .product) then
        let element := domain.element
        let sort ← family element
        if sort.hasSum then
          if form == .product && !sort.hasProduct then
            refuseHere "NL6" span s!"`∏` needs elements of a ring; `{← renderTypeE element}` is not one"
          let row := Typing.Rows.seqFold (if form == .sum then "sum" else "product") element domain.count
          return applyRowNode span element row #[xs]
    -- what the fold of terms of a type is: an accumulator from its start, combining it with each
    -- term, or the terms collected for the row of the form
    let kindOf (type : ClosedType) : ElabM (FoldKind ElabM) := do
      if isNatural type then
        match form with
        | .sum => return .carried .sum .nat (pure (.literal (info span .nat) (.nat 0)))
        | .product => return .carried .product .nat (pure (.literal (info span .nat) (.nat 1)))
        | _ => refuseHere "TY11" span s!"`{symbol}` needs `bool` elements"
      if type == .bool then
        match form with
        | .all => return .carried .all .bool (pure (.literal (info span .bool) (.bool true)))
        | .any => return .carried .any .bool (pure (.literal (info span .bool) (.bool false)))
        | _ => refuseHere "NL6" span s!"`{symbol}` is not defined for `bool`"
      if isDeclared type then
        let unit := if form == .sum then "zero" else "one"
        return .carried .declared type (homeCall span type unit symbol #[] (some type))
      let sort ← family type
      unless sort.hasSum do
        refuseHere "NL6" span s!"`{symbol}` is not defined for `{← renderTypeE type}`"
      if form == .product && !sort.hasProduct then
        refuseHere "NL6" span s!"`∏` needs elements of a ring; `{← renderTypeE type}` is not one"
      return .collected type
    -- the accumulator combined with a term
    let combine (accumulator : Typed.Expr) (term : Typed.Expr) (stepped : Bool) : ElabM Typed.Expr := do
      if isNatural term.type then
        let operation : Typed.CoreOperation := if form == .sum then .natAdd else .natMul
        return operationNode span .nat operation #[accumulator, naturalView term]
      if term.type == .bool || (stepped && (form == .all || form == .any)) then
        let element ← if stepped then convertTo term .bool span (.text "") else pure term
        return operationNode span .bool (if form == .all then .boolAnd else .boolOr) #[accumulator, element]
      let function := if form == .sum then "add" else "mul"
      homeCall span term.type function symbol #[.typed accumulator span (.text ""), .typed term span quote]
        (some term.type)
    -- `∑` (`∏`) by the members `add` and `zero` (`mul` and `one`) of the interface of a module
    -- parameter (NL6, SP12): the accumulator combined with a term, when the term's type is a type
    -- member, or the place was resolved to a member
    let combineMember? (accumulator : Typed.Binder) (term : Typed.Expr) : ElabM (Option Typed.Expr) := do
      unless form == .sum || form == .product do return none
      let use : Typed.Expr := .local (info span accumulator.type) accumulator.id
      let function := if form == .sum then "add" else "mul"
      memberOperator? span term.type function #[.typed use span (.text ""), .typed term span quote] none
    let startMember? (type : ClosedType) : ElabM (Option Typed.Expr) :=
      memberOperator? span type (if form == .sum then "zero" else "one") #[] none
    let member? (accumulator : Typed.Binder) (term : Typed.Expr) : ElabM (Option (Typed.Expr × Typed.Expr)) := do
      let some next ← combineMember? accumulator term | return none
      let some start ← startMember? term.type | return none
      return some (next, start)
    -- a fold whose iterations are typed one by one: the term of each iteration
    let steppedFold (terms : Array Typed.Expr) : ElabM Typed.Expr := do
      match terms[0]? with
      | none =>
        -- no iteration: the start of the form
        match form with
        | .all | .any => return .literal (info span .bool) (.bool (form == .all))
        | _ => return .literal (info span .nat) (.nat (if form == .sum then 0 else 1))
      | some first =>
        -- by the members of an interface
        let accumulator ← freshBinder "%accumulator" span first.type (.accumulator .declared) (mutable := true)
        let use : Typed.Expr := .local (info span first.type) accumulator.id
        if (form == .sum || form == .product) &&
            ((first.type matches .«opaque» ..) ||
              (← getContext).resolutions.contains (resolvedPlace span (if form == .sum then "add" else "mul"))) then
          -- the start once, then each term combined
          let some unit ← startMember? first.type | throw .abandoned
          let mut memberUpdates := #[]
          for term in terms do
            let some next ← combineMember? accumulator term | throw .abandoned
            memberUpdates := memberUpdates.push (#[Typed.Stmt.update span accumulator.id next {}], #[])
          let (index, item, iterations) ← steppedLoop domain memberUpdates
          let loop : Typed.Loop := .loop index (domain.typed item) #[] (.stepped iterations)
          return .block (info span first.type) #[.bind span accumulator unit {},
            .for span loop (carrying accumulator)] use
        match ← kindOf first.type with
        | .carried accumulation type start =>
          let accumulator ← freshBinder "%accumulator" span type (.accumulator accumulation) (mutable := true)
          let use : Typed.Expr := .local (info span type) accumulator.id
          let mut updates := #[]
          for term in terms do
            updates := updates.push (#[Typed.Stmt.update span accumulator.id (← combine use term true) {}], #[])
          let start ← start
          let (index, item, iterations) ← steppedLoop domain updates
          let loop : Typed.Loop := .loop index (domain.typed item) #[] (.stepped iterations)
          return .block (info span type) #[.bind span accumulator start {},
            .for span loop (carrying accumulator)] use
        | .collected type =>
          let collectedType : ClosedType := .seq type (some terms.size)
          let collected ← freshBinder "%collected" span collectedType (.accumulator .terms)
          let (index, item, iterations) ← steppedLoop domain (terms.map fun term => (#[], #[term]))
          let row := Typing.Rows.seqFold (if form == .sum then "sum" else "product") type (some terms.size)
          let loop : Typed.Loop := .loop index (domain.typed item) #[collected] (.stepped iterations)
          return .block (info span type) #[.for span loop {}]
            (applyRowNode span type row #[.local (info span collectedType) collected.id])
    -- one typing for every iteration
    let attempt : ElabM Typed.Expr := do
      let (index, item, term) ← inSuite do
        let (index, item) ← bindItem domain none
        let term ← match body, item with
          | some body, _ => elabExpr body elementExpected
          | none, some item => pure (.local (info span item.type) item.id)
          | none, none => refuseHere "TY11" span "the form has no body"
        let term ← match elementExpected with
          | some target => convertTo term target span quote
          | none => pure term
        return (index, item, term)
      let typedDomain := domain.typed item
      -- by the members of an interface
      let accumulator ← freshBinder "%accumulator" span term.type (.accumulator .declared) (mutable := true)
      if let some (next, start) ← member? accumulator term then
        let use : Typed.Expr := .local (info span term.type) accumulator.id
        let loop : Typed.Loop := .loop index typedDomain #[] (.uniform #[.update span accumulator.id next {}] #[])
        return .block (info span term.type) #[.bind span accumulator start {},
          .for span loop (carrying accumulator)] use
      match ← kindOf term.type with
      | .carried accumulation type start =>
        let accumulator ← freshBinder "%accumulator" span type (.accumulator accumulation) (mutable := true)
        let use : Typed.Expr := .local (info span type) accumulator.id
        let update := Typed.Stmt.update span accumulator.id (← combine use term false) {}
        let loop : Typed.Loop := .loop index typedDomain #[] (.uniform #[update] #[])
        let start ← start
        -- a sum of naturals over a static range whose term mentions the index: term by term
        if accumulation == .sum then
          if let (some n, some _, some body) := (domain.count, domain.start, body) then
            if domain.item.isNone && domain.index.origin == .written && n ≤ 4096 &&
                body.locals.contains domain.index.id then
              checkStepped n span
              return ← steppedFold (← perIteration domain n (elabExpr body elementExpected))
        return .block (info span type) #[.bind span accumulator start {},
          .for span loop (carrying accumulator)] use
      | .collected type =>
        -- the terms collected, then the row of the form
        let collectedType : ClosedType := .seq type domain.count
        let collected ← freshBinder "%collected" span collectedType (.accumulator .terms)
        let row := Typing.Rows.seqFold (if form == .sum then "sum" else "product") type domain.count
        let loop : Typed.Loop := .loop index typedDomain #[collected] (.uniform #[] #[term])
        return .block (info span type) #[.for span loop {}]
          (applyRowNode span type row #[.local (info span collectedType) collected.id])
    onceOrPerIteration domain span attempt fun n => do
      let some body := body | throw (.staticIndex ((indexName domain).getD ""))
      steppedFold (← perIteration domain n (elabExpr body elementExpected))

  /-- `⟪a, b⟫` and `inner(a, b)` (TY11): points first, then their scalars. -/
  partial def elabInner (span : Span) (a b : Lowered.Expr) : ElabM Typed.Expr := do
    let x ← elabExpr a none
    let y ← elabExpr b none
    match x.type, y.type with
    | .seq points (some m), .seq scalars (some n) =>
      unless m == n do
        refuseHere "TY11" span
          s!"`⟪{← textOf a.span}, {← textOf b.span}⟫` takes two collections of one size; they have {m} and {n} elements"
      if (← family points).isElement then
        let some scalar ← liftM (scalarOf points : CompileM _)
          | refuseHere "NL6" span s!"`⟪ ⟫` is not defined for `{← renderTypeE points}`"
        let scalarsAreGroup := (← family scalars) matches .group
        if scalarsAreGroup || (!typeEq scalars scalar && !typeEq scalars points) then
          if scalarsAreGroup && typeEq points scalar then
            refuseHere "NL6" span
              s!"`⟪a, b⟫` takes the points first and their scalars second: write `⟪{← textOf b.span}, {← textOf a.span}⟫`"
        let target := ClosedType.seq scalar (some n)
        let converted ← convertTo y target span (.span b.span)
        return applyRowNode span points (Typing.Rows.seqInner points n) #[x, converted]
      -- of naturals: the sum of the products, term by term (§3.5)
      if isNatural points && isNatural scalars then
        let (xBinder, xUse) ← operandBinder x
        let (yBinder, yUse) ← operandBinder y
        let index ← madeBinder "%index" span .written
        let result ← freshBinder "%sum" span .nat (.accumulator .sum) (mutable := true)
        let use : Typed.Expr := .local (info span .nat) result.id
        let typedIndex ← bindLocal index .nat
        let elementAt (xs : Typed.Expr) (element : ClosedType) : Typed.Expr :=
          naturalView (operationNode span element .seqAt #[xs, .local (info span .nat) index.id])
        let term := operationNode span .nat .natMul #[elementAt xUse points, elementAt yUse scalars]
        let body : Array Typed.Stmt :=
          #[.update span result.id (operationNode span .nat .natAdd #[use, term]) {}]
        let loop : Typed.Loop := .loop typedIndex
          (.range (staticNode span 0 .number) (staticNode span m .number) (some m)) #[]
          (.uniform body #[])
        return afterOperands span #[(xBinder, x), (yBinder, y)]
          (.block (info span .nat)
            #[.bind span result (.literal (info span .nat) (.nat 0)) {},
              .for span loop (carrying result)] use)
      refuseHere "NL6" span
        s!"`⟪ ⟫` is not defined for `{← renderTypeE x.type}` and `{← renderTypeE y.type}`"
    | _, _ =>
      refuseHere "TY11" span s!"`⟪{← textOf a.span}, {← textOf b.span}⟫` takes two collections of one static size"

  /-- `sum`, `product`, `all`, `any` and `inner` of the fixed table. -/
  partial def elabFixed (span : Span) (function : FixedFunction) (arguments : Array Lowered.Argument)
      (expected : Option ClosedType) : ElabM Typed.Expr := do
    let values := arguments.filterMap fun
      | .positional _ value => some value
      | _ => none
    match function, values with
    | .inner, #[a, b] => elabInner span a b
    | .inner, _ => refuseHere "FN6" span "`inner` takes two collections"
    | _, #[collection] =>
      let form : Fold := match function with
        | .sum => .sum | .product => .product | .all => .all | _ => .any
      match collection with
      | .comprehension _ element generator none => elabFold span form generator (some element) expected
      | _ =>
        let item ← madeBinder "_" span .patternValue
        let iteration ← madeBinder "%iteration" span .iteration
        elabFold span form (.collection item iteration collection) none expected
    | _, _ => refuseHere "FN6" span "the function takes one collection"

  /-- An expression in a `rational` context (TY8): every operand is a `rational`, a natural, a
  size and a number converted; `+ - * /` are exact, `^` takes an integer exponent, prefix `-`
  applies, and `%` is refused. The operations have no form in the core. -/
  partial def elabRational (expr : Lowered.Expr) : ElabM Typed.Expr := do
    let rational (span : Span) (what : String) (operands : Array Typed.Expr) : Typed.Expr :=
      .apply (info span .rational) (.specification what) operands
    match expr with
    | .number span _ => return rational span "a number as a `rational`" #[]
    | .operator span .add #[a, b] =>
      return rational span "the sum of `rational`s" #[← elabRational a, ← elabRational b]
    | .operator span .subtract #[a, b] =>
      return rational span "the difference of `rational`s" #[← elabRational a, ← elabRational b]
    | .operator span .multiply #[a, b] =>
      return rational span "the product of `rational`s" #[← elabRational a, ← elabRational b]
    | .operator span .divide #[a, b] =>
      return rational span "the quotient of `rational`s" #[← elabRational a, ← elabRational b]
    | .operator span .remainder _ => refuseHere "TY8" span "`%` is defined on naturals, not on `rational`"
    | .operator span .power #[base, exponent] =>
      let x ← elabRational base
      return rational span "a power of a `rational`" #[x, ← elabInteger exponent]
    | .operator span .negate #[operand] =>
      return rational span "the negation of a `rational`" #[← elabRational operand]
    | .conditional span .ifThenElse condition onTrue onFalse =>
      elabIf span condition onTrue onFalse (some .rational)
    | _ => toRational (← elabExpr expr none) expr

  /-- A typed value as a `rational`: a natural is converted. -/
  partial def toRational (typed : Typed.Expr) (expr : Lowered.Expr) : ElabM Typed.Expr := do
    if typed.type == .rational then return typed
    if isNatural typed.type then
      return .apply (info typed.span .rational) (.specification "a natural as a `rational`") #[naturalView typed]
    refuseHere "TY5" expr.span
      s!"`{← textOf expr.span}` is a `{← renderTypeE typed.type}`; a `rational` is expected here"

  /-- The exponent of a `rational`: an integer, a natural or its negation (TY8). -/
  partial def elabInteger (expr : Lowered.Expr) : ElabM Typed.Expr := do
    match expr with
    | .operator span .negate #[operand] =>
      return .apply (info span .nat) (.specification "the negation of an integer") #[← elabInteger operand]
    | _ =>
      let typed ← elabExpr expr none
      unless isNatural typed.type do
        refuseHere "TY8" expr.span
          s!"the exponent of a `rational` is an integer; `{← textOf expr.span}` is a `{← renderTypeE typed.type}`"
      return naturalView typed

  /-- `a and b` (`conjunction`) or `a or b`: a conditional with a literal arm (§4.2). Whether it is
  computed by the boolean operation or by a local `if` is decided at emission. -/
  partial def elabLogic (span : Span) (conjunction : Bool) (a b : Lowered.Expr) : ElabM Typed.Expr := do
    let left ← elabBool a
    let right ← elabBool b
    if conjunction then
      return .conditional (info span .bool) .and left right (.literal (info span .bool) (.bool false))
    return .conditional (info span .bool) .or left (.literal (info span .bool) (.bool true)) right

  /-- `if c then a else b`: the arm taken when `c` is static (TY9); otherwise a local `if` whose
  arms are at the join of their types (TY5). -/
  partial def elabIf (span : Span) (condition onTrue onFalse : Lowered.Expr)
      (expected : Option ClosedType) : ElabM Typed.Expr := do
    if let some taken ← staticCondition? condition then
      return ← elabExpr (if taken then onTrue else onFalse) expected
    let test ← elabBool condition
    let arm (branch : Lowered.Expr) (target : Option ClosedType) : ElabM Typed.Expr := do
      let typed ← elabExpr branch target
      match target with
      | some type => convertTo typed type branch.span (.span branch.span)
      | none => return typed
    let (x, y, type) ← match expected with
      | some type => do
        let x ← arm onTrue (some type)
        let y ← arm onFalse (some type)
        pure (x, y, type)
      | none => do
        let thenLiteral ← isLiteral onTrue
        let elseLiteral ← isLiteral onFalse
        let (x, y) ← if thenLiteral && !elseLiteral then do
            let y ← arm onFalse none
            let x ← arm onTrue (← sameSibling y.type)
            pure (x, y)
          else do
            let x ← arm onTrue none
            let sibling ← sameSibling x.type
            let y ← arm onFalse (if elseLiteral then sibling else none)
            pure (x, y)
        match join x.type y.type with
        | some joined =>
          let x ← if typeEq x.type joined then pure x else arm onTrue (some joined)
          let y ← if typeEq y.type joined then pure y else arm onFalse (some joined)
          pure (x, y, joined)
        | none =>
          refuseHere "TY5" span
            s!"the arms of the `if` are a `{← renderTypeE x.type}` and a `{← renderTypeE y.type}`, which have no join"
    return .conditional (info span type) .ifThenElse test x y

  /-- A local name: its binder at the type it has, or the number it stands for. -/
  partial def localPath (span : Span) (binder : LocalId) : ElabM Typed.Expr := do
    -- a name that a refused statement would have bound: what reads it is not elaborated, and
    -- makes no diagnostic
    if (← get).refused.contains binder then throw .abandoned
    if let some what := (← get).valueless[binder]? then
      refuseHere "RM3" span s!"`{← textOf span}` is {what}: it is no value"
    if (← get).specificationPorts.contains binder && !(← getContext).specification then
      refuseHere "SX4" span
        s!"`{← textOf span}` is a `spec` port, which no role holds: it stands only in a specification"
    match ← localOf? binder with
    | some entry =>
      match entry.static? with
      | some value => return staticNode span value (.local binder)
      | none => return .local (info span entry.binder.type) binder
    | none => refuseHere "NL3" span s!"`{← textOf span}` is not bound here"

  /-- A path that stands for a value: a static natural. -/
  partial def elabPath (reference : Lowered.Reference) (_expected : Option ClosedType) :
      ElabM Typed.Expr := do
    let .reference span segments := reference
    let steps : List Frontend.Step := segments.toList.map fun (.segment step _ _) => step
    match steps with
    | [.bareAlternative name] => elabBare span name #[] _expected
    | _ =>
      match steps.getLast? with
      | some (.alternative _ _) =>
        match ← calleeOf reference with
        | .alternative previous scopes «variant» index =>
          elabAlternative span previous scopes «variant» index #[] _expected
        | _ => throw .abandoned
      | _ =>
        let env ← staticEnv
        let text ← textOf span
        let source : Typed.StaticSource := match steps with
          | [.parameter parameter] => .parameter parameter
          | _ => .declared text
        let thing ← liftM (evalSegments env segments span : CompileM Thing)
        match thing with
        | .value (.natural value) => return staticNode span value source
        | .value (.type _) => refuseHere "TY1" span s!"`{text}` is a type; a value is expected here"
        | .value (.«module» _) => refuseHere "TY1" span s!"`{text}` is a module; a value is expected here"
        | .declarations _ _ =>
          match ← liftM (thingValue env thing none span (pure text) : CompileM StaticValue) with
          | .natural value => return staticNode span value source
          | _ => refuseHere "TY1" span s!"`{text}` is no value"
        | _ => refuseHere "TY1" span s!"`{text}` is no value"
end

end Zkc.Frontend.Elab
