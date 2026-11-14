module

public import Zkc.Core.Raw

public section

/-! Elaboration of raw syntax into the typed model, as an ordinary function.

`elaborate : Raw.Package → Except Refusal Typed` is defined by structural recursion
on the raw syntax. It builds the intrinsically typed terms of the model and decides
every rule of legality: an ill-typed reference is a refusal, and so is a residual
violation of a definition or of the package's tables.

A value number is its position in binding order, so the reference of value `n` in a
context of depth `d` is the position `d - 1 - n`. Each context is carried with a
`Scope`, which finds the type at a position in logarithmic time; no list of numbers
and no walk over the context is involved.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- Why a raw package has no typed term. -/
inductive Refusal.Cause where
  /-- A value, row or definition number names nothing. -/
  | dangling
  /-- An operand has another type or holder than its position requires. -/
  | operand
  /-- A row is used as another kind than it has, or it is applied or sampled although an
  output type of it has no value. -/
  | kind
  /-- A deployed definition uses a specification-only one. -/
  | specification
  /-- A literal is outside its type: a `fin` literal not below its bound, or a byte not
  below 256. -/
  | literal
  /-- The static data of an operation the core owns do not fit: a position beyond the
  components of a tuple, the fields of a record or the alternatives of a variant, or a
  `fin` widened to a smaller bound. -/
  | builtin
  /-- A type names a record or a variant that the package does not declare. -/
  | declaration
  /-- An agreement has no port, or ports of different types. -/
  | agreement
  /-- A residual condition of a typed definition or of the tables fails. -/
  | residual (violation : Violation)
  deriving Repr, DecidableEq

/-- The definition that a refusal is in: a function or a protocol, by its number among the
definitions of its kind, in program order. -/
inductive Refusal.Definition where
  | function (number : Nat)
  | protocol (number : Nat)
  deriving Repr, DecidableEq

/-- A refusal of elaboration: why a raw package has no typed term, and where.

`definition` is the function or the protocol that is refused; a refusal of the tables or
of the names of the package has none. `path` says where in the body of the definition, in
the numbering of the check of facts (`Unjustified.path`): the number of the instruction in
the body, then, for an instruction inside a nested region, the number of that region among
the regions of its instruction and the number of the instruction in it, and so on; the body
of a block is numbered like a region without a region number. A refusal of the values that
a region returns has the number after its last instruction. A refusal of the header of a
definition, of its agreements or of a residual condition of its body has the empty path. -/
structure Refusal where
  cause : Refusal.Cause
  definition : Option Refusal.Definition
  path : List Nat
  deriving Repr, DecidableEq

namespace Refusal

/-- A refusal for a cause, not yet placed. -/
@[expose] def of (cause : Cause) : Refusal := ⟨cause, none, []⟩

/-- A refusal inside the instruction, or the nested region, with a number. -/
@[expose] def under (number : Nat) (refusal : Refusal) : Refusal :=
  { refusal with path := number :: refusal.path }

/-- A refusal of what follows an instruction or a region: its first number counts one
more. -/
@[expose] def later (refusal : Refusal) : Refusal :=
  match refusal.path with
  | first :: rest => { refusal with path := (first + 1) :: rest }
  | [] => refusal

/-- A refusal inside a definition. -/
@[expose] def within (definition : Definition) (refusal : Refusal) : Refusal :=
  { refusal with definition := some definition }

end Refusal

/-- The scope of a table whose rows are named by position. -/
def tableScope {α : Type} : (table : List α) → Scope table
  | [] => .empty
  | row :: rest => (tableScope rest).push row

/-- The types of several values, each by `typeOf`. -/
@[expose] def typesWith {α : Type} (typeOf : Nat → Option α) : List Nat → Option (List α)
  | [] => some []
  | value :: values =>
      match typeOf value, typesWith typeOf values with
      | some type, some types => some (type :: types)
      | _, _ => none

/-- The types of values are one per value. -/
theorem typesWith_length {α : Type} (typeOf : Nat → Option α) :
    ∀ (values : List Nat) (types : List α), typesWith typeOf values = some types →
      types.length = values.length
  | [], _, found => by
      cases Option.some.inj found
      rfl
  | value :: values, types, found => by
      unfold typesWith at found
      split at found
      · rename_i type rest _ later
        cases Option.some.inj found
        exact congrArg (· + 1) (typesWith_length typeOf values rest later)
      · cases found

/-! ## Literals -/

/-- The bytes of a literal, each below 256. -/
@[expose] def elaborateBytes : List Nat → Option (List (Fin 256))
  | [] => some []
  | byte :: rest =>
      if below : byte < 256 then
        match elaborateBytes rest with
        | some bytes => some (⟨byte, below⟩ :: bytes)
        | none => none
      else none

/-- The typed literal of a raw one: a `fin` literal and the bytes are checked against
their bounds. -/
@[expose] def elaborateLiteral : Raw.Literal → Option Literal
  | .nat value => some (.nat value)
  | .bool value => some (.bool value)
  | .fin bound value => if below : value < bound then some (.fin bound ⟨value, below⟩) else none
  | .nominal row data => some (.nominal row data)
  | .bytes data =>
      match elaborateBytes data with
      | some bytes => some (.bytes bytes)
      | none => none

/-! ## Operations the core owns -/

/-- The typed operation of a raw one: its types are read in the type table, a position is
looked up among the components, the fields or the alternatives, and a widening is checked to
grow its bound. -/
@[expose] def elaborateBuiltin (typeTable : TypeTable) : Raw.Builtin → Option Builtin
  | .natAdd => some .natAdd
  | .natMul => some .natMul
  | .natPow => some .natPow
  | .natEqual => some .natEqual
  | .natLess => some .natLess
  | .natSub => some .natSub
  | .natDiv => some .natDiv
  | .natRem => some .natRem
  | .boolAnd => some .boolAnd
  | .boolOr => some .boolOr
  | .boolNot => some .boolNot
  | .boolEqual => some .boolEqual
  | .seqLength element size => (Ty.fill typeTable element).map (.seqLength · size)
  | .seqAt element size => (Ty.fill typeTable element).map (.seqAt · size)
  | .seqSlice element size result => (Ty.fill typeTable element).map (.seqSlice · size result)
  | .seqConcat element left right => (Ty.fill typeTable element).map (.seqConcat · left right)
  | .seqFill element count => (Ty.fill typeTable element).map (.seqFill · count)
  | .seqMake element count => (Ty.fill typeTable element).map (.seqMake · count)
  | .seqSized element size => (Ty.fill typeTable element).map (.seqSized · size)
  | .seqUnsized element size => (Ty.fill typeTable element).map (.seqUnsized · size)
  | .natBelow bound => some (.natBelow bound)
  | .finToNat bound => some (.finToNat bound)
  | .finWiden bound wider =>
      if fits : Nat.ble bound wider = true then some (.finWiden bound wider fits) else none
  | .tupleMake components => (Ty.fillAll typeTable components).map .tupleMake
  | .tupleGet components position =>
      match Ty.fillAll typeTable components with
      | some components =>
          match found : components[position]? with
          | some type => some (.tupleGet components type ⟨position, found⟩)
          | none => none
      | none => none
  | .recordMake declaration =>
      match typeTable.records[declaration]? with
      | some record => some (.recordMake declaration record.use record.fields)
      | none => none
  | .recordGet declaration position =>
      match typeTable.records[declaration]? with
      | some record =>
          match found : record.fields[position]? with
          | some type => some (.recordGet declaration record.use record.fields type ⟨position, found⟩)
          | none => none
      | none => none
  | .variantMake declaration position =>
      match typeTable.variants[declaration]? with
      | some variant =>
          match found : variant.alternatives[position]? with
          | some payload =>
              some (.variantMake declaration variant.alternatives payload ⟨position, found⟩)
          | none => none
      | none => none

/-- The records and variants that a raw operation names, itself or in its types, are
declared. An operation that names an undeclared one is refused as a type that does is. -/
@[expose] def builtinDeclared (typeTable : TypeTable) : Raw.Builtin → Bool
  | .seqLength element _ | .seqAt element _ | .seqSlice element .. | .seqConcat element ..
  | .seqFill element _ | .seqMake element _ | .seqSized element _ | .seqUnsized element _ =>
      (Ty.fill typeTable element).isSome
  | .tupleMake components | .tupleGet components _ => (Ty.fillAll typeTable components).isSome
  | .recordMake declaration | .recordGet declaration _ =>
      (typeTable.records[declaration]?).isSome
  | .variantMake declaration _ => (typeTable.variants[declaration]?).isSome
  | _ => true

/-! ## Local regions -/

section Local

variable {operations : List OperationSignature} {functions : List FunctionHeader}
variable (typeTable : TypeTable) (rows : Scope operations) (callees : Scope functions)
  (deployed : Bool)

/-- A typed local operation with its nested regions and the numbers of its operands. -/
structure LocalElaborated (operations : List OperationSignature) (functions : List FunctionHeader)
    (deployed : Bool) where
  op : LocalOp operations functions deployed
  bodies : Regions (LocalDialect operations functions deployed) op.regions
  operands : List Nat

mutual
  /-- `typeOf` gives the type of a value of the surrounding context, local or protocol. -/
  @[expose] def elaborateLocalStep (typeOf : Nat → Option Ty) :
      Raw.LocalStep → Except Refusal (LocalElaborated operations functions deployed)
    | .op row operands =>
        match rows.at? row with
        | some ⟨⟨inputs, outputs, kind⟩, reference⟩ =>
            if applies : OperationSignature.applies ⟨inputs, outputs, kind⟩ = true then
              .ok ⟨.op reference applies, .nil, operands⟩
            else .error (.of .kind)
        | none => .error (.of .dangling)
    | .call callee operands =>
        match callees.value? callee with
        | some ⟨header, reference⟩ =>
            if permitted : (deployed && header.specificationOnly) = false then
              .ok ⟨.call reference permitted, .nil, operands⟩
            else .error (.of .specification)
        | none => .error (.of .dangling)
    | .conditional condition captures outputs onTrue onFalse =>
        match typesWith typeOf captures, Ty.fillAll typeTable outputs with
        | some captureTypes, some outputs =>
            match elaborateLocalRegion (bindAll [] captureTypes) (Scope.empty.bindAll captureTypes)
                  outputs onTrue,
                elaborateLocalRegion (bindAll [] captureTypes) (Scope.empty.bindAll captureTypes)
                  outputs onFalse with
            | .ok onTrue, .ok onFalse =>
                .ok ⟨.conditional captureTypes outputs, .cons onTrue (.cons onFalse .nil),
                  condition :: captures⟩
            | .error refusal, _ => .error (refusal.under 0)
            | _, .error refusal => .error (refusal.under 1)
        | none, _ => .error (.of .dangling)
        | _, none => .error (.of .declaration)
    | .match declaration value captures outputs arms =>
        match typeTable.variants[declaration]?, typesWith typeOf captures,
            Ty.fillAll typeTable outputs with
        | some variant, some captureTypes, some outputs =>
            match elaborateLocalArms
                (variant.alternatives.map fun payload => (payload :: captureTypes, outputs)) arms with
            | .ok bodies =>
                .ok ⟨.match declaration variant.alternatives captureTypes outputs, bodies,
                  value :: captures⟩
            | .error refusal => .error refusal
        | none, _, _ => .error (.of .declaration)
        | _, none, _ => .error (.of .dangling)
        | _, _, none => .error (.of .declaration)
    | .loop count carried captures collected body =>
        match typesWith typeOf carried, typesWith typeOf captures,
            Ty.fillAll typeTable collected with
        | some carriedTypes, some captureTypes, some collectedTypes =>
            match elaborateLocalRegion (bindAll [] (.nat :: (carriedTypes ++ captureTypes)))
                (Scope.empty.bindAll (.nat :: (carriedTypes ++ captureTypes)))
                (collectedTypes ++ carriedTypes) body with
            | .ok body =>
                .ok ⟨.loop count.typed carriedTypes collectedTypes captureTypes, .cons body .nil,
                  count.operands ++ (carried ++ captures)⟩
            | .error refusal => .error (refusal.under 0)
        | none, _, _ => .error (.of .dangling)
        | _, none, _ => .error (.of .dangling)
        | _, _, none => .error (.of .declaration)
    | .guard reason condition => .ok ⟨.guard reason, .nil, [condition]⟩
    | .literal value =>
        match elaborateLiteral value with
        | some literal => .ok ⟨.literal literal, .nil, []⟩
        | none => .error (.of .literal)
    | .builtin operation operands =>
        match elaborateBuiltin typeTable operation with
        | some operation => .ok ⟨.builtin operation, .nil, operands⟩
        | none => .error (.of (cond (builtinDeclared typeTable operation) .builtin .declaration))

  @[expose] def elaborateLocalRegion (Γ : List Ty) (scope : Scope Γ) (out : List Ty) :
      Raw.LocalRegion → Except Refusal (Region (LocalDialect operations functions deployed) Γ out)
    | .ret values =>
        match scope.operands? out values with
        | some operands => .ok (.ret operands)
        | none => .error ((Refusal.of .operand).under 0)
    | .stop reason => .ok (.stop reason)
    | .step instruction rest =>
        match elaborateLocalStep scope.type? instruction with
        | .ok ⟨op, bodies, values⟩ =>
            match scope.operands? op.arguments values,
                elaborateLocalRegion (bindAll Γ op.results) (scope.bindAll op.results) out rest with
            | some arguments, .ok rest => .ok (.letOp op arguments bodies rest)
            | none, _ => .error ((Refusal.of .operand).under 0)
            | _, .error refusal => .error refusal.later
        | .error refusal => .error (refusal.under 0)
    | .block outputs body rest =>
        match Ty.fillAll typeTable outputs with
        | some outputs =>
            match elaborateLocalRegion Γ scope outputs body,
                elaborateLocalRegion (bindAll Γ outputs) (scope.bindAll outputs) out rest with
            | .ok body, .ok rest => .ok (.bind body rest)
            | .error refusal, _ => .error (refusal.under 0)
            | _, .error refusal => .error refusal.later
        | none => .error ((Refusal.of .declaration).under 0)

  /-- Closed regions, one per signature: the regions of a `match`. -/
  @[expose] def elaborateLocalArms :
      (signatures : List (List Ty × List Ty)) → Raw.LocalArms →
        Except Refusal (Regions (LocalDialect operations functions deployed) signatures)
    | [], .none => .ok .nil
    | (inputs, outputs) :: signatures, .arm region rest =>
        match elaborateLocalRegion (bindAll [] inputs) (Scope.empty.bindAll inputs) outputs region,
            elaborateLocalArms signatures rest with
        | .ok body, .ok tail => .ok (.cons body tail)
        | .error refusal, _ => .error (refusal.under 0)
        | _, .error refusal => .error refusal.later
    | [], .arm .. => .error (.of .operand)
    | _ :: _, .none => .error (.of .operand)
end

end Local

/-! ## Protocol regions -/

section Protocol

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader}
variable (typeTable : TypeTable) (rows : Scope operations) (callees : Scope functions)
  (applied : Scope protocols) (deployed : Bool)

structure ProtocolElaborated (operations : List OperationSignature)
    (functions : List FunctionHeader) (protocols : List ProtocolHeader) (deployed : Bool) where
  op : ProtocolOp operations functions protocols deployed
  bodies : Regions (ProtocolDialect operations functions protocols deployed) op.regions
  operands : List Nat

/-- The type of a located value, without its holder. -/
@[expose] def localType {Γ : List Located} (scope : Scope Γ) (value : Nat) : Option Ty :=
  match scope.type? value with
  | some located => some located.type
  | none => none

mutual
  @[expose] def elaborateProtocolStep {Γ : List Located} (scope : Scope Γ) :
      Raw.ProtocolStep → Except Refusal (ProtocolElaborated operations functions protocols deployed)
    | .at role instruction =>
        match elaborateLocalStep typeTable rows callees deployed (localType scope) instruction with
        | .ok ⟨op, bodies, operands⟩ => .ok ⟨.at role op bodies, .nil, operands⟩
        | .error refusal => .error refusal
    | .exchange sender receiver site value =>
        match scope.type? value with
        | some located => .ok ⟨.exchange sender receiver site located.type, .nil, [value]⟩
        | none => .error (.of .dangling)
    | .draw owner receivers site law operands =>
        match rows.at? law with
        | some ⟨⟨_, [output], .sampling⟩, reference⟩ =>
            if populated : output.populated = true then
              .ok ⟨.draw owner receivers site reference populated, .nil, operands⟩
            else .error (.of .kind)
        | some _ => .error (.of .kind)
        | none => .error (.of .dangling)
    | .sample owner site law operands =>
        match rows.at? law with
        | some ⟨⟨_, [output], .sampling⟩, reference⟩ =>
            if populated : output.populated = true then
              .ok ⟨.sample owner site reference populated, .nil, operands⟩
            else .error (.of .kind)
        | some _ => .error (.of .kind)
        | none => .error (.of .dangling)
    | .repeat participants count carried captures collected body =>
        match typesWith scope.type? carried, typesWith scope.type? captures,
            Located.fillAll typeTable collected with
        | some carriedTypes, some captureTypes, some collectedTypes =>
            if covered : Located.heldBy participants collectedTypes = true then
              match elaborateProtocolRegion
                  (bindAll [] (Located.ofRoles .nat participants ++ (carriedTypes ++ captureTypes)))
                  (Scope.empty.bindAll
                    (Located.ofRoles .nat participants ++ (carriedTypes ++ captureTypes)))
                  (collectedTypes ++ carriedTypes) body with
              | .ok body =>
                  .ok ⟨.repeat participants count.typed carriedTypes collectedTypes captureTypes
                      covered, .cons body .nil, count.operands ++ (carried ++ captures)⟩
              | .error refusal => .error (refusal.under 0)
            else .error (.of .operand)
        | none, _, _ => .error (.of .dangling)
        | _, none, _ => .error (.of .dangling)
        | _, _, none => .error (.of .declaration)
    | .choose participants tags tag captures outputs arms =>
        match ChoiceTag.fill typeTable tag, typesWith scope.type? captures,
            Located.fillAll typeTable outputs with
        | some tag, some captureTypes, some outputs =>
            if covered : Located.heldBy participants outputs = true then
              match elaborateProtocolArms (tag.regions participants captureTypes outputs) arms with
              | .ok arms =>
                  .ok ⟨.choose participants tag captureTypes outputs covered, arms, tags ++ captures⟩
              | .error refusal => .error refusal
            else .error (.of .operand)
        | none, _, _ => .error (.of .declaration)
        | _, none, _ => .error (.of .dangling)
        | _, _, none => .error (.of .declaration)
    | .apply callee roleMap site operands =>
        match applied.value? callee with
        | some ⟨header, reference⟩ =>
            if permitted : (deployed && header.specificationOnly) = false then
              .ok ⟨.apply reference roleMap site permitted, .nil, operands⟩
            else .error (.of .specification)
        | none => .error (.of .dangling)

  @[expose] def elaborateProtocolRegion (Γ : List Located) (scope : Scope Γ) (out : List Located) :
      Raw.ProtocolRegion →
        Except Refusal (Region (ProtocolDialect operations functions protocols deployed) Γ out)
    | .ret values =>
        match scope.operands? out values with
        | some operands => .ok (.ret operands)
        | none => .error ((Refusal.of .operand).under 0)
    | .stop reason => .ok (.stop reason)
    | .step instruction rest =>
        match elaborateProtocolStep scope instruction with
        | .ok ⟨op, bodies, values⟩ =>
            match scope.operands? op.arguments values,
                elaborateProtocolRegion (bindAll Γ op.results) (scope.bindAll op.results) out rest with
            | some arguments, .ok rest => .ok (.letOp op arguments bodies rest)
            | none, _ => .error ((Refusal.of .operand).under 0)
            | _, .error refusal => .error refusal.later
        | .error refusal => .error (refusal.under 0)
    | .block outputs body rest =>
        match Located.fillAll typeTable outputs with
        | some outputs =>
            match elaborateProtocolRegion Γ scope outputs body,
                elaborateProtocolRegion (bindAll Γ outputs) (scope.bindAll outputs) out rest with
            | .ok body, .ok rest => .ok (.bind body rest)
            | .error refusal, _ => .error (refusal.under 0)
            | _, .error refusal => .error refusal.later
        | none => .error ((Refusal.of .declaration).under 0)

  /-- Closed regions, one per signature. -/
  @[expose] def elaborateProtocolArms :
      (signatures : List (List Located × List Located)) → Raw.ProtocolArms →
        Except Refusal (Regions (ProtocolDialect operations functions protocols deployed) signatures)
    | [], .none => .ok .nil
    | (inputs, outputs) :: signatures, .arm region rest =>
        match elaborateProtocolRegion (bindAll [] inputs) (Scope.empty.bindAll inputs) outputs region,
            elaborateProtocolArms signatures rest with
        | .ok body, .ok tail => .ok (.cons body tail)
        | .error refusal, _ => .error (refusal.under 0)
        | _, .error refusal => .error refusal.later
    | [], .arm .. => .error (.of .operand)
    | _ :: _, .none => .error (.of .operand)
end

end Protocol

/-! ## Signatures -/

/-- The copy at a port, at the agreement's type. -/
@[expose] def elaborateCopy (ports : List Located) (type : Ty) (port : Nat) : Option (Copy ports type) :=
  match found : ports[port]? with
  | some located =>
      if same : located.type = type then
        some ⟨located.holder, port, by subst same; exact found⟩
      else none
  | none => none

/-- The copies of an agreement at the agreement's type. -/
@[expose] def elaborateCopies (ports : List Located) (type : Ty) : List Nat → Option (List (Copy ports type))
  | [] => some []
  | port :: rest =>
      match elaborateCopy ports type port, elaborateCopies ports type rest with
      | some copy, some copies => some (copy :: copies)
      | _, _ => none

/-- An agreement has the type of its first port. -/
@[expose] def elaborateAgreement (ports : List Located) : List Nat → Option (Agreement ports)
  | [] => none
  | first :: rest =>
      match ports[first]? with
      | some located =>
          match elaborateCopy ports located.type first, elaborateCopies ports located.type rest with
          | some copy, some copies => some ⟨located.type, copy, copies⟩
          | _, _ => none
      | none => none

/-- The agreements over one list of ports: those of the raw list on the given side. -/
@[expose] def elaborateSide (ports : List Located) (overOutputs : Bool) :
    List Raw.Agreement → Option (List (Agreement ports))
  | [] => some []
  | agreement :: rest =>
      match elaborateSide ports overOutputs rest with
      | some later =>
          if agreement.overOutputs = overOutputs then
            match elaborateAgreement ports agreement.ports with
            | some first => some (first :: later)
            | none => none
          else some later
      | none => none

@[expose] def elaborateAgreements (inputs outputs : List Located) (agreements : List Raw.Agreement) :
    Option (Agreements inputs outputs) :=
  match elaborateSide inputs false agreements, elaborateSide outputs true agreements with
  | some overInputs, some overOutputs => some ⟨overInputs, overOutputs⟩
  | _, _ => none

/-! ## Definitions, programs and packages -/

/-- The header of a raw function: its types read in the type table. -/
@[expose] def Raw.Function.header (typeTable : TypeTable) (function : Raw.Function) :
    Option FunctionHeader :=
  match Ty.fillAll typeTable function.inputs, Ty.fillAll typeTable function.outputs with
  | some inputs, some outputs => some ⟨inputs, outputs, function.specificationOnly⟩
  | _, _ => none

@[expose] def elaborateFunction (typeTable : TypeTable) {operations : List OperationSignature}
    {functions : List FunctionHeader} (rows : Scope operations) (callees : Scope functions)
    (header : FunctionHeader) (body : Raw.LocalRegion) :
    Except Refusal (FunctionDefinition operations functions header) :=
  match elaborateLocalRegion typeTable rows callees (!header.specificationOnly)
      (bindAll [] header.inputs) (Scope.empty.bindAll header.inputs) header.outputs body with
  | .ok body => .ok ⟨body⟩
  | .error refusal => .error refusal

@[expose] def elaborateProtocol (typeTable : TypeTable) {operations : List OperationSignature}
    {functions : List FunctionHeader} {protocols : List ProtocolHeader} (rows : Scope operations)
    (callees : Scope functions) (applied : Scope protocols) (protocol : Raw.Protocol) :
    Except Refusal
      ((header : ProtocolHeader) × ProtocolDefinition operations functions protocols header) :=
  match Located.fillAll typeTable protocol.inputs, Located.fillAll typeTable protocol.outputs with
  | some inputs, some outputs =>
      match elaborateAgreements inputs outputs protocol.agreements with
      | some agreements =>
          match elaborateProtocolRegion typeTable rows callees applied (!protocol.specificationOnly)
              (bindAll [] inputs) (Scope.empty.bindAll inputs) outputs protocol.body with
          | .ok body =>
              .ok ⟨⟨protocol.roles, inputs, outputs, agreements, protocol.specificationOnly⟩, ⟨body⟩⟩
          | .error refusal => .error refusal
      | none => .error (.of .agreement)
  | _, _ => .error (.of .declaration)

/-- The functions elaborated so far, with their headers and the scope of the headers. -/
structure FunctionsElaborated (typeTable : TypeTable) (operations : List OperationSignature) where
  headers : List FunctionHeader
  scope : Scope headers
  functions : Functions typeTable operations headers

/-- Extend the functions by the remaining raw ones, each checked for residual
violations. -/
@[expose] def elaborateFunctions (typeTable : TypeTable) {operations : List OperationSignature}
    (rows : Scope operations) :
    List Raw.Function → FunctionsElaborated typeTable operations →
      Except Refusal (FunctionsElaborated typeTable operations)
  | [], state => .ok state
  | function :: rest, ⟨headers, scope, functions⟩ =>
      match function.header typeTable with
      | none => .error ((Refusal.of .declaration).within (.function headers.length))
      | some header =>
          match function.body with
          | some body =>
              match elaborateFunction typeTable rows scope header body with
              | .ok definition =>
                  match wellFormed : definition.violation typeTable with
                  | none =>
                      elaborateFunctions typeTable rows rest
                        ⟨header :: headers, scope.push header, .snoc functions definition wellFormed⟩
                  | some violation =>
                      .error ((Refusal.of (.residual violation)).within
                        (.function headers.length))
              | .error refusal => .error (refusal.within (.function headers.length))
          | none =>
              -- A function known by its header only: the types of its signature are decided.
              if named : (Ty.allNamed typeTable header.inputs &&
                  Ty.allNamed typeTable header.outputs) = true then
                elaborateFunctions typeTable rows rest
                  ⟨header :: headers, scope.push header, .opaque functions header named⟩
              else .error ((Refusal.of (.residual .nominalRow)).within (.function headers.length))

/-- The protocols elaborated so far. -/
structure ProtocolsElaborated (typeTable : TypeTable) (operations : List OperationSignature)
    (functions : List FunctionHeader) where
  headers : List ProtocolHeader
  scope : Scope headers
  protocols : Protocols typeTable operations functions headers

@[expose] def elaborateProtocols (typeTable : TypeTable) {operations : List OperationSignature}
    {functions : List FunctionHeader} (rows : Scope operations) (callees : Scope functions) :
    List Raw.Protocol → ProtocolsElaborated typeTable operations functions →
      Except Refusal (ProtocolsElaborated typeTable operations functions)
  | [], state => .ok state
  | protocol :: rest, ⟨headers, scope, protocols⟩ =>
      match elaborateProtocol typeTable rows callees scope protocol with
      | .ok ⟨header, definition⟩ =>
          match wellFormed : definition.violation typeTable with
          | none =>
              elaborateProtocols typeTable rows callees rest
                ⟨header :: headers, scope.push header, .snoc protocols definition wellFormed⟩
          | some violation =>
              .error ((Refusal.of (.residual violation)).within (.protocol headers.length))
      | .error refusal => .error (refusal.within (.protocol headers.length))

/-- The role counts of protocols, in program order. -/
def roleCounts (protocols : List ProtocolHeader) : List Nat :=
  (protocols.map (·.roles)).reverse

/-- A typed package: the tables, the program over the signatures of the operation
table, and the names. The tables and the names satisfy their residual conditions. -/
structure Typed where
  types : List CatalogueRow
  records : List RecordDeclaration
  variants : List VariantDeclaration
  table : List Operation
  functions : List FunctionHeader
  protocols : List ProtocolHeader
  program : Program (typeTableOf types records variants) (table.map (·.signature)) functions
    protocols
  names : Option Raw.Names
  tablesFormed : tablesViolation types records variants table = none
  namesFormed : namesViolation names functions.length (roleCounts protocols) = none

/-! ## Tables -/

/-- A static argument with its type read in the type table. -/
@[expose] def Static.fill (typeTable : TypeTable) : Static → Option Static
  | .type given =>
      match Ty.fill typeTable given with
      | some filled => some (.type filled)
      | none => none
  | .domain name => some (.domain name)
  | .nat value => some (.nat value)

/-- Every entry of a list, each by `fill`. -/
@[expose] def fillEach {α : Type} (fill : α → Option α) : List α → Option (List α)
  | [] => some []
  | entry :: rest =>
      match fill entry, fillEach fill rest with
      | some entry, some rest => some (entry :: rest)
      | _, _ => none

/-- A catalogue row with the types of its static arguments read in the type table. -/
@[expose] def CatalogueRow.fill (typeTable : TypeTable) (row : CatalogueRow) : Option CatalogueRow :=
  match fillEach (Static.fill typeTable) row.statics with
  | some statics => some ⟨row.name, statics⟩
  | none => none

/-- A row of the operation table with its types read in the type table. -/
@[expose] def Operation.fill (typeTable : TypeTable) (row : Operation) : Option Operation :=
  match row.identity.fill typeTable, Ty.fillAll typeTable row.signature.inputs,
      Ty.fillAll typeTable row.signature.outputs with
  | some identity, some inputs, some outputs => some ⟨identity, ⟨inputs, outputs, row.signature.kind⟩⟩
  | _, _, _ => none

/-- Elaboration: the typed package of a raw one, or the reason it has none. The types of
the tables are read in the type table first; the declarations carry their shapes. -/
@[expose] def elaborate (raw : Raw.Package) : Except Refusal Typed :=
  let reading := typeTableOf raw.types raw.records raw.variants
  match fillEach (CatalogueRow.fill reading) raw.types,
      fillEach (Operation.fill reading) raw.operations with
  | some types, some operations =>
      match tablesFormed : tablesViolation types raw.records raw.variants operations with
      | some violation => .error (.of (.residual violation))
      | none =>
          match elaborateFunctions (typeTableOf types raw.records raw.variants)
              (tableScope (operations.map (·.signature))) raw.functions ⟨[], .empty, .nil⟩ with
          | .error refusal => .error refusal
          | .ok ⟨functions, callees, typedFunctions⟩ =>
              match elaborateProtocols (typeTableOf types raw.records raw.variants)
                  (tableScope (operations.map (·.signature))) callees raw.protocols
                  ⟨[], .empty, .nil⟩ with
              | .error refusal => .error refusal
              | .ok ⟨protocols, _, typedProtocols⟩ =>
                  match namesFormed : namesViolation raw.names functions.length
                      (roleCounts protocols) with
                  | some violation => .error (.of (.residual violation))
                  | none =>
                      .ok ⟨types, raw.records, raw.variants, operations, functions, protocols,
                        ⟨typedFunctions, typedProtocols⟩, raw.names, tablesFormed, namesFormed⟩
  | _, _ => .error (.of .declaration)

/-- Elaboration of a program as written: its sites are also numbered without gaps. -/
@[expose] def elaborateWritten (raw : Raw.Package) : Except Refusal Typed :=
  match elaborate raw with
  | .ok typed => cond typed.program.dense (.ok typed) (.error (.of (.residual .siteGap)))
  | .error refusal => .error refusal

/-- The type table of a typed package. -/
@[expose, reducible] def Typed.typeTable (typed : Typed) : TypeTable :=
  typeTableOf typed.types typed.records typed.variants

/-- The typed package of a raw package that elaboration accepts. -/
def Typed.ofRaw (raw : Raw.Package) (accepted : (elaborate raw).isOk = true) : Typed :=
  match elaborate raw, accepted with
  | .ok typed, _ => typed

end Zkc.Core
