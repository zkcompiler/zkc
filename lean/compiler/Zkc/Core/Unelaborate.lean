module

public import Zkc.Core.Elaborate

public section

/-! The raw syntax of a typed term, by structural recursion on the term.

The number of a value is its position in binding order: in a context of depth `d` the
reference at position `i` is value `d - 1 - i`. A function or protocol is numbered the
same way among the functions or protocols before the definition that names it.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- The raw form of a typed literal: the numbers of a `fin` literal and of the bytes. -/
@[expose] def unelaborateLiteral : Literal → Raw.Literal
  | .nat value => .nat value
  | .bool value => .bool value
  | .fin bound value => .fin bound value.val
  | .nominal row data => .nominal row data
  | .bytes data => .bytes (data.map Fin.val)

/-- The raw form of an operation the core owns: positions as numbers, types stripped, a
record or a variant by its declaration. -/
@[expose] def unelaborateBuiltin : Builtin → Raw.Builtin
  | .natAdd => .natAdd
  | .natMul => .natMul
  | .natPow => .natPow
  | .natEqual => .natEqual
  | .natLess => .natLess
  | .natSub => .natSub
  | .natDiv => .natDiv
  | .natRem => .natRem
  | .boolAnd => .boolAnd
  | .boolOr => .boolOr
  | .boolNot => .boolNot
  | .boolEqual => .boolEqual
  | .seqLength element size => .seqLength element.strip size
  | .seqAt element size => .seqAt element.strip size
  | .seqSlice element size result => .seqSlice element.strip size result
  | .seqConcat element left right => .seqConcat element.strip left right
  | .seqFill element count => .seqFill element.strip count
  | .seqMake element count => .seqMake element.strip count
  | .seqSized element size => .seqSized element.strip size
  | .seqUnsized element size => .seqUnsized element.strip size
  | .natBelow bound => .natBelow bound
  | .finToNat bound => .finToNat bound
  | .finWiden bound wider _ => .finWiden bound wider
  | .tupleMake components => .tupleMake (Ty.stripAll components)
  | .tupleGet components _ position => .tupleGet (Ty.stripAll components) position.index
  | .recordMake declaration _ _ => .recordMake declaration
  | .recordGet declaration _ _ _ position => .recordGet declaration position.index
  | .variantMake declaration _ _ position => .variantMake declaration position.index

section Local

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool}

/-- A local operation with the numbers of its operands and its nested raw regions.
`functionCount` is the number of functions the operation may call. -/
@[expose] def unelaborateLocalStep (functionCount : Nat) :
    LocalOp operations functions deployed → List Nat → List Raw.LocalRegion → Raw.LocalStep
  | .op row _, operands, _ => .op row.index operands
  | .call callee _, operands, _ => .call (Scope.number functionCount callee) operands
  | .conditional _ outputs, condition :: captures, [onTrue, onFalse] =>
      .conditional condition captures (Ty.stripAll outputs) onTrue onFalse
  | .match declaration _ _ outputs, value :: captures, arms =>
      .match declaration value captures (Ty.stripAll outputs) (.ofList arms)
  | .loop (.static count) carried collected _, operands, [body] =>
      .loop (.static count) (operands.take carried.length) (operands.drop carried.length)
        (Ty.stripAll collected) body
  | .loop (.runtime maximum) carried collected _, count :: rest, [body] =>
      .loop (.runtime maximum count) (rest.take carried.length) (rest.drop carried.length)
        (Ty.stripAll collected) body
  | .guard reason, [condition], _ => .guard reason condition
  | .literal value, _, _ => .literal (unelaborateLiteral value)
  | .builtin operation, operands, _ => .builtin (unelaborateBuiltin operation) operands
  | _, _, _ => .guard .abort 0

mutual
  /-- A local region in a context of the given depth. -/
  @[expose] def unelaborateLocalRegion (functionCount : Nat) {Γ out : List Ty} (depth : Nat) :
      Region (LocalDialect operations functions deployed) Γ out → Raw.LocalRegion
    | .ret values => .ret (Scope.numbers depth values)
    | .stop reason => .stop reason
    | .letOp op arguments bodies rest =>
        .step (unelaborateLocalStep functionCount op (Scope.numbers depth arguments)
            (unelaborateLocalRegions functionCount bodies))
          (unelaborateLocalRegion functionCount (depth + (LocalOp.results op).length) rest)
    | .bind (mid := mid) body rest =>
        .block (Ty.stripAll mid) (unelaborateLocalRegion functionCount depth body)
          (unelaborateLocalRegion functionCount (depth + mid.length) rest)

  @[expose] def unelaborateLocalRegions (functionCount : Nat) {signatures : List (List Ty × List Ty)} :
      Regions (LocalDialect operations functions deployed) signatures → List Raw.LocalRegion
    | .nil => []
    | .cons (inputs := inputs) body tail =>
        unelaborateLocalRegion functionCount inputs.length body ::
          unelaborateLocalRegions functionCount tail
end

end Local

section Protocol

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}

/-- A protocol operation. `protocolCount` is the number of protocols it may apply. -/
@[expose] def unelaborateProtocolStep (functionCount protocolCount : Nat) :
    ProtocolOp operations functions protocols deployed → List Nat → List Raw.ProtocolRegion →
      Raw.ProtocolStep
  | .at role op bodies, operands, _ =>
      .at role (unelaborateLocalStep functionCount op operands
        (unelaborateLocalRegions functionCount bodies))
  | .exchange sender receiver site _, [value], _ => .exchange sender receiver site value
  | .draw owner receivers site law _, operands, _ => .draw owner receivers site law.index operands
  | .sample owner site law _, operands, _ => .sample owner site law.index operands
  | .repeat participants (.static number) carried collected _ _, operands, [body] =>
      .repeat participants (.static number) (operands.take carried.length)
        (operands.drop carried.length) (Located.stripAll collected) body
  | .repeat participants (.runtime maximum) carried collected _ _, operands, [body] =>
      .repeat participants (.runtime maximum (operands.take participants.length))
        ((operands.drop participants.length).take carried.length)
        ((operands.drop participants.length).drop carried.length) (Located.stripAll collected)
        body
  | .choose participants tag _ outputs _, operands, arms =>
      .choose participants (operands.take participants.length) tag.strip
        (operands.drop participants.length) (Located.stripAll outputs) (.ofList arms)
  | .apply callee roleMap site _, operands, _ =>
      .apply (Scope.number protocolCount callee) roleMap site operands
  | _, _, _ => .exchange 0 0 0 0

mutual
  @[expose] def unelaborateProtocolRegion (functionCount protocolCount : Nat) {Γ out : List Located}
      (depth : Nat) :
      Region (ProtocolDialect operations functions protocols deployed) Γ out → Raw.ProtocolRegion
    | .ret values => .ret (Scope.numbers depth values)
    | .stop reason => .stop reason
    | .letOp op arguments bodies rest =>
        .step (unelaborateProtocolStep functionCount protocolCount op
            (Scope.numbers depth arguments)
            (unelaborateProtocolRegions functionCount protocolCount bodies))
          (unelaborateProtocolRegion functionCount protocolCount
            (depth + (ProtocolOp.results op).length) rest)
    | .bind (mid := mid) body rest =>
        .block (Located.stripAll mid) (unelaborateProtocolRegion functionCount protocolCount depth body)
          (unelaborateProtocolRegion functionCount protocolCount (depth + mid.length) rest)

  @[expose] def unelaborateProtocolRegions (functionCount protocolCount : Nat)
      {signatures : List (List Located × List Located)} :
      Regions (ProtocolDialect operations functions protocols deployed) signatures →
        List Raw.ProtocolRegion
    | .nil => []
    | .cons (inputs := inputs) body tail =>
        unelaborateProtocolRegion functionCount protocolCount inputs.length body ::
          unelaborateProtocolRegions functionCount protocolCount tail
end

end Protocol

@[expose] def unelaborateAgreement {ports : List Located} (overOutputs : Bool) (agreement : Agreement ports) :
    Raw.Agreement :=
  ⟨overOutputs, agreement.copies.map (·.port.index)⟩

@[expose] def unelaborateSide {ports : List Located} (overOutputs : Bool)
    (agreements : List (Agreement ports)) : List Raw.Agreement :=
  agreements.map (unelaborateAgreement overOutputs)

/-- The agreements over the inputs, then those over the outputs. -/
@[expose] def unelaborateAgreements {inputs outputs : List Located} (agreements : Agreements inputs outputs) :
    List Raw.Agreement :=
  unelaborateSide false agreements.inputs ++ unelaborateSide true agreements.outputs

/-- A function that may call `functionCount` functions. -/
@[expose] def unelaborateFunction {operations : List OperationSignature} {functions : List FunctionHeader}
    (functionCount : Nat) {header : FunctionHeader}
    (definition : FunctionDefinition operations functions header) : Raw.Function :=
  ⟨header.specificationOnly, Ty.stripAll header.inputs, Ty.stripAll header.outputs,
    some (unelaborateLocalRegion functionCount header.inputs.length definition.body)⟩

/-- A function known by its header only. -/
@[expose] def unelaborateOpaque (header : FunctionHeader) : Raw.Function :=
  ⟨header.specificationOnly, Ty.stripAll header.inputs, Ty.stripAll header.outputs, none⟩

@[expose] def unelaborateProtocol {operations : List OperationSignature} {functions : List FunctionHeader}
    {protocols : List ProtocolHeader} (functionCount protocolCount : Nat) {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header) : Raw.Protocol :=
  ⟨header.specificationOnly, header.roles, Located.stripAll header.inputs,
    Located.stripAll header.outputs, unelaborateAgreements header.agreements,
    unelaborateProtocolRegion functionCount protocolCount header.inputs.length definition.body⟩

/-- The raw functions of a program, oldest first, before `later`. `count` is the number
of the functions. -/
@[expose] def unelaborateFunctions {typeTable : TypeTable} {operations : List OperationSignature} :
    {functions : List FunctionHeader} → (count : Nat) → Functions typeTable operations functions →
      List Raw.Function → List Raw.Function
  | _, _, .nil, later => later
  | _, count, .snoc earlier definition _, later =>
      unelaborateFunctions (count - 1) earlier (unelaborateFunction (count - 1) definition :: later)
  | _, count, .opaque earlier header _, later =>
      unelaborateFunctions (count - 1) earlier (unelaborateOpaque header :: later)

@[expose] def unelaborateProtocols {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} (functionCount : Nat) :
    {protocols : List ProtocolHeader} → (count : Nat) →
      Protocols typeTable operations functions protocols → List Raw.Protocol → List Raw.Protocol
  | _, _, .nil, later => later
  | _, count, .snoc earlier definition _, later =>
      unelaborateProtocols functionCount (count - 1) earlier
        (unelaborateProtocol functionCount (count - 1) definition :: later)

/-- The raw form of a static argument: its type stripped. -/
@[expose] def Static.strip : Static → Static
  | .type given => .type given.strip
  | .domain name => .domain name
  | .nat value => .nat value

/-- The raw form of a catalogue row. -/
@[expose] def CatalogueRow.strip (row : CatalogueRow) : CatalogueRow :=
  ⟨row.name, row.statics.map Static.strip⟩

/-- The raw form of a row of the operation table. -/
@[expose] def Operation.strip (row : Operation) : Operation :=
  ⟨row.identity.strip, ⟨Ty.stripAll row.signature.inputs, Ty.stripAll row.signature.outputs,
    row.signature.kind⟩⟩

@[expose] def unelaborate (typed : Typed) : Raw.Package :=
  ⟨typed.types.map CatalogueRow.strip, typed.records, typed.variants,
    typed.table.map Operation.strip,
    unelaborateFunctions typed.functions.length typed.program.functions [],
    unelaborateProtocols typed.functions.length typed.protocols.length typed.program.protocols [],
    typed.names⟩

end Zkc.Core
