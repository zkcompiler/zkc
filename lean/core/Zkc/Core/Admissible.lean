module

public import Zkc.Core.NormalProtocol
public import Zkc.Core.ProtocolFactsProject

public section

/-! The check of facts on the normal form.

A program is *admissible* when the normal form of every body (`Region.normal`: blocks
removed, nested regions opened, equal applications shared) passes the check of facts. The
check and its soundness proof are those of `Facts`, `ProtocolFacts` and their soundness
modules, unchanged; the normal form has the denotation of the body as written
(`Region.normal_denote`), so what the check guarantees of the normal form holds of the body
as written.

For a model that satisfies the domain laws of its restricted rows, every function, every
protocol at every side and every role program of an admissible program never stops
`undefined`.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader}

/-! ## Normal forms of definitions -/

/-- The normal form of a function. -/
@[expose] def FunctionDefinition.normal {header : FunctionHeader}
    (definition : FunctionDefinition operations functions header) :
    FunctionDefinition operations functions header :=
  ⟨definition.body.normal localNormalizer⟩

/-- The normal form of a protocol. -/
@[expose] def ProtocolDefinition.normal {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header) :
    ProtocolDefinition operations functions protocols header :=
  ⟨definition.body.normal protocolNormalizer⟩

/-- The normal form of a function passes the check of facts. -/
@[expose] def FunctionDefinition.admissible {header : FunctionHeader}
    (definition : FunctionDefinition operations functions header) : Bool :=
  definition.normal.justified

/-- The normal form of a protocol passes the check of facts. -/
@[expose] def ProtocolDefinition.admissible {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header) : Bool :=
  definition.normal.justified

/-- The normal form of every function passes the check of facts. A function known by its
header only has no body to check. -/
@[expose] def Functions.admissible {typeTable : TypeTable} :
    {functions : List FunctionHeader} → Functions typeTable operations functions → Bool
  | _, .nil => true
  | _, .snoc earlier definition _ => earlier.admissible && definition.admissible
  | _, .opaque earlier _ _ => earlier.admissible

/-- The normal form of every protocol passes the check of facts. -/
@[expose] def Protocols.admissible {typeTable : TypeTable} :
    {protocols : List ProtocolHeader} → Protocols typeTable operations functions protocols → Bool
  | _, .nil => true
  | _, .snoc earlier definition _ => earlier.admissible && definition.admissible

/-- The normal form of every body of a program passes the check of facts. -/
@[expose] def Program.admissible {typeTable : TypeTable}
    (program : Program typeTable operations functions protocols) : Bool :=
  program.functions.admissible && program.protocols.admissible

/-- An application that is not justified in the normal form, placed in the body as written:
the path of the instruction as written. What is found at no instruction (the way a region
ends) has the empty path: a path of the normal form names another instruction of the body as
written, or none. -/
@[expose] def Unjustified.placed (origins : List Trace) (unjustified : Unjustified) : Unjustified :=
  match Trace.written origins unjustified.path with
  | some path => { unjustified with path }
  | none => { unjustified with path := [] }

/-- The first application of a function's normal form that is not justified, at its path in
the body as written. -/
@[expose] def FunctionDefinition.inadmissible {header : FunctionHeader}
    (definition : FunctionDefinition operations functions header) : Option Unjustified :=
  definition.normal.unjustified.map
    (Unjustified.placed (definition.body.origins localNormalizer Tracer.none))

/-- The first application of a protocol's normal form that is not justified, at its path in
the body as written. -/
@[expose] def ProtocolDefinition.inadmissible {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header) : Option Unjustified :=
  definition.normal.unjustified.map
    (Unjustified.placed (definition.body.origins protocolNormalizer protocolTracer))

/-- The functions whose normal form does not pass, by their numbers in program order, each
with the first application of its normal form that is not justified, at its path in the body
as written. -/
@[expose] def Functions.inadmissible {typeTable : TypeTable} :
    {functions : List FunctionHeader} → Functions typeTable operations functions →
      List (Nat × Unjustified)
  | _, .nil => []
  | _, .snoc (functions := functions) earlier definition _ =>
      earlier.inadmissible ++
        match definition.inadmissible with
        | some unjustified => [(functions.length, unjustified)]
        | none => []
  | _, .opaque earlier _ _ => earlier.inadmissible

/-- The protocols whose normal form does not pass, by their numbers in program order, each
with the first application of its normal form that is not justified. -/
@[expose] def Protocols.inadmissible {typeTable : TypeTable} :
    {protocols : List ProtocolHeader} → Protocols typeTable operations functions protocols →
      List (Nat × Unjustified)
  | _, .nil => []
  | _, .snoc (protocols := protocols) earlier definition _ =>
      earlier.inadmissible ++
        match definition.inadmissible with
        | some unjustified => [(protocols.length, unjustified)]
        | none => []

/-! ## The guarantee for the body as written -/

variable {model : Model}

/-- A function whose normal form passes the check of facts never stops `undefined`, as
written. -/
theorem FunctionDefinition.neverUndefined_of_admissible (laws : model.DomainLaws operations)
    {table : FunctionTable model functions} (defined : DefinedTable table)
    (quiet : QuietTable table) {header : FunctionHeader}
    (definition : FunctionDefinition operations functions header)
    (passes : definition.admissible = true) (arguments : Values model.Value header.inputs) :
    NeverStops .undefined (definition.meaning model table arguments) := by
  have safe := definition.normal.neverUndefined laws defined passes arguments
  unfold FunctionDefinition.meaning FunctionDefinition.normal at safe
  rw [Region.normal_denote (localNormalizer_sound quiet)] at safe
  exact safe

/-- The functions of a program whose normal forms all pass the check of facts never stop
`undefined`. -/
theorem Functions.table_defined_of_admissible (laws : model.DomainLaws operations)
    {typeTable : TypeTable} :
    ∀ {functions : List FunctionHeader} (program : Functions typeTable operations functions),
      program.admissible = true → DefinedTable (program.table model)
  | _, .nil, _ => fun callee => callee.elimNil
  | _, .snoc earlier definition wellFormed, passes => by
      have both : earlier.admissible = true ∧ definition.admissible = true :=
        Bool.and_eq_true_iff.mp passes
      intro callee
      exact Var.cases
        (motive := fun header callee => ∀ arguments : Values model.Value header.inputs,
          NeverStops (I := Effects model) (A := Values model.Value header.outputs) .undefined
            (Values.get ((Functions.snoc earlier definition wellFormed).table model) callee
              arguments))
        (fun arguments => definition.neverUndefined_of_admissible laws
          (Functions.table_defined_of_admissible laws earlier both.1)
          (Functions.table_quiet earlier) both.2 arguments)
        (fun callee => Functions.table_defined_of_admissible laws earlier both.1 callee) callee
  | _, .opaque earlier other named, passes => by
      intro callee
      exact Var.cases
        (motive := fun header callee => ∀ arguments : Values model.Value header.inputs,
          NeverStops (I := Effects model) (A := Values model.Value header.outputs) .undefined
            (Values.get ((Functions.opaque earlier other named).table model) callee arguments))
        (fun arguments => partialProcess_neverStops _)
        (fun callee => Functions.table_defined_of_admissible laws earlier passes callee) callee

/-- A protocol whose normal form passes the check of facts never stops `undefined`, as
written, at every side. -/
theorem ProtocolDefinition.neverUndefined_of_admissible (laws : model.DomainLaws operations)
    {functionTable : FunctionTable model functions} (defined : DefinedTable functionTable)
    (quiet : QuietTable functionTable) {table : ProtocolTable model protocols}
    (earlier : DefinedProtocols table) {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header)
    (passes : definition.admissible = true) (identity : Nat) (path : List Nat) (side : Side)
    (arguments : Values (SideValue model side) header.inputs) :
    NeverStops .undefined
      (definition.meaning model functionTable table identity path side arguments) := by
  have safe := definition.normal.neverUndefined laws defined earlier passes identity path side
    arguments
  unfold ProtocolDefinition.meaning ProtocolDefinition.normal at safe
  rw [Region.normal_denote (protocolNormalizer_sound quiet table (ownSites identity path) side)]
    at safe
  exact safe

/-- The protocols of a program whose normal forms all pass the check of facts, over functions
that never stop `undefined` and perform no effect, never stop `undefined`. -/
theorem Protocols.table_defined_of_admissible (laws : model.DomainLaws operations)
    {typeTable : TypeTable} {functionTable : FunctionTable model functions}
    (defined : DefinedTable functionTable) (quiet : QuietTable functionTable)
    (identities : Identities) :
    ∀ {protocols : List ProtocolHeader}
      (program : Protocols typeTable operations functions protocols),
      program.admissible = true → DefinedProtocols (program.table model functionTable identities)
  | _, .nil, _ => fun callee => callee.elimNil
  | _, .snoc earlier definition wellFormed, passes => by
      have both : earlier.admissible = true ∧ definition.admissible = true :=
        Bool.and_eq_true_iff.mp passes
      intro callee
      exact Var.cases
        (motive := fun header callee => ∀ (path : List Nat) (side : Side)
          (arguments : Values (SideValue model side) header.inputs),
          NeverStops (I := Effects model) (A := Values (SideValue model side) header.outputs)
            .undefined
            (Values.get ((Protocols.snoc earlier definition wellFormed).table model functionTable
              identities) callee path side arguments))
        (fun path side arguments => definition.neverUndefined_of_admissible laws defined quiet
          (Protocols.table_defined_of_admissible laws defined quiet identities earlier both.1)
          both.2 _ path side arguments)
        (fun callee =>
          Protocols.table_defined_of_admissible laws defined quiet identities earlier both.1 callee)
        callee

section Programs

variable {typeTable : TypeTable}

/-- Every function of an admissible program never stops `undefined`. -/
theorem Program.never_undefined_of_admissible (laws : model.DomainLaws operations)
    (program : Program typeTable operations functions protocols)
    (passes : program.admissible = true) {header : FunctionHeader}
    (callee : Var functions header) (arguments : Values model.Value header.inputs) :
    NeverStops .undefined ((program.functionTable model).get callee arguments) :=
  Functions.table_defined_of_admissible laws program.functions
    (Bool.and_eq_true_iff.mp passes).1 callee arguments

/-- Every protocol of an admissible program never stops `undefined`, under any path, for any
side, on any values, whatever the replies of its effects. -/
theorem Program.protocols_never_undefined_of_admissible (laws : model.DomainLaws operations)
    (program : Program typeTable operations functions protocols)
    (passes : program.admissible = true) (identities : Identities) {header : ProtocolHeader}
    (callee : Var protocols header) (path : List Nat) (side : Side)
    (arguments : Values (SideValue model side) header.inputs) :
    NeverStops .undefined
      ((program.protocolTable model identities).get callee path side arguments) :=
  Protocols.table_defined_of_admissible laws
    (Functions.table_defined_of_admissible laws program.functions
      (Bool.and_eq_true_iff.mp passes).1)
    (Functions.table_quiet program.functions) identities program.protocols
    (Bool.and_eq_true_iff.mp passes).2 callee path side arguments

/-- The program of a role of a protocol of an admissible program never stops `undefined`,
under any path and on any arguments, whatever the replies of its effects. -/
theorem Program.role_never_undefined_of_admissible (laws : model.DomainLaws operations)
    (program : Program typeTable operations functions protocols)
    (passes : program.admissible = true) (identities : Identities)
    (projected : Projected operations functions protocols)
    (projects : projectProtocols program.protocols = .ok projected) {header : ProtocolHeader}
    (callee : Var protocols header) (role : Nat)
    (calling : Var projected.headers (roleHeader role header))
    (named : projected.callees.find callee role = some calling) (path : List Nat)
    (arguments : Values model.Value (roleHeader role header).inputs) :
    NeverStops .undefined
      ((projected.programs.table model (program.functionTable model) identities).get calling path
        arguments) := by
  have held : NeverStops .undefined
      ((projected.programs.table model (program.functionTable model) identities).get calling path
        (ownValues model (single role) role (Side.single_inside role) header.inputs
          (onlyValues model role header.inputs arguments))) := by
    rw [(projectProtocols_sound (functionTable := program.functionTable model) identities
      program.protocols projected projects).program callee role calling named path (single role)
      (Side.only_single role header.roles) (Side.single_inside role)
      (onlyValues model role header.inputs arguments)]
    exact NeverStops.bind
      (Program.protocols_never_undefined_of_admissible laws program passes identities callee path
        (single role) (onlyValues model role header.inputs arguments))
      fun _ => NeverStops.done _ _
  rw [ownValues_onlyValues] at held
  exact held

end Programs

end Zkc.Core
