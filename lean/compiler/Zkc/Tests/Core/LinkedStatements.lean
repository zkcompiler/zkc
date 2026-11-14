import Zkc.Tests.Core.Linked
import Zkc.Core.Entry
import Zkc.Core.ProjectProgramMeaning
import Zkc.Tests.Core.Check

/-! Statements about a printed package, proved from the printed declarations.

A statement about one definition names that definition's link: its typed term is
`p0.definition`, and the facts the kernel decided when the link was checked are its
fields. A statement about the package reaches a definition through the assembly, which
is a chain of constructor applications over the links: the kernel unfolds the chain and
no body. -/

set_option autoImplicit false

open Zkc.Source Zkc.Core

/-- A result that the kernel evaluates to a program has one. Only the head of the result
is evaluated. -/
theorem exists_of_isProgram {ε α : Type} (result : Except ε α)
    (isProgram : (match result with | .ok _ => true | _ => false) = true) :
    ∃ program, result = .ok program := by
  match result, isProgram with
  | .ok program, _ => exact ⟨program, rfl⟩

namespace LinkedSchnorr

/-- The protocols of the typed package are the one linked definition. -/
theorem protocols_eq :
    typed.program.protocols = Protocols.snoc Protocols.nil p0.definition p0.wellFormed :=
  rfl

/-- The body of the protocol begins with the prover's sample at site 0: the typed term
is in constructor form. -/
theorem begins_with_sample :
    ∃ next, p0.definition.body =
      Region.letOp (ProtocolOp.sample 0 0 row0 rfl) Values.nil Regions.nil next :=
  ⟨_, rfl⟩

/-- Projection gives the verifier a program. The kernel evaluates projection on this
definition alone; the protocol applies no other, so its table of callees is empty. -/
theorem verifier_projects :
    ∃ program, projectProtocol (programs := []) 1 ProjectedCallees.empty p0.definition = .ok program :=
  exists_of_isProgram _ kernel_rfl%

/-- The projection theorem at the linked definition: the verifier's program denotes the
protocol's meaning for the side that has the verifier alone. -/
theorem verifier_meaning (model : Model) (functionTable : FunctionTable model functionHeaders0)
    (identity : Nat) (path : List Nat)
    (arguments : Values (SideValue model (single 1)) ph0.inputs) :
    ∃ program : RoleProgram signatures functionHeaders0 [] (roleHeader 1 ph0),
      projectProtocol 1 ProjectedCallees.empty p0.definition = .ok program ∧
      program.body.denote (roleMeaning model functionTable .nil (ownSites identity path))
          (Environment.ofValues
            (ownValues model (single 1) 1 (Side.single_inside 1) ph0.inputs arguments)) =
        (p0.definition.meaning model functionTable .nil identity path (single 1) arguments).bind
          fun values =>
          .done (ownValues model (single 1) 1 (Side.single_inside 1) ph0.outputs values) := by
  obtain ⟨program, projects⟩ := verifier_projects
  exact ⟨program, projects,
    projectProtocol_single CalleesSound.empty p0.definition program projects identity path
      arguments⟩

/-- The statement is about the raw package: `typed` is its elaboration, and the
definition is the protocol of `typed`. -/
theorem about_the_raw_package :
    elaborate raw = .ok typed ∧
      typed.program.protocols = Protocols.snoc Protocols.nil p0.definition p0.wellFormed :=
  ⟨elaborates, protocols_eq⟩

#print axioms verifier_meaning
#print axioms about_the_raw_package

end LinkedSchnorr

namespace LinkedSumcheck

/-- The protocols of the typed package are the two linked definitions, in order. The
kernel unfolds the two steps of the assembly and no body. -/
theorem protocols_eq :
    typed.program.protocols =
      Protocols.snoc (Protocols.snoc Protocols.nil p0.definition p0.wellFormed) p1.definition
        p1.wellFormed :=
  rfl

/-- A fact that the link carries is used without evaluation. -/
theorem last_function_wellFormed : f2.definition.violation typeTable = none := f2.wellFormed

end LinkedSumcheck

/-! The raw package that the tool printed is the raw package that Lean's own run of the
reader gives for the same file. The two constants come by different routes: the tool
printed one as source, which Lean parsed and elaborated; the command `raw_package` ran
the reader in Lean and turned its value into a term. The kernel compares them. -/

namespace LinkedSchnorr

raw_package read from file "fixtures/schnorr.json"

theorem raw_is_read : raw = read := kernel_rfl%

end LinkedSchnorr

namespace LinkedSumcheck

raw_package read from file "fixtures/sumcheck.json"

theorem raw_is_read : raw = read := kernel_rfl%

end LinkedSumcheck

/-! The projection theorem at linked definitions whose entry applies another protocol: the
verifier's program of the Sumcheck entry calls the verifier's program of the round it
applies, and denotes the entry's meaning for a side whose only member among the entry's
roles is the verifier. The chain, with what checks each step:

1. `raw = read`: the raw package of the printed links is the reader's (the kernel);
2. `elaborateWritten raw = .ok typed` (the links and the round trip);
3. the protocols of `typed` are the two linked definitions (the kernel, by unfolding the
   assembly);
4. projection accepts them (the kernel evaluates it), and the statement about them. -/

namespace LinkedSumcheck

/-- The two protocols of the package, the entry last, as their linked definitions. -/
noncomputable def linkedProtocols :
    Protocols typeTable signatures functionHeaders3 protocolHeaders2 :=
  Protocols.snoc (Protocols.snoc Protocols.nil p0.definition p0.wellFormed) p1.definition
    p1.wellFormed

/-- The value of a result that is known to be one. -/
def okValue {ε α : Type} (result : Except ε α) (accepted : result.isOk = true) : α :=
  match result, accepted with
  | .ok value, _ => value

theorem okValue_eq {ε α : Type} (result : Except ε α) (accepted : result.isOk = true) :
    result = .ok (okValue result accepted) := by
  match result, accepted with
  | .ok value, _ => rfl

/-- The role programs of a program that projection accepts. -/
noncomputable def projectedOf {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} {protocols : List ProtocolHeader}
    (program : Protocols typeTable operations functions protocols)
    (accepted : (projectProtocols program).isOk = true) : Projected operations functions protocols :=
  okValue (projectProtocols program) accepted

theorem projectedOf_eq {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} {protocols : List ProtocolHeader}
    (program : Protocols typeTable operations functions protocols)
    (accepted : (projectProtocols program).isOk = true) :
    projectProtocols program = .ok (projectedOf program accepted) :=
  okValue_eq (projectProtocols program) accepted

/-- Projection accepts the two linked definitions: the kernel evaluates it on them. -/
theorem projects : (projectProtocols linkedProtocols).isOk = true := kernel_rfl%

noncomputable def projected : Projected signatures functionHeaders3 protocolHeaders2 :=
  projectedOf linkedProtocols projects

/-- The verifier of the entry has a program. -/
theorem verifier_has_program :
    (projected.callees.find (Var.here : Var protocolHeaders2 ph1) 1).isSome = true := kernel_rfl%

/-- The projection theorem at the linked definitions, for the verifier of the entry: its
program, which calls the verifier's program of the round, denotes the entry's meaning for a
side whose only member among the entry's roles is the verifier. The model, the meanings of
the functions, the side and the inputs are arbitrary. -/
theorem verifier_meaning (model : Model) (functionTable : FunctionTable model functionHeaders3)
    (identities : Identities) (path : List Nat) (side : Side) (only : side.Only 1 ph1.roles)
    (arguments : Values (SideValue model side) ph1.inputs) :
    ∃ program : Var projected.headers (roleHeader 1 ph1),
      projected.callees.find (Var.here : Var protocolHeaders2 ph1) 1 = some program ∧
      (projected.programs.table model functionTable identities).get program path
          (ownValues model side 1 (only.inside rfl) ph1.inputs arguments) =
        ((linkedProtocols.table model functionTable identities).get
            (Var.here : Var protocolHeaders2 ph1) path side arguments).bind fun values =>
          .done (ownValues model side 1 (only.inside rfl) ph1.outputs values) := by
  have sound := projectProtocols_sound (model := model) (functionTable := functionTable)
    identities linkedProtocols projected (projectedOf_eq linkedProtocols projects)
  match found : projected.callees.find (Var.here : Var protocolHeaders2 ph1) 1,
      verifier_has_program with
  | some program, _ =>
      exact ⟨program, rfl,
        sound.program Var.here 1 program found path side only (only.inside rfl) arguments⟩

/-- The statement is about the raw package: its raw package is the reader's, it elaborates
to `typed`, and the protocols of `typed` are the linked definitions. -/
theorem about_the_raw_package :
    raw = read ∧ elaborateWritten raw = .ok typed ∧ typed.program.protocols = linkedProtocols :=
  ⟨raw_is_read, elaboratesWritten, protocols_eq⟩

#print axioms verifier_meaning
#print axioms about_the_raw_package

end LinkedSumcheck

/-! The axioms of the composition theorems and of a linked package. -/

#print axioms Zkc.Core.LinkedPackage.unelaborates
#print axioms Zkc.Core.LinkedPackage.elaborates
#print axioms Zkc.Core.LinkedPackage.elaboratesWritten
#print axioms LinkedSchnorr.unelaborates
#print axioms LinkedSchnorr.elaborates
#print axioms LinkedSchnorr.elaboratesWritten
#print axioms LinkedSumcheck.elaboratesWritten
#print axioms LinkedSchnorr.p0
