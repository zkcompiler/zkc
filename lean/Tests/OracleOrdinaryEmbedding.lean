module

public import Zkc.Source.Structured.ProtocolEmbeddingCheck
meta import Zkc.Source.Structured.ProtocolEmbeddingCheck
public import Zkc.Source.KernelRfl
public import Tests.IndexServices
meta import Tests.IndexServices

@[expose] public section

/-! Specialization on exact source-generated tiny index-service snapshots. Every
statement quantifies over the actual ABI, all optional inputs and every role.
No randomness, completeness, delivery or provider honesty is assumed. -/

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace Tests.OracleOrdinaryEmbedding
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.ProtocolEmbedding

namespace Scalar
abbrev snapshot := Tests.IndexServices.Scalar.Source.snapshot

abbrev program := Tests.IndexServices.Scalar.program
abbrev imported := Tests.IndexServices.Scalar.imported

theorem source_admitted : Structured.check snapshot = .ok program :=
  Tests.IndexServices.Scalar.source_admitted

theorem all_inputs (source : OrdinarySource snapshot) (model : DomainModel) (self : Nat)
    (inputs : Values (Component model.Value) source.imported.program.payload.entry.inputs) :
    (source.imported.program.oracleParticipant model self
      (ProtocolValue.embedComponents inputs)).interpret (eraseInternal model.toCarriers) =
      ((source.imported.program.participantOn model self inputs).interpret
        (OracleProtocol.actions model)).bind
          (fun result ↦ .done (ProtocolValue.embedComponents result)) :=
  source.embedding model self inputs

end Scalar

namespace Block
abbrev snapshot := Tests.IndexServices.Block.Source.snapshot

abbrev program := Tests.IndexServices.Block.program
abbrev imported := Tests.IndexServices.Block.imported

theorem source_admitted : Structured.check snapshot = .ok program :=
  Tests.IndexServices.Block.source_admitted

theorem all_inputs (source : OrdinarySource snapshot) (model : DomainModel) (self : Nat)
    (inputs : Values (Component model.Value) source.imported.program.payload.entry.inputs) :
    (source.imported.program.oracleParticipant model self
      (ProtocolValue.embedComponents inputs)).interpret (eraseInternal model.toCarriers) =
      ((source.imported.program.participantOn model self inputs).interpret
        (OracleProtocol.actions model)).bind
          (fun result ↦ .done (ProtocolValue.embedComponents result)) :=
  source.embedding model self inputs

end Block

namespace Local
abbrev snapshot := Tests.IndexServices.Local.Source.snapshot

abbrev program := Tests.IndexServices.Local.program
abbrev imported := Tests.IndexServices.Local.imported

theorem source_admitted : Structured.check snapshot = .ok program :=
  Tests.IndexServices.Local.source_admitted

theorem all_inputs (source : OrdinarySource snapshot) (model : DomainModel) (self : Nat)
    (inputs : Values (Component model.Value) source.imported.program.payload.entry.inputs) :
    (source.imported.program.oracleParticipant model self
      (ProtocolValue.embedComponents inputs)).interpret (eraseInternal model.toCarriers) =
      ((source.imported.program.participantOn model self inputs).interpret
        (OracleProtocol.actions model)).bind
          (fun result ↦ .done (ProtocolValue.embedComponents result)) :=
  source.embedding model self inputs

end Local

namespace Repeated
abbrev snapshot := Tests.IndexServices.Repeated.Source.snapshot

abbrev program := Tests.IndexServices.Repeated.program
abbrev imported := Tests.IndexServices.Repeated.imported

theorem source_admitted : Structured.check snapshot = .ok program :=
  Tests.IndexServices.Repeated.source_admitted

theorem all_inputs (source : OrdinarySource snapshot) (model : DomainModel) (self : Nat)
    (inputs : Values (Component model.Value) source.imported.program.payload.entry.inputs) :
    (source.imported.program.oracleParticipant model self
      (ProtocolValue.embedComponents inputs)).interpret (eraseInternal model.toCarriers) =
      ((source.imported.program.participantOn model self inputs).interpret
        (OracleProtocol.actions model)).bind
          (fun result ↦ .done (ProtocolValue.embedComponents result)) :=
  source.embedding model self inputs

end Repeated

private def run : IO Unit := do
  for snapshot in [Scalar.snapshot, Block.snapshot, Local.snapshot, Repeated.snapshot] do
    let .ok _ := checkOrdinarySource snapshot
      | throw (IO.userError "generated exact source did not produce an ordinary embedding witness")
  IO.println "oracle-ordinary-embedding: four exact generated sources certified"

#eval run
end Tests.OracleOrdinaryEmbedding
