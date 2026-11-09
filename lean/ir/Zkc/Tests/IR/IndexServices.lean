module

public import Zkc.Tests.IR.IndexServicesData
public import Zkc.IR.Construction.ServiceConnection
public import Zkc.IR.Source.Structured.NormalForm.Soundness
public import Zkc.Program.Source.KernelRfl
public import Zkc.IR.Construction.CatalogueAdmission

@[expose] public section

/-! Small source-backed admission, identity, routing and outcome controls.
The snapshots and both endpoints are fresh native exports of the retained
fixture, not hand-written interpreters. All service meanings remain generic. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace Tests.IndexServices
open Zkc.Source Zkc.Source.Structured Zkc.Construction

abbrev contract := "random.koala-bear.ext4-binomial3/0"
abbrev suite := "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"

namespace Scalar

def program : Program := (Structured.check Source.snapshot).toOption.get (by decide +kernel)
theorem source_admitted : Structured.check Source.snapshot = .ok program := by kernel_rfl
def imported : Imported Source.snapshot := ⟨program, source_admitted⟩
theorem input_types : program.payload.entry.inputs = [.service contract] := by kernel_rfl
def context : Context := (exportContext Source.snapshot Validator.participant).get (by decide +kernel)
def queryTemplate : Template := ⟨Source.snapshot.entry, [],
  ["query", Source.snapshot.entry, "label_706f736974696f6e", "input_0", contract, "index", "role00000001"]⟩
def messageTemplate : Template := ⟨Source.snapshot.entry, [],
  ["message", Source.snapshot.entry, "label_64656c6976657279_0", "label_64656c6976657279_0",
    "role00000001", "role00000000"]⟩
def routing (mode : Domain.Mode) : Original.Routing :=
  ⟨Source.snapshot, context, mode, 17, [messageTemplate], [queryTemplate],
    [⟨queryTemplate, messageTemplate⟩], []⟩

example : checkCompiled imported Validator.participant = .ok () := by decide +kernel
example : AuthoredPair.checkProducer program context Producer.participant = .ok () := by decide +kernel
example : SourceOccurrences.check Source.snapshot context Producer.participant = .ok () := by decide +kernel
example : Validator.participant.checkCatalogue Validator.catalogue Validator.catalogue = .ok () := by decide +kernel
example : SourceOccurrences.requestAt Source.snapshot context queryTemplate = some (.sampleIndex 8) := by decide +kernel
example : SourceDelivery.checked Source.snapshot context queryTemplate messageTemplate = true := by decide +kernel
example : (routing .validator).serviceRequest [] "label_706f736974696f6e" (.sampleIndex 8) 17 =
    some (context.query "label_706f736974696f6e" (.sampleIndex 8)) := by decide +kernel
example : (routing .validator).serviceRequest [] "label_706f736974696f6e" (.sampleIndex 7) 17 = none := by decide +kernel
example : (routing .validator).serviceRequest [] "label_706f736974696f6e" (.sampleIndex 8) 18 = none := by decide +kernel
example : (routing .producer).typedDelivery [] "label_64656c6976657279_0" .index 1 =
    some (.sampleIndex 8, context.query "label_706f736974696f6e" (.sampleIndex 8),
      context.message "label_64656c6976657279_0" 1 0) := by decide +kernel
example : (routing .producer).typedDelivery [] "label_64656c6976657279_0" .indices 1 = none := by decide +kernel
example : (routing .producer).serviceRequest [⟨"forged",0⟩] "label_706f736974696f6e" (.sampleIndex 8) 17 = none := by decide +kernel
end Scalar

namespace Block

def program : Program := (Structured.check Source.snapshot).toOption.get (by decide +kernel)
theorem source_admitted : Structured.check Source.snapshot = .ok program := by kernel_rfl
def imported : Imported Source.snapshot := ⟨program, source_admitted⟩
theorem input_types : program.payload.entry.inputs = [.service contract] := by kernel_rfl
def context : Context := (exportContext Source.snapshot Validator.participant).get (by decide +kernel)
def queryTemplate : Template := ⟨Source.snapshot.entry, [],
  ["query", Source.snapshot.entry, "label_706f736974696f6e73", "input_0", contract, "indices", "role00000001"]⟩
def messageTemplate : Template := ⟨Source.snapshot.entry, [],
  ["message", Source.snapshot.entry, "label_64656c6976657279_0", "label_64656c6976657279_0",
    "role00000001", "role00000000"]⟩
def routing (mode : Domain.Mode) : Original.Routing :=
  ⟨Source.snapshot, context, mode, 17, [messageTemplate], [queryTemplate],
    [⟨queryTemplate, messageTemplate⟩], []⟩
example : checkCompiled imported Validator.participant = .ok () := by decide +kernel
example : AuthoredPair.checkProducer program context Producer.participant = .ok () := by decide +kernel
example : SourceOccurrences.check Source.snapshot context Producer.participant = .ok () := by decide +kernel
example : SourceOccurrences.requestAt Source.snapshot context queryTemplate = some (.sampleIndices 8 3) := by decide +kernel
example : SourceDelivery.checked Source.snapshot context queryTemplate messageTemplate = true := by decide +kernel
example : (routing .validator).serviceRequest [] "label_706f736974696f6e73" (.sampleIndices 8 2) 17 = none := by decide +kernel
example : (routing .validator).serviceRequest [] "label_706f736974696f6e73" (.sampleIndices 16 3) 17 = none := by decide +kernel
example : (routing .producer).typedDelivery [] "label_64656c6976657279_0" .indices 1 =
    some (.sampleIndices 8 3, context.query "label_706f736974696f6e73" (.sampleIndices 8 3),
      context.message "label_64656c6976657279_0" 1 0) := by decide +kernel
end Block

namespace Local
def program : Program := (Structured.check Source.snapshot).toOption.get (by decide +kernel)
theorem source_admitted : Structured.check Source.snapshot = .ok program := by kernel_rfl
def imported : Imported Source.snapshot := ⟨program, source_admitted⟩
def context : Context := (exportContext Source.snapshot Validator.participant).get (by decide +kernel)
def port : ServicePort := ⟨"service_0", "role00000000", 0, 0, contract⟩
def template : Template := ⟨Source.snapshot.entry, [],
  ["query", Source.snapshot.entry, "s0", "input_0", contract, "index", "role00000000"]⟩
def verifierPort : ServicePort := ⟨"service_0", "role00000001", 1, 0, contract⟩
def verifierTemplate : Template := ⟨Source.snapshot.entry, [],
  ["query", Source.snapshot.entry, "s4", "input_1", contract, "index", "role00000001"]⟩
example : checkCompiled imported Validator.participant = .ok () := by decide +kernel
example : AuthoredPair.checkProducer program context Producer.participant = .ok () := by decide +kernel
example : SourceOccurrences.check Source.snapshot context Producer.participant = .ok () := by decide +kernel
example : SourceOccurrences.check Source.snapshot context Validator.participant = .ok () := by decide +kernel
example : SourceOccurrences.localValid Source.snapshot context port (.sampleIndex 3) template = true := by decide +kernel
example : SourceOccurrences.localValid Source.snapshot context verifierPort (.sampleIndex 3) verifierTemplate = true := by decide +kernel
example : SourceOccurrences.localValid Source.snapshot context { port with root := 2 }
    (.sampleIndex 3) template = false := by decide +kernel
example : SourceOccurrences.valid Source.snapshot context verifierTemplate = false := by decide +kernel
example : SourceOccurrences.localValid Source.snapshot context port (.sampleIndex 8) template = false := by decide +kernel
end Local

namespace Repeated
def program : Program := (Structured.check Source.snapshot).toOption.get (by decide +kernel)
theorem source_admitted : Structured.check Source.snapshot = .ok program := by kernel_rfl
def imported : Imported Source.snapshot := ⟨program, source_admitted⟩
def context : Context := (exportContext Source.snapshot Validator.participant).get (by decide +kernel)
def queryTemplate : Template := ⟨Source.snapshot.entry, [.repeat Source.snapshot.entry "s4"],
  ["query", Source.snapshot.entry, "label_706f736974696f6e", "input_0", contract, "index", "role00000001"]⟩
def routing : Original.Routing :=
  ⟨Source.snapshot, context, .validator, 17, [], [queryTemplate], [], []⟩
example : checkCompiled imported Validator.participant = .ok () := by decide +kernel
example : AuthoredPair.checkProducer program context Producer.participant = .ok () := by decide +kernel
example : SourceOccurrences.check Source.snapshot context Producer.participant = .ok () := by decide +kernel
example : SourceOccurrences.requestAt Source.snapshot context queryTemplate = some (.sampleIndex 8) := by decide +kernel
example : routing.serviceRequest [⟨"s4",1⟩] (queryTemplate.qualify "label_706f736974696f6e") (.sampleIndex 8) 17 =
    some (Domain.atCoordinates (context.query "label_706f736974696f6e" (.sampleIndex 8)) [1]) := by
  let updated := context.mapReplacement fun replacement =>
    { replacement with request := some (.sampleIndex 8) }
  have valid : SourceOccurrences.valid Source.snapshot updated queryTemplate = true := by decide +kernel
  have base : queryTemplate.origin updated =
      some (updated.query "label_706f736974696f6e" (.sampleIndex 8)) := by decide +kernel
  have dynamic : Domain.templateOrigin updated queryTemplate [1] =
      some (Domain.atCoordinates (updated.query "label_706f736974696f6e" (.sampleIndex 8)) [1]) := by kernel_rfl
  change OccurrenceResolution.resolve Source.snapshot updated
      (updated.query "label_706f736974696f6e" (.sampleIndex 8)) [⟨"s4",1⟩] [queryTemplate] = _
  have sites : SourceOccurrences.repeatSites queryTemplate = ["s4"] := by decide +kernel
  have matched : OccurrenceResolution.matchesOccurrence Source.snapshot updated
      (updated.query "label_706f736974696f6e" (.sampleIndex 8)) [⟨"s4",1⟩] queryTemplate = true := by
    unfold OccurrenceResolution.matchesOccurrence
    simp only [List.map]
    rw [valid, sites, base, dynamic]
    simp only [BEq.rfl, Bool.and_self]
  simp only [OccurrenceResolution.resolve, List.filter_cons, List.filter_nil, matched, ite_true]
  rfl
example : routing.serviceRequest [] "label_706f736974696f6e" (.sampleIndex 8) 17 = none := by decide +kernel
example : routing.serviceRequest [⟨"other",1⟩] "label_706f736974696f6e" (.sampleIndex 8) 17 = none := by decide +kernel
example : routing.serviceRequest [⟨"s4",1⟩,⟨"s4",1⟩] "label_706f736974696f6e" (.sampleIndex 8) 17 = none := by decide +kernel
end Repeated

/-- Mutation controls retain the original source and alter one independent
constructed request parameter. Matching result sorts confer no authority. -/
def changedBlockCount : Participant :=
  { Block.Producer.participant with instructions := Block.Producer.participant.instructions.map fun instruction =>
      match instruction.operation with
      | .blockChallenge suite bound _ template =>
          { instruction with operation := .blockChallenge suite bound 2 template }
      | _ => instruction }

def changedScalarBound : Participant :=
  { Scalar.Producer.participant with instructions := Scalar.Producer.participant.instructions.map fun instruction =>
      match instruction.operation with
      | .indexChallenge suite _ template =>
          { instruction with operation := .indexChallenge suite 16 template }
      | _ => instruction }

example : SourceOccurrences.check Block.Source.snapshot Block.context changedBlockCount =
    .error "construction-source-occurrence" := by decide +kernel
example : SourceOccurrences.check Scalar.Source.snapshot Scalar.context changedScalarBound =
    .error "construction-source-occurrence" := by decide +kernel

/-- These controls mutate only stored source syntax; admission and its existing
checker soundness theorem still own all interpretation. -/
def changeRoot (snapshot : Snapshot) (edit : Structured.Instruction → Structured.Instruction) : Snapshot :=
  { snapshot with definitions := snapshot.definitions.map fun
      | .function function =>
          if function.name = snapshot.entry then
            .function { function with body := match function.body with
              | .block instructions terminator => .block (instructions.map edit) terminator }
          else .function function
      | definition => definition }

def wrongScalarResult : Snapshot := changeRoot Scalar.Source.snapshot fun
  | .instruction (.sampleIndex owner contract) operands _ regions site =>
      .instruction (.sampleIndex owner contract) operands [.indices] regions site
  | instruction => instruction

def missingScalarBound : Snapshot := changeRoot Scalar.Source.snapshot fun
  | .instruction (.sampleIndex owner contract) operands results regions site =>
      .instruction (.sampleIndex owner contract) (operands.take 1) results regions site
  | instruction => instruction

def wrongScalarContract : Snapshot := changeRoot Scalar.Source.snapshot fun
  | .instruction (.sampleIndex owner _) operands results regions site =>
      .instruction (.sampleIndex owner "random.other/0") operands results regions site
  | instruction => instruction

example : (Structured.check wrongScalarResult).toOption.isSome = false := by decide +kernel
example : (Structured.check missingScalarBound).toOption.isSome = false := by decide +kernel
example : (Structured.check wrongScalarContract).toOption.isSome = false := by decide +kernel

-- Source formation accepts non-power-of-two domains; providers choose their
-- own narrower supported domains. Zero and values above u64 are not formed.
example : (Request.sampleIndex 3).valid = true := by decide
example : (Request.sampleIndices 3 1048577).valid = true := by decide
example : (Request.sampleIndex 3).nativeSupported = false := by decide
example : (Request.sampleIndices 3 2).nativeSupported = false := by decide
example : (Request.sampleIndices 8 1048577).nativeSupported = false := by decide
example : (Request.sampleIndex (2^63)).nativeSupported = true := by decide
example : (Request.sampleIndices 1 1048576).nativeSupported = true := by decide
example : (Request.sampleIndex 0).valid = false := by rfl
example : (Request.sampleIndices 8 0).valid = false := by decide
example : (Request.sampleIndex (2^64)).valid = false := by decide
example : (⟨"index", [8,3], .index⟩ : Request).valid = false := by decide
example : (⟨"draw", [8], .index⟩ : Request).operation contract = none := by decide
example : (⟨"indices", [8,3], .index⟩ : Request).operation contract = none := by decide

variable (carriers : Carriers)
example : (Request.sampleIndex 8).accepts (carriers := carriers) (8 : Nat) = false := by rfl
example : (Request.sampleIndices 8 3).accepts (carriers := carriers) [1,2] = false := by rfl
example : (Request.sampleIndices 8 3).accepts (carriers := carriers) [1,2,8] = false := by rfl
example : (Request.sampleIndices 8 3).accepts (carriers := carriers) [1,2,7] = true := rfl
example (value : Fin 8) : Request.decode (carriers := carriers) (.sampleIndex 8) value = some value.val := rfl
example (values : Fin 3 → Fin 8) :
    Request.decode (carriers := carriers) (.sampleIndices 8 3) values =
      some (List.ofFn fun i => (values i).val) := rfl
example : (Scalar.context.query "same" (.sampleIndices 8 3)) ≠
    Scalar.context.query "same" (.sampleIndex 8) := by decide
example : Domain.requestOperands (carriers := carriers) [.data (.index 8)] [0] (.sampleIndex 8) = true := rfl
example : Domain.requestOperands (carriers := carriers) [.data (.index 8)] [0] (.sampleIndex 1) = false := rfl

example : (ServiceOp.sampleIndex contract).checkedReply
    (carriers := carriers) (.cons 17 (.cons 8 .nil)) 8 = .halt .refused := rfl
example : (ServiceOp.sampleIndices contract).checkedReply
    (carriers := carriers) (.cons 17 (.cons 8 (.cons 3 .nil))) [1,2] = .halt .refused := rfl
example : (ServiceOp.sampleIndices contract).checkedReply
    (carriers := carriers) (.cons 17 (.cons 8 (.cons 3 .nil))) [1,2,8] = .halt .refused := rfl
example : checkServiceBlock [none, some 0]
    (.block [.instruction (.sampleIndex "V" contract) [0,1] [.index] [] "q"] (.ret [0])) =
      .error "structured-index-service-positive" := by decide
example : checkServiceBlock [none, none]
    (.block [.instruction (.sampleIndex "V" contract) [0,1] [.index] [] "q"] (.ret [0])) =
      .error "structured-index-service-constant" := by decide
example : checkServiceBlock [none, some 3, some 1048577]
    (.block [.instruction (.sampleIndices "V" contract) [0,1,2] [.indices] [] "q"] (.ret [0])) =
      .ok () := by decide

end Tests.IndexServices
