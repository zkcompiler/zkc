import Tests.ConnectionCertificate

/-! Exact typed-source normalization and finite partial-calculation controls.
These direct bounded-read bodies exercise the formed protocol carrier. The
separate helper controls exercise snapshot-admitted mathematical functions. -/
set_option autoImplicit false
noncomputable section
namespace Tests.ConnectionPartialCertificate
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionCertificate

def field : Ty := .field "bls12-381.fr"
def inputs : List Ty := [.vector "bls12-381.fr", .index]
def boundedBody : Region protocolDialect inputs [field] :=
  .letOp (.calculate (.boundedAt "bls12-381.fr") rfl)
    (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil))

def source : CheckedProtocol :=
  ⟨⟨"bounded", ["P"], inputs, [field], [[0], [0]], [[0]]⟩,
    boundedBody.erase, boundedBody, boundedBody.elaborate_erase⟩
def routing : Original.Routing := Tests.ConnectionCertificate.arithmeticRouting
def presentPattern : InputPattern inputs := .cons .present (.cons .present .nil)
def optionalPattern : InputPattern inputs := .cons .optional (.cons .optional .nil)
def absentPattern : InputPattern inputs := .cons .absent (.cons .optional .nil)
def absentIndexPattern : InputPattern inputs := .cons .present (.cons .absent .nil)
def presentLayout : Layout presentPattern.scope :=
  [.data (.present (.var .here)), .data (.present (.var (.there .here)))]
def optionalLayout : Layout optionalPattern.scope := [.data (.input .here), .data (.input (.there .here))]
def boundedView : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.calculation model (.boundedAt "bls12-381.fr") [0, 1] [.data field])
    Domain.View.empty

def presentAccepted : Certificate routing [] {} [] 0 1 source presentPattern
    [.data 2] presentLayout boundedView := by derive_connection_alignment
def optionalAccepted : Certificate routing [] {} [] 0 1 source optionalPattern
    [.data 2] optionalLayout boundedView := by derive_connection_alignment
def absentAccepted : Certificate routing [] {} [] 0 1 source absentPattern
    [.absent] [] (fun _ => Domain.View.empty) := by derive_connection_alignment
def absentIndexAccepted : Certificate routing [] {} [] 0 1 source absentIndexPattern
    [.absent] [] (fun _ => Domain.View.empty) := by derive_connection_alignment

-- A total instruction eliminated by normalization still precedes the partial
-- call in the physical view. The proposer retains it and its checkpoints.
def literalBody : Region protocolDialect [.vector "bls12-381.fr"] [field] :=
  .letOp (.calculate (.indexConstant 0) rfl) .nil .nil <|
  .letOp (.calculate (.boundedAt "bls12-381.fr") rfl)
    (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil))
def literalSource : CheckedProtocol :=
  ⟨⟨"literalRead", ["P"], [.vector "bls12-381.fr"], [field], [[0]], [[0]]⟩,
    literalBody.erase, literalBody, literalBody.elaborate_erase⟩
def literalView : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.calculation model (.indexConstant 0) [] [.data .index]) <|
  Domain.View.sequence (Domain.View.calculation model (.boundedAt "bls12-381.fr") [0, 1] [.data field])
    Domain.View.empty
def literalAccepted : Certificate routing [] {} [] 0 1 literalSource (.cons .present .nil)
    [.data 2] [.data (.present (.var .here))] literalView := by derive_connection_alignment
example : literalAccepted.alignment.size = 3 := rfl

-- The second operation reuses the original optional vector and index through
-- both presence refinements and the first actual result binder.
def repeatedBody : Region protocolDialect inputs [field, field] :=
  .letOp (.calculate (.boundedAt "bls12-381.fr") rfl)
    (.cons .here (.cons (.there .here) .nil)) .nil <|
  .letOp (.calculate (.boundedAt "bls12-381.fr") rfl)
    (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))
def repeatedSource : CheckedProtocol :=
  ⟨⟨"repeated", ["P"], inputs, [field, field], [[0], [0]], [[0], [0]]⟩,
    repeatedBody.erase, repeatedBody, repeatedBody.elaborate_erase⟩
def repeatedView : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.calculation model (.boundedAt "bls12-381.fr") [0, 1] [.data field]) <|
  Domain.View.sequence (Domain.View.calculation model (.boundedAt "bls12-381.fr") [0, 1] [.data field])
    Domain.View.empty
def repeatedAccepted : Certificate routing [] {} [] 0 1 repeatedSource optionalPattern
    [.data 3, .data 2] optionalLayout repeatedView := by derive_connection_alignment

-- Without a physical witness both optional branches are actually certified.
-- Repeated use of the same optional source input must refine it only once.
def ignoredBody : Region protocolDialect [field] [.boolean] :=
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons .here (.cons .here .nil)) .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl)
    (.cons (.there .here) (.cons (.there .here) .nil)) .nil <|
  .letOp (.calculate (.booleanConstant true) rfl) .nil .nil (.ret (.cons .here .nil))
def ignoredSource : CheckedProtocol :=
  ⟨⟨"ignored", ["P"], [field], [.boolean], [[0]], [[0]]⟩,
    ignoredBody.erase, ignoredBody, ignoredBody.elaborate_erase⟩
def ignoredPattern : InputPattern [field] := .cons .optional .nil
def ignoredView : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.calculation model (.booleanConstant true) [] [.data .boolean])
    Domain.View.empty
def ignoredAccepted : Certificate routing [] {} [] 0 1 ignoredSource ignoredPattern
    [.data 1] [.unused] ignoredView := by derive_connection_alignment
example : normalize {} ignoredBody 0 1 ignoredPattern = .ok
    (.split (.input .here) (.done (.cons (.present (.bool true)) .nil))
      (.done (.cons (.present (.bool true)) .nil))) := rfl
example : presentAccepted.alignment.size = 2 := rfl
example : optionalAccepted.alignment.size = 4 := rfl
example : repeatedAccepted.alignment.size = 5 := rfl
example : ignoredAccepted.alignment.size = 5 := rfl

-- The public interface starts at the actual typed body, with arbitrary
-- nominal input, tables, source state/history, ABI and physical environment.
example (model : DomainModel) (tables : Tables model (Occurrence.signature model.toCarriers))
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (state : Original.State model.toCarriers) (stack : state.frames = [])
    (binders : Binders model optionalPattern.scope) (abi : Original.InputABI)
    (captured : Domain.Environment model.toCarriers)
    (sorts : Domain.sortsMatch abi.sorts captured = true)
    (bound : Original.LocationsBound captured.length abi.locations)
    (inputRead : Original.ValuesHolds captured abi.locations (optionalPattern.environment model binders))
    (environment : Domain.Environment model.toCarriers)
    (related : Holds model binders state.history optionalLayout environment)
    (retained : ArtifactBinding.Captures captured environment) :
    Original.Simulation (Returns [.data 3, .data 2] state captured)
      (Original.InputLive abi (optionalPattern.environment model binders) captured)
      (Original.fold routing (repeatedBody.denote
        (participantMeaningWithOn model (.silent _) Occurrence.actions tables 0 protocols {} Occurrence.iterations)
        (optionalPattern.environment model binders).get) state) (repeatedView model environment) :=
  repeatedAccepted.simulation rfl (RosterDistinct.root _ _) model tables (fun entry => entry.elim0)
    protocols state stack binders abi captured sorts bound inputRead environment related retained

-- Actual source meanings preserve missing components, successful values and
-- OOB refusal, without a hypothesis that the operation returns.
def run (model : DomainModel) (pattern : InputPattern inputs) (binders : Binders model pattern.scope) :=
  boundedBody.denote (participantMeaningWithOn model (.silent _) Occurrence.actions ⟨[], []⟩
    0 [] {} Occurrence.iterations) (pattern.environment model binders).get
example (model : DomainModel) (index : Option Nat) :
    run model optionalPattern (.cons none (.cons index .nil)) = .done (.cons none .nil) := by kernel_rfl
example (model : DomainModel) (values : List (model.Field "bls12-381.fr")) :
    run model optionalPattern (.cons (some values) (.cons none .nil)) = .done (.cons none .nil) := by kernel_rfl
example (model : DomainModel) (value : model.Field "bls12-381.fr") :
    run model presentPattern (.cons [value] (.cons 0 .nil)) = .done (.cons (some value) .nil) := by kernel_rfl
example (model : DomainModel) (value : model.Field "bls12-381.fr") :
    run model presentPattern (.cons [value] (.cons 1 .nil)) = .halt .refused := by kernel_rfl
example (model : DomainModel) :
    run model presentPattern (.cons [] (.cons 0 .nil)) = .halt .refused := by kernel_rfl

-- Refusal has an entry checkpoint and no success/exit checkpoint. Success
-- retains both checkpoints and appends the exact nominal returned field.
example (model : DomainModel) (value : model.Field "bls12-381.fr") :
    boundedView model [.data (.vector "bls12-381.fr" [value]), .data (.index 1)] =
      .call (.checkpoint [.data (.vector "bls12-381.fr" [value]), .data (.index 1)])
        (fun _ => .halt .refused) := by kernel_rfl
example (model : DomainModel) (value : model.Field "bls12-381.fr") :
    boundedView model [.data (.vector "bls12-381.fr" [value]), .data (.index 0)] =
      .call (.checkpoint [.data (.vector "bls12-381.fr" [value]), .data (.index 0)]) (fun _ =>
        .call (.checkpoint [.data (.vector "bls12-381.fr" [value]), .data (.index 0), .data (.field "bls12-381.fr" value)])
          (fun _ => .done [.data (.vector "bls12-381.fr" [value]), .data (.index 0), .data (.field "bls12-381.fr" value)])) := by
  kernel_rfl

/-- error: alignment-return-or-view-mismatch -/
#guard_msgs (substring := true) in
example : Certificate routing [] {} [] 0 1 source absentPattern [.data 2] []
    (fun _ => Domain.View.empty) := by derive_connection_alignment

/-- error: alignment-return-or-view-mismatch -/
#guard_msgs (substring := true) in
example : Certificate routing [] {} [] 0 1 source presentPattern [.data 0] presentLayout boundedView := by
  derive_connection_alignment

/-- error: alignment-compute-view-mismatch -/
#guard_msgs (substring := true) in
example : Certificate routing [] {} [] 0 1 source presentPattern [.data 2] presentLayout
    (fun _ => Domain.View.empty) := by derive_connection_alignment

-- Without actual physical input cells the absent branch cannot be skipped.
/-- error: alignment-operand-not-data -/
#guard_msgs (substring := true) in
example : Certificate routing [] {} [] 0 1 source optionalPattern [.data 2] [.unused, .unused] boundedView := by
  derive_connection_alignment

/-- error: alignment-compute-operation-or-view-mismatch -/
#guard_msgs (substring := true) in
example : Certificate routing [] {} [] 0 1 source presentPattern [.data 2] presentLayout
    (fun model => Domain.View.sequence
      (Domain.View.calculation model (.fieldAdd "bls12-381.fr") [0, 1] [.data field]) Domain.View.empty) := by
  derive_connection_alignment

-- Certifying just the matching absent branch would be unsound here.
/-- error: alignment-return-or-view-mismatch -/
#guard_msgs (substring := true) in
example : Derivation routing [] {} [] [] [] [] ([.unused] : Layout [.component .boolean])
    (.split (.input .here) (.done .nil) (.halt .incomplete))
    (fun _ => Domain.View.empty) := by derive_connection_alignment

end Tests.ConnectionPartialCertificate
