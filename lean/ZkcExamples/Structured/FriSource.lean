module

public import ZkcExamples.Structured.FriSourceViews
public import Zkc.Source.Structured.PublishedWordsFrame

@[expose] public section

/-! The selected Direct scalar FRI root in the logical publication experiment.
The original private vector belongs to the holder. The verifier observes its
actual returned Boolean and the first successfully published word. -/

set_option autoImplicit false
namespace ZkcExamples.Structured.FriSource
open Zkc.Source Zkc.Source.Structured

abbrev imported := FriSourceViews.imported
abbrev extension := "koala-bear.ext8-binomial3"

def checkedUnit : CheckedOracleUnit :=
  imported.program.payload.oracleUnit.get (by decide +kernel)

def coordinates : CommonCoordinate.UnitCertificate FriSourceData.snapshot
    imported.program.payload.protocols imported.program.payload.protocols :=
  (CommonCoordinate.certify FriSourceData.snapshot imported.program.payload.protocols).toOption.get
    (by decide +kernel)

def subject : OracleSubject FriSourceData.snapshot :=
  ⟨imported, checkedUnit, by kernel_rfl, coordinates⟩

/-- A root input vector is ordinary data. Its publication occurs in the callee. -/
theorem rootBindings : OracleIngress.sourceBindings subject.imported.program.payload.entry =
    .ok [] := by kernel_rfl

variable {model : DomainModel} {Aux E : Type}

/-- Both participants begin with the same shape and public parameters. The
verifier receives its sampling service, the holder its private vector. -/
def inputs (self : Nat) (word : List (model.Field extension))
    (shift : model.Field extension) (rounds queries service : Nat) :
    Values (Component model.Value) subject.imported.program.payload.entry.inputs :=
  .cons (if self == 0 then some word else none)
    (.cons (some shift) (.cons (some rounds) (.cons (some queries)
      (.cons (if self == 1 then some service else none) .nil))))

/-- Start from no previous publications. All entries and frames are produced
by the selected source execution. -/
def start (self : Fin 2) (word : List (model.Field extension))
    (shift : model.Field extension) (rounds queries service : Nat) (auxiliary : Aux) :
    OracleStart subject model self.val (PublishedWords.State model Aux) where
  bindings := []
  sourceBindings := rootBindings
  rows := []
  ordinaryInputs := inputs self.val word shift rounds queries service
  installed := ⟨ProtocolValue.embedComponents (inputs self.val word shift rounds queries service), [], .empty⟩
  constructed := rfl
  provider := ⟨[], auxiliary⟩

abbrev Execution (model : DomainModel) (Aux E : Type) :=
  PIR.Execution (OracleProtocol.State model subject.unit.snapshot subject.unit.domains
    subject.unit.math (PublishedWords.State model Aux)) (OracleProtocol.Event E)
    (Values (Component (ProtocolValue model.toCarriers)) subject.imported.program.payload.entry.outputs)

/-- The complete verifier outcome and trace, including unsuccessful executions. -/
def verifier {m : Type → Type} [Monad m] [LawfulMonad m]
    (shift : model.Field extension) (rounds queries service : Nat) (auxiliary : Aux)
    (ordinary : PublishedWords.Table model →
      PIR.MonadHandler m (participantInterfaceOn model.toCarriers) Aux E)
    (choose : PublishedWords.Chooser m model Aux E) : m (Execution model Aux E) :=
  PublishedWords.sourceRunM (start 1 [] shift rounds queries service auxiliary) ordinary choose

def accepted (execution : Execution model Aux E) : Prop :=
  match execution.outcome with
  | .stopped _ => False
  | .returned values => (values.get .here).bind ProtocolValue.toConcrete = some true

/-- The word is private until its first publication; the predicate is on the
nominal first word and is never supplied as a verifier input. -/
def acceptsFirst (far : List (model.Field extension) → Prop)
    (execution : Execution model Aux E) : Prop :=
  accepted execution ∧ ∃ stored : PublishedWords.Word model (.field extension),
    execution.state.oracle.provider.words.getLast? = some ⟨.field extension, stored⟩ ∧
    far stored.cells

end ZkcExamples.Structured.FriSource
