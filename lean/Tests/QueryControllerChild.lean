module

public import Zkc.Realization.QueryControllerChild

@[expose] public section
set_option autoImplicit false
namespace Tests.QueryControllerChild
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Realization QueryController

def frameLayout := QueryContinuation.layout "Frame" 0
def referenceLayout := Child.referenceLayout "ChildReference"
def framePlacement : RecordAppend.Placement := ⟨12, 9, [3, 4, 1, 2]⟩
def frameBody := RecordAppend.instructions frameLayout framePlacement
def positionRegion : InstructionRegion := ⟨[.data .index], [], [0]⟩
def positionInstruction : Zkc.Construction.Instruction :=
  ⟨.mathCompute, [2], [.data .index], [positionRegion]⟩
def body := frameBody ++ [positionInstruction] ++ Child.referenceInstructions "ChildReference" 11 ++
  IndexLiterals.instructions [7]
def checked : Child.Recognized body :=
  ⟨frameBody, ⟨frameLayout, framePlacement, rfl⟩, positionInstruction, "ChildReference", 11, [7], rfl⟩
def output : Child.Output := ⟨18, 5, 5, 7, [8], [10]⟩

def record (model : DomainModel) (outer outerInstance parent position : Nat) :
    model.Value frameLayout.type := (outer, outerInstance, parent, position, ())

def environment (model : DomainModel) (records : List (model.Value frameLayout.type))
    (parent position outer outerInstance answer constructor anchorInstance : Nat) :
    Domain.Environment model.toCarriers :=
  [ .data (.index 3), .data (.index parent), .data (.index position), .data (.index outer),
    .data (.index outerInstance), .data (.index 0), .data (.index 0), .data (.index answer),
    .data (.index 19), .data ⟨.sequence frameLayout.type, rfl, records⟩,
    .data (.index 23), .data ⟨referenceLayout.type, rfl, (constructor, anchorInstance, ())⟩ ]

def identityBody : Region dialect [.index] [.index] := .ret (.cons .here .nil)
def identityAligned : ConnectionMathRegion.Alignment [] identityBody [.data 0] 1
    (fun _ ↦ Domain.View.empty) [0] 1 := .returned _ _ _ _ rfl

theorem recognized : (Child.recognize 12 body).isSome = true := by decide +kernel

/-- A whole child transition preserves both adjacent stores and the old answer,
appends the exact parent frame, and installs the computed child coordinates.
The emitted kind and phase both reuse an earlier zero rather than fresh literals. -/
theorem actual (model : DomainModel) (program : Program) (context : Context)
    (records : List (model.Value frameLayout.type))
    (parent position outer outerInstance answer constructor anchorInstance : Nat) :
    Nonempty (Original.Simulation Eq
      (fun _ frame ↦ environment model records parent position outer outerInstance answer constructor anchorInstance <+: frame)
      (if records.length < indexLimit then
        .done (Child.outputValues model frameLayout rfl records (record model outer outerInstance parent position)
          position constructor anchorInstance 7 0 answer [.data (.index 19)] [.data (.index 23)])
       else .halt .exhausted)
      ((Domain.evaluate model program context body
        (environment model records parent position outer outerInstance answer constructor anchorInstance)).bind fun final ↦
          match Domain.read final (output.references 12) with
          | some values => .done values
          | none => .halt .refused)) := by
  let initial := environment model records parent position outer outerInstance answer constructor anchorInstance
  let saved := RecordAppend.result model frameLayout rfl initial records (record model outer outerInstance parent position)
  have math := identityAligned.embedded (region := positionRegion) (.cons .here .nil) rfl
    model program context rfl rfl (by intro frame; rfl) rfl rfl rfl
    (.cons position .nil) saved [2] rfl
  have positionLaw : Original.Simulation
      (fun value frame ↦ frame = Child.positioned model frameLayout rfl initial records
        (record model outer outerInstance parent position) value)
      (fun _ frame ↦ ArtifactBinding.Captures saved frame)
      (PIR.Process.done (I := Domain.effects model.toCarriers) position)
      (Domain.step model program context positionInstruction saved) := by
    change Original.Simulation _ _
      (.done (show Values model.Value [.index] from .cons position .nil)) _ at math
    have joined := math.bind (sourceNext := fun values ↦ .done (values.get .here))
        (targetNext := fun frame ↦ .done frame)
        (returnRelation := fun value frame ↦ frame = Child.positioned model frameLayout rfl
          initial records (record model outer outerInstance parent position) value)
        (nextLive := fun _ frame ↦ ArtifactBinding.Captures saved frame)
        (fun _ _ retained ↦ retained) (fun values frame equal ↦ by
          cases values with
          | cons value rest => cases rest; exact .done equal)
    exact joined
  obtain ⟨connected⟩ := checked.simulation model program context rfl rfl initial records
    (record model outer outerInstance parent position) rfl rfl rfl constructor anchorInstance rfl
    (by intro value member; simp only [checked, List.mem_singleton] at member; subst value; decide)
    (.done position) positionLaw
  dsimp only [checked] at connected
  by_cases room : records.length < indexLimit
  · simp only [room, ↓reduceIte, PIR.Process.interpret, PIR.Process.bind] at connected ⊢
    refine ⟨connected.continueDone (fun _ held ↦ held) ?_⟩
    have projected := Child.read_output model frameLayout rfl initial records
      (record model outer outerInstance parent position) position constructor anchorInstance [7] output
      7 0 answer [.data (.index 19)] [.data (.index 23)] rfl rfl rfl rfl rfl rfl
    simp only [show initial.length = 12 from rfl] at projected
    rw [projected]
    exact .done rfl
  · simp only [room, ↓reduceIte] at connected ⊢
    exact ⟨connected.continueHalt _ (fun _ held ↦ held)⟩

theorem saved_parent (model : DomainModel) (records : List (model.Value frameLayout.type))
    (outer outerInstance parent position : Nat) :
    QueryContinuation.Stored "Frame" 0
      (records ++ [record model outer outerInstance parent position]) records.length
      ⟨outer, outerInstance, parent, position, []⟩ :=
  QueryContinuation.stored_append records ⟨(), rfl, rfl⟩

/-- Reversing two same-typed projections fails whole-tail admission. -/
theorem swapped_reference :
    (Child.recognize 12 (frameBody ++ [positionInstruction] ++
      (Child.referenceInstructions "ChildReference" 11).reverse ++
      IndexLiterals.instructions [7])).isNone = true := by decide +kernel

#print axioms actual
#print axioms saved_parent
#print axioms swapped_reference
end Tests.QueryControllerChild
