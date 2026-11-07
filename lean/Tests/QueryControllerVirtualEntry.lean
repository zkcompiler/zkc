module

public import Zkc.Realization.QueryControllerVirtualEntry

@[expose] public section
set_option autoImplicit false
namespace Tests.QueryControllerVirtualEntry
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Realization QueryController

def frameLayout := QueryContinuation.layout "VirtualFrame" 0
def anchorLayout : RecordProjection.Layout :=
  ⟨"VirtualAnchor", "Record", .cons .index (.cons (Child.referenceLayout "Source").type .nil)⟩
def lookupPlacement : RecordLookup.Placement := ⟨12, 0, 1, 9, "anchor"⟩
def lookupBody := RecordLookup.instructions ⟨3, anchorLayout.type⟩ lookupPlacement ++
  RecordProjection.instructions anchorLayout 14 (RecordProjection.allFields anchorLayout.fields)
def lookup : RecordLookupProjection.Recognized lookupBody :=
  ⟨_, _, ⟨⟨3, anchorLayout.type⟩, lookupPlacement, rfl⟩,
    ⟨anchorLayout, 14, RecordProjection.allFields anchorLayout.fields, rfl⟩, rfl, rfl, rfl⟩
def state := List.range 9
def entryBody := RequiredIndices.constantInstructions 10 5 0 "kind" ++ lookupBody ++
  DomainGuard.instructions 17 2 15 "domain"
def entry : EntryPrefix.Recognized entryBody :=
  ⟨10, 0, 5, "kind", 2, 15, "domain", state, lookupBody, lookup, rfl, rfl, rfl, rfl⟩
def framePlacement : RecordAppend.Placement := ⟨18, 8, [3, 4, 1, 2]⟩
def frameBody := RecordAppend.instructions frameLayout framePlacement
def positionRegion : InstructionRegion := ⟨[.data .index], [], [0]⟩
def positionInstruction : Zkc.Construction.Instruction :=
  ⟨.mathCompute, [2], [.data .index], [positionRegion]⟩
def childBody := frameBody ++ [positionInstruction] ++ Child.referenceInstructions "Source" 16 ++
  IndexLiterals.instructions [7]
def child : Child.Recognized childBody :=
  ⟨frameBody, ⟨frameLayout, framePlacement, rfl⟩, positionInstruction, "Source", 16, [7], rfl⟩
def output : Child.Output := ⟨24, 10, 10, 7, [], []⟩
def body := entryBody ++ childBody
def yielded := output.references 18
def checked : VirtualEntry.Recognized body yielded :=
  ⟨entryBody, childBody, entry, child, output, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def header (position outer outerInstance answer : Nat) : Header :=
  ⟨⟨3, 0, position, outer, outerInstance⟩, 0, 0, answer⟩
def anchor (model : DomainModel) (rows constructor anchorInstance : Nat) : model.Value anchorLayout.type :=
  (rows, (constructor, anchorInstance, ()), ())
def stores (model : DomainModel) (frames : List (model.Value frameLayout.type)) : Domain.Environment model.toCarriers :=
  [.data ⟨.sequence frameLayout.type, rfl, frames⟩]
def environment (model : DomainModel) (frames : List (model.Value frameLayout.type))
    (position rows outer outerInstance answer constructor anchorInstance : Nat) : Domain.Environment model.toCarriers :=
  (header position outer outerInstance answer).encode (stores model frames) ++
    [.data ⟨.sequence anchorLayout.type, rfl, [anchor model rows constructor anchorInstance]⟩]
def saved (model : DomainModel) (position outer outerInstance : Nat) : model.Value frameLayout.type :=
  (outer, outerInstance, 0, position, ())
def identityBody : Region dialect [.index] [.index] := .ret (.cons .here .nil)
def identityAligned : ConnectionMathRegion.Alignment [] identityBody [.data 0] 1
    (fun _ ↦ Domain.View.empty) [0] 1 := .returned _ _ _ _ rfl

theorem recognized : (VirtualEntry.recognize 10 state body yielded).isSome = true := by decide +kernel

/-- The complete arm derives saved parent association and output routing from
the actual header. Domain rejection precedes capacity; Math follows both. -/
theorem actual (model : DomainModel) (program : Program) (context : Context)
    (frames : List (model.Value frameLayout.type))
    (position rows outer outerInstance answer constructor anchorInstance : Nat) :
    Nonempty (Original.Simulation Eq
      (fun _ frame ↦ environment model frames position rows outer outerInstance answer constructor anchorInstance <+: frame)
      (if DomainGuard.Accepted position rows then
        if frames.length < indexLimit then
          .done (Child.outputValues model frameLayout rfl frames (saved model position outer outerInstance)
            position constructor anchorInstance 7 0 answer [] [])
        else .halt .exhausted
       else .halt .refused)
      ((Domain.evaluate model program context body
        (environment model frames position rows outer outerInstance answer constructor anchorInstance)).bind fun final ↦
          match Domain.read final yielded with
          | some values => .done values
          | none => .halt .refused)) := by
  let initial := environment model frames position rows outer outerInstance answer constructor anchorInstance
  let ready := VirtualEntry.admitted checked model rfl initial (anchor model rows constructor anchorInstance)
  let allocated := RecordAppend.result model frameLayout rfl ready frames (saved model position outer outerInstance)
  have math := identityAligned.embedded (region := positionRegion) (.cons .here .nil) rfl
    model program context rfl rfl (by intro frame; rfl) rfl rfl rfl
    (.cons position .nil) allocated [2] rfl
  have positionLaw : Original.Simulation
      (fun value frame ↦ frame = Child.positioned model frameLayout rfl ready frames
        (saved model position outer outerInstance) value)
      (fun _ frame ↦ ArtifactBinding.Captures allocated frame)
      (PIR.Process.done (I := Domain.effects model.toCarriers) position)
      (Domain.step model program context positionInstruction allocated) := by
    change Original.Simulation _ _
      (.done (show Values model.Value [.index] from .cons position .nil)) _ at math
    exact math.bind (sourceNext := fun values ↦ .done (values.get .here))
      (targetNext := fun frame ↦ .done frame)
      (returnRelation := fun value frame ↦ frame = Child.positioned model frameLayout rfl ready frames
        (saved model position outer outerInstance) value)
      (nextLive := fun _ frame ↦ ArtifactBinding.Captures allocated frame)
      (fun _ _ retained ↦ retained) (fun values frame equal ↦ by
        cases values with
        | cons value rest => cases rest; exact .done equal)
  exact checked.simulation model program context (header position outer outerInstance answer)
    (stores model frames) initial rfl rfl rfl (by decide) rfl
    (RecordProjection.allFields_local _ rfl) 0 [anchor model rows constructor anchorInstance]
    (anchor model rows constructor anchorInstance) rfl rfl rfl rfl (by decide) rows rfl
    rfl frames rfl constructor anchorInstance rfl
    (by intro value member; simp only [checked, child, List.mem_singleton] at member; subst value; decide)
    (.done position) positionLaw 7 0 (by intro value; exact ⟨rfl, rfl, rfl⟩)

/-- Equal-typed parent coordinates cannot be swapped when saving the frame. -/
theorem wrong_parent :
    (VirtualEntry.recognize 10 state
      (entryBody ++ RecordAppend.instructions frameLayout ⟨18, 8, [4, 3, 1, 2]⟩ ++
        [positionInstruction] ++ Child.referenceInstructions "Source" 16 ++ IndexLiterals.instructions [7])
      yielded).isNone = true := by decide +kernel

theorem wrong_output :
    (VirtualEntry.recognize 10 state body [22, 23, 21, 24, 18, 10, 10, 2, 20]).isNone = true := by decide +kernel

#print axioms actual
#print axioms wrong_parent
#print axioms wrong_output
end Tests.QueryControllerVirtualEntry
