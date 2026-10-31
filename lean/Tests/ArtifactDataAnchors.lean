module

public import Zkc.Construction.Participant

@[expose] public section

/-! Closed-data fixtures for the declaration reporter. Digest fields are kept
identical in the negative cases: full source and participant values matter. -/
namespace Tests.ArtifactDataAnchors
open Zkc.Source.Structured Zkc.Construction

def original : Snapshot := ⟨"source", "entry", [], [], [], [], [], ⟨[], [], []⟩, {}⟩
def changedOriginal : Snapshot := { original with domains := [⟨"extra", [], [], 0⟩] }
def participant : Participant :=
  ⟨"source", "candidate", ⟨"entry", "P", "V", 0, "suite", [], [], [], "format", "fs"⟩,
    "validator", [], [], [], [], []⟩
def changedParticipant : Participant :=
  { participant with instructions := [⟨.guard "extra", [], [], []⟩] }
def producer : Participant := { participant with symbol := "producer" }

structure Pair where
  source : Snapshot
  prover : Participant
  verifier : Participant

def pair : Pair := ⟨original, producer, participant⟩
/-- An ordinary generic projection, without a protocol-specific adapter. -/
def select {α : Type} (project : Pair → α) (value : Pair) : α := project value
def selectedOriginal : Snapshot := select Pair.source pair
def selectedParticipant : Participant := select Pair.verifier pair

end Tests.ArtifactDataAnchors
