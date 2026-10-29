import Zkc.Construction.ConnectionRouteCoverage
import Tests.ConnectionSymbolicRepeat
import Tests.ConnectionHelperCertificate

/-! Existing finite certificates produce source coverage for symbolic nested
repeats and genuinely partial retained helpers, with arbitrary nominal models,
counts, inputs, histories and all typed responses. -/
set_option autoImplicit false
noncomputable section
namespace Tests.ConnectionRouteCoverageLoops
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionCertificate

namespace Nested
open Tests.ConnectionSymbolicRepeat

def plain (model : DomainModel) (outer inner seed : Nat) (history : Domain.History model.toCarriers) :=
  plainAccepted.routeCoverage (RosterDistinct.root 1 2) model (Occurrence.helpers model program.payload)
    (fun entry => entry.elim0) (Occurrence.table model program.payload)
    (.cons outer (.cons inner (.cons seed .nil))) history
    [.data (.index outer), .data (.index inner), .data (.index seed)]
    (.cons ⟨outer,rfl,rfl⟩ (.cons ⟨inner,rfl,rfl⟩ (.cons ⟨seed,rfl,rfl⟩ .nil)))

def fs (model : DomainModel) (outer inner seed : Nat) (history : Domain.History model.toCarriers) :=
  fsAccepted.routeCoverage (RosterDistinct.root 1 2) model (Occurrence.helpers model program.payload)
    (fun entry => entry.elim0) (Occurrence.table model program.payload)
    (.cons outer (.cons inner (.cons seed .nil))) history
    [.data (.index outer), .data (.index inner), .data (.index seed), .transcript "suite" history]
    (.cons ⟨outer,rfl,rfl⟩ (.cons ⟨inner,rfl,rfl⟩ (.cons ⟨seed,rfl,rfl⟩ (.cons rfl .nil))))

def producer (model : DomainModel) (outer inner seed : Nat) (history : Domain.History model.toCarriers) :=
  fsProducerAccepted.routeCoverage (RosterDistinct.root 0 2) model (Occurrence.helpers model program.payload)
    (fun entry => entry.elim0) (Occurrence.table model program.payload)
    (.cons outer (.cons inner (.cons seed .nil))) history
    [.data (.index outer), .data (.index inner), .data (.index seed), .transcript "suite" history]
    (.cons ⟨outer,rfl,rfl⟩ (.cons ⟨inner,rfl,rfl⟩ (.cons ⟨seed,rfl,rfl⟩ (.cons rfl .nil))))
end Nested

namespace Helpers
open Tests.ConnectionHelperCertificate

def partialHelper (model : DomainModel) (values : model.Value (.vector "bls12-381.fr")) (index : Nat)
    (history : Domain.History model.toCarriers) :=
  readAccepted.routeCoverage (RosterDistinct.root 0 1) model (Occurrence.helpers model readProgram.payload)
    (fun _ => rfl) (Occurrence.table model readProgram.payload)
    (.cons (some values) (.cons (some index) .nil)) history
    [.data (.vector "bls12-381.fr" values), .data (.index index)]
    (.cons ⟨values,rfl,rfl⟩ (.cons ⟨index,rfl,rfl⟩ .nil))
end Helpers

#print axioms Nested.plain
#print axioms Nested.fs
#print axioms Nested.producer
#print axioms Helpers.partialHelper
end Tests.ConnectionRouteCoverageLoops
