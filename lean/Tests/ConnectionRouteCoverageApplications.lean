import Zkc.Construction.ConnectionRouteCoverageApplications
import Tests.ConnectionSharedLibrary

/-! Both linked placements reuse the one generic coverage theorem. Arbitrary
caller guards, helper outcomes and ordered enclosing coordinates are retained. -/
set_option autoImplicit false
noncomputable section
namespace Tests.ConnectionRouteCoverageApplications
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open Tests.ConnectionSharedLibrary

def firstCoverage (model : DomainModel) (guard helper : Bool) (seed outer inner : Nat)
    (history : Domain.History model.toCarriers) :=
  first.routeCoverage .empty model
    (.cons guard (.cons helper (.cons seed (.cons outer (.cons inner .nil))))) .nil history
    [.data (.boolean guard), .data (.boolean helper), .data (.index seed),
      .data (.index outer), .data (.index inner)]
    (.cons ⟨guard,rfl,rfl⟩ (.cons ⟨helper,rfl,rfl⟩ (.cons ⟨seed,rfl,rfl⟩
      (.cons ⟨outer,rfl,rfl⟩ (.cons ⟨inner,rfl,rfl⟩ .nil)))))

def secondCoverage (model : DomainModel) (guard helper : Bool) (seed outer inner : Nat)
    (history : Domain.History model.toCarriers) :=
  second.routeCoverage .empty model
    (.cons guard (.cons helper (.cons seed (.cons outer (.cons inner .nil))))) .nil history
    [.data (.boolean guard), .data (.boolean helper), .data (.index seed),
      .data (.index outer), .data (.index inner)]
    (.cons ⟨guard,rfl,rfl⟩ (.cons ⟨helper,rfl,rfl⟩ (.cons ⟨seed,rfl,rfl⟩
      (.cons ⟨outer,rfl,rfl⟩ (.cons ⟨inner,rfl,rfl⟩ .nil)))))

#print axioms ConnectionApplications.Certificate.routeCoverage
#print axioms firstCoverage
#print axioms secondCoverage
end Tests.ConnectionRouteCoverageApplications
