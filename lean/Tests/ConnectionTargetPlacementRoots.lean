import Tests.ConnectionTargetPlacement
import ZkcTools.ConstructionBindings.Root
import Zkc.Construction.ConnectionRootRoutes
import Zkc.Construction.ConnectionRouteCoverageRoot
import Tests.ConnectionPlacementMetrics

/-! Actual nested-loop root assembly must use the checked family twice.
Strict proposal mode refuses body traversal when reuse cannot be established.
The aliased placement also feeds the existing application simulation consumer.
-/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
noncomputable section
namespace Tests.ConnectionTargetPlacementRoots
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionLibrary ConnectionCertificate ConnectionTargetPlacement
open Tests.ConnectionTargetPlacement

def library : Bundle program.payload := ⟨[optionalTemplate.key], .extend .empty optionalTemplate⟩

def rootRouting : Original.Routing := ConnectionRootRoutes.routing program.snapshot
  Tests.SourceConnectionPilot.context .validator [] Tests.SourceConnectionPilot.artifact (by decide +kernel)

set_option zkc.connection.requireReusableBodies true in
def nested : ConnectionRoot.RootCertificate program rootRouting 1 Tests.SourceConnectionPilot.artifact := by
  derive_root_connection_with_library
    target Tests.SourceConnectionPilot.rootView
    correspondence Tests.SourceConnectionPilot.body_view
    services [] library library

example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  nested.simulation model physical

def nestedFacts := nested.facts
example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  nestedFacts.coverage model physical

abbrev aliasScope : Scope := [.value .boolean, .value .index, .value .index, .value .index]
def aliasArguments : Values (Argument [] aliasScope) template.pattern.scope :=
  .cons (.var .here) (.cons (.var .here) (.cons (.var (.there .here)) .nil))
def aliasLayout : Layout aliasScope :=
  [.unused, .unused, .unused, .data (.present (.var .here)),
    .data (.present (.var (.there .here))),
    .data (.present (.var (.there (.there .here)))),
    .data (.present (.var (.there (.there (.there .here)))))]
def aliasFrames : ScopedFrames aliasScope :=
  [⟨"outer", .var (.there (.there .here))⟩,
   ⟨"inner", .var (.there (.there (.there .here)))⟩]
def aliasContext : ProtocolContext := ({} : ProtocolContext).enter "first" [0,1]

def aliased : ConnectionApplications.Certificate template routing aliasContext aliasArguments
    [.data 8] none aliasFrames aliasLayout (stepSpine routing aliasContext 3 3 4).block where
  distinct := RosterDistinct.ofSeparate (by decide +kernel) (by decide +kernel)
  alignment := (checkedStep routing rfl .unselected aliasContext aliasFrames aliasLayout
    (.var .here) (.var .here) (.var (.there .here)) 3 3 4 true
    (.boolean _ 3 (.data 3 rfl .nil))
    (.guardedOriginal 3 rfl (.data 4 rfl .nil))
    (Tests.SourceConnectionPilot.messageTemplate "first") (by decide +kernel)).alignment

def allReplies (model : DomainModel) (guard : Bool) (seed outer inner : Nat)
    (history : Domain.History model.toCarriers) :=
  aliased.simulation .empty model (.cons guard (.cons seed (.cons outer (.cons inner .nil)))) .nil
    ⟨[⟨"outer", outer⟩, ⟨"inner", inner⟩], history⟩ rfl
    ([.data (.index 19), .data (.boolean false), .data (.index 27),
      .data (.boolean guard), .data (.index seed), .data (.index outer), .data (.index inner)] :
      Domain.Environment model.toCarriers) _
    (.cons trivial (.cons trivial (.cons trivial (.cons ⟨guard, rfl, rfl⟩
      (.cons ⟨seed, rfl, rfl⟩ (.cons ⟨outer, rfl, rfl⟩ (.cons ⟨inner, rfl, rfl⟩ .nil)))))))
    (by
      simp only [ArtifactBinding.Captures, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero, List.cons.injEq, and_true]
      exact ⟨rfl, rfl, rfl⟩)

#print axioms nested
#print axioms nestedFacts
#print axioms allReplies
audit_placements nested 2 [checkedOptionalPresentStep]
end Tests.ConnectionTargetPlacementRoots
