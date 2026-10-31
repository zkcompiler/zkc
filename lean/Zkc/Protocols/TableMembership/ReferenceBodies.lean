module

public import Zkc.Protocols.TableMembership.SourceBodies
public import Zkc.Protocols.TableMembership.BatchSourceBodies
public import Zkc.Source.Structured.ReferenceLibrary

@[expose] public section

/-! Mathematical leaf rules shared by exact source installations. The complete
Boolean is retained, including a previously false accumulator. -/
namespace Zkc.Protocols.TableMembership
open Zkc.Source Zkc.Source.Structured

namespace Source

def containsDecisionLaw (model : DomainModel) (field : String) (bindings : Names) :
    ReferenceLaw model (containsDecisionHelper field bindings).inputs [.boolean] where
  body := containsDecisionBody field bindings
  Requires _ _ := True
  reference args := .returned (.cons (args.get .here ||
    decide (args.get (.there .here) = args.get (.there (.there .here)))) .nil)
  valid _ args _ := by
    cases args with | cons found rest => ?_
    cases rest with | cons row rest => ?_
    cases rest with | cons value rest => ?_
    cases rest
    rfl

end Source

namespace BatchSource

def checkOpeningLaw (model : DomainModel) (field : String) (bindings : Names) :
    ReferenceLaw model (checkOpeningHelper field bindings).inputs [.boolean] where
  body := checkOpeningBody field bindings
  Requires _ _ := True
  reference args := .returned (.cons (args.get .here &&
    decide (args.get (.there .here) = args.get (.there (.there (.there .here)))) &&
    decide (args.get (.there (.there .here)) = args.get (.there (.there (.there (.there .here)))))) .nil)
  valid _ args _ := by
    cases args with | cons valid rest => ?_
    cases rest with | cons point rest => ?_
    cases rest with | cons value rest => ?_
    cases rest with | cons expectedPoint rest => ?_
    cases rest with | cons expectedValue rest => ?_
    cases rest
    rfl

end BatchSource
end Zkc.Protocols.TableMembership
