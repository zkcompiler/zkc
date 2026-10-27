module

public import Zkc.Source.Structured.FiniteDomains

@[expose] public section

/-! Ordered collection with arbitrary stopping callbacks. Predicate and body
use the same complete item/domain/capture tuple; false appends nothing. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

def Collection.pack {carriers : Carriers} : (collection : Collection) →
    List (carriers.Value collection.element) → carriers.Value collection.type
  | .vector _, values => values
  | .sequence _, values => values

namespace Evaluation

/-- The private accumulator is reversed; the public result restores source order once. -/
def collectTransition {carriers : Carriers} {interface : PIR.Signature}
    (table : HelperTable carriers.Value interface) (spec : CollectSpec)
    (arguments : Values carriers.Value spec.domain.inputs)
    (captures : Values carriers.Value spec.captures)
    (collected : List (carriers.Value spec.collection.element))
    (item : Values carriers.Value spec.domain.items) :
    PIR.Process interface (List (carriers.Value spec.collection.element)) :=
  let callbackArguments := item.append (arguments.append captures)
  let enabled : PIR.Process interface (Values carriers.Value [.boolean]) :=
    if spec.predicate.isEmpty then .done (.cons true .nil)
    else invoke table spec.predicateHelper callbackArguments
  enabled.bind fun result =>
    if result.get .here then
      (invoke table spec.bodyHelper callbackArguments).bind fun value =>
        .done (value.get .here :: collected)
    else .done collected

def denoteCollect {carriers : Carriers} {interface : PIR.Signature}
    (table : HelperTable carriers.Value interface) (spec : CollectSpec)
    (values : Values carriers.Value spec.arguments) :
    PIR.Process interface (Values carriers.Value [spec.collection.type]) :=
  let (arguments, captures) := values.split spec.domain.inputs
  Finite.admitThen (spec.domain.admit arguments) fun items =>
    (Finite.fold (collectTransition table spec arguments captures) items []).bind fun collected =>
      .done (.cons (spec.collection.pack collected.reverse) .nil)

end Evaluation
end Zkc.Source.Structured
