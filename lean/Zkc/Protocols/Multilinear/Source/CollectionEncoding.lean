module

public import Zkc.Source.Structured.CollectionRepresentation
public import Zkc.Polynomial.Multilinear

@[expose] public section

/-! Collection encoding for Boolean tables in the existing MSB-first vertex
order. Source admission and callback equations remain explicit parameters; no
source identifier or particular scalar formula selects this representation. -/

set_option autoImplicit false
namespace Zkc.Protocols.Multilinear.Source.CollectionEncoding
open Zkc.Source Zkc.Source.Structured Zkc.Polynomial.Multilinear

/-- Any arity of tables and any tuple constructor use the same ordering law.
This is a representation theorem, independent of a protocol or callback body. -/
theorem collect {carriers : Carriers} {interface : PIR.Signature} {R F : Type} {n : Nat}
    (table : HelperTable carriers.Value interface) (spec : CollectSpec)
    (arguments : Values carriers.Value spec.domain.inputs)
    (captures : Values carriers.Value spec.captures)
    (rows : R → Table F n) (fallback : F)
    (pack : (R → F) → Values carriers.Value spec.domain.items)
    (admitted : spec.domain.admit arguments = .returned ((List.range (2 ^ n)).map
      (fun index => pack (fun row =>
        (List.ofFn (fun position => rows row (vertex n position)))[index]?.getD fallback))))
    (absent : spec.predicate.isEmpty = true)
    (formula : (R → F) → carriers.Value spec.collection.element)
    (law : ∀ values,
      invoke table spec.bodyHelper ((pack values).append (arguments.append captures)) =
        .done (.cons (formula values) .nil)) :
    Evaluation.denoteCollect table spec (arguments.append captures) =
      .done (.cons (spec.collection.pack (List.ofFn (fun position =>
        formula (fun row => rows row (vertex n position))))) .nil) :=
  Evaluation.denoteCollect_ofFn table spec arguments captures
    (fun row position => rows row (vertex n position)) fallback pack admitted absent formula law

end Zkc.Protocols.Multilinear.Source.CollectionEncoding
