module

public import Zkc.Source.Structured.CollectLaws

@[expose] public section

/-! Ordered collection correspondence and finite-row representation. Admission
is an equation about the actual source domain, including its stopping branches.
The finite encoding choice is separate from arbitrary callback execution. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.Evaluation

variable {carriers : Carriers} {interface : PIR.Signature}

/-- An indexed presentation of the actual domain preserves admission failure,
callback effects and stops, and the complete packed result. In particular, a
strict zip must supply its actual admission equation, not a truncated length. -/
theorem denoteCollect_indexed_process
    (table : HelperTable carriers.Value interface) (spec : CollectSpec)
    (arguments : Values carriers.Value spec.domain.inputs)
    (captures : Values carriers.Value spec.captures)
    (shape : PIR.Outcome Nat) (pack : Nat → Values carriers.Value spec.domain.items)
    (admitted : spec.domain.admit arguments = Finite.continueWith shape
      (fun length => .returned ((List.range length).map pack)))
    (absent : spec.predicate.isEmpty = true)
    (callback : Nat → PIR.Process interface (carriers.Value spec.collection.element))
    (law : ∀ index,
      invoke table spec.bodyHelper ((pack index).append (arguments.append captures)) =
        (callback index).bind fun value => .done (.cons value .nil)) :
    denoteCollect table spec (arguments.append captures) =
      Finite.admitThen shape fun length =>
        ((List.range length).mapM callback).bind fun values =>
          .done (.cons (spec.collection.pack values) .nil) := by
  cases shape with
  | stopped reason =>
      exact denoteCollect_admission_stop table spec arguments captures reason admitted
  | returned length =>
      exact denoteCollect_process table spec arguments captures (List.range length)
        pack admitted absent callback law

/-- Pointwise operations commute with a chosen ordered finite encoding, for
any number of operand rows and any scalar formula. All reads are in bounds;
the fallback cannot replace admission of any operand. -/
theorem map_range_ofFn {R F B : Type} {length : Nat}
    (rows : R → Fin length → F) (fallback : F) (formula : (R → F) → B) :
    (List.range length).map
        (fun index => formula (fun row => (List.ofFn (rows row))[index]?.getD fallback)) =
      List.ofFn (fun index => formula (fun row => rows row index)) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_ofFn]
  · intro index left right
    have bound : index < length := by simpa only [List.length_map, List.length_range] using left
    simp [bound]

/-- A total scalar callback on encoded rows yields the pointwise encoded
result. The tuple constructor retains arbitrary arity, domain inputs and
captures. Only the chosen successful encoding is specialized here. -/
theorem denoteCollect_ofFn {R F : Type} {length : Nat}
    (table : HelperTable carriers.Value interface) (spec : CollectSpec)
    (arguments : Values carriers.Value spec.domain.inputs)
    (captures : Values carriers.Value spec.captures)
    (rows : R → Fin length → F) (fallback : F)
    (pack : (R → F) → Values carriers.Value spec.domain.items)
    (admitted : spec.domain.admit arguments = .returned ((List.range length).map
      (fun index => pack (fun row => (List.ofFn (rows row))[index]?.getD fallback))))
    (absent : spec.predicate.isEmpty = true)
    (formula : (R → F) → carriers.Value spec.collection.element)
    (law : ∀ values,
      invoke table spec.bodyHelper ((pack values).append (arguments.append captures)) =
        .done (.cons (formula values) .nil)) :
    denoteCollect table spec (arguments.append captures) =
      .done (.cons (spec.collection.pack
        (List.ofFn (fun index => formula (fun row => rows row index)))) .nil) := by
  rw [denoteCollect_reference table spec arguments captures (List.range length)
    (fun index => pack (fun row => (List.ofFn (rows row))[index]?.getD fallback))
    admitted absent
    (fun index => formula (fun row => (List.ofFn (rows row))[index]?.getD fallback))
    (fun index _ => law _), map_range_ofFn]

end Zkc.Source.Structured.Evaluation
