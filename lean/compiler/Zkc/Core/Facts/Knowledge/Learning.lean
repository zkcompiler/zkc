module

public import Zkc.Core.Facts.Knowledge.Forms

@[expose] public section

namespace Zkc.Core.BodyAnalysis.Knowledge

variable {Raw Val : Type} {Run : Raw → List Val → List Val → Prop} {R : Reading Val}
    {table : Table Raw} {ρ : Leaves Val}

theorem resultForm_reads {ops : KnowledgeOperations Raw} (laws : ops.Lawful R Run)
    (slots : table.WF) {id : Ident} {form : ResultForm} {ids : List Ident} {v : Val}
    (found : resultForm ops table id = some (form, ids)) (read : Reads Run R.bool table ρ id v) :
    ∃ xs, ReadsAll Run R.bool table ρ ids xs ∧ FactCheck.FormHolds R form xs v := by
  unfold resultForm at found
  obtain ⟨⟨shape,port⟩, shapeAt, found⟩ := Option.bind_eq_some_iff.mp found
  split at found
  · next op args eq =>
    rw [eq] at shapeAt
    obtain ⟨f, named, same⟩ := Option.bind_eq_some_iff.mp found
    cases same
    obtain ⟨entry, mem, shape, below, pos⟩ := Table.formOf_spec shapeAt
    obtain ⟨xs, ys, reads, run, at_⟩ := read.application slots mem shape below pos
    obtain ⟨y, head, meaning⟩ := laws.form _ _ _ _ named run
    rw [List.head?_eq_getElem?, at_] at head
    cases head
    exact ⟨xs, reads, meaning⟩
  · cases found

/-- A reading of a conversion result witnesses the operand's reading in the same table. -/
private theorem conversionOperand_reads {ops : KnowledgeOperations Raw} (laws : ops.Lawful R Run)
    (slots : table.WF) {id source : Ident} {v : Val}
    (found : conversionOperand ops table id = some source) (read : Reads Run R.bool table ρ id v) :
    ∃ x, Reads Run R.bool table ρ source x ∧ R.nat x = R.nat v := by
  unfold conversionOperand at found
  split at found
  · next op arg shape =>
    split at found
    · next preserves =>
      cases found
      obtain ⟨entry, mem, form, below, pos⟩ := Table.formOf_spec shape
      obtain ⟨xs, ys, inputs, run, atResult⟩ := read.application slots mem form below pos
      obtain ⟨x, y, rfl, head, same⟩ := laws.preservesNumber op xs ys preserves run
      rw [List.head?_eq_getElem?, atResult] at head
      cases head
      cases inputs with | cons sourceRead _ => exact ⟨x, sourceRead, same⟩
    · cases found
  · cases found

private theorem refineConversionSources_sound {ops : KnowledgeOperations Raw}
    (laws : ops.Lawful R Run) (slots : table.WF) :
    ∀ fuel {k id v}, Means Run R k table ρ → Reads Run R.bool table ρ id v →
      Means Run R (refineConversionSources ops table fuel k id) table ρ
  | 0, _, _, _, h, _ => h
  | fuel+1, k, id, v, h, read => by
    simp only [refineConversionSources]
    split
    · exact h
    · next source found =>
      split
      · exact h
      · next bound known =>
        obtain ⟨x, sourceRead, same⟩ := conversionOperand_reads laws slots found read
        obtain ⟨n, number, fits⟩ := cachedRange laws.functional slots h read known
        apply refineConversionSources_sound laws slots fuel _ sourceRead
        apply addRange_sound (r := some bound) laws.functional slots h sourceRead
        intro other equal
        cases equal
        exact ⟨n, same.trans number, fits⟩

private theorem refineComparedSources_sound {ops : KnowledgeOperations Raw}
    (laws : ops.Lawful R Run) (slots : table.WF) {left right : Ident} {x y : Val} {k : BufferedFacts}
    (first : Reads Run R.bool table ρ left x) (second : Reads Run R.bool table ρ right y)
    (h : Means Run R k table ρ) : Means Run R (refineComparedSources ops table k left right) table ρ :=
  refineConversionSources_sound laws slots _ (refineConversionSources_sound laws slots _ h first) second

theorem literalTruth_sound {ops : KnowledgeOperations Raw} (laws : ops.Lawful R Run) (slots : table.WF)
    {id : Ident} {v : Val} {b : Bool} (read : Reads Run R.bool table ρ id v)
    (found : literalTruth ops table id = some b) : R.bool v = some b := by
  unfold literalTruth at found
  split at found
  · next c ids eq =>
    cases found
    obtain ⟨_, _, meaning⟩ := resultForm_reads laws slots eq read
    exact meaning
  · cases found

theorem readSelection {id c a b : Ident} {v : Val} (slots : table.WF)
    (shape : table.formOf id = some (.select c a b, 0)) (read : Reads Run R.bool table ρ id v) :
    ∃ cond which, Reads Run R.bool table ρ c cond ∧ R.bool cond = some which ∧
      Reads Run R.bool table ρ (if which then a else b) v := by
  obtain ⟨entry, mem, form, below, same⟩ := Table.formOf_spec shape
  cases read with
  | leaf => cases same
  | @app other op args j xs ys val listed opForm pos reads run result =>
    obtain rfl := slots.apart _ _ listed mem _ _ pos below (Ident.val.inj same)
    rw [opForm] at form
    cases form
  | @select other cond x y w which val listed opForm decided truth selected =>
    obtain rfl := slots.apart _ _ listed mem 0 0 (slots.select_pos listed opForm) below
      ((Nat.add_zero _).trans (Ident.val.inj same))
    rw [opForm] at form
    cases form
    exact ⟨w, which, decided, truth, selected⟩

private theorem learnSelection_sound {ops : KnowledgeOperations Raw} (laws : ops.Lawful R Run)
    (slots : table.WF) {learn : BufferedFacts → Ident → Bool → BufferedFacts}
    (keeps : ∀ {k id b v}, Means Run R k table ρ → Reads Run R.bool table ρ id v → R.bool v = some b →
      Means Run R (learn k id b) table ρ) {k id v b} (h : Means Run R k table ρ)
    (read : Reads Run R.bool table ρ id v) (val : R.bool v = some b) :
    Means Run R (learnSelection ops table learn k id b) table ρ := by
  unfold learnSelection
  split
  · next c x y shape =>
    obtain ⟨cond, which, condRead, condVal, selected⟩ := readSelection slots shape read
    split
    · next second =>
      cases which
      · have wrong := literalTruth_sound laws slots selected (beq_iff_eq.mp second)
        rw [val] at wrong
        cases b <;> contradiction
      · exact keeps (keeps h condRead condVal) selected val
    · split
      · next first =>
        cases which
        · exact keeps (keeps h condRead condVal) selected val
        · have wrong := literalTruth_sound laws slots selected (beq_iff_eq.mp first)
          rw [val] at wrong
          cases b <;> contradiction
      · exact h
  · exact h

theorem learnTruth_sound {ops : KnowledgeOperations Raw} (laws : ops.Lawful R Run)
    (slots : table.WF) {asks : Asks} (external : asks.Sound Run R table ρ) :
    ∀ fuel {k id b v}, Means Run R k table ρ → Reads Run R.bool table ρ id v → R.bool v = some b →
      Means Run R (learnTruth ops asks table fuel k id b) table ρ
  | 0, _, _, _, _, h, read, val => assume_sound laws.functional slots external h read val
  | fuel+1, k, id, b, v, h, read, val => by
    simp only [learnTruth]
    split
    · exact h
    have learned := assume_sound laws.functional slots external h read val
    split
    · next left right eq =>
      obtain ⟨_, reads, a, c, x, y, rfl, na, nc, result⟩ := resultForm_reads laws slots eq read
      cases reads with | cons first tail =>
        cases tail with | cons second _ =>
          rw [val] at result
          apply refineComparedSources_sound laws slots first second
          apply rememberComparison_sound laws.functional slots external learned first second na nc
          intro state i j assignment facts hx hy
          cases b
          · simpa using facts.pushLe hy hx (by simp at result; omega)
          · simpa using facts.pushLess hx hy (by simpa using result.symm)
    · next left right eq =>
      obtain ⟨_, reads, a, c, x, y, rfl, na, nc, result⟩ := resultForm_reads laws slots eq read
      cases reads with | cons first tail =>
        cases tail with | cons second _ =>
          rw [val] at result
          apply refineComparedSources_sound laws slots first second
          apply rememberComparison_sound laws.functional slots external learned first second na nc
          intro state i j assignment facts hx hy
          cases b
          · simpa using facts.pushDifferent hx hy (by simpa using result.symm)
          · have same : x = y := by simpa using result.symm
            subst y
            simpa using facts.pushEqual hx hy
    · next operand eq =>
      obtain ⟨_, reads, a, x, rfl, operandVal, result⟩ := resultForm_reads laws slots eq read
      cases reads with | cons first _ =>
        apply learnTruth_sound laws slots external fuel learned first
        rw [val] at result
        cases x <;> cases b <;> simp_all
    · next left right eq =>
      cases b
      · exact learned
      · obtain ⟨_, reads, a, c, x, y, rfl, va, vc, result⟩ := resultForm_reads laws slots eq read
        rw [val] at result
        have ⟨hx,hy⟩ : x = true ∧ y = true := by simpa using result.symm
        cases reads with | cons first tail =>
          cases tail with | cons second _ =>
            exact learnTruth_sound laws slots external fuel
              (learnTruth_sound laws slots external fuel learned first (hx ▸ va)) second (hy ▸ vc)
    · next left right eq =>
      cases b
      · obtain ⟨_, reads, a, c, x, y, rfl, va, vc, result⟩ := resultForm_reads laws slots eq read
        rw [val] at result
        have ⟨hx,hy⟩ : x = false ∧ y = false := by simpa using result.symm
        cases reads with | cons first tail =>
          cases tail with | cons second _ =>
            exact learnTruth_sound laws slots external fuel
              (learnTruth_sound laws slots external fuel learned first (hx ▸ va)) second (hy ▸ vc)
      · exact learned
    · exact learnSelection_sound laws slots (learnTruth_sound laws slots external fuel) learned read val

end Zkc.Core.BodyAnalysis.Knowledge
