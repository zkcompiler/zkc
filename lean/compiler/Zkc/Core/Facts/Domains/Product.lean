module

public import Zkc.Core.Facts.Domains.Interface

@[expose] public section

namespace Zkc.Core.BodyAnalysis

variable {T Raw Val : Type} {Run : Raw → List Val → List Val → Prop} {R : Reading Val}
    {Typed : Val → T → Prop}

theorem answer_orElse {α : Type} {a b : Option α} {x : α}
    (found : a.orElse (fun _ => b) = some x) : a = some x ∨ b = some x := by
  cases a with
  | none => exact .inr found
  | some _ => exact .inl found

theorem Asks.Sound.orElse {q r : Asks} {table : Table Raw} {ρ : Leaves Val}
    (hq : q.Sound Run R table ρ) (hr : r.Sound Run R table ρ) :
    (q.orElse r).Sound Run R table ρ where
  truth id b found := (answer_orElse found).elim (hq.truth id b) (hr.truth id b)
  exact id n found := (answer_orElse found).elim (hq.exact id n) (hr.exact id n)
  upper id n found := (answer_orElse found).elim (hq.upper id n) (hr.upper id n)

/-- The combined state means that both components hold on the same table and leaf assignment. -/
def Domain.Lawful.prod {A B : Domain T Raw} (a : A.Lawful Run R Typed) (b : B.Lawful Run R Typed) :
    (A.prod B).Lawful Run R Typed where
  Means s t ρ := a.Means s.1 t ρ ∧ b.Means s.2 t ρ
  mono sub extend holds := ⟨a.mono sub extend holds.1, b.mono sub extend holds.2⟩
  init t ρ := ⟨a.init t ρ, b.init t ρ⟩
  dead found holds := (Bool.or_eq_true_iff.mp found).elim (fun h => a.dead h holds.1)
    (fun h => b.dead h holds.2)
  answers holds := (a.answers holds.1).orElse (b.answers holds.2)
  leaves slots holds typed := ⟨a.leaves slots holds.1 typed, b.leaves slots holds.2 typed⟩
  transfer slots external holds member reads := by
    have left := a.transfer slots (external.orElse (b.answers holds.2)) holds.1 member reads
    exact ⟨left, b.transfer slots (external.orElse (a.answers left)) holds.2 member reads⟩
  observe slots external holds src dst num truth := by
    have left := a.observe slots (external.orElse (b.answers holds.2)) holds.1 src dst num truth
    exact ⟨left, b.observe slots (external.orElse (a.answers left)) holds.2 src dst num truth⟩
  assume slots external holds read known := by
    have left := a.assume slots (external.orElse (b.answers holds.2)) holds.1 read known
    exact ⟨left, b.assume slots (external.orElse (a.answers left)) holds.2 read known⟩
  truth slots external holds read found := (answer_orElse found).elim
    (a.truth slots (external.orElse (b.answers holds.2)) holds.1 read)
    (b.truth slots (external.orElse (a.answers holds.1)) holds.2 read)
  after slots prior member exit external results :=
    ⟨a.after slots prior.1 (List.mem_map_of_mem member) exit.1 (external.orElse (b.answers exit.2)) results,
     b.after slots prior.2 (List.mem_map_of_mem member) exit.2 (external.orElse (a.answers exit.1)) results⟩
  enter slots prior counts extend below iteration external := by
    have rightHere := b.mono (fun _ member => member) extend prior.2
    have left := a.enter slots prior.1 counts extend below iteration (external.orElse (b.answers rightHere))
    exact ⟨left, b.enter slots prior.2 counts extend below iteration (external.orElse (a.answers left))⟩
  afterLoop slots before prior counts initial history extend results := by
    constructor
    · apply a.afterLoop slots (before.orElse (b.answers prior.2)) prior.1 counts initial _ extend results
      intro k below
      obtain ⟨leaves, le, atIteration, out, exit, read⟩ := history k below
      exact ⟨leaves, le, atIteration, out.1, exit.orElse (b.answers out.2), read⟩
    · apply b.afterLoop slots (before.orElse (a.answers prior.1)) prior.2 counts initial _ extend results
      intro k below
      obtain ⟨leaves, le, atIteration, out, exit, read⟩ := history k below
      exact ⟨leaves, le, atIteration, out.2, exit.orElse (a.answers out.1), read⟩

theorem prodLawful : ProdLawfulStatement :=
  fun _ _ _ _ _ a b => ⟨a.prod b, fun _ _ _ => Iff.rfl⟩

#print axioms prodLawful

end Zkc.Core.BodyAnalysis
