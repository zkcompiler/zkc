module

public import Zkc.Obligations.Token

public section

/-! Mathematical claim boundaries. A relation owns its witness predicate and
its possibly gapped No side. A pending claim is not evidence for either side.
Source visibility marks and extraction registrations stay with their owning
declarations and requests; they do not change these predicates. -/

namespace Zkc.Obligations
universe u v w x

structure ClaimRelation (Statement : Type u) (Witness : Type v) where
  Holds : Statement → Witness → Prop
  No : Statement → Prop
  no_excludes : ∀ statement witness, No statement → Holds statement witness → False

namespace ClaimRelation
variable {S : Type u} {W : Type v} {T : Type w} {V : Type x}

@[expose] def token (relation : ClaimRelation S W) : Token S where
  Yes statement := ∃ witness, relation.Holds statement witness
  No := relation.No
  disjoint statement yes no := by
    obtain ⟨witness, holds⟩ := yes
    exact relation.no_excludes statement witness no holds

@[expose] def exact (holds : S → W → Prop) : ClaimRelation S W where
  Holds := holds
  No statement := ¬ ∃ witness, holds statement witness
  no_excludes _ witness no yes := no ⟨witness, yes⟩

@[expose] def pullback (relation : ClaimRelation T W) (map : S → T) : ClaimRelation S W where
  Holds statement := relation.Holds (map statement)
  No statement := relation.No (map statement)
  no_excludes statement := relation.no_excludes (map statement)

/-- The map is chosen separately. A soundness adapter transports the actual No
side, including its distance threshold; Yes equivalence is insufficient. -/
@[expose] def SoundLink (source : ClaimRelation S W) (target : ClaimRelation T V)
    (map : S → T) : Prop := ∀ statement, source.No statement → target.No (map statement)

/-- Honest transport has no extraction content. In particular, this proposition
does not provide an executable witness map or its inverse. -/
@[expose] def HonestLink (source : ClaimRelation S W) (target : ClaimRelation T V)
    (map : S → T) : Prop :=
  ∀ statement, source.token.Yes statement → target.token.Yes (map statement)

theorem SoundLink.id (relation : ClaimRelation S W) : relation.SoundLink relation id :=
  fun _ no => no

theorem HonestLink.id (relation : ClaimRelation S W) : relation.HonestLink relation id :=
  fun _ yes => yes

theorem SoundLink.comp {U : Type*} {X : Type*}
    {source : ClaimRelation S W} {middle : ClaimRelation T V} {target : ClaimRelation U X}
    {first : S → T} {second : T → U}
    (left : source.SoundLink middle first) (right : middle.SoundLink target second) :
    source.SoundLink target (second ∘ first) :=
  fun statement no => right _ (left statement no)

theorem HonestLink.comp {U : Type*} {X : Type*}
    {source : ClaimRelation S W} {middle : ClaimRelation T V} {target : ClaimRelation U X}
    {first : S → T} {second : T → U}
    (left : source.HonestLink middle first) (right : middle.HonestLink target second) :
    source.HonestLink target (second ∘ first) :=
  fun statement yes => right _ (left statement yes)

end ClaimRelation

/-- A partial readback establishes a predicate only when it is defined.
Absence never chooses a mathematical value and never discharges a claim. -/
@[expose] def ReadbackHolds {S : Type u} (predicate : S → Prop) (readback : Option S) : Prop :=
  ∃ statement, readback = some statement ∧ predicate statement

theorem ReadbackHolds.some {S : Type u} {predicate : S → Prop} {value : S} :
    ReadbackHolds predicate (some value) ↔ predicate value := by
  simp only [ReadbackHolds, Option.some.injEq, exists_eq_left']

theorem ReadbackHolds.none {S : Type u} (predicate : S → Prop) :
    ¬ ReadbackHolds predicate none := by
  rintro ⟨_, impossible, _⟩
  cases impossible

theorem ReadbackHolds.mono {S : Type u} {before after : S → Prop} {readback : Option S}
    (implies : ∀ value, before value → after value)
    (holds : ReadbackHolds before readback) : ReadbackHolds after readback := by
  obtain ⟨value, defined, proof⟩ := holds
  exact ⟨value, defined, implies value proof⟩

end Zkc.Obligations
