module

public import Zkc.Core.Facts.Domains.UnaryMeasurements
public import Zkc.Core.Facts.Knowledge.Transfer

@[expose] public section
namespace Zkc.Core.BodyAnalysis.UnaryMeasurements
variable {T Raw Val : Type} {R : Reading Val} {Run : Raw → List Val → List Val → Prop}
variable {measure : Val → Option Nat} {table : Table Raw} {ρ : Leaves Val}

/-- The two readings of every recorded pair agree, including after table growth. -/
def Links (Run : Raw → List Val → List Val → Prop) (R : Reading Val)
    (left right : Val → Option Nat) (pairs : NatMap Ident) (table : Table Raw) (ρ : Leaves Val) : Prop :=
  ∀ (i j : Ident), pairs.find i.key = some j → ∃ x y, Reads Run R.bool table ρ i x ∧ Reads Run R.bool table ρ j y ∧ left x = right y

structure Holds (Run : Raw → List Val → List Val → Prop) (R : Reading Val)
    (measure : Val → Option Nat) (s : State) (table : Table Raw) (ρ : Leaves Val) : Prop where
  subjects : Links Run R measure measure s.subjects table ρ
  measurements : Links Run R measure R.nat s.measurements table ρ
  numbers : Links Run R R.nat R.nat s.numbers table ρ

variable {left right : Val → Option Nat} {pairs : NatMap Ident}

theorem Links.empty : Links Run R left right .leaf table ρ := fun _ _ m => nomatch m

theorem Links.mono (h : Links Run R left right pairs table ρ) {other : Table Raw} {more : Leaves Val}
    (sub : table.Le other) (ext : ρ.Le more) : Links Run R left right pairs other more := by
  intro i j mem
  obtain ⟨x,y,rx,ry,same⟩ := h i j mem
  exact ⟨x,y,rx.mono sub ext,ry.mono sub ext,same⟩

theorem Holds.mono {s : State} {other : Table Raw} {more : Leaves Val}
    (h : Holds Run R measure s table ρ) (sub : table.Le other) (ext : ρ.Le more) :
    Holds Run R measure s other more :=
  ⟨h.subjects.mono sub ext, h.measurements.mono sub ext, h.numbers.mono sub ext⟩

theorem Links.insert (h : Links Run R left right pairs table ρ) {i j x y}
    (rx : Reads Run R.bool table ρ i x) (ry : Reads Run R.bool table ρ j y) (eq : left x = right y) :
    Links Run R left right (pairs.insert i.key j) table ρ := by
  intro a b found
  rw [NatMap.find_insert] at found
  split at found
  · next key =>
    obtain rfl := Ident.key_injective key
    cases found
    exact ⟨_,_,rx,ry,eq⟩
  · exact h _ _ found

theorem Links.link (h : Links Run R left right pairs table ρ) {i j x y}
    (rx : Reads Run R.bool table ρ i x) (ry : Reads Run R.bool table ρ j y) (eq : left x = right y) :
    Links Run R left right (link pairs i j) table ρ := by
  unfold UnaryMeasurements.link
  split
  · exact h
  · exact h.insert rx ry eq

variable (functional : ∀ op xs ys zs, Run op xs ys → Run op xs zs → ys = zs)
include functional in
theorem Links.representative (wf : table.WF) (h : Links Run R left left pairs table ρ) {i x}
    (rx : Reads Run R.bool table ρ i x) :
    ∃ y, Reads Run R.bool table ρ (representative pairs i) y ∧ left x = left y := by
  cases found : pairs.find i.key with
  | none => exact ⟨x, by simpa [UnaryMeasurements.representative, found] using rx, rfl⟩
  | some j =>
    obtain ⟨a,b,ra,rb,eq⟩ := h _ _ found
    cases Reads.functionalOn functional wf rx ra
    exact ⟨b, by simpa [UnaryMeasurements.representative, found] using rb, eq⟩

include functional in
theorem observe_sound {s : State} (wf : table.WF) (h : Holds Run R measure s table ρ) {i j x y}
    (rx : Reads Run R.bool table ρ i x) (ry : Reads Run R.bool table ρ j y)
    (num : R.nat x = R.nat y) (same : measure x = measure y) : Holds Run R measure (observe s i j) table ρ := by
  obtain ⟨u,ru,mu⟩ := h.subjects.representative functional wf rx
  obtain ⟨v,rv,nv⟩ := h.numbers.representative functional wf rx
  exact ⟨h.subjects.link ry ru (same.symm.trans mu), h.measurements, h.numbers.link ry rv (num.symm.trans nv)⟩

include functional in
theorem record_sound {s : State} (wf : table.WF) (h : Holds Run R measure s table ρ) {i j x y}
    (rx : Reads Run R.bool table ρ i x) (ry : Reads Run R.bool table ρ j y)
    (eq : R.nat y = measure x) : Holds Run R measure (record s j i) table ρ := by
  obtain ⟨u,ru,mu⟩ := h.subjects.representative functional wf rx
  simp only [record]
  split
  · exact ⟨h.subjects, h.measurements.insert ru ry (mu.symm.trans eq.symm), h.numbers⟩
  · next first found =>
    obtain ⟨a,b,ra,rb,m⟩ := h.measurements _ _ found
    cases Reads.functionalOn functional wf ru ra
    exact ⟨h.subjects, h.measurements, h.numbers.link ry rb (eq.trans (mu.trans m))⟩

variable {measures : Raw → Bool}
variable (readsMeasure : ∀ op x vs v, measures op = true → Run op [x] vs →
  vs[0]? = some v → R.nat v = measure x)
include functional readsMeasure in
theorem transfer_sound {s : State} {e : Entry Raw} (wf : table.WF)
    (h : Holds Run R measure s table ρ) (mem : e ∈ table)
    (live : ∀ j, j < e.count → ∃ v, Reads Run R.bool table ρ (.val (e.lo+j)) v) :
    Holds Run R measure (transfer measures s e) table ρ := by
  unfold transfer
  split
  · next op x shape =>
    split
    · next ok =>
      obtain ⟨isMeasure, liveSlot⟩ := Bool.and_eq_true_iff.mp ok
      have pos : 0 < e.count := of_decide_eq_true liveSlot
      obtain ⟨v,ry⟩ := live 0 pos
      obtain ⟨xs,vs,inputs,run,first⟩ := ry.application wf mem shape pos rfl
      cases inputs with | cons rx rest =>
        cases rest
        exact record_sound functional wf h rx ry (readsMeasure _ _ _ _ isMeasure run first)
    · exact h
  · exact h

def lawful (functional : ∀ op xs ys zs, Run op xs ys → Run op xs zs → ys = zs)
    (readsMeasure : ∀ op x vs v, measures op = true → Run op [x] vs →
      vs[0]? = some v → R.nat v = measure x)
    (congruent : ∀ {x y}, R.SameSubject x y → measure x = measure y)
    (typed : Val → T → Prop) : (domain measures).Lawful Run R typed where
  Means := Holds Run R measure
  mono sub ext h := h.mono sub ext
  init _ _ := ⟨Links.empty, Links.empty, Links.empty⟩
  dead := by intros; contradiction
  answers h := ⟨by intros; contradiction, by intros; contradiction, by intros; contradiction,
    h.numbers⟩
  leaves _ h _ := h
  transfer wf _ h mem live := transfer_sound functional readsMeasure wf h mem live
  observe wf _ h rx ry eq := observe_sound functional wf h rx ry eq.number (congruent eq.subject)
  assume _ _ h _ _ := h
  truth := by intros; contradiction
  after _ h _ _ _ _ := h
  enter _ h _ ext _ _ _ := h.mono (fun _ m => m) ext
  afterLoop _ _ h _ _ _ ext _ := h.mono (fun _ m => m) ext

end Zkc.Core.BodyAnalysis.UnaryMeasurements
