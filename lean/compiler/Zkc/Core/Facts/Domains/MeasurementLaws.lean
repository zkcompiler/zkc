module

public import Zkc.Core.Facts.Domains.UnaryMeasurements
public import Zkc.Core.Facts.Knowledge.Transfer

@[expose] public section
namespace Zkc.Core.BodyAnalysis.UnaryMeasurements
variable {T Raw Val : Type} {R : Reading Val} {Run : Raw → List Val → List Val → Prop}
variable {measure : Val → Option Nat} {table : Table Raw} {ρ : Leaves Val}

abbrev At (Run : Raw → List Val → List Val → Prop) (R : Reading Val) :=
  Reads Run R.bool

/-- Each cached answer has a reading even when the table subsequently grows. -/
structure Holds (Run : Raw → List Val → List Val → Prop) (R : Reading Val)
    (measure : Val → Option Nat) (s : State) (table : Table Raw) (ρ : Leaves Val) : Prop where
  sample : ∀ y x, (y,x) ∈ s.samples → ∃ u v, At Run R table ρ x u ∧ At Run R table ρ y v ∧ R.nat v = measure u
  known : ∀ x n, (x,n) ∈ s.exacts → ∃ u, At Run R table ρ x u ∧ measure u = some n
  answer : ∀ y x n, (y,x) ∈ s.samples → (x,n) ∈ s.exacts → ∃ v, At Run R table ρ y v ∧ R.nat v = some n

theorem Holds.mono {s : State} {other : Table Raw} {more : Leaves Val}
    (h : Holds Run R measure s table ρ) (sub : table.Le other) (ext : ρ.Le more) :
    Holds Run R measure s other more where
  sample y x mem := by
    obtain ⟨u,v,rx,ry,eq⟩ := h.sample y x mem
    exact ⟨u,v,rx.mono sub ext,ry.mono sub ext,eq⟩
  known x n mem := by
    obtain ⟨u,rx,eq⟩ := h.known x n mem
    exact ⟨u,rx.mono sub ext,eq⟩
  answer y x n seen known := by
    obtain ⟨v,ry,eq⟩ := h.answer y x n seen known
    exact ⟨v,ry.mono sub ext,eq⟩

theorem lookup_mem {A B : Type} [BEq A] [LawfulBEq A] {xs : List (A × B)} {a : A} {b : B}
    (found : xs.lookup a = some b) : (a,b) ∈ xs := by
  obtain ⟨before,after,rfl,_⟩ := List.lookup_eq_some_iff.mp found
  simp

theorem exact_sound {s : State} (h : Holds Run R measure s table ρ) {id : Ident} {n : Nat}
    (answer : exact s id = some n) : ∃ v, At Run R table ρ id v ∧ R.nat v = some n := by
  obtain ⟨x,hit,known⟩ := Option.bind_eq_some_iff.mp answer
  exact h.answer _ _ _ (lookup_mem hit) (lookup_mem known)

variable (functional : ∀ op xs ys zs, Run op xs ys → Run op xs zs → ys = zs)
include functional in
theorem close {s : State} (wf : table.WF)
    (sample : ∀ y x, (y,x) ∈ s.samples → ∃ u v, At Run R table ρ x u ∧ At Run R table ρ y v ∧ R.nat v = measure u)
    (known : ∀ x n, (x,n) ∈ s.exacts → ∃ u, At Run R table ρ x u ∧ measure u = some n) :
    Holds Run R measure s table ρ where
  sample := sample
  known := known
  answer y x n seen cached := by
    obtain ⟨u,v,rx,ry,eq⟩ := sample y x seen
    obtain ⟨u',rx',value⟩ := known x n cached
    cases Reads.functionalOn functional wf rx rx'
    exact ⟨v,ry,eq.trans value⟩

include functional in
theorem learn_sound {asks : Asks} {s : State} (wf : table.WF)
    (peer : asks.Sound Run R table ρ) (h : Holds Run R measure s table ρ) :
    Holds Run R measure (learn asks s) table ρ := by
  apply close (s := learn asks s) functional wf h.sample
  intro x n mem
  rcases List.mem_append.mp mem with fresh | old
  · have fresh := (List.mem_filter.mp fresh).1
    obtain ⟨⟨y,z⟩,seen,found⟩ := List.mem_filterMap.mp fresh
    obtain ⟨m,answer,eq⟩ := Option.map_eq_some_iff.mp found
    cases eq
    obtain ⟨v,ry,value⟩ := peer.exact y n answer
    obtain ⟨u,v',rx,ry',eq⟩ := h.sample y x seen
    cases Reads.functionalOn functional wf ry ry'
    exact ⟨u,rx,eq.symm.trans value⟩
  · exact h.known x n old

variable {measures : Raw → Bool}
variable (readsMeasure : ∀ op x vs v, measures op = true → Run op [x] vs →
  vs[0]? = some v → R.nat v = measure x)
include functional readsMeasure in
theorem transfer_sound {s : State} {e : Entry Raw} (wf : table.WF)
    (h : Holds Run R measure s table ρ) (mem : e ∈ table)
    (live : ∀ j, j < e.count → ∃ v, At Run R table ρ (.val (e.lo+j)) v) :
    Holds Run R measure (transfer measures s e) table ρ := by
  unfold transfer
  split
  · next op x shape =>
    split
    · next ok =>
      obtain ⟨isMeasure, liveSlot⟩ := Bool.and_eq_true_iff.mp ok
      have pos : 0 < e.count := of_decide_eq_true liveSlot
      apply close (s := { s with samples := (.val e.lo,x) :: s.samples }) functional wf (known := h.known)
      intro y z seen
      rcases List.mem_cons.mp seen with same | old
      · cases same
        obtain ⟨v,ry⟩ := live 0 pos
        obtain ⟨xs,vs,inputs,run,first⟩ := ry.application wf mem shape pos rfl
        cases inputs with | cons rx rest =>
          cases rest
          exact ⟨_,v,rx,ry,readsMeasure _ _ _ _ isMeasure run first⟩
      · exact h.sample y z old
    · exact h
  · exact h

def lawful (functional : ∀ op xs ys zs, Run op xs ys → Run op xs zs → ys = zs)
    (readsMeasure : ∀ op x vs v, measures op = true → Run op [x] vs →
      vs[0]? = some v → R.nat v = measure x) (typed : Val → T → Prop) : (domain measures).Lawful Run R typed where
  Means := Holds Run R measure
  mono sub ext h := h.mono sub ext
  init _ _ := ⟨by intros; contradiction, by intros; contradiction, by intros; contradiction⟩
  dead := by intros; contradiction
  answers h := ⟨by intros; contradiction, fun _ _ a => exact_sound h a, fun _ n a => by
    obtain ⟨v,r,eq⟩ := exact_sound h a
    exact ⟨v,n,r,eq,Nat.le_refl _⟩⟩
  leaves _ h _ := h
  transfer wf _ h mem live := transfer_sound functional readsMeasure wf h mem live
  observe _ _ h _ _ _ _ := h
  assume wf peer h _ _ := learn_sound functional wf peer h
  truth := by intros; contradiction
  after _ h _ _ _ _ := h
  enter _ h _ ext _ _ _ := h.mono (fun _ m => m) ext
  afterLoop _ _ h _ _ _ ext _ := h.mono (fun _ m => m) ext

end Zkc.Core.BodyAnalysis.UnaryMeasurements
