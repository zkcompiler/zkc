import Std


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace Zkc.Modules.Factor

/-- Symbolic origin and variable order, not equality of table contents or
    physical addresses. A source adapter must justify these identities. -/
structure Key where
  origin : Nat
  axes : List Nat
  deriving DecidableEq, Repr
structure Fact where
  key : Key
  handle : Nat
  applied : List Nat
  remaining : Nat
  deriving DecidableEq, Repr
structure Query where
  key : Key
  point : List Nat
  deriving DecidableEq, Repr

/-- Pure factor evaluation only. Correlated-resource acquisition and transcript
    effects are not expressions in this language. -/
inductive Plan where
  | direct
  | reuse (fact : Fact) (suffix : List Nat)
  deriving DecidableEq, Repr

variable {K : Type}
structure State (K : Type) where
  base : Key → List K → K
  view : Nat → List K → K
  challenge : Nat → K

def Means (s : State K) (f : Fact) : Prop :=
  ∀ tail, tail.length = f.remaining →
    s.view f.handle tail = s.base f.key (f.applied.map s.challenge ++ tail)
def Valid (s : State K) (facts : List Fact) : Prop := ∀ f ∈ facts, Means s f

def runQuery (s : State K) (q : Query) := s.base q.key (q.point.map s.challenge)
def runPlan (s : State K) (q : Query) : Plan → K
  | .direct => runQuery s q
  | .reuse f suffix => s.view f.handle (suffix.map s.challenge)

def eligible (available : List Nat) (q : Query) (f : Fact) : Bool := decide (
  f.key = q.key ∧ f.applied ++ q.point.drop f.applied.length = q.point ∧
  f.remaining = (q.point.drop f.applied.length).length ∧
  q.point.length = q.key.axes.length ∧
  (∀ x ∈ q.point, x ∈ available))

/-- Independently check a proposed plan against the consumer's query/facts.
    Its supplied fact does not establish its own availability or source. -/
def check (facts : List Fact) (available : List Nat) (q : Query) : Plan → Bool
  | .direct => true
  | .reuse f suffix => decide (f ∈ facts ∧ eligible available q f = true ∧
      suffix = q.point.drop f.applied.length)

theorem checked_value (s : State K) (facts : List Fact) (available : List Nat)
    (q : Query) (p : Plan) (valid : Valid s facts) (ok : check facts available q p = true) :
    runPlan s q p = runQuery s q := by
  cases p with
  | direct => rfl
  | reuse f suffix =>
    obtain ⟨member,accepted,hs⟩ := of_decide_eq_true ok
    obtain ⟨hk,hp,hr,_,_⟩ := of_decide_eq_true accepted
    subst suffix
    change s.view f.handle ((q.point.drop f.applied.length).map s.challenge) = _
    calc
      _ = s.base f.key (f.applied.map s.challenge ++
          (q.point.drop f.applied.length).map s.challenge) := valid f member _ (by simpa using hr.symm)
      _ = runQuery s q := by rw [hk,← List.map_append,hp]; rfl

/-- Invalidation is mandatory when a materialized handle is overwritten. -/
def kill (handle : Nat) (facts : List Fact) := facts.filter (fun f => f.handle != handle)
def overwrite (s : State K) (handle : Nat) (v : List K → K) : State K :=
  {s with view := fun h => if h = handle then v else s.view h}

theorem kill_valid (s : State K) (facts : List Fact) (valid : Valid s facts)
    (handle : Nat) (v : List K → K) : Valid (overwrite s handle v) (kill handle facts) := by
  intro f hf
  obtain ⟨hm,hn⟩ := List.mem_filter.mp hf
  have hn' : f.handle ≠ handle := by simpa using hn
  intro tail ht
  simpa [overwrite,hn'] using valid f hm tail ht

/-- Semantic producer: materializing an applied prefix establishes a new fact.
    Native phase adapters still owe this representation interpretation. -/
def retain (s : State K) (f : Fact) : State K :=
  overwrite s f.handle (fun tail => s.base f.key (f.applied.map s.challenge ++ tail))
def remember (f : Fact) (facts : List Fact) := f :: kill f.handle facts

theorem remember_valid (s : State K) (facts : List Fact) (valid : Valid s facts) (f : Fact) :
    Valid (retain s f) (remember f facts) := by
  intro g hg
  rcases List.mem_cons.mp hg with h | h
  · subst g
    intro tail _
    simp [retain,overwrite]
  · exact kill_valid s facts valid f.handle _ g h

end Zkc.Modules.Factor
