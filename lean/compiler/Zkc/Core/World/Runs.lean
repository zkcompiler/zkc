module

public import Zkc.Core.World.Network

@[expose] public section

/-!
Runs: of a protocol against what the world gives, and of one role alone.
-/

namespace Zkc.Core

section
variable {V : Vocabulary} (M : Model V)

/-- How a run of a protocol ends. -/
inductive GEnd (A : Type) where
  | returned (a : A)
  | stopped (who : List Role) (why : Stop)

/-- An event of a run of a protocol: a value that flows, or what the world gives, with its
occurrence, its type and its value. -/
inductive Event where
  | flow (kind : FlowKind) (giver : Role) (getters : List Role) (at_ : Occurrence) (τ : V.Ty)
      (value : M.Val τ)
  | given (kind : GivenKind V) (owner : Role) (hearers : List Role) (at_ : Occurrence)
      (τ : V.Ty) (value : M.Val τ)

/-- What was sent in a run, in order. -/
def Event.sent : List (Event M) → List (Sent M)
  | [] => []
  | .flow kind giver getters at_ τ value :: rest =>
      ⟨giver, kind, getters, at_, τ, value⟩ :: Event.sent rest
  | .given .. :: rest => Event.sent rest

/-- A run of a protocol against what the world gives, with its events in order. -/
inductive GRun (source : Source M) {A : Type} :
    Protocol M A → List (Event M) → GEnd A → Prop where
  | done {a} : GRun source (.done a) [] (.returned a)
  | halt {who why} : GRun source (.halt (who, why)) [] (.stopped who why)
  | flow {kind giver getters at_ τ x} {k : Unit → Protocol M A} {events e} :
      GRun source (k ()) events e →
      GRun source (.call (.flow kind giver getters at_ τ x) k)
        (.flow kind giver getters at_ τ x :: events) e
  | given {kind owner hearers at_ ins payload τ v} {k : M.Val τ → Protocol M A} {events e} :
      source at_ τ = some v → GRun source (k v) events e →
      GRun source (.call (.given kind owner hearers at_ ins payload τ) k)
        (.given kind owner hearers at_ τ v :: events) e

/-- A run of a protocol against what the world gives. -/
def GExec (source : Source M) {A : Type} (p : Protocol M A) (e : GEnd A) : Prop :=
  ∃ events, GRun M source p events e

/-- The source answers a run of the protocol, whatever is drawn in public: a coin that some
role hears may be any value that its law allows; at every other event that the world gives,
the source has a value. -/
def Fed (source : Source M) {A : Type} : Protocol M A → Prop
  | .done _ => True
  | .halt _ => True
  | .call (.flow ..) k => Fed source (k ())
  | .call (.given (.coin law) _ (_ :: _) _ ins payload τ) k =>
      ∀ v, Allows M (.coin law) ins payload τ v → Fed source (k v)
  | .call (.given _ _ _ at_ _ _ τ) k => ∃ v, source at_ τ = some v ∧ Fed source (k v)

/-- Every answer that the source gives along a run of the protocol is one that the world may
give there. -/
def Lawful (source : Source M) {A : Type} : Protocol M A → Prop
  | .done _ => True
  | .halt _ => True
  | .call (.flow ..) k => Lawful source (k ())
  | .call (.given kind _ _ at_ ins payload τ) k =>
      ∀ v, source at_ τ = some v → Allows M kind ins payload τ v ∧ Lawful source (k v)

/-- Every answer that the source gives at non-heard events (private coins and service requests) is
lawful along every lawful branch of heard coins, matching `Fed`. -/
def LawfulPrivate (source : Source M) {A : Type} : Protocol M A → Prop
  | .done _ => True
  | .halt _ => True
  | .call (.flow ..) k => LawfulPrivate source (k ())
  | .call (.given (.coin law) _ (_ :: _) _ ins payload τ) k =>
      ∀ v, Allows M (.coin law) ins payload τ v → LawfulPrivate source (k v)
  | .call (.given kind _ _ at_ ins payload τ) k =>
      ∀ v, source at_ τ = some v → Allows M kind ins payload τ v ∧ LawfulPrivate source (k v)

/-- Two events at the same occurrence, alike but for their values, which differ. -/
def Event.Diverge : Event M → Event M → Prop
  | .flow kind giver getters at_ τ x, .flow kind' giver' getters' at' τ' x' =>
      kind = kind' ∧ giver = giver' ∧ getters = getters' ∧ at_ = at' ∧
        ∃ h : τ = τ', cast (congrArg M.Val h) x ≠ x'
  | .given kind owner hearers at_ τ x, .given kind' owner' hearers' at' τ' x' =>
      kind = kind' ∧ owner = owner' ∧ hearers = hearers' ∧ at_ = at' ∧
        ∃ h : τ = τ', cast (congrArg M.Val h) x ≠ x'
  | _, _ => False

/-- Two runs, as their events in order, fork: an equal prefix, then two events at the same
occurrence with different values. -/
def Fork (first second : List (Event M)) : Prop :=
  ∃ before x y rest₁ rest₂, first = before ++ x :: rest₁ ∧ second = before ++ y :: rest₂ ∧
    Event.Diverge M x y

/-- The network has ended as the protocol's run did: where the run returned, every role has
returned its part; where it stopped, the roles that stop have stopped with its reason. -/
def Ended {A : Type} {B : Role → Type} (post : ∀ r, A → B r → Prop)
    (net : Net M (fun _ => Stop) B) : GEnd A → Prop
  | .returned a => ∀ r, ∃ b, net r = .done b ∧ post r a b
  | .stopped who why => ∀ r, r ∈ who → net r = .halt why

/-- How the run of one role ends. -/
inductive Ending (B H : Type) where
  | returned (b : B)
  | stopped (payload : H)
  /-- It waits for a message that nothing below it gives. -/
  | blocked (at_ : Occurrence)

/-- The run of one role whose handlers have answered what they answer: the world gives it
coins, what it gives goes out, and nothing gives it a message. Messages that a run is given
are a handler of the channel, above this. The beginning of an attempt is answered `0`. The
record is what the role did, in order. -/
inductive Alone (source : Source M) (r : Role) {H B : Type} :
    Process (RSig M) H B → List (Happened M) → Ending B H → Prop where
  | done {b} : Alone source r (.done b) [] (.returned b)
  | halt {payload} : Alone source r (.halt payload) [] (.stopped payload)
  | give {kind getters at_ τ x} {k : Unit → Process (RSig M) H B} {record e} :
      Alone source r (k ()) record e →
      Alone source r (.call (.give kind getters at_ τ x) k)
        (.gave r kind getters at_ τ x :: record) e
  | waits {kind giver at_ τ} {k : M.Val τ → Process (RSig M) H B} :
      Alone source r (.call (.get kind giver at_ τ) k) [] (.blocked at_)
  | own {kind hearers at_ ins payload τ v} {k : M.Val τ → Process (RSig M) H B} {record e} :
      source at_ τ = some v → Alone source r (k v) record e →
      Alone source r (.call (.own kind hearers at_ ins payload τ) k)
        (.owned r kind at_ τ v :: record) e
  | hear {kind owner at_ τ v} {k : M.Val τ → Process (RSig M) H B} {record e} :
      source at_ τ = some v → Alone source r (k v) record e →
      Alone source r (.call (.hear kind owner at_ τ) k) (.heard r kind owner at_ τ v :: record) e
  | begin {at_} {k : Nat → Process (RSig M) H B} {record e} :
      Alone source r (k 0) record e →
      Alone source r (.call (.begin at_) k) (.began r at_ :: record) e
  | settle {at_} {k : Unit → Process (RSig M) H B} {record e} :
      Alone source r (k ()) record e →
      Alone source r (.call (.settle at_) k) (.settled r at_ :: record) e

/-- A legal prefix of a run of one role alone: what the role did so far, by the same steps as
`Alone`, stopping anywhere. -/
inductive AlonePrefix (source : Source M) (r : Role) {H B : Type} :
    Process (RSig M) H B → List (Happened M) → Prop where
  | start {p} : AlonePrefix source r p []
  | give {kind getters at_ τ x} {k : Unit → Process (RSig M) H B} {record} :
      AlonePrefix source r (k ()) record →
      AlonePrefix source r (.call (.give kind getters at_ τ x) k)
        (.gave r kind getters at_ τ x :: record)
  | own {kind hearers at_ ins payload τ v} {k : M.Val τ → Process (RSig M) H B} {record} :
      source at_ τ = some v → AlonePrefix source r (k v) record →
      AlonePrefix source r (.call (.own kind hearers at_ ins payload τ) k)
        (.owned r kind at_ τ v :: record)
  | hear {kind owner at_ τ v} {k : M.Val τ → Process (RSig M) H B} {record} :
      source at_ τ = some v → AlonePrefix source r (k v) record →
      AlonePrefix source r (.call (.hear kind owner at_ τ) k) (.heard r kind owner at_ τ v :: record)
  | begin {at_} {k : Nat → Process (RSig M) H B} {record} :
      AlonePrefix source r (k 0) record →
      AlonePrefix source r (.call (.begin at_) k) (.began r at_ :: record)
  | settle {at_} {k : Unit → Process (RSig M) H B} {record} :
      AlonePrefix source r (k ()) record →
      AlonePrefix source r (.call (.settle at_) k) (.settled r at_ :: record)

end

end Zkc.Core
