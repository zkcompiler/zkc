module

public import Zkc.Core.Meaning.Events

@[expose] public section

/-!
The network of the roles of a protocol: what is pending, what the world gives, the
steps of an execution and its record.
-/

namespace Zkc.Core

/-! ## The network -/

section
variable {V : Vocabulary} (M : Model V)

/-- A message that waits for one receiver. -/
structure Delivery where
  sender : Role
  kind : FlowKind
  τ : V.Ty
  value : M.Val τ

/-- What is pending: a message for one receiver at one occurrence, which a receive by that
receiver consumes. A message to several receivers is pending once per receiver. -/
abbrev Pending : Type := Occurrence → Role → Option (Delivery M)

def Pending.empty : Pending M := fun _ _ => none

def Pending.put (pending : Pending M) (at_ : Occurrence) (receiver : Role) (d : Delivery M) :
    Pending M :=
  fun at' r => if at' = at_ ∧ r = receiver then some d else pending at' r

def Pending.take (pending : Pending M) (at_ : Occurrence) (receiver : Role) : Pending M :=
  fun at' r => if at' = at_ ∧ r = receiver then none else pending at' r

def Pending.post (pending : Pending M) (at_ : Occurrence) (getters : List Role) (d : Delivery M) :
    Pending M :=
  getters.foldl (fun p r => p.put M at_ r d) pending

/-- One program per role. A role's stop carries what its kind of program carries: a reason,
or a reason with the state of its handlers. -/
abbrev Net (H B : Role → Type) : Type := ∀ r, Process (RSig M) (H r) (B r)

def Net.set {H B : Role → Type} (net : Net M H B) (r : Role) (q : Process (RSig M) (H r) (B r)) :
    Net M H B :=
  fun r' => if h : r' = r then h ▸ q else net r'

/-- What the world gives at each occurrence. -/
abbrev Source : Type := Occurrence → (τ : V.Ty) → Option (M.Val τ)

/-- What one step of a run was: which role did what, where, with which value. The record of
an execution is the list of these, and only grows. -/
inductive Happened where
  | gave (r : Role) (kind : FlowKind) (getters : List Role) (at_ : Occurrence) (τ : V.Ty)
      (value : M.Val τ)
  | got (r : Role) (kind : FlowKind) (giver : Role) (at_ : Occurrence) (τ : V.Ty)
      (value : M.Val τ)
  | owned (r : Role) (kind : GivenKind V) (at_ : Occurrence) (τ : V.Ty) (value : M.Val τ)
  | heard (r : Role) (kind : GivenKind V) (owner : Role) (at_ : Occurrence) (τ : V.Ty)
      (value : M.Val τ)
  | began (r : Role) (at_ : Occurrence)
  | settled (r : Role) (at_ : Occurrence)

/-- A value that one role gave to others. -/
structure Sent where
  giver : Role
  kind : FlowKind
  getters : List Role
  at_ : Occurrence
  τ : V.Ty
  value : M.Val τ

/-- What was sent in a record, in order. -/
def Happened.sent : List (Happened M) → List (Sent M)
  | [] => []
  | .gave r kind getters at_ τ value :: rest => ⟨r, kind, getters, at_, τ, value⟩ :: sent rest
  | _ :: rest => sent rest

/-- A step of the network: one role performs one effect. A role gets only what was given to
it, from the role it names, and getting it consumes it. The beginning of an attempt is
answered `0`, and the end of its body nothing. -/
inductive Step (source : Source M) {H B : Role → Type} :
    Net M H B × Pending M → Happened M → Net M H B × Pending M → Prop where
  | give {net pending r kind getters at_ τ x k} :
      net r = .call (.give kind getters at_ τ x) k →
      (∀ g, g ∈ getters → pending at_ g = none) →
      Step source (net, pending) (.gave r kind getters at_ τ x)
        (net.set M r (k ()), pending.post M at_ getters ⟨r, kind, τ, x⟩)
  | get {net pending r kind giver at_ τ x} {k : M.Val τ → Process (RSig M) (H r) (B r)} :
      net r = .call (.get kind giver at_ τ) k → pending at_ r = some ⟨giver, kind, τ, x⟩ →
      Step source (net, pending) (.got r kind giver at_ τ x)
        (net.set M r (k x), pending.take M at_ r)
  | own {net pending r kind hearers at_ ins payload τ v}
      {k : M.Val τ → Process (RSig M) (H r) (B r)} :
      net r = .call (.own kind hearers at_ ins payload τ) k → source at_ τ = some v →
      Step source (net, pending) (.owned r kind at_ τ v) (net.set M r (k v), pending)
  | hear {net pending r kind owner at_ τ v} {k : M.Val τ → Process (RSig M) (H r) (B r)} :
      net r = .call (.hear kind owner at_ τ) k → source at_ τ = some v →
      Step source (net, pending) (.heard r kind owner at_ τ v) (net.set M r (k v), pending)
  | begin {net pending r at_} {k : Nat → Process (RSig M) (H r) (B r)} :
      net r = .call (.begin at_) k →
      Step source (net, pending) (.began r at_) (net.set M r (k 0), pending)
  | settle {net pending r at_} {k : Unit → Process (RSig M) (H r) (B r)} :
      net r = .call (.settle at_) k →
      Step source (net, pending) (.settled r at_) (net.set M r (k ()), pending)

/-- An execution of the network, with its record. -/
inductive Reach (source : Source M) {H B : Role → Type} :
    Net M H B × Pending M → List (Happened M) → Net M H B × Pending M → Prop where
  | refl {c} : Reach source c [] c
  | step {c c' c'' h record} : Step M source c h c' → Reach source c' record c'' →
      Reach source c (h :: record) c''

/-- No role can move. -/
def Quiescent (source : Source M) {H B : Role → Type} (c : Net M H B × Pending M) : Prop :=
  ∀ h c', ¬ Step M source c h c'

/-- The role waits for a message that is not pending: it is blocked, which is neither a
return nor a stop. -/
def Waits {H B : Role → Type} (c : Net M H B × Pending M) (r : Role) (at_ : Occurrence) : Prop :=
  ∃ kind giver τ k, c.1 r = .call (.get kind giver at_ τ) k ∧
    ∀ x, c.2 at_ r ≠ some ⟨giver, kind, τ, x⟩

/-- The role is at an effect of what the world gives, at an occurrence and a type that the
source does not answer: it starves, which is neither a return nor a stop. -/
def Starves (source : Source M) {H B : Role → Type} (c : Net M H B × Pending M) (r : Role)
    (at_ : Occurrence) : Prop :=
  ∃ τ, source at_ τ = none ∧
    ((∃ kind hearers ins payload k, c.1 r = .call (.own kind hearers at_ ins payload τ) k) ∨
      ∃ kind owner k, c.1 r = .call (.hear kind owner at_ τ) k)

end

end Zkc.Core
