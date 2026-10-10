/-! Structural provenance of provider-mediated sampling.

The four components have different meanings. A received coordinate is directly
peer-controlled; a received value absorbed into provider state is historical
input to a later sample. Moving it to history neither proves independence nor
establishes a random-oracle or Fiat–Shamir theorem.

These transfer laws specify the analysis abstraction. They do not certify the
native implementation or give a cryptographic interpretation to a provider.
-/

namespace Zkc.Compiler.Analysis.Sampling

variable {Origin : Type}

structure Provenance (Origin : Type) where
  draws : Origin → Prop
  received : Origin → Prop
  history : Origin → Prop
  unknown : Origin → Prop

def empty : Provenance Origin := ⟨fun _ => False, fun _ => False,
  fun _ => False, fun _ => False⟩

def join (a b : Provenance Origin) : Provenance Origin :=
  ⟨fun o => a.draws o ∨ b.draws o, fun o => a.received o ∨ b.received o,
   fun o => a.history o ∨ b.history o, fun o => a.unknown o ∨ b.unknown o⟩

/-- A message starts a new adversarial provenance boundary, even if its
authored honest sender computes the same value from trusted randomness. -/
def reception (event : Origin) : Provenance Origin :=
  { empty with received := fun o => o = event }

def observe (inputs : Provenance Origin) : Provenance Origin :=
  { empty with
    history := fun o => inputs.history o ∨ inputs.received o
    unknown := inputs.unknown }

/-- `arguments` excludes provider state. For a bounded index this includes
the bound, so absorbing a root cannot erase a peer-selected bound. -/
def sample (event : Origin) (provider arguments : Provenance Origin) : Provenance Origin :=
  { draws := fun o => o = event ∨ arguments.draws o
    received := arguments.received
    history := fun o => (join provider arguments).history o ∨
      (join provider arguments).received o
    unknown := (join provider arguments).unknown }

/-- The provider successor retains history and unknown coverage, rather than
pretending that all earlier samples directly select every later coordinate. -/
def successor (provider arguments : Provenance Origin) : Provenance Origin :=
  observe (join provider arguments)

def Refines (a b : Provenance Origin) : Prop :=
  (∀ o, a.draws o → b.draws o) ∧ (∀ o, a.received o → b.received o) ∧
  (∀ o, a.history o → b.history o) ∧ (∀ o, a.unknown o → b.unknown o)

theorem join_monotone {a b c d : Provenance Origin}
    (left : Refines a b) (right : Refines c d) : Refines (join a c) (join b d) := by
  rcases left with ⟨ld, lr, lh, lu⟩
  rcases right with ⟨rd, rr, rh, ru⟩
  exact ⟨fun o => Or.imp (ld o) (rd o), fun o => Or.imp (lr o) (rr o),
    fun o => Or.imp (lh o) (rh o), fun o => Or.imp (lu o) (ru o)⟩

theorem observe_monotone {a b : Provenance Origin}
    (h : Refines a b) : Refines (observe a) (observe b) := by
  rcases h with ⟨_, hr, hh, hu⟩
  exact ⟨fun _ => False.elim, fun _ => False.elim,
    fun o => Or.imp (hh o) (hr o), hu⟩

theorem sample_monotone (event : Origin) {p q a b : Provenance Origin}
    (provider : Refines p q) (arguments : Refines a b) :
    Refines (sample event p a) (sample event q b) := by
  have merged := join_monotone provider arguments
  exact ⟨fun o => Or.imp id (arguments.1 o), arguments.2.1,
    fun o => Or.imp (merged.2.2.1 o) (merged.2.1 o), merged.2.2.2⟩

theorem successor_monotone {p q a b : Provenance Origin}
    (provider : Refines p q) (arguments : Refines a b) :
    Refines (successor p a) (successor q b) :=
  observe_monotone (join_monotone provider arguments)

theorem sample_records_event (event : Origin) (p a : Provenance Origin) :
    (sample event p a).draws event := Or.inl rfl

theorem sample_preserves_direct_argument (event o : Origin) (p a : Provenance Origin)
    (h : a.received o) : (sample event p a).received o := h

theorem absorbed_reception_is_history (event o : Origin) (p a : Provenance Origin)
    (h : p.received o) : (sample event (observe p) a).history o :=
  Or.inl (Or.inl (Or.inr h))

theorem provider_history_does_not_imply_direct_control (event o : Origin)
    (p a : Provenance Origin) (h : ¬ a.received o) :
    ¬ (sample event p a).received o := h

theorem reception_does_not_inherit_draws (event o : Origin) :
    ¬ (reception event).draws o := id

theorem unknown_provider_is_retained (event o : Origin) (p a : Provenance Origin)
    (h : p.unknown o) : (sample event p a).unknown o := Or.inl h

end Zkc.Compiler.Analysis.Sampling
