import Zkc.Protocols.ScalarBytecode.Endpoint.Execution

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.Suppliers
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint

/-- Representation relation at the three actual external operations.
    These are local obligations, not an assumed whole-program equivalence. -/
structure SupplierRel {S T : Type} (l : Supplier S) (r : Supplier T)
    (R : S → T → Prop) : Prop where
  read : ∀ k n s t, R s t →
    (l.read k n s).1 = (r.read k n t).1 ∧ R (l.read k n s).2 (r.read k n t).2
  ended : ∀ k s t, R s t →
    (l.ended k s).1 = (r.ended k t).1 ∧ R (l.ended k s).2 (r.ended k t).2
  challenge : ∀ k n s t, R s t → R (l.challenge k n s) (r.challenge k n t)

def WorldRel {S T : Type} (R : S → T → Prop) (a : World S) (b : World T) : Prop :=
  a.verifier = b.verifier ∧ R a.external b.external

theorem supplier_refl {S : Type} (s : Supplier S) : SupplierRel s s Eq where
  read := by intros; subst_vars; exact ⟨rfl,rfl⟩
  ended := by intros; subst_vars; exact ⟨rfl,rfl⟩
  challenge := by intros; subst_vars; rfl

theorem serve_related {S T : Type} {l : Supplier S} {r : Supplier T} {R : S → T → Prop}
    (h : SupplierRel l r R) (i : Instr) (v : Local) (s : S) (t : T) (hst : R s t) :
    (serve l i v s).1 = (serve r i v t).1 ∧ R (serve l i v s).2 (serve r i v t).2 := by
  rcases i with ⟨site,op,x,y,n,data,label,dest⟩
  cases op <;> simp only [serve]
  all_goals first | exact h.read _ _ _ _ hst | exact h.ended _ _ _ hst | exact ⟨True.intro,hst⟩

theorem notify_related {S T : Type} {l : Supplier S} {r : Supplier T} {R : S → T → Prop}
    (h : SupplierRel l r R) (p : Public) (es : List Event) (s : S) (t : T) (hst : R s t) :
    R (notify l p es s) (notify r p es t) := by
  induction es generalizing s t with
  | nil => exact hst
  | cons e es ih =>
    simp only [notify,List.foldl_cons]
    split
    · exact ih _ _ (h.challenge _ _ _ _ hst)
    · exact ih s t hst

theorem supplier_step {S T : Type} {l : Supplier S} {r : Supplier T} {R : S → T → Prop}
    (h : SupplierRel l r R) (hash : Hash) (i : Instr) (a : World S) (b : World T)
    (hab : WorldRel R a b) :
    Lift (WorldRel R) (openStep hash l i a) (openStep hash r i b) := by
  rcases a with ⟨av,s⟩; rcases b with ⟨bv,t⟩
  rcases hab with ⟨hv,hs⟩
  dsimp only at hv hs
  subst bv
  have ha := serve_related h i av s t hs
  unfold openStep
  dsimp only
  generalize serve l i av s = x at ha ⊢
  generalize serve r i av t = y at ha ⊢
  rcases x with ⟨xa,xs⟩; rcases y with ⟨ya,ys⟩
  rcases ha with ⟨he,hr⟩
  dsimp only at he hr ⊢
  subst ya
  have hn := notify_related h av.subject (eventsOf (update hash i xa av)) xs ys hr
  generalize update hash i xa av = out at hn ⊢
  cases out <;> exact (by constructor; exact ⟨rfl,hn⟩)

/-- All finite actual Zkc.Protocols.ScalarBytecode.Execution instruction clients, arbitrary public labels, hash,
    raw local states and related external representations, including failures. -/
theorem supplier_run {S T : Type} {l : Supplier S} {r : Supplier T} {R : S → T → Prop}
    (h : SupplierRel l r R) (hash : Hash) (ops : List Instr) (a : World S) (b : World T)
    (hab : WorldRel R a b) :
    TerminalRel (WorldRel R) (run (openStep hash l) ops a) (run (openStep hash r) ops b) :=
  simulation _ _ _ (supplier_step h hash) ops a b hab

/-- A deliberately weaker contract than immutable-tape representation.
    Closure is persistent through reads, end queries, and public notices. -/
structure ClosedLaw {S : Type} (supplier : Supplier S) (closed : S → Prop) : Prop where
  read_empty : ∀ k n s, closed s → (supplier.read k n s).1.val = []
  read_preserves : ∀ k n s, closed s → closed (supplier.read k n s).2
  end_true : ∀ k s, closed s → (supplier.ended k s).1 = true
  end_preserves : ∀ k s, closed s → closed (supplier.ended k s).2
  end_closes : ∀ k s, (supplier.ended k s).1 = true → closed (supplier.ended k s).2
  challenge_preserves : ∀ k n s, closed s → closed (supplier.challenge k n s)

inductive Call where
  | read (key : Key) (bound : Nat)
  | ended (key : Key)
  | challenge (key : Key) (value : Nat)

def advance {S : Type} (supplier : Supplier S) : Call → S → S
  | .read k n,s => (supplier.read k n s).2
  | .ended k,s => (supplier.ended k s).2
  | .challenge k n,s => supplier.challenge k n s

theorem closed_calls {S : Type} {supplier : Supplier S} {closed : S → Prop}
    (h : ClosedLaw supplier closed) (calls : List Call) (s : S) (hs : closed s) :
    closed (calls.foldl (fun s c => advance supplier c s) s) := by
  induction calls generalizing s with
  | nil => exact hs
  | cons c cs ih =>
    apply ih
    cases c with
    | read k n => exact h.read_preserves k n s hs
    | ended k => exact h.end_preserves k s hs
    | challenge k n => exact h.challenge_preserves k n s hs

theorem end_then_calls {S : Type} {supplier : Supplier S} {closed : S → Prop}
    (h : ClosedLaw supplier closed) (k : Key) (s : S)
    (he : (supplier.ended k s).1 = true) (calls : List Call) (k' : Key) (n : Nat) :
    let t := calls.foldl (fun s c => advance supplier c s) (supplier.ended k s).2
    (supplier.ended k' t).1 = true ∧ (supplier.read k' n t).1.val = [] := by
  have ht := closed_calls h calls _ (h.end_closes k s he)
  exact ⟨h.end_true k' _ ht,h.read_empty k' n _ ht⟩

end Zkc.Protocols.ScalarBytecode.Suppliers
