module

public import Zkc.Formal.Written.TableVerifier
public import Zkc.Formal.ProbabilisticProcess

@[expose] public section
namespace Zkc.Formal.Written.TableService
open Core Frontend.Emit TableVerifier ProbabilisticProcess

abbrev Draw := Fin 40 → Fin 1024
structure Offer (H R : Type) where
  handle : H
  data : Fin 1024 → R

/-- An opener may choose its response after seeing the request. -/
abbrev Opener (H R : Type) := H → List Nat → H × List R

inductive State (H R : Type) where
  | empty
  | registered (offer : Offer H R)
  | drawn (offer : Offer H R) (positions : Draw)
  | answered (offer : Offer H R) (positions : Draw) (claimed : H) (rows : List R)
  | closed

def request (ps : Draw) := List.ofFn fun i => (ps i).val
def values {R : Type} (data : Fin 1024 → R) (ps : Draw) := List.ofFn fun i => data (ps i)

/-- Look up the actual requested indices in order, including repeated requests. -/
def honest {H R : Type} (data : Fin 1024 → R) : Opener H R :=
  fun h ix => (h, ix.filterMap fun i => if within : i < 1024 then some (data ⟨i,within⟩) else none)

theorem honest_rows {H R : Type} (data : Fin 1024 → R) (h : H) (ps : Draw) :
    honest data h (request ps) = (h,values data ps) := by
  simp [honest, request, values]

/-- The opening binds the registered handle, the opener's handle, the actual indices
and both copies of the returned rows to the immutable table. -/
def opens {H R : Type} [DecidableEq H] [DecidableEq R] (offer : Offer H R)
    (ps : Draw) (submitted : H × List R) (h : H) (ix : List Nat) (rows : List R) : Bool :=
  decide (h = offer.handle ∧ submitted.1 = h ∧ ix = request ps ∧
    rows = submitted.2 ∧ rows = values offer.data ps)

theorem honest_opens {H R : Type} [DecidableEq H] [DecidableEq R] (offer : Offer H R) (ps : Draw) :
    opens offer ps (honest offer.data offer.handle (request ps)) offer.handle (request ps)
      (values offer.data ps) = true := by simp [honest_rows, opens]

variable {b : Bindings} (M : Model b.vocabulary) (handle : b.vocabulary.Ty)
abbrev Session := State (M.Val handle) (M.Val (scalar b))
def deliver {t u : b.vocabulary.Ty} (value : M.Val t) : Option (M.Val u) :=
  if eq : t = u then some (eq ▸ value) else none

theorem deliver_self {t : b.vocabulary.Ty} (v : M.Val t) : deliver M (u := t) v = some v := by
  simp [deliver]

variable [DecidableEq (M.Val handle)] [DecidableEq (M.Val (scalar b))]
variable (offer : Offer (M.Val handle) (M.Val (scalar b))) (opener : Opener (M.Val handle) (M.Val (scalar b)))

/-- Replay one tape at the positions draw. The reader receives the opener's registered
handle and row batch. Its own opening request carries all three SSA operands. -/
def answer (ps : Draw) (op : ROp M) (state : Session M handle) : Option ((RSig M).Reply op) × Session M handle :=
  match op, state with
  | .hear (.request ⟨0⟩) 0 ⟨[],⟨1⟩⟩ t, .empty =>
    (deliver M (u := t) offer.handle, .registered offer)
  | .own (.coin law) [0] ⟨[],⟨2⟩⟩ [] .nil t, .registered fixed =>
    if (show Zkc.Vocabulary.LawKey from law) = .uniform (.seq (.fin 1024) (some 40)) then
      (deliver M (t := positions b) (u := t) (request ps), .drawn fixed ps)
    else (none,state)
  | .hear (.request ⟨1⟩) 0 ⟨[],⟨4⟩⟩ t, .drawn fixed ix =>
    let proposal := opener fixed.handle (request ix)
    (deliver M (t := rows b) (u := t) proposal.2, .answered fixed ix proposal.1 proposal.2)
  | .own (.request ⟨2⟩) [] ⟨[],⟨6⟩⟩ [_] (.cons arg .nil) t, .answered fixed sampled claimed rs =>
    if h : _ = Ty.tuple (claim handle) then
      let input : M.Val (.tuple (claim handle)) := cast (congrArg M.Val h) arg
      (deliver M (t := .bool) (u := t) (opens fixed sampled (claimed,rs) input.1 input.2.1 input.2.2.1), .closed)
    else (none,state)
  | _, _ => (none,state)

def service (ps : Draw) : Service (RSig M) (Session M handle) :=
  fun op s => pure (answer M handle offer opener ps op s)

/-- Deterministic response traversal conditioned on one tape. -/
def outcome {S : Sig} {σ H A : Type} (reply : (op : S.Op) → σ → Option (S.Reply op) × σ)
    (program : Process S H A) : σ → Outcome H A × σ :=
  program.interpret ⟨fun op next s => match reply op s with
    | (none,t) => (.unavailable,t)
    | (some x,t) => next x t⟩ (fun a s => (.returned a,s)) (fun e s => (.halted e,s))

theorem run_pointMass {S : Sig} {σ H A : Type} (reply : (op : S.Op) → σ → Option (S.Reply op) × σ)
    (program : Process S H A) (state : σ) :
    run (fun op s => pure (reply op s)) program state = pure (outcome reply program state) := by
  induction program generalizing state with
  | done | halt => rfl
  | call op next ih =>
    simp only [run, outcome, Process.interpret, pure_bind]
    rcases h : reply op state with ⟨_ | x,s⟩
    · rfl
    · exact ih x s

def returned {H A σ : Type} (out : Outcome H A × σ) : Bool :=
  match out.1 with | .returned _ => true | _ => false

def accepted {A : Type} (ps : Draw) (program : Program M A) : Bool :=
  returned (outcome (answer M handle offer opener ps) program .empty)

end Zkc.Formal.Written.TableService
