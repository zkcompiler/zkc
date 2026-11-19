module

public import Zkc.Core.World.Runs
public import Zkc.Core.Statements
public import Zkc.Formal.ProcessJudgment

@[expose] public section
set_option autoImplicit false

namespace Zkc.Formal.World
open Core
variable {V : Vocabulary} {M : Model V}

/-- A joint observer sees the full call and the reply. Each service transition may read its
payload and update private state. Stops and returns preserve the final service state. -/
abbrev Service (M : Model V) (State : Type) :=
  State → (op : GOp M) → (GSig M).Reply op → State → Prop

inductive Observed {State A : Type} (service : Service M State) :
    State → Protocol M A → EffectTrace (GSig M) → GEnd A → State → Prop where
  | done {s a} : Observed service s (.done a) [] (.returned a) s
  | halt {s who why} : Observed service s (.halt (who, why)) [] (.stopped who why) s
  | call {s s' last op k v tail e} : service s op v s' → Observed service s' (k v) tail e last →
      Observed service s (.call op k) (⟨op,v⟩ :: tail) e last

def Service.judgment {State : Type} (service : Service M State) :
    ProcessJudgment (GSig M) (State → EffectTrace (GSig M) → State → Prop) where
  node op next s trace last := ∃ v rest s', trace = ⟨op,v⟩ :: rest ∧ service s op v s' ∧ next v s' rest last

/-- The joint semantics is a state-and-trace instance of the same process traversal. -/
theorem observed_iff_interpret {State A : Type} (service : Service M State) (p : Protocol M A)
    (s : State) (trace : EffectTrace (GSig M)) (result : GEnd A) (last : State) :
    Observed service s p trace result last ↔ p.interpret (Service.judgment service)
      (fun a x t y => result = .returned a ∧ t = [] ∧ x = y)
      (fun h x t y => result = .stopped h.1 h.2 ∧ t = [] ∧ x = y) s trace last := by
  induction p generalizing s trace last with
  | done a =>
    constructor
    · intro h; cases h; exact ⟨rfl,rfl,rfl⟩
    · rintro ⟨rfl,rfl,rfl⟩; exact .done
  | halt h =>
    obtain ⟨_,_⟩ := h
    constructor
    · intro h; cases h; exact ⟨rfl,rfl,rfl⟩
    · rintro ⟨rfl,rfl,rfl⟩; exact .halt
  | call op k ih =>
    constructor
    · intro h
      cases h with | call ok tail => exact ⟨_, _, _, rfl, ok, (ih ..).mp tail⟩
    · rintro ⟨v, tail, s', rfl, ok, next⟩
      exact .call ok ((ih v s' tail last).mpr next)

def sourceService (source : Source M) : Service M Unit :=
  fun _ op => match op with
    | .flow .. => fun _ _ => True
    | .given _ _ _ at_ _ _ ty => fun v _ => source at_ ty = some v

def forgetPayload : ((op : GOp M) × (GSig M).Reply op) → Event M
  | ⟨.flow kind giver getters at_ ty val, _⟩ => .flow kind giver getters at_ ty val
  | ⟨.given kind owner hearers at_ _ _ ty, v⟩ => .given kind owner hearers at_ ty v

/-- Erase request payloads to reproduce exactly the existing joint run for a fixed source. -/
theorem observed_iff_grun {A : Type} (source : Source M) (p : Protocol M A) (events) (e) :
    GRun M source p events e ↔ ∃ trace,
      Observed (sourceService source) () p trace e () ∧ trace.map forgetPayload = events := by
  constructor
  · intro run
    induction run with
    | done => exact ⟨[], .done, rfl⟩
    | halt => exact ⟨[], .halt, rfl⟩
    | flow _ ih =>
      obtain ⟨_, h, rfl⟩ := ih
      exact ⟨_, .call (v := ()) trivial h, rfl⟩
    | given reply _ ih =>
      obtain ⟨_, h, rfl⟩ := ih
      exact ⟨_, .call reply h, rfl⟩
  · rintro ⟨_, run, rfl⟩
    exact forget run
where
  forget {s last : Unit} {term : Protocol M A} {trace end_}
      (run : Observed (sourceService source) s term trace end_ last) :
      GRun M source term (trace.map forgetPayload) end_ := by
    induction run with
    | done => exact .done
    | halt => exact .halt
    | @call s s' last op k v tail end_ ok _ ih =>
      cases op with
      | flow => cases v; exact .flow ih
      | given => exact .given ok ih

/-- Project the evidence in one joint call to exactly the arguments and reply visible to
the role at that effect. The listener receives the result without the request arguments. -/
def roleEntry (r : Role) : ((op : GOp M) × (GSig M).Reply op) → Option ((op : ROp M) × (RSig M).Reply op)
  | ⟨.given kind owner listeners at_ ins args ty, v⟩ =>
    if r = owner then some ⟨.own kind listeners at_ ins args ty, v⟩
    else if r ∈ listeners then some ⟨.hear kind owner at_ ty, v⟩ else none
  | ⟨.flow kind giver getters at_ ty v, _⟩ =>
    if r = giver then some ⟨.give kind getters at_ ty v, ()⟩
    else if r ∈ getters then some ⟨.get kind giver at_ ty, v⟩ else none

theorem listener_entry {kind : GivenKind V} {owner r : Role} {listeners : List Role}
    (other : r ≠ owner) (listens : r ∈ listeners) (at_ : Occurrence) {ins : List V.Ty}
    (args : HList M.Val ins) (ty : V.Ty) (reply : M.Val ty) :
    roleEntry r ⟨.given kind owner listeners at_ ins args ty, reply⟩ =
      some ⟨.hear kind owner at_ ty, reply⟩ := by simp [roleEntry, other, listens]

/-- The role's operation for a world read is an owner request or a reply-only notification.
A deployment supplies the authority table for each operation and actual principal. -/
structure Access (V : Vocabulary) where
  owns : Role → GivenKind V → List Role → Occurrence → List V.Ty → V.Ty → Prop
  hears : Role → GivenKind V → Role → Occurrence → V.Ty → Prop

/-- A grant assigns the read to its declared owner and its explicitly named listeners.
The declaration can range over occurrence paths without enumerating loop iterations. -/
structure Grant (V : Vocabulary) where
  kind : GivenKind V
  owner : Role
  listeners : List Role
  occurrence : Occurrence
  inputs : List V.Ty
  type : V.Ty

def Access.fromGrants (declared : Grant V → Prop) : Access V where
  owns r kind listeners at_ ins ty := declared ⟨kind, r, listeners, at_, ins, ty⟩
  hears r kind owner at_ ty := ∃ listeners ins, declared ⟨kind, owner, listeners, at_, ins, ty⟩ ∧ r ∈ listeners

def Access.operation (a : Access V) (r : Role) : ROp M → Prop
  | .own kind listeners at_ ins _ ty => a.owns r kind listeners at_ ins ty
  | .hear kind owner at_ ty => a.hears r kind owner at_ ty
  | _ => True

def Access.record (a : Access V) : Happened M → Prop
  | .owned r kind at_ ty _ => ∃ listeners ins, a.owns r kind listeners at_ ins ty
  | .heard r kind owner at_ ty _ => a.hears r kind owner at_ ty
  | _ => True

/-- Every continuation of a replacement strategy respects the role's source-read authority. -/
def Scoped {H B : Type} (access : Access V) (r : Role) (p : Process (RSig M) H B) : Prop :=
  p.interpret ⟨fun op next => access.operation r op ∧ ∀ v, next v⟩ (fun _ => True) (fun _ => True)

variable {H B : Role → Type} {source : Source M}
abbrev NetworkScoped (access : Access V) (net : Net M H B) := ∀ r, Scoped access r (net r)

/-- An operation offered on some continuation of the reference role, over all possible
replies. Source-read authority is fixed from the honest projections before substitution. -/
def Offers {X Y : Type} (p : Process (RSig M) X Y) (op : ROp M) : Prop :=
  p.interpret ⟨fun actual next => actual = op ∨ ∃ reply, next reply⟩
    (fun _ => False) (fun _ => False)

theorem scoped_iff_offers {X Y : Type} (access : Access V) (r : Role)
    (p : Process (RSig M) X Y) :
    Scoped access r p ↔ ∀ op, Offers p op → access.operation r op := by
  induction p with
  | done | halt => exact ⟨fun _ _ h => False.elim h, fun _ => trivial⟩
  | call op next ih =>
    constructor
    · rintro ⟨head, tails⟩ q (eq | ⟨v, offered⟩)
      · exact eq ▸ head
      · exact (ih v).mp (tails v) q offered
    · intro accepts
      exact ⟨accepts op (.inl rfl), fun v => (ih v).mpr fun q h => accepts q (.inr ⟨v,h⟩)⟩

/-- The read authority of the projected processes on the selected inputs. A replacement
owner may choose a new request payload. The principal, listeners, kind, occurrence and
input and reply types still have to be offered by the corresponding reference role. -/
def Access.ofProjections (net : Net M H B) : Access V where
  owns r kind listeners at_ ins ty := ∃ args, Offers (net r) (.own kind listeners at_ ins args ty)
  hears r kind owner at_ ty := Offers (net r) (.hear kind owner at_ ty)

theorem projections_scoped (net : Net M H B) : NetworkScoped (Access.ofProjections net) net := by
  intro r
  apply (scoped_iff_offers ..).mpr
  intro op offered
  cases op with
  | own => exact ⟨_, offered⟩
  | hear => exact offered
  | give | get | begin | settle => trivial

private theorem set_scoped {access : Access V} {net : Net M H B} {r : Role} {q}
    (all : NetworkScoped access net) (hq : Scoped access r q) :
    NetworkScoped access (net.set M r q) := by
  intro r'
  by_cases eq : r' = r
  · subst r'; simpa [Net.set] using hq
  · simpa [Net.set, eq] using all r'

private theorem scoped_call {access : Access V} {net : Net M H B} {r : Role}
    {op : ROp M} {k : (RSig M).Reply op → Process (RSig M) (H r) (B r)}
    (all : NetworkScoped access net) (eq : net r = .call op k) : Scoped access r (.call op k) :=
  eq ▸ all r

theorem step_scoped {access : Access V} {c c' : Net M H B × Pending M} {h}
    (all : NetworkScoped access c.1) (step : Step M source c h c') :
    access.record h ∧ NetworkScoped access c'.1 := by
  cases step with
  | own atCall _ =>
    have ok := scoped_call all atCall
    exact ⟨⟨_, _, ok.1⟩, set_scoped all (ok.2 _)⟩
  | give atCall _ | get atCall _ | hear atCall _ | begin atCall | settle atCall =>
    have ok := scoped_call all atCall
    exact ⟨ok.1, set_scoped all (ok.2 _)⟩

theorem reach_scoped {access : Access V} {c c' : Net M H B × Pending M} {trace}
    (all : NetworkScoped access c.1) (run : Reach M source c trace c') :
    (∀ h ∈ trace, access.record h) ∧ NetworkScoped access c'.1 := by
  induction run with
  | refl => exact ⟨by simp, all⟩
  | step step _ ih =>
    obtain ⟨head, next⟩ := step_scoped all step
    obtain ⟨tail, last⟩ := ih next
    exact ⟨fun h mem => (List.mem_cons.mp mem).elim (fun eq => eq ▸ head) (tail h), last⟩

/-- Starting from any reference network, replace a single role by a strategy respecting
that role's reference permissions. Every reached read obeys the original permissions. -/
theorem replacement_reads {net : Net M H B} {role : Role} {strategy} {pending last trace}
    (allowed : Scoped (Access.ofProjections net) role strategy)
    (run : Reach M source (net.set M role strategy, pending) trace last) :
    ∀ h ∈ trace, (Access.ofProjections net).record h :=
  (reach_scoped (set_scoped (projections_scoped net) allowed) run).1

/-- Fix the authority before choosing the replacement, using precisely the selected
admitted protocol, invocation path and shared inputs. -/
theorem admitted_replacement_reads (a : Admitted V) {hdr : ProtocolHeader V}
    (entry : Member a.program.headers.protocols hdr) (path : List Frame)
    (inputs : HList (LVal M) hdr.ins) (role : Role)
    (strategy : Program M (HList (RV M role) hdr.outs)) :
    let start := Statements.projections a.program M entry path inputs
    let access := Access.ofProjections start.1
    Scoped access role strategy → ∀ {trace last},
      Reach M source (start.1.set M role strategy, start.2) trace last → ∀ h ∈ trace, access.record h :=
  fun allowed {_ _} run => replacement_reads allowed run

end Zkc.Formal.World
