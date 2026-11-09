module

public import ZkcProgram.Execution

@[expose] public section

/-! Nominal custody: the role-local affine permission of a logical resource unit.

A live custody entry has an exact nominal slot, a holder (the owning role), a
lineage and the call frame that owns it. `create` adds a fresh entry that starts
its own lineage; `pass` consumes the current entry and adds its successor in the
same lineage; `consume` removes the entry without a successor. An operation on
an entry that is not live (never created, already consumed or passed, or
retired with its frame), of another slot, of another holder or of another frame
refuses. Equal slots never connect a destroyed entry to a fresh one:
`consume; create` starts a new lineage, while `pass` continues the old one.

A frame owns the entries it receives and creates. On a return only the returned
entries move to the caller and every other entry of the frame is retired; on a
stop no entry of the frame survives. Entries of enclosing frames are untouched
either way.

The ledger is ghost ownership state of the formal execution. It models neither
a native allocator nor a codec, and its tokens are never transcript or payload
data. `Zkc.Source.Structured.CustodySoundness` connects it to the structured
evaluator. -/

set_option autoImplicit false
namespace PIR.Custody

/-- The ghost identity of one entry. -/
abbrev Token := Nat

structure Entry where
  token : Token
  slot : String
  holder : String
  /-- The token that started this entry's pass chain. -/
  lineage : Token
  /-- The call frame that owns the entry. -/
  frame : Nat
  deriving DecidableEq, Repr

inductive Refusal where
  /-- The token is not live: never created, already used or retired. -/
  | stale
  | slot
  | holder
  /-- The entry belongs to another frame and was not transferred to this one. -/
  | frame
  /-- A token appears twice where distinct entries are required. -/
  | duplicate
  deriving DecidableEq, Repr

structure Ledger where
  next : Token := 0
  live : List Entry := []
  depth : Nat := 0
  /-- The first refused request, if any. -/
  refused : Option Refusal := none
  deriving DecidableEq, Repr

namespace Ledger

def find? (ledger : Ledger) (token : Token) : Option Entry :=
  ledger.live.find? (·.token == token)

def Live (ledger : Ledger) (token : Token) : Prop := ∃ entry ∈ ledger.live, entry.token = token

def remove (ledger : Ledger) (token : Token) : Ledger :=
  { ledger with live := ledger.live.filter (·.token != token) }

/-- The entry a request may use: live, of the slot and holder, in the current frame. -/
def check (ledger : Ledger) (slot holder : String) (token : Token) : Except Refusal Entry :=
  match ledger.find? token with
  | none => .error .stale
  | some entry =>
    if entry.slot != slot then .error .slot
    else if entry.holder != holder then .error .holder
    else if entry.frame != ledger.depth then .error .frame
    else .ok entry

def create (ledger : Ledger) (slot holder : String) : Token × Ledger :=
  (ledger.next,
    { ledger with
      next := ledger.next + 1
      live := ⟨ledger.next, slot, holder, ledger.next, ledger.depth⟩ :: ledger.live })

def pass (ledger : Ledger) (slot holder : String) (token : Token) :
    Except Refusal (Token × Ledger) :=
  match ledger.check slot holder token with
  | .error reason => .error reason
  | .ok entry =>
    let rest := ledger.remove token
    .ok (ledger.next,
      { rest with
        next := ledger.next + 1
        live := ⟨ledger.next, slot, holder, entry.lineage, ledger.depth⟩ :: rest.live })

def consume (ledger : Ledger) (slot holder : String) (token : Token) : Except Refusal Ledger :=
  match ledger.check slot holder token with
  | .error reason => .error reason
  | .ok _ => .ok (ledger.remove token)

/-- Each token of a frame transfer: live, of the holder when one is required,
and in the current frame. -/
def transferRefusal (ledger : Ledger) (holder : Option String) (tokens : List Token) :
    Option Refusal :=
  if !tokens.Nodup then some .duplicate
  else tokens.findSome? fun token =>
    match ledger.find? token with
    | none => some .stale
    | some entry =>
      if holder.any (· != entry.holder) then some .holder
      else if entry.frame != ledger.depth then some .frame
      else none

/-- Enter a callee frame that receives the given distinct entries of one holder. -/
def enter (ledger : Ledger) (holder : String) (arguments : List Token) : Except Refusal Ledger :=
  match ledger.transferRefusal (some holder) arguments with
  | some reason => .error reason
  | none => .ok
    { ledger with
      depth := ledger.depth + 1
      live := ledger.live.map fun entry =>
        if arguments.contains entry.token then { entry with frame := ledger.depth + 1 } else entry }

/-- The ledger after a return from the current frame. -/
def returnFrame (ledger : Ledger) (returned : List Token) : Ledger :=
  { ledger with
    depth := ledger.depth - 1
    live := ledger.live.filterMap fun entry =>
      if entry.frame != ledger.depth then some entry
      else if returned.contains entry.token then some { entry with frame := ledger.depth - 1 }
      else none }

/-- Return from the current frame: the returned entries move to the caller and
every other entry of the frame is retired. -/
def exit (ledger : Ledger) (returned : List Token) : Except Refusal Ledger :=
  match ledger.transferRefusal none returned with
  | some reason => .error reason
  | none => .ok (ledger.returnFrame returned)

/-- Stop in the current frame: no entry of the frame survives. -/
def stop (ledger : Ledger) : Ledger :=
  { ledger with depth := ledger.depth - 1, live := ledger.live.filter (·.frame != ledger.depth) }

/-- Tokens are unique and below the allocation counter. -/
def Bounded (ledger : Ledger) : Prop :=
  (ledger.live.map (·.token)).Nodup ∧ ∀ entry ∈ ledger.live, entry.token < ledger.next

end Ledger

/-! ## Effect interface

The three transfers are requests of an effect interface, so that a typed
evaluator issues them like any other effect. A refusal stops the run and is
recorded in the ledger. -/

inductive Request where
  | create (slot holder : String)
  | pass (slot holder : String) (token : Token)
  | consume (slot holder : String) (token : Token)
  deriving DecidableEq, Repr

def interface : Signature where
  Op := Request
  Reply
    | .create .. => Token
    | .pass .. => Token
    | .consume .. => Unit

def refuse {A : Type} (ledger : Ledger) (request : Request) (reason : Refusal) :
    Execution Ledger Request A :=
  ⟨.stopped .refused, { ledger with refused := ledger.refused.orElse fun _ => some reason }, [request]⟩

/-- The ledger handler. Every request is recorded as an event. -/
def handler : Handler interface Ledger Request
  | request@(.create slot holder), ledger =>
    let (token, next) := ledger.create slot holder
    ⟨.returned token, next, [request]⟩
  | request@(.pass slot holder token), ledger =>
    match ledger.pass slot holder token with
    | .ok (successor, next) => ⟨.returned successor, next, [request]⟩
    | .error reason => refuse ledger request reason
  | request@(.consume slot holder token), ledger =>
    match ledger.consume slot holder token with
    | .ok next => ⟨.returned (), next, [request]⟩
    | .error reason => refuse ledger request reason

/-- Payload erasure: every token is zero and nothing is checked. -/
def forget {J : Signature} : (request : Request) → Process J (interface.Reply request)
  | .create .. => .done (0 : Token)
  | .pass .. => .done (0 : Token)
  | .consume .. => .done ()

namespace Ledger

/-! ## Laws -/

@[simp] theorem create_token (ledger : Ledger) (slot holder : String) :
    (ledger.create slot holder).1 = ledger.next := rfl

@[simp] theorem create_live (ledger : Ledger) (slot holder : String) :
    (ledger.create slot holder).2.live =
      ⟨ledger.next, slot, holder, ledger.next, ledger.depth⟩ :: ledger.live := rfl

@[simp] theorem create_next (ledger : Ledger) (slot holder : String) :
    (ledger.create slot holder).2.next = ledger.next + 1 := rfl

@[simp] theorem create_depth (ledger : Ledger) (slot holder : String) :
    (ledger.create slot holder).2.depth = ledger.depth := rfl

@[simp] theorem remove_live (ledger : Ledger) (token : Token) :
    (ledger.remove token).live = ledger.live.filter (·.token != token) := rfl

theorem find?_some {ledger : Ledger} {token : Token} {entry : Entry}
    (found : ledger.find? token = some entry) : entry ∈ ledger.live ∧ entry.token = token := by
  unfold find? at found
  exact ⟨List.mem_of_find?_eq_some found, by simpa using List.find?_some found⟩

theorem find?_token_of_mem : ∀ (entries : List Entry), (entries.map (·.token)).Nodup →
    ∀ {entry : Entry}, entry ∈ entries → entries.find? (·.token == entry.token) = some entry
  | [], _, _, member => by cases member
  | head :: rest, unique, entry, member => by
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with rfl | member
    · simp
    · have different : head.token ≠ entry.token := by
        intro same
        exact unique.1 (List.mem_map.mpr ⟨entry, member, same.symm⟩)
      have unequal : (head.token == entry.token) = false := by simpa using different
      rw [List.find?_cons, unequal]
      exact find?_token_of_mem rest unique.2 member

/-- On a ledger with unique tokens, a live entry is the one its token finds. -/
theorem find?_of_mem {ledger : Ledger} (unique : (ledger.live.map (·.token)).Nodup)
    {entry : Entry} (member : entry ∈ ledger.live) : ledger.find? entry.token = some entry :=
  find?_token_of_mem ledger.live unique member

/-- A live entry of the request's slot, holder and frame passes its check. -/
theorem check_of_mem {ledger : Ledger} (unique : (ledger.live.map (·.token)).Nodup)
    {entry : Entry} (member : entry ∈ ledger.live) :
    ledger.check entry.slot entry.holder entry.token = .ok entry ∨ entry.frame ≠ ledger.depth := by
  by_cases frame : entry.frame = ledger.depth
  · left
    simp [check, find?_of_mem unique member, frame]
  · exact .inr frame

theorem find?_none {ledger : Ledger} {token : Token} :
    ledger.find? token = none ↔ ¬ ledger.Live token := by
  unfold find? Live
  simp [List.find?_eq_none]

theorem live_remove {ledger : Ledger} {token other : Token} :
    (ledger.remove token).Live other ↔ ledger.Live other ∧ other ≠ token := by
  unfold Live
  simp only [remove_live, List.mem_filter, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨entry, ⟨member, different⟩, rfl⟩
    exact ⟨⟨entry, member, rfl⟩, different⟩
  · rintro ⟨⟨entry, member, rfl⟩, different⟩
    exact ⟨entry, ⟨member, different⟩, rfl⟩

/-- Creation returns the next unused token as a new lineage of the current frame. -/
theorem create_entry (ledger : Ledger) (slot holder : String) :
    (ledger.create slot holder).1 = ledger.next ∧
      ⟨ledger.next, slot, holder, ledger.next, ledger.depth⟩ ∈ (ledger.create slot holder).2.live := by
  simp

/-- A created token was not live before: creation is fresh on a bounded ledger. -/
theorem create_fresh {ledger : Ledger} (bounded : ledger.Bounded) (slot holder : String) :
    ¬ ledger.Live (ledger.create slot holder).1 := by
  rintro ⟨entry, member, same⟩
  have below : entry.token < ledger.next := bounded.2 entry member
  rw [same, create_token] at below
  exact Nat.lt_irrefl _ below

/-- Creation keeps every other live entry. -/
theorem create_keeps (ledger : Ledger) (slot holder : String) {entry : Entry}
    (member : entry ∈ ledger.live) : entry ∈ (ledger.create slot holder).2.live := by
  simp [member]

theorem create_bounded {ledger : Ledger} (bounded : ledger.Bounded) (slot holder : String) :
    (ledger.create slot holder).2.Bounded := by
  refine ⟨?_, ?_⟩
  · simp only [create_live, List.map_cons, List.nodup_cons]
    refine ⟨?_, bounded.1⟩
    intro member
    obtain ⟨entry, inLive, same⟩ := List.mem_map.mp member
    have below : entry.token < ledger.next := bounded.2 entry inLive
    rw [same] at below
    exact Nat.lt_irrefl _ below
  · intro entry member
    simp only [create_live, List.mem_cons] at member
    rcases member with rfl | member
    · simp
    · have below : entry.token < ledger.next := bounded.2 entry member
      simp only [create_next]
      exact Nat.lt_succ_of_lt below

theorem remove_bounded {ledger : Ledger} (bounded : ledger.Bounded) (token : Token) :
    (ledger.remove token).Bounded := by
  refine ⟨?_, ?_⟩
  · simp only [remove_live]
    exact List.Nodup.sublist (List.Sublist.map _ (List.filter_sublist)) bounded.1
  · intro entry member
    simp only [remove_live, List.mem_filter] at member
    exact bounded.2 entry member.1

theorem check_entry {ledger : Ledger} {slot holder : String} {token : Token} {entry : Entry}
    (checked : ledger.check slot holder token = .ok entry) :
    entry ∈ ledger.live ∧ entry.token = token ∧ entry.slot = slot ∧ entry.holder = holder ∧
      entry.frame = ledger.depth := by
  unfold check at checked
  cases found : ledger.find? token with
  | none => simp [found] at checked
  | some found' =>
    simp only [found] at checked
    by_cases slotSame : found'.slot = slot
    · by_cases holderSame : found'.holder = holder
      · by_cases frameSame : found'.frame = ledger.depth
        · simp [slotSame, holderSame, frameSame] at checked
          subst checked
          obtain ⟨member, same⟩ := find?_some found
          exact ⟨member, same, slotSame, holderSame, frameSame⟩
        · simp [slotSame, holderSame, frameSame] at checked
      · simp [slotSame, holderSame] at checked
    · simp [slotSame] at checked

/-- A request on a token that is not live refuses as stale. -/
theorem check_stale {ledger : Ledger} {slot holder : String} {token : Token}
    (absent : ¬ ledger.Live token) : ledger.check slot holder token = .error .stale := by
  have none := find?_none.mpr absent
  simp [check, none]

theorem check_holder {ledger : Ledger} {slot holder : String} {token : Token} {entry : Entry}
    (found : ledger.find? token = some entry) (sameSlot : entry.slot = slot)
    (other : entry.holder ≠ holder) : ledger.check slot holder token = .error .holder := by
  simp [check, found, sameSlot, other]

theorem check_slot {ledger : Ledger} {slot holder : String} {token : Token} {entry : Entry}
    (found : ledger.find? token = some entry) (other : entry.slot ≠ slot) :
    ledger.check slot holder token = .error .slot := by
  simp [check, found, other]

theorem pass_ok {ledger : Ledger} {slot holder : String} {token successor : Token}
    {next : Ledger} (passed : ledger.pass slot holder token = .ok (successor, next)) :
    ∃ entry, ledger.check slot holder token = .ok entry ∧ successor = ledger.next ∧
      next = { ledger.remove token with
        next := ledger.next + 1
        live := ⟨ledger.next, slot, holder, entry.lineage, ledger.depth⟩ ::
          (ledger.remove token).live } := by
  unfold pass at passed
  split at passed
  · cases passed
  · rename_i entry checked
    simp only [Except.ok.injEq, Prod.mk.injEq] at passed
    exact ⟨entry, checked, passed.1.symm, passed.2.symm⟩

theorem pass_bounded {ledger : Ledger} {slot holder : String} {token successor : Token}
    {next : Ledger} (bounded : ledger.Bounded)
    (passed : ledger.pass slot holder token = .ok (successor, next)) : next.Bounded := by
  obtain ⟨entry, _, rfl, rfl⟩ := pass_ok passed
  have rest := remove_bounded bounded token
  refine ⟨?_, ?_⟩
  · simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, rest.1⟩
    intro member
    obtain ⟨old, inLive, same⟩ := List.mem_map.mp member
    have below : old.token < ledger.next := rest.2 old inLive
    rw [same] at below
    exact Nat.lt_irrefl _ below
  · intro old member
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (rest.2 old member)

theorem pass_of_check {ledger : Ledger} {slot holder : String} {token : Token} {entry : Entry}
    (checked : ledger.check slot holder token = .ok entry) :
    ledger.pass slot holder token = .ok (ledger.next,
      { ledger.remove token with
        next := ledger.next + 1
        live := ⟨ledger.next, slot, holder, entry.lineage, ledger.depth⟩ ::
          (ledger.remove token).live }) := by
  unfold pass
  rw [checked]

theorem consume_of_check {ledger : Ledger} {slot holder : String} {token : Token} {entry : Entry}
    (checked : ledger.check slot holder token = .ok entry) :
    ledger.consume slot holder token = .ok (ledger.remove token) := by
  unfold consume
  rw [checked]

theorem mem_remove {ledger : Ledger} {token : Token} {entry : Entry} :
    entry ∈ (ledger.remove token).live ↔ entry ∈ ledger.live ∧ entry.token ≠ token := by
  simp [remove_live, List.mem_filter]

/-- A live entry of the current frame, of the request's slot and holder, passes its check. -/
theorem check_live {ledger : Ledger} (unique : (ledger.live.map (·.token)).Nodup)
    {entry : Entry} (member : entry ∈ ledger.live) {slot holder : String}
    (slotSame : entry.slot = slot) (holderSame : entry.holder = holder)
    (frameSame : entry.frame = ledger.depth) :
    ledger.check slot holder entry.token = .ok entry := by
  simp [check, find?_of_mem unique member, slotSame, holderSame, frameSame]

/-- Pass consumes the current token and continues its lineage with a fresh successor. -/
theorem pass_succession {ledger : Ledger} {slot holder : String} {token successor : Token}
    {next : Ledger} (passed : ledger.pass slot holder token = .ok (successor, next)) :
    ∃ entry ∈ ledger.live, entry.token = token ∧ entry.slot = slot ∧ entry.holder = holder ∧
      successor = ledger.next ∧
      ⟨successor, slot, holder, entry.lineage, ledger.depth⟩ ∈ next.live ∧
      (∀ other, next.Live other ↔ other = successor ∨ (ledger.Live other ∧ other ≠ token)) := by
  obtain ⟨entry, checked, rfl, rfl⟩ := pass_ok passed
  obtain ⟨member, same, slotSame, holderSame, _⟩ := check_entry checked
  refine ⟨entry, member, same, slotSame, holderSame, rfl, by simp, ?_⟩
  intro other
  constructor
  · rintro ⟨found, inLive, rfl⟩
    simp only [List.mem_cons] at inLive
    rcases inLive with rfl | inLive
    · exact .inl rfl
    · exact .inr (live_remove.mp ⟨found, inLive, rfl⟩)
  · rintro (rfl | old)
    · exact ⟨_, List.mem_cons_self, rfl⟩
    · obtain ⟨found, inLive, same⟩ := live_remove.mpr old
      exact ⟨found, List.mem_cons_of_mem _ inLive, same⟩

theorem consume_ok {ledger : Ledger} {slot holder : String} {token : Token} {next : Ledger}
    (consumed : ledger.consume slot holder token = .ok next) :
    ∃ entry, ledger.check slot holder token = .ok entry ∧ next = ledger.remove token := by
  unfold consume at consumed
  split at consumed
  · cases consumed
  · rename_i entry checked
    exact ⟨entry, checked, (Except.ok.inj consumed).symm⟩

/-- Consume retires the token and adds nothing. -/
theorem consume_retires {ledger : Ledger} {slot holder : String} {token : Token} {next : Ledger}
    (consumed : ledger.consume slot holder token = .ok next) :
    ledger.Live token ∧ ∀ other, next.Live other ↔ ledger.Live other ∧ other ≠ token := by
  obtain ⟨entry, checked, rfl⟩ := consume_ok consumed
  obtain ⟨member, same, _⟩ := check_entry checked
  exact ⟨⟨entry, member, same⟩, fun _ => live_remove⟩

theorem consume_stale {ledger : Ledger} {slot holder : String} {token : Token}
    (absent : ¬ ledger.Live token) : ledger.consume slot holder token = .error .stale := by
  simp [consume, check_stale absent]

theorem pass_stale {ledger : Ledger} {slot holder : String} {token : Token}
    (absent : ¬ ledger.Live token) : ledger.pass slot holder token = .error .stale := by
  simp [pass, check_stale absent]

/-- A used token is stale: a second consume of it refuses. -/
theorem consume_twice {ledger : Ledger} {slot holder : String} {token : Token} {next : Ledger}
    (consumed : ledger.consume slot holder token = .ok next) (slot' holder' : String) :
    next.consume slot' holder' token = .error .stale :=
  consume_stale fun live => ((consume_retires consumed).2 token |>.mp live).2 rfl

/-- A passed token is stale: using it again refuses. -/
theorem pass_then_stale {ledger : Ledger} {slot holder : String} {token successor : Token}
    {next : Ledger} (bounded : ledger.Bounded)
    (passed : ledger.pass slot holder token = .ok (successor, next)) :
    ¬ next.Live token := by
  obtain ⟨entry, member, same, _, _, fresh, _, live⟩ := pass_succession passed
  intro alive
  rcases (live token).mp alive with equal | ⟨_, different⟩
  · have below : entry.token < ledger.next := bounded.2 entry member
    rw [same, equal, fresh] at below
    exact Nat.lt_irrefl _ below
  · exact different rfl

/-- `consume; create` is not `pass`: the entry `create` adds starts its own
lineage, which on a bounded ledger is no lineage present before, while `pass`
continues the lineage of the consumed entry. -/
theorem consume_create_new_lineage {ledger next : Ledger} {slot holder : String} {token : Token}
    (lineages : ∀ entry ∈ ledger.live, entry.lineage < ledger.next)
    (consumed : ledger.consume slot holder token = .ok next) (slot' holder' : String) :
    ⟨next.next, slot', holder', next.next, next.depth⟩ ∈ (next.create slot' holder').2.live ∧
      ∀ entry ∈ ledger.live, entry.lineage ≠ (next.create slot' holder').1 := by
  obtain ⟨_, _, rfl⟩ := consume_ok consumed
  refine ⟨by simp, ?_⟩
  intro entry member equal
  have below : entry.lineage < ledger.next := lineages entry member
  rw [equal] at below
  exact Nat.lt_irrefl _ below

/-- Returning keeps exactly the returned entries of the frame, now owned by the
caller, and leaves every entry of enclosing frames untouched. -/
theorem returnFrame_live (ledger : Ledger) (returned : List Token) (entry : Entry) :
    entry ∈ (ledger.returnFrame returned).live ↔
      (entry ∈ ledger.live ∧ entry.frame ≠ ledger.depth) ∨
      (∃ old ∈ ledger.live, old.frame = ledger.depth ∧ old.token ∈ returned ∧
        entry = { old with frame := ledger.depth - 1 }) := by
  simp only [returnFrame, List.mem_filterMap]
  constructor
  · rintro ⟨old, member, image⟩
    by_cases inside : old.frame = ledger.depth
    · by_cases inReturned : old.token ∈ returned
      · simp only [inside, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          List.contains_iff_mem, inReturned, Option.some.injEq] at image
        exact .inr ⟨old, member, inside, inReturned, image.symm⟩
      · simp [inside, inReturned] at image
    · have outside : (old.frame != ledger.depth) = true := by simpa using inside
      simp only [outside, ↓reduceIte, Option.some.injEq] at image
      subst image
      exact .inl ⟨member, inside⟩
  · rintro (⟨member, outside⟩ | ⟨old, member, inside, returnedToken, rfl⟩)
    · exact ⟨entry, member, by simp [outside]⟩
    · exact ⟨old, member, by simp [inside, returnedToken]⟩

theorem exit_ok {ledger next : Ledger} {returned : List Token}
    (exited : ledger.exit returned = .ok next) : next = ledger.returnFrame returned := by
  unfold exit at exited
  split at exited
  · cases exited
  · exact (Except.ok.inj exited).symm

/-- Stopping retires every entry of the frame and nothing else. -/
theorem stop_live (ledger : Ledger) (entry : Entry) :
    entry ∈ ledger.stop.live ↔ entry ∈ ledger.live ∧ entry.frame ≠ ledger.depth := by
  simp [stop, List.mem_filter]

end Ledger

/-! ## The handler -/

theorem handler_create (ledger : Ledger) (slot holder : String) :
    handler (.create slot holder) ledger =
      ⟨.returned (ledger.create slot holder).1, (ledger.create slot holder).2,
        [.create slot holder]⟩ := rfl

/-- A request that fails its check stops the run and records the refusal. -/
theorem handler_consume_refused {ledger : Ledger} {slot holder : String} {token : Token}
    {reason : Refusal} (refused : ledger.consume slot holder token = .error reason) :
    (handler (.consume slot holder token) ledger).outcome = .stopped .refused ∧
      (handler (.consume slot holder token) ledger).state.refused.isSome := by
  refine ⟨by simp [handler, refused, refuse], ?_⟩
  simp only [handler, refused, refuse]
  cases ledger.refused <;> rfl

theorem handler_pass_refused {ledger : Ledger} {slot holder : String} {token : Token}
    {reason : Refusal} (refused : ledger.pass slot holder token = .error reason) :
    (handler (.pass slot holder token) ledger).outcome = .stopped .refused ∧
      (handler (.pass slot holder token) ledger).state.refused.isSome := by
  refine ⟨by simp [handler, refused, refuse], ?_⟩
  simp only [handler, refused, refuse]
  cases ledger.refused <;> rfl

end PIR.Custody
