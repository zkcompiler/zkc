import Zkc.Protocols.ScalarBytecode.Execution
import Zkc.Semantics.Locality

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.Endpoint
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution

abbrev Word := {bs : Bytes // bs.length ≤ 8}
abbrev Input : Op → Type
  | .read => Word
  | .expectEnd => Bool
  | _ => Unit

def window (op : Op) (bs : Bytes) : Input op :=
  match op with
  | .read => ⟨bs.take 8, by simp only [List.length_take]; omega⟩
  | .expectEnd => bs.isEmpty
  | .init | .absorb | .draw | .add | .mul | .check | .accept | .constant | .gexp | .gmul | .missing => ()

def inputBytes (op : Op) : Input op → Bytes :=
  match op with
  | .read => fun w => w.val
  | .expectEnd => fun (ended : Bool) => if ended then [] else [⟨0,by decide⟩]
  | _ => fun _ => []

/-- The whole effect, including failed-read bytes and provider state, factors
    through the permitted response. This is not constancy before reception. -/
theorem effect_window (hash : Hash) (r : Request sig) (c : Core) (bs : Bytes) :
    effect hash r c (inputBytes r.op (window r.op bs)) = effect hash r c bs := by
  rcases r with ⟨site,op,arg⟩
  cases op <;> simp [window,inputBytes,effect,List.take_take]

/-- Consumption depends on word completeness, also for noncanonical values. -/
def wordConsumed (w : Word) : Nat := if w.val.length = 8 then 8 else 0

theorem read_consumed (hash : Hash) (site : Nat) (arg : Args) (c : Core) (w : Word) :
    (effect hash ⟨site,.read,arg⟩ c w.val).2.2.1 = wordConsumed w := by
  have ht : w.val.take 8 = w.val := List.take_of_length_le w.property
  by_cases hw : w.val.length = 8 <;>
    by_cases hv : valueBE w.val < arg.a <;>
    simp [effect, ht, wordConsumed, hw, hv]

structure Public where
  artifact : String
  family : String
  parameter : Nat
  deriving DecidableEq, Repr

structure Key where
  subject : Public
  site : Nat
  deriving DecidableEq, Repr

inductive Observed where
  | word : Bytes → Observed
  | endAnswer : Bool → Observed
  | internal
  deriving DecidableEq, Repr

def observed (op : Op) : Input op → Observed :=
  match op with
  | .read => fun w => .word w.val
  | .expectEnd => fun ended => .endAnswer ended
  | _ => fun _ => .internal

structure Receipt where
  key : Key
  op : Op
  input : Observed
  deriving DecidableEq, Repr

/-- Core is explicitly initialized verifier memory. Its pure-hash transcript
    state is permitted here; a private/random provider needs another interface. -/
structure Local where
  subject : Public
  core : Core
  offset : Nat
  pc : Nat
  history : List Receipt

structure World (S : Type) where
  verifier : Local
  external : S

def view {S : Type} (g : World S) : Local := g.verifier
def representative (v : Local) : World Bytes := ⟨v,[]⟩

theorem representative_section (g : World Bytes) :
    view (representative (view g)) = view g := rfl

def nextRequest (ops : List Instr) (v : Local) : Option (Key × Request sig) :=
  (ops[v.pc]?).map (fun i => (⟨v.subject,i.site⟩,request i v.core))

theorem request_local {S : Type} (ops : List Instr) :
    Zkc.Semantics.Locality.FiberConstant (view (S := S)) (fun g => nextRequest ops g.verifier) := by
  intro g h same
  exact congrArg (nextRequest ops) same

def update (hash : Hash) (i : Instr) (a : Input i.op) (v : Local) : Step Local Event :=
  let e := effect hash (request i v.core) v.core (inputBytes i.op a)
  let t : Local := {v with
    core := e.2.1
    offset := v.offset + e.2.2.1
    pc := v.pc + 1
    history := v.history ++ [⟨⟨v.subject,i.site⟩,i.op,observed i.op a⟩]}
  match e.1 with
  | .reject why => .halt (.reject why) t e.2.2.2
  | .unavailable why => .halt (.unavailable why) t e.2.2.2
  | .ok value =>
    let t := {t with core := put t.core i.dest value}
    if i.op = .accept then .halt .accept t e.2.2.2 else .next t e.2.2.2

def respond (hash : Hash) (i : Instr) (a : Input i.op) (g : World Bytes) :
    (Option Exit × List Event) × World Bytes :=
  let out := update hash i a g.verifier
  ((exitOf out,eventsOf out),⟨stateOf out,g.external⟩)

theorem response_stable (hash : Hash) (i : Instr) (a : Input i.op) :
    Zkc.Semantics.Locality.FiberConstant view (fun g => Zkc.Semantics.Locality.projectedResult view (respond hash i a g)) := by
  intro g h same
  simp only [Zkc.Semantics.Locality.projectedResult,respond,view] at *
  rw [same]

/-- N9's representative construction now agrees with the actual local update
    on the same byte/effect subject, conditional on the received input. -/
theorem actual_descent (hash : Hash) (i : Instr) (a : Input i.op) (g : World Bytes) :
    Zkc.Semantics.Locality.localStep view representative (fun a => respond hash i a) a (view g) =
      Zkc.Semantics.Locality.projectedResult view (respond hash i a g) :=
  Zkc.Semantics.Locality.step_descent view representative representative_section
    (fun a => respond hash i a) (response_stable hash i) a g

theorem counter_and_history (hash : Hash) (i : Instr) (a : Input i.op) (v : Local) :
    (stateOf (update hash i a v)).pc = v.pc + 1 ∧
    (stateOf (update hash i a v)).history.length = v.history.length + 1 := by
  unfold update
  generalize effect hash (request i v.core) v.core (inputBytes i.op a) = e
  rcases e with ⟨reply,core,consumed,events⟩
  cases reply with
  | reject why => exact ⟨rfl,by simp [stateOf]⟩
  | unavailable why => exact ⟨rfl,by simp [stateOf]⟩
  | ok value =>
    dsimp only
    split <;> exact ⟨rfl,by simp [stateOf]⟩

def HistoryAligned (v : Local) : Prop := v.pc = v.history.length
theorem history_aligned_preserved (hash : Hash) (i : Instr) (a : Input i.op) (v : Local)
    (h : HistoryAligned v) : HistoryAligned (stateOf (update hash i a v)) := by
  rcases counter_and_history hash i a v with ⟨hc,hh⟩
  simp only [HistoryAligned,hc,hh]
  exact congrArg (fun n => n+1) h

def initial (p : Public) : Local := ⟨p,⟨fun _ => 0,[],0⟩,0,0,[]⟩
theorem initial_history_aligned (p : Public) : HistoryAligned (initial p) := rfl

end Zkc.Protocols.ScalarBytecode.Endpoint
