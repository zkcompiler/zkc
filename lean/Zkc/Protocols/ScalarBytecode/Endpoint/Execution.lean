import Zkc.Protocols.ScalarBytecode.Endpoint.State
import Zkc.Realization.InstructionSimulation

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.Endpoint
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution

/-- A deterministic strategy may carry arbitrary private state and emit any
    raw word window. Only declared demands and challenge notices reach it.
    This is a semantic transducer, with no efficiency/randomness assumption. -/
structure Supplier (S : Type) where
  read : Key → Nat → S → Word × S
  ended : Key → S → Bool × S
  challenge : Key → Nat → S → S

def serve {S : Type} (supplier : Supplier S) (i : Instr) (v : Local) (s : S) :
    Input i.op × S :=
  match i.op with
  | .read => supplier.read ⟨v.subject,i.site⟩ i.literal s
  | .expectEnd => supplier.ended ⟨v.subject,i.site⟩ s
  | .init | .absorb | .draw | .add | .mul | .check | .accept | .constant | .gexp | .gmul | .missing => ((),s)

def notify {S : Type} (supplier : Supplier S) (p : Public) (events : List Event) (s : S) : S :=
  events.foldl (fun t e => if e.op = .draw then supplier.challenge ⟨p,e.site⟩ e.value t else t) s

def openStep {S : Type} (hash : Hash) (supplier : Supplier S) (i : Instr) (g : World S) :
    Step (World S) Event :=
  let a := serve supplier i g.verifier g.external
  let out := update hash i a.1 g.verifier
  let s := notify supplier g.verifier.subject (eventsOf out) a.2
  mapStep (fun v => ⟨v,s⟩) out

def bufferSupplier : Supplier Bytes where
  read := fun _ _ bs =>
    let w : Word := ⟨bs.take 8,by simp only [List.length_take]; omega⟩
    (w,bs.drop (wordConsumed w))
  ended := fun _ bs => (bs.isEmpty,bs)
  challenge := fun _ _ bs => bs

@[simp] theorem notify_buffer (p : Public) (es : List Event) (bs : Bytes) :
    notify bufferSupplier p es bs = bs := by
  induction es generalizing bs with
  | nil => rfl
  | cons e es ih => simp only [notify,List.foldl_cons]; split <;> exact ih _

theorem serve_buffer (hash : Hash) (i : Instr) (v : Local) (bs : Bytes) :
    serve bufferSupplier i v bs =
    (window i.op bs, bs.drop (effect hash (request i v.core) v.core bs).2.2.1) := by
  have he := effect_window hash (request i v.core) v.core bs
  rw [← he]
  rcases i with ⟨site,op,x,y,literal,data,label,dest⟩
  cases op <;> simp [serve,bufferSupplier,window,inputBytes,request,effect,wordConsumed,List.take_take]
  all_goals split <;> (first | rfl | split <;> rfl)

def toTail (g : World Bytes) : Tail := ⟨g.external,g.verifier.offset,g.verifier.core⟩

/-- Exact one-step erasure; no hidden suffix is supplied to local update. -/
theorem buffer_step (hash : Hash) (i : Instr) (g : World Bytes) :
    mapStep toTail (openStep hash bufferSupplier i g) = tailStep hash i (toTail g) := by
  unfold openStep
  rw [serve_buffer hash]
  simp only [notify_buffer]
  unfold update
  have he := effect_window hash (request i g.verifier.core) g.verifier.core g.external
  change effect hash (request i g.verifier.core) g.verifier.core
    (inputBytes i.op (window i.op g.external)) = _ at he
  rw [he]
  simp only [tailStep,tailHandler,toTail]
  generalize effect hash (request i g.verifier.core) g.verifier.core g.external = e
  rcases e with ⟨reply,core,consumed,events⟩
  cases reply <;> by_cases hi : i.op = .accept <;> simp [hi,mapStep,toTail]

theorem buffer_run (hash : Hash) (ops : List Instr) (g : World Bytes) :
    TerminalRel (fun s t => toTail s = t)
      (run (openStep hash bufferSupplier) ops g) (run (tailStep hash) ops (toTail g)) := by
  apply simulation _ _ _ _ ops g (toTail g) rfl
  intro i s t h
  subst t
  rw [← buffer_step hash i s]
  exact lift_map toTail _

/-- The initialized history/PC invariant applies to arbitrary supplier states,
    including rejection and unavailable terminals. -/
theorem open_counter {S : Type} (hash : Hash) (supplier : Supplier S) (i : Instr) (g : World S) :
    (stateOf (openStep hash supplier i g)).verifier.pc = g.verifier.pc + 1 ∧
    (stateOf (openStep hash supplier i g)).verifier.history.length = g.verifier.history.length + 1 := by
  have h := counter_and_history hash i (serve supplier i g.verifier g.external).1 g.verifier
  dsimp only [openStep]
  generalize update hash i (serve supplier i g.verifier g.external).1 g.verifier = out at h ⊢
  cases out <;> exact h

theorem open_history_aligned {S : Type} (hash : Hash) (supplier : Supplier S)
    (ops : List Instr) (g : World S) (h : HistoryAligned g.verifier) :
    HistoryAligned (run (openStep hash supplier) ops g).state.verifier := by
  induction ops generalizing g with
  | nil => exact h
  | cons i ops ih =>
    have hc := open_counter hash supplier i g
    cases he : openStep hash supplier i g with
    | halt outcome t es =>
      simp only [he,stateOf] at hc
      simpa [run,he,HistoryAligned,hc.1,hc.2] using h
    | next t es =>
      simp only [he,stateOf] at hc
      have ht : HistoryAligned t.verifier := by
        unfold HistoryAligned at *
        omega
      simpa [run,he] using ih t ht

def endpoint {S : Type} (hash : Hash) (supplier : Supplier S) (code : List Instr) :
    Nat → World S → Terminal (World S) Event
  | 0,g => ⟨.incomplete,g,[]⟩
  | fuel+1,g => match code[g.verifier.pc]? with
    | none => ⟨.incomplete,g,[]⟩
    | some i => match openStep hash supplier i g with
      | .halt x t es => ⟨x,t,es⟩
      | .next t es =>
        let out := endpoint hash supplier code fuel t
        ⟨out.outcome,out.state,es ++ out.events⟩

/-- Actual dispatch uses only local PC. The external strategy never selects
    which instruction the fixed public list executes. -/
theorem endpoint_list {S : Type} (hash : Hash) (supplier : Supplier S)
    (pre ops : List Instr) (g : World S) (h : g.verifier.pc = pre.length) :
    endpoint hash supplier (pre ++ ops) ops.length g = run (openStep hash supplier) ops g := by
  induction ops generalizing pre g with
  | nil => rfl
  | cons i ops ih =>
    have hc := open_counter hash supplier i g
    have hi : (pre ++ i :: ops)[g.verifier.pc]? = some i := by
      rw [h,List.getElem?_append_right (Nat.le_refl pre.length)]
      simp
    simp only [List.length_cons,endpoint,hi]
    cases he : openStep hash supplier i g with
    | halt x t es => simp [run,he]
    | next t es =>
      have ht : t.verifier.pc = (pre ++ [i]).length := by
        simpa [he,stateOf,h] using hc.1
      have hh := ih (pre ++ [i]) t ht
      have hh' : endpoint hash supplier (pre ++ i :: ops) ops.length t =
          run (openStep hash supplier) ops t := by simpa only [List.append_assoc,List.singleton_append] using hh
      simp only [run,he]
      rw [hh']

end Zkc.Protocols.ScalarBytecode.Endpoint
