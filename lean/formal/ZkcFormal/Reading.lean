module

public import ZkcFormal.OracleProcess

@[expose] public section

/-!
A process read as a computation that may stop.

A statement about a process reads it as a computation with oracles whose value is a result or a
stop (`embed`). A proof reads the same computation with the stop as an exception: `read p` is
`embed p` under `ExceptT.mk`, so that a result is a `pure`, a stop is a `throw`, an effect is a
query followed by the rest, and a process composed by `Process.bind`, `Process.map`,
`Process.mapHalt`, `Process.iterate` or a Boolean choice is the computation composed by the
monad's bind, map, the exception's map, a `for` over a range, and `if`. There is one definition
from a process into VCVio's computations, `embed`; `read` unfolds to it, and what is proved of
`read p` is a statement about what the statement of soundness reads.

`decode` is the inverse: every computation of that type is the reading of one process
(`read_decode`, `decode_read`). So a result about a computation that was not written as a
process (a handled program, a program after a transformation) is a result about a process.
-/

namespace ZkcFormal.Reading
open Zkc.Core ProbabilisticProcess OracleComp

variable {S : Sig} {H H' A B : Type}

/-- A computation over the effects of a signature that returns a value or stops. -/
abbrev Comp (S : Sig) (H : Type) := ExceptT H (OracleComp (specOf S))

/-- One effect, as a computation that returns its reply. -/
def ask (S : Sig) (H : Type) (op : S.Op) : Comp S H (S.Reply op) :=
  ExceptT.lift ((specOf S).query op)

/-- A result or a stop, as a value or an exception. -/
def pack : A ⊕ H → Except H A := Sum.elim Except.ok Except.error

/-- A value or an exception, as a result or a stop. -/
def unpack : Except H A → A ⊕ H
  | .ok a => .inl a
  | .error h => .inr h

theorem unpack_pack (v : A ⊕ H) : unpack (pack v) = v := by cases v <;> rfl

theorem pack_unpack (v : Except H A) : pack (unpack v) = v := by cases v <;> rfl

/-- **The reading of a process**: the computation that the statement reads, with the stop as an
exception. -/
def read (p : Process S H A) : Comp S H A := ExceptT.mk (pack <$> embed p)

/-- The reading is the embedding, by definition. -/
theorem read_run (p : Process S H A) : (read p).run = pack <$> embed p := rfl

/-- The embedding, from the reading. -/
theorem embed_eq (p : Process S H A) : embed p = unpack <$> (read p).run := by
  rw [read_run, Functor.map_map]
  have same : (unpack ∘ pack : A ⊕ H → A ⊕ H) = id := funext unpack_pack
  change embed p = (unpack ∘ pack) <$> embed p
  rw [same]
  exact (id_map (embed p)).symm

/-! ## The reading at each constructor -/

theorem read_done (a : A) : read (.done a : Process S H A) = pure a := rfl

theorem read_halt (h : H) : read (.halt h : Process S H A) = throw h := rfl

theorem read_call (op : S.Op) (k : S.Reply op → Process S H A) :
    read (.call op k) = ask S H op >>= fun reply => read (k reply) := rfl

/-! ## The reading of a composed process -/

/-- The embedding of a process followed by another. -/
theorem embed_bind (p : Process S H A) (k : A → Process S H B) :
    embed (p.bind k) =
      embed p >>= fun x => x.elim (fun a => embed (k a)) (fun h => pure (.inr h)) := by
  induction p with
  | done => simp [Process.bind, embed]
  | halt => simp [Process.bind, embed]
  | call op next ih =>
    change OracleComp.queryBind (spec := specOf S) op _ = OracleComp.queryBind op _
    congr 1
    funext reply
    exact ih reply

/-- A process followed by another reads as the bind of the readings. -/
theorem read_bind (p : Process S H A) (k : A → Process S H B) :
    read (p.bind k) = read p >>= fun a => read (k a) := by
  apply ExceptT.ext
  simp only [read, ExceptT.run_mk, ExceptT.run_bind, embed_bind, map_bind, bind_map_left]
  refine bind_congr fun x => ?_
  cases x <;> simp [pack]

/-- A process with its result mapped reads as the reading mapped. -/
theorem read_map (f : A → B) (p : Process S H A) : read (p.map f) = f <$> read p := by
  induction p with
  | done a => rfl
  | halt h => rfl
  | call op next ih =>
    change read (.call op fun reply => (next reply).map f) = _
    rw [read_call, read_call, map_bind]
    exact congrArg _ (funext ih)

/-- A process with its stop mapped reads as the reading with its exception mapped. -/
theorem read_mapHalt (f : H → H') (p : Process S H A) :
    read (p.mapHalt f) = ExceptT.adapt f (read p) := by
  apply ExceptT.ext
  induction p with
  | done a => rfl
  | halt h => rfl
  | call op next ih =>
    exact congrArg (OracleComp.queryBind (spec := specOf S) op) (funext ih)

/-- An iteration reads as a `for` over the range of its iteration numbers. -/
theorem read_iterate (count : Nat) (step : Nat → A → Process S H A) (start : Nat) (a : A) :
    read (Process.iterate count step start a) =
      forIn (List.range' start count) a fun i a => ForInStep.yield <$> read (step i a) := by
  induction count generalizing start a with
  | zero => rfl
  | succ n ih =>
    simp only [Process.iterate, read_bind, List.range'_succ, List.forIn_cons, bind_map_left, ih]

/-- A Boolean choice of processes reads as `if`. -/
theorem read_cond (c : Bool) (p q : Process S H A) :
    read (bif c then p else q) = if c then read p else read q := by cases c <;> rfl

/-! ## Every computation is the reading of one process -/

/-- The process of a computation. -/
def decode : OracleComp (specOf S) (Except H A) → Process S H A
  | .pure (.ok a) => .done a
  | .pure (.error h) => .halt h
  | .liftBind op k => .call op fun reply => decode (k reply)

/-- The process of a reading is the process read. -/
theorem decode_read (p : Process S H A) : decode (read p).run = p := by
  induction p with
  | done | halt => rfl
  | call op next ih => exact congrArg (Process.call (S := S) op) (funext ih)

/-- The reading of the process of a computation is the computation. -/
theorem read_decode (x : Comp S H A) : read (decode x.run) = x := by
  apply ExceptT.ext
  generalize x.run = y
  induction y with
  | pure v => cases v <;> rfl
  | queryBind op k ih => exact congrArg (OracleComp.queryBind (spec := specOf S) op) (funext ih)

/-- Two processes with one reading are one process. -/
theorem read_injective {p q : Process S H A} (same : read p = read q) : p = q := by
  rw [← decode_read p, ← decode_read q, same]

end ZkcFormal.Reading
