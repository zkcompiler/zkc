import Zkc.Protocols.ScalarBytecode.ReadPackets
import PolyFun.PFunctor.Free.Basic

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ZkcArkLib.PolyFun.Reads
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint PFunctor Zkc.Protocols.ScalarBytecode.ReadPackets

-- A site belongs to the operation, so consecutive reads can query distinct
-- semantic occurrences. Bounds remain in the result type until client erasure.
inductive Op where
  | read : Nat → Nat → Op
  | abort : Exit → Op
abbrev signature : PFunctor where
  A := Op
  B := fun op => match op with
    | .read _ bound => Except Exit (Fin bound)
    | .abort _ => PEmpty

def readValue (site bound : Nat) : FreeM signature (Fin bound) :=
  .liftBind (.read site bound) (fun result => match result with
    | .ok v => .pure v
    | .error why => .liftBind (.abort why) PEmpty.elim)

abbrev M (S : Type) := ExceptT Exit (StateM (World S × List Event))

theorem bind_state {S X Y : Type} (a : M S X) (f : X → M S Y)
    (s : World S × List Event) :
    (a >>= f).run s =
      let p := a.run s
      match p.1 with
      | .error why => (.error why,p.2)
      | .ok x => (f x).run p.2 := by
  simp only [bind,ExceptT.bind,ExceptT.run,ExceptT.mk,StateT.bind,ExceptT.bindCont]
  cases h : a s with
  | mk result state => cases result <;> rfl

def interpret {S : Type} (hash : Hash) (supplier : Supplier S) :
    (op : signature.A) → M S (signature.B op)
  | .read site bound => fun s =>
    let p := receive hash supplier site bound s.1
    (.ok p.result,p.world,s.2 ++ p.events)
  | .abort why => fun s => (.error why,s)

theorem read_semantics {S : Type} (hash : Hash) (supplier : Supplier S)
    (site bound : Nat) (g : World S) (log : List Event) :
    ((readValue site bound).liftM (interpret hash supplier)).run (g,log) =
      ((receive hash supplier site bound g).result,
       (receive hash supplier site bound g).world,
       log ++ (receive hash supplier site bound g).events) := by
  simp only [readValue,FreeM.liftM,bind_state]
  dsimp only [interpret,ExceptT.run]
  cases h : (receive hash supplier site bound g).result <;>
    simp only [FreeM.liftM,interpret,bind,ExceptT.bind,ExceptT.mk,
      StateT.bind,ExceptT.bindCont,pure,ExceptT.pure,StateT.pure]

def two (s1 b1 s2 b2 : Nat) : FreeM signature (Fin b1 × Fin b2) := do
  let x ← readValue s1 b1
  let y ← readValue s2 b2
  pure (x,y)

theorem two_semantics {S : Type} (hash : Hash) (supplier : Supplier S)
    (s1 b1 s2 b2 : Nat) (g : World S) (log : List Event) :
    ((two s1 b1 s2 b2).liftM (interpret hash supplier)).run (g,log) =
    let p := receive hash supplier s1 b1 g
    match p.result with
    | .error why => (.error why,p.world,log ++ p.events)
    | .ok x =>
      let q := receive hash supplier s2 b2 p.world
      (q.result.map (fun y => (x,y)),q.world,(log ++ p.events) ++ q.events) := by
  simp only [two,FreeM.liftM_bind,FreeM.liftM_pure]
  rw [bind_state]
  rw [read_semantics]
  dsimp only
  cases h : (receive hash supplier s1 b1 g).result with
  | error why => rfl
  | ok x =>
    dsimp only
    rw [bind_state,read_semantics]
    dsimp only
    cases (receive hash supplier s2 b2 (receive hash supplier s1 b1 g).world).result <;> rfl

theorem two_erasure {S : Type} (hash : Hash) (supplier : Supplier S)
    (s1 b1 s2 b2 : Nat) (g : World S) :
    erasedTerminal (((two s1 b1 s2 b2).liftM (interpret hash supplier)).run (g,[])) =
      run (openStep hash supplier) [readInstr s1 b1,readInstr s2 b2] g := by
  rw [two_semantics]
  simp only [run,← receive_erasure]
  generalize receive hash supplier s1 b1 g = p
  unfold erase
  cases hp : p.result with
  | error why => simp [erasedTerminal]
  | ok x =>
    simp only
    generalize receive hash supplier s2 b2 p.world = q
    cases hq : q.result <;> simp [erasedTerminal,Except.map]

end ZkcArkLib.PolyFun.Reads
