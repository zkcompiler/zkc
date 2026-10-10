import Zkc.Compiler.Blocks.Execution
import PolyFun.PFunctor.Free.Basic

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ZkcArkLib.PolyFun.Blocks
open Zkc.Compiler.Blocks PFunctor

variable {V A O S E : Type}

def signature (V A : Type) : PFunctor where
  A := Sum (Zkc.Compiler.Blocks.Key V) A
  B := fun _ => V

def encode : Program V A O → FreeM (signature V A) O
  | .done o => .pure o
  | .pureCall k next => .liftBind (.inl k) (fun v => encode (next v))
  | .action a next => .liftBind (.inr a) (fun v => encode (next v))

def interpret (f : Zkc.Compiler.Blocks.Key V → V) (h : A → S → V × S × List E) :
    (a : (signature V A).A) → StateM (S × List E) ((signature V A).B a)
  | .inl k => fun s => (f k,s)
  | .inr a => fun s =>
    let r := h a s.1
    (r.1,(r.2.1,s.2 ++ r.2.2))

-- Uses the upstream cslib free monad exposed by PolyFun and its liftM interpreter.
theorem liftM_agrees (f : Zkc.Compiler.Blocks.Key V → V) (h : A → S → V × S × List E)
    (p : Program V A O) (s : S) (log : List E) :
    (encode p).liftM (interpret f h) (s,log) =
      ((runProgram f h p s).2.1, (runProgram f h p s).2.2, log ++ (runProgram f h p s).1) := by
  induction p generalizing s log with
  | done o => change (o,s,log) = (o,s,log ++ []); simp
  | pureCall k next ih => exact ih (f k) s log
  | action a next ih =>
    change (encode (next (h a s).1)).liftM (interpret f h)
      ((h a s).2.1,log ++ (h a s).2.2) = _
    rw [ih]
    simp only [runProgram,List.append_assoc]

def execute (f : Zkc.Compiler.Blocks.Key V → V) (h : A → S → V × S × List E)
    (p : Program V A O) (s : S) : List E × O × S :=
  let r := (encode p).liftM (interpret f h) (s,[])
  (r.2.2,r.1,r.2.1)

theorem execute_agrees (f : Zkc.Compiler.Blocks.Key V → V) (h : A → S → V × S × List E)
    (p : Program V A O) (s : S) : execute f h p s = runProgram f h p s := by
  simp [execute,liftM_agrees]

end ZkcArkLib.PolyFun.Blocks
