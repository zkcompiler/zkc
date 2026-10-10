import Zkc.Compiler.Readback.Syntax
import Zkc.Compiler.Blocks.Analysis

set_option autoImplicit false

namespace Zkc.Compiler.Readback
variable {L NativeOp V A O S E : Type}

def embed (literal : L → V) : Term L String → Zkc.Compiler.Blocks.Expr V
  | .input i => .input i
  | .literal v => .literal (literal v)
  | .apply op a b => .apply op (embed literal a) (embed literal b)
  | .choose c a b => .choose (embed literal c) (embed literal a) (embed literal b)

def embedBlock (literal : L → V) (b : Block L String) : Zkc.Compiler.Blocks.Block V :=
  b.map fun (i,e) => (i,embed literal e)

-- Logical native-plan meaning. A resolved native symbol is interpreted by
-- its provider contract. This does not assert semantics of arbitrary Rust.
def compileNative (resolve : NativeOp → Option String) (literal : L → V)
    (env : Nat → V) (truth : V → Bool) :
    Term L NativeOp → (V → Zkc.Compiler.Blocks.Program V A O) → Zkc.Compiler.Blocks.Program V A O
  | .input i, next => next (env i)
  | .literal v, next => next (literal v)
  | .apply op a b, next =>
    compileNative resolve literal env truth a (fun x =>
      compileNative resolve literal env truth b (fun y =>
        .pureCall ((resolve op).getD "unresolved-native-operation",x,y) next))
  | .choose c a b, next =>
    compileNative resolve literal env truth c (fun v =>
      if truth v then compileNative resolve literal env truth a next
      else compileNative resolve literal env truth b next)

def compileNativeBlock (resolve : NativeOp → Option String) (literal : L → V)
    (truth : V → Bool) : Block L NativeOp → (Nat → V) →
      ((Nat → V) → Zkc.Compiler.Blocks.Program V A O) → Zkc.Compiler.Blocks.Program V A O
  | [],env,next => next env
  | (i,e)::rest,env,next => compileNative resolve literal env truth e
      (fun v => compileNativeBlock resolve literal truth rest (Function.update env i v) next)

theorem read_term_program (resolve : NativeOp → Option String) (literal : L → V)
    (env : Nat → V) (truth : V → Bool) (native : Term L NativeOp)
    (source : Term L String) (h : readTerm resolve native = some source)
    (next : V → Zkc.Compiler.Blocks.Program V A O) :
    compileNative resolve literal env truth native next =
      Zkc.Compiler.Blocks.compile env truth (embed literal source) next := by
  induction native generalizing source next with
  | input i => cases h; rfl
  | literal v => cases h; rfl
  | apply op a b iha ihb =>
    simp only [readTerm,Option.bind_eq_bind] at h
    cases hr : resolve op with
    | none => simp [hr] at h
    | some op' =>
      cases ha : readTerm resolve a with
      | none => simp [hr,ha] at h
      | some a' =>
        cases hb : readTerm resolve b with
        | none => simp [hr,ha,hb] at h
        | some b' =>
          have hs : Term.apply op' a' b' = source := by simpa [hr,ha,hb] using h
          subst source
          simp only [compileNative,embed,Zkc.Compiler.Blocks.compile]
          rw [iha a' ha]
          congr 1
          funext x
          rw [ihb b' hb]
          simp [hr]
  | choose c a b ihc iha ihb =>
    cases hc : readTerm resolve c with
    | none => simp [readTerm,hc] at h
    | some c' =>
      cases ha : readTerm resolve a with
      | none => simp [readTerm,hc,ha] at h
      | some a' =>
        cases hb : readTerm resolve b with
        | none => simp [readTerm,hc,ha,hb] at h
        | some b' =>
          have hs : Term.choose c' a' b' = source := by simpa [readTerm,hc,ha,hb] using h
          subst source
          simp only [compileNative,embed,Zkc.Compiler.Blocks.compile]
          rw [ihc c' hc]
          congr 1
          funext v
          split
          · exact iha _ ha next
          · exact ihb _ hb next

theorem read_block_program (resolve : NativeOp → Option String) (literal : L → V)
    (truth : V → Bool) (native : Block L NativeOp) (source : Block L String)
    (h : readBlock resolve native = some source) (env : Nat → V)
    (next : (Nat → V) → Zkc.Compiler.Blocks.Program V A O) :
    compileNativeBlock resolve literal truth native env next =
      Zkc.Compiler.Blocks.compileBlock truth (embedBlock literal source) env next := by
  induction native generalizing source env with
  | nil => cases h; rfl
  | cons row rest ih =>
    obtain ⟨i,e⟩ := row
    cases he : readTerm resolve e with
    | none => simp [readBlock,he] at h
    | some e' =>
      cases hr : readBlock resolve rest with
      | none => simp [readBlock,he,hr] at h
      | some rest' =>
        have hs : (i,e')::rest'=source := by simpa [readBlock,he,hr] using h
        subst source
        simp only [compileNativeBlock,embedBlock,List.map_cons,Zkc.Compiler.Blocks.compileBlock]
        rw [read_term_program resolve literal env truth e e' he]
        congr 1
        funext v
        exact ih _ hr _

end Zkc.Compiler.Readback
