import Zkc.Protocols.ScalarBytecode.Suppliers.Contracts

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.Suppliers
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint

structure TapeCursor where
  full : Bytes
  position : Nat

def cursorSupplier : Supplier TapeCursor where
  read := fun _ _ s =>
    let w : Word := ⟨(s.full.drop s.position).take 8,by simp only [List.length_take]; omega⟩
    (w,{s with position := s.position + wordConsumed w})
  ended := fun _ s => ((s.full.drop s.position).isEmpty,s)
  challenge := fun _ _ s => s

def CursorRel (s : TapeCursor) (bs : Bytes) := s.full.drop s.position = bs

theorem cursor_represents : SupplierRel cursorSupplier bufferSupplier CursorRel where
  read := by
    intro k n s bs h
    dsimp [CursorRel] at h
    constructor
    · simp [cursorSupplier,bufferSupplier,h]
    · simp [cursorSupplier,bufferSupplier,CursorRel,← List.drop_drop,h]
  ended := by
    intro k s bs h
    exact ⟨congrArg List.isEmpty h,h⟩
  challenge := by intros; assumption

def counted {S : Type} (supplier : Supplier S) : Supplier (S × Nat) where
  read := fun k n s =>
    let a := supplier.read k n s.1
    (a.1,(a.2,s.2+1))
  ended := fun k s =>
    let a := supplier.ended k s.1
    (a.1,(a.2,s.2+1))
  challenge := fun k n s => (supplier.challenge k n s.1,s.2+1)

theorem counted_represents {S : Type} (supplier : Supplier S) :
    SupplierRel (counted supplier) supplier (fun a b => a.1 = b) where
  read := by intro k n s t h; subst t; exact ⟨rfl,rfl⟩
  ended := by intro k s t h; subst t; exact ⟨rfl,rfl⟩
  challenge := by intro k n s t h; subst t; rfl

theorem cursor_run (hash : Hash) (ops : List Instr) (v : Local) (s : TapeCursor) :
    TerminalRel (WorldRel CursorRel)
      (run (openStep hash cursorSupplier) ops ⟨v,s⟩)
      (run (openStep hash bufferSupplier) ops ⟨v,s.full.drop s.position⟩) :=
  supplier_run cursor_represents hash ops _ _ ⟨rfl,rfl⟩

theorem counted_run {S : Type} (supplier : Supplier S) (hash : Hash)
    (ops : List Instr) (v : Local) (s : S) (n : Nat) :
    TerminalRel (WorldRel (fun a b => a.1 = b))
      (run (openStep hash (counted supplier)) ops ⟨v,(s,n)⟩)
      (run (openStep hash supplier) ops ⟨v,s⟩) :=
  supplier_run (counted_represents supplier) hash ops _ _ ⟨rfl,rfl⟩

theorem buffer_closed : ClosedLaw bufferSupplier (fun bs => bs = []) where
  read_empty := by intros; subst_vars; rfl
  read_preserves := by intros; subst_vars; rfl
  end_true := by intros; subst_vars; rfl
  end_preserves := by intros; assumption
  end_closes := by intro k s h; exact List.isEmpty_iff.mp h
  challenge_preserves := by intros; assumption

/-- A closed one-word interaction can adapt before delivering that word.
    End queries are truthful about this state; notices cannot reopen closure. -/
structure AdaptiveState where
  value : Nat
  closed : Bool
  deriving DecidableEq, Repr

def adaptive : Supplier AdaptiveState where
  read := fun _ _ s =>
    if s.closed then (⟨[],by simp⟩,s)
    else (⟨Zkc.Protocols.ScalarBytecode.Codec.enc s.value,by simp [Zkc.Protocols.ScalarBytecode.Codec.enc]⟩,{s with closed := true})
  ended := fun _ s => (s.closed,s)
  challenge := fun _ n s => if s.closed then s else {s with value := n}

theorem adaptive_closed : ClosedLaw adaptive (fun s => s.closed = true) where
  read_empty := by intro k n s hs; simp [adaptive,hs]
  read_preserves := by intro k n s hs; simp [adaptive,hs]
  end_true := by intros; assumption
  end_preserves := by intros; assumption
  end_closes := by intros; assumption
  challenge_preserves := by intro k n s hs; simp [adaptive,hs]

end Zkc.Protocols.ScalarBytecode.Suppliers
