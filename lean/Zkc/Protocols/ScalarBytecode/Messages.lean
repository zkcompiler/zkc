import Zkc.Protocols.AlgebraicRounds.ParameterFamily
import Zkc.Protocols.ScalarBytecode.Parameters
import Zkc.Semantics.OperationContract
import Zkc.Realization.ByteEncoding

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.Messages
open Zkc.Source.PublicDimensions Zkc.Protocols.AlgebraicRounds.ParameterFamily

variable {n m : Nat}

inductive ValueSort where
  | scalar | groupWire
  deriving Repr, DecidableEq
-- GroupWire is a distinct canonical residue code, NOT a subgroup certificate.
structure GroupWire where
  word : Fin 4611686018427394499
  deriving Repr, DecidableEq
abbrev Carrier : ValueSort → Type
  | .scalar => Fin Zkc.Protocols.ScalarBytecode.Parameters.modulus
  | .groupWire => GroupWire
inductive Kind where
  | read | send
  deriving Repr, DecidableEq
structure Op (p : Params) where
  kind : Kind
  round : Fin p.rounds
  sort : ValueSort

def Arg (p : Params) : Op p → Type
  | ⟨.read,_,_⟩ => Zkc.Realization.ByteEncoding.Bytes
  | ⟨.send,_,s⟩ => List (Carrier s)
def signature (p : Params) : Zkc.Semantics.OperationContract.Signature where
  Op := Op p
  Arg := Arg p
  Result := fun
    | ⟨.read,_,s⟩, _ => List (Carrier s)
    | ⟨.send,_,_⟩, _ => Unit
  legalArg := fun
    | ⟨.read,_,_⟩, _ => True
    | ⟨.send,_,_⟩, a => a.length = p.degree + 1
  legalResult := fun
    | ⟨.read,_,_⟩, _, v => v.length = p.degree + 1
    | ⟨.send,_,_⟩, _, _ => True

def send (p : Params) (r : Fin p.rounds) (s : ValueSort) (site : Nat)
    (xs : List (Carrier s)) : Zkc.Semantics.OperationContract.Request (signature p) :=
  ⟨site,⟨.send,r,s⟩,xs⟩
def read (p : Params) (r : Fin p.rounds) (s : ValueSort) (site : Nat)
    (bs : Zkc.Realization.ByteEncoding.Bytes) : Zkc.Semantics.OperationContract.Request (signature p) := ⟨site,⟨.read,r,s⟩,bs⟩

theorem all_raw_reads_legal (p : Params) (r : Fin p.rounds) (s : ValueSort)
    (site : Nat) (bs : Zkc.Realization.ByteEncoding.Bytes) :
    (signature p).legalArg (read p r s site bs).op (read p r s site bs).arg := by trivial

-- A syntax-instantiation law consumed directly by the dependent Zkc.Realization.InstructionSequence request.
-- No coefficient equation or honesty assumption restricts xs.
def instantiateRequest (f : Family n) (σ : Fin n → Dim m) (ρ : Fin m → Nat)
    (r : Dim n) (hr : r.eval (fun i => (σ i).eval ρ) <
      (f.inst (fun i => (σ i).eval ρ)).rounds)
    (s : ValueSort) (site : Nat) (xs : List (Carrier s)) :
    Zkc.Semantics.OperationContract.Request (signature ((f.subst σ).inst ρ)) :=
  send _ ⟨(r.subst σ).eval ρ, by simpa [inst_subst, eval_subst] using hr⟩ s site xs

theorem formation_substitution (f : Family n) (σ : Fin n → Dim m)
    (ρ : Fin m → Nat) (r : Dim n)
    (hr : r.eval (fun i => (σ i).eval ρ) < (f.inst (fun i => (σ i).eval ρ)).rounds)
    (s : ValueSort) (site : Nat) (xs : List (Carrier s))
    (hx : xs.length = (f.inst (fun i => (σ i).eval ρ)).degree + 1) :
    let req := instantiateRequest f σ ρ r hr s site xs
    req.site = site ∧ req.op.round.val = r.eval (fun i => (σ i).eval ρ) ∧
    (signature ((f.subst σ).inst ρ)).legalArg req.op req.arg := by
  simp [instantiateRequest, send, signature, eval_subst, inst_subst, hx]

def fixed : Params := ⟨2,2⟩
def scalarize (xs : List Nat) (h : ∀ x ∈ xs, x < Zkc.Protocols.ScalarBytecode.Parameters.modulus) : List (Carrier .scalar) :=
  xs.attach.map (fun x => ⟨x.val,h x.val x.property⟩)
@[simp] theorem scalarize_length (xs : List Nat) (h) : (scalarize xs h).length = xs.length := by
  simp [scalarize]

end Zkc.Protocols.ScalarBytecode.Messages
