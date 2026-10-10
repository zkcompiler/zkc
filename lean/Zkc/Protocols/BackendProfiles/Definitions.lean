import Zkc.Compiler.Readback.Syntax

set_option autoImplicit false

namespace Zkc.Protocols.BackendProfiles
inductive Literal where
  | unit
  | shift (n : Nat)
  | scalar (n : Nat)
  deriving DecidableEq, Repr

inductive NativeOp where
  | addmod (modulus : Nat)
  | mulmod (modulus : Nat)
  | node (binding : String)
  | ofWords (binding : String)
  | odd (width : Nat)
  | shift (width : Nat)
  deriving DecidableEq, Repr

inductive Profile where
  | scalar
  | fri
  deriving DecidableEq, Repr

def modulus : Nat := 2305843009213697249
def provider : String := "p3:3da346791c813433b201299afc3d10bf42f8a078:r26"

def resolve : Profile → NativeOp → Option String
  | .scalar, .addmod q => if q=modulus then some "field.add" else none
  | .scalar, .mulmod q => if q=modulus then some "field.mul" else none
  | .fri, .node id => if id=provider then some "p3.node" else none
  | .fri, .ofWords id => if id=provider then some "digest.of_words" else none
  | .fri, .odd w => if w=64 then some "word.odd" else none
  | .fri, .shift w => if w=64 then some "word.shr" else none
  | _, _ => none

abbrev Term (Op : Type) := Zkc.Compiler.Readback.Term Literal Op
abbrev Block (Op : Type) := Zkc.Compiler.Readback.Block Literal Op

def readTerm (profile : Profile) : Term NativeOp → Option (Term String) :=
  Zkc.Compiler.Readback.readTerm (resolve profile)

def readBlock (profile : Profile) : Block NativeOp → Option (Block String) :=
  Zkc.Compiler.Readback.readBlock (resolve profile)

def inScope {Op : Type} (n : Nat) : Term Op → Bool
  | .input i => i < n
  | .literal .unit => true
  | .literal (.shift k) => k < 64
  | .literal (.scalar k) => k < modulus
  | .apply _ a b => inScope n a && inScope n b
  | .choose c a b => inScope n c && inScope n a && inScope n b

-- A deliberately sufficient dense-register plan; input bindings are checked
-- by the source readback wrapper, not inferred from local variable names.
def scopedBlock {Op : Type} : Nat → Block Op → Bool
  | _, [] => true
  | n, (i,e)::rest => i == n && inScope n e && scopedBlock (n+1) rest

structure Request where
  profile : Profile
  inputs : Nat
  expected : Block String
  expectedExports : List Nat
  native : Block NativeOp
  nativeExports : List Nat
  deriving DecidableEq, Repr

inductive Decision where
  | accepted
  | sourceScope
  | nativeScope
  | unsupportedBinding
  | bodyMismatch
  | exportMismatch
  deriving DecidableEq, Repr

def check (r : Request) : Decision :=
  if !scopedBlock r.inputs r.expected then .sourceScope
  else if !scopedBlock r.inputs r.native then .nativeScope
  else match readBlock r.profile r.native with
  | none => .unsupportedBinding
  | some b =>
    if b != r.expected then .bodyMismatch
    else if r.nativeExports != r.expectedExports || r.expectedExports.isEmpty ||
      !(r.expectedExports.all (· < r.inputs+r.expected.length)) then .exportMismatch
    else .accepted

theorem accepted_readback (r : Request) (h : check r = .accepted) :
    readBlock r.profile r.native = some r.expected ∧ r.nativeExports=r.expectedExports := by
  unfold check at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  next b hb =>
    split at h <;> try contradiction
    next he =>
      split at h <;> try contradiction
      next hx =>
        have heq : b=r.expected := by simpa using he
        have ho : r.nativeExports=r.expectedExports := by
          simp only [Bool.or_eq_true, Bool.not_eq_true, bne_iff_ne, not_or] at hx
          exact Classical.not_not.mp hx.1.1
        exact ⟨heq ▸ hb,ho⟩

end Zkc.Protocols.BackendProfiles
