module

public import Zkc.Core.Admission.Theorems
public import Zkc.Core.Scheme.Roles
public import Zkc.Vocabulary.Project
public import ZkcFormal.Written.Execution
public import ZkcFormal.Written.Extraction

@[expose] public section
set_option autoImplicit false

namespace ZkcFormal.Written
open Zkc.Core

def singletonProgram {V : Vocabulary} (hdr : ProtocolHeader V) (ns : Names hdr.ins)
    (body : Prot V ⟨[], []⟩ hdr ns) (ok : ProtocolConditions hdr body) : Typed V :=
  ⟨⟨[], [hdr]⟩, .protocol hdr ns body ok .nil, by simp [Headers.keys]⟩

unseal Zkc.Core.roleMeaning in
/-- A singleton root executes the projection of its body in the initial input environment.
Instantiate this equation before replaying instructions to keep the program table opaque. -/
theorem singleton_role_returns {V : Vocabulary} (M : Model V) (hdr : ProtocolHeader V)
    (ns : Names hdr.ins) (body : Prot V ⟨[], []⟩ hdr ns) (ok : ProtocolConditions hdr body)
    (r : Role) (path : List Frame) (vals : HList (RV M r) hdr.ins) (trace) :
    Returns (roleMeaning M (singletonProgram hdr ns body ok) Member.head r path vals) trace ↔
    Returns ((project r body).denote (roleSem M r (Defs.fnTable M .nil) (Defs.rTable M .nil))
      path (Env.empty.extend ns vals)) trace := Iff.rfl

abbrev Standard := (Zkc.Vocabulary.Project.Bindings.mk [] (by decide)).vocabulary
abbrev pointTy : Standard.Ty := .nominal (.inl (.group .g1))
abbrev scalarTy : Standard.Ty := .nominal (.inl (.field .bls12381Fr))
abbrev challengeLaw : Standard.LawKey := .uniform (.nominal (.field .bls12381Fr))

/-- Interpretation of the verifier's three pure standard rows at their actual signatures. -/
structure GroupRows (M : Model Standard) (ops : Operations (M.Val scalarTy) (M.Val pointTy))
    [DecidableEq (M.Val pointTy)] : Prop where
  scale : ∀ p k, M.apply (.inl (.group .scale (.group .g1))) _ rfl (.cons p (.cons k .nil)) =
    some (.cons (ops.scale p k) .nil)
  add : ∀ p q, M.apply (.inl (.group .add (.group .g1))) _ rfl (.cons p (.cons q .nil)) =
    some (.cons (ops.add p q) .nil)
  equal : ∀ (p q : M.Val pointTy), M.apply (.inl (.group .equal (.group .g1))) _ rfl (.cons p (.cons q .nil)) =
    some (.cons (decide (p = q)) .nil)

/-- These inputs have no request payload to compare. The description retains every field
of the Core operation, including its occurrence and reply type. -/
inductive InputPort (V : Vocabulary) where
  | get (kind : FlowKind) (giver : Role) (at_ : Occurrence) (ty : V.Ty)
  | own (kind : GivenKind V) (peers : List Role) (at_ : Occurrence) (ty : V.Ty)
  deriving DecidableEq

namespace InputPort

variable {V : Vocabulary} (M : Model V)

def operation : InputPort V → ROp M
  | .get kind who at_ ty => .get kind who at_ ty
  | .own kind peers at_ ty => .own kind peers at_ [] .nil ty

def ofOp : ROp M → Option (InputPort V)
  | .get kind who at_ ty => some (.get kind who at_ ty)
  | .own kind peers at_ [] .nil ty => some (.own kind peers at_ ty)
  | _ => none

theorem ofOp_operation (p : InputPort V) : ofOp M (operation M p) = some p := by cases p <;> rfl

theorem operation_ofOp {p : InputPort V} {op : ROp M} (h : ofOp M op = some p) :
    op = operation M p := by
  cases op with
  | get => cases h; rfl
  | own kind peers at_ ins payload ty =>
    cases payload with
    | nil => cases h; rfl
    | cons => cases h
  | give | hear | begin | settle => cases h

def input (p : InputPort V) (v : (RSig M).Reply (operation M p)) : Input (RSig M) :=
  ⟨operation M p, v, fun op =>
    if h : ofOp M op = some p then isTrue (operation_ofOp M h)
    else isFalse (fun e => h (e.symm ▸ ofOp_operation M p))⟩
end InputPort

/-- The complete returning record expected by a three-message fork, in source order. -/
def forkFields {V : Zkc.Core.Vocabulary} (history challenge response : V.Ty)
    (commitmentSite challengeSite responseSite : Key) : Fields V :=
  .cons (.key commitmentSite) (.val history) <|
    .cons (.key challengeSite) (.val challenge) <| .cons (.key responseSite) (.val response) .nil

def forkInputs (M : Model Standard) (history : Standard.Ty) (path : List Frame) (prover : Role)
    (commitmentSite challengeSite responseSite : Key)
    (a : M.Val history) (b : Branch (M.Val scalarTy)) : List (Input (RSig M)) :=
  [(InputPort.get .message prover ⟨path, commitmentSite⟩ history).input M a,
   (InputPort.own (.coin challengeLaw) [prover] ⟨path, challengeSite⟩ scalarTy).input M b.challenge,
   (InputPort.get .message prover ⟨path, responseSite⟩ scalarTy).input M b.suffix]

/-- Valid message values and a supported challenge suffice to realize this whole fork leaf. -/
theorem permitted_fork (M : Model Standard) (history : Standard.Ty) (path : List Frame) (prover : Role)
    (commitmentSite challengeSite responseSite : Key) (a : M.Val history) (b : Branch (M.Val scalarTy))
    (ha : M.Valid history a) (hc : Allows M (.coin challengeLaw) [] .nil scalarTy b.challenge)
    (hz : M.Valid scalarTy b.suffix) :
    ∀ e ∈ (forkInputs M history path prover commitmentSite challengeSite responseSite a b).map Input.entry,
      Permitted M e.1 e.2 := by
  intro e mem
  simp only [forkInputs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact ha
  · exact hc
  · exact hz

/-- All fields of each observed operation are retained, including peers, law, type and occurrence. -/
def forkTrace (M : Model Standard) (path : List Frame) (prover : Role)
    (commitmentSite challengeSite responseSite : Key)
    (a : M.Val pointTy) (b : Branch (M.Val scalarTy)) : List ((op : ROp M) × (RSig M).Reply op) :=
  [⟨.get .message prover ⟨path, commitmentSite⟩ pointTy, a⟩,
   ⟨.own (.coin challengeLaw) [prover] ⟨path, challengeSite⟩ [] .nil scalarTy, b.challenge⟩,
   ⟨.get .message prover ⟨path, responseSite⟩ scalarTy, b.suffix⟩]

end ZkcFormal.Written
