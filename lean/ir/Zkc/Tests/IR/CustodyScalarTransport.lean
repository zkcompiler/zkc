module

public import Zkc.IR.Construction.ScalarAdapter
public import Zkc.IR.Executable.Helpers

@[expose] public section

/-! Exact-slot local transport is independent of wire payload eligibility. -/
set_option autoImplicit false
namespace Tests.CustodyScalarTransport
open Zkc.Source Zkc.Construction
variable {F G : Type}

example (slot : String) (token : Structured.CustodyToken) :
    Value.decode (.resourceUnit slot)
      (Value.encode (.resourceUnit slot) token : Value F G) = some token :=
  Value.decode_encode_local (ty := .resourceUnit slot) (by rfl) token

example {expected actual : String} (different : expected ≠ actual)
    (token : Structured.CustodyToken) :
    Value.decode (.resourceUnit expected) (.custody actual token : Value F G) = none :=
  Value.custody_wrong_slot different token

example (slot : String) (token : Structured.CustodyToken) :
    Value.decode .index (.custody slot token : Value F G) = none := rfl

example (slot : String) (token : Structured.CustodyToken) :
    Value.decode (.resourceUnit slot) (.index token : Value F G) = none := rfl

example (slot : String) : dataType (.resourceUnit slot) = false := rfl
example (slot : String) : localType (.resourceUnit slot) = true := rfl

example (slot : String) (token : Structured.CustodyToken) :
    dataAt [(.custody slot token : Value F G)] 0 = none := rfl

example (slot : String) (token : Structured.CustodyToken) :
    Uniform.DomainAdapter.embedData (.custody slot token : Value F G) =
      some (.custody slot token) := rfl

example (slot : String) (token : Structured.CustodyToken) :
    Uniform.DomainAdapter.readbackData
      (.custody slot token : Domain.Value (Structured.uniformCarriers F G)) =
      some (.custody slot token) := rfl

example (slot : String) (token : Structured.CustodyToken) :
    (Domain.Value.custody slot token (carriers := Structured.uniformCarriers F G)).sort =
      .data (.resourceUnit slot) := rfl

/-! Local construction and executable recipes cannot turn custody into wire data. -/
example (slot : String) : isLocalValue (some (.data (.resourceUnit slot))) = true := rfl
example (slot : String) : isData (some (.data (.resourceUnit slot))) = false := rfl

example (slot : String) :
    Zkc.Executable.CustodyTransfer.erased (F := F) (G := G) .create slot [] =
      .returned [.custody slot 0] := rfl

example (slot : String) (token : Structured.CustodyToken) :
    Zkc.Executable.CustodyTransfer.erased (F := F) (G := G) .pass slot [.custody slot token] =
      .returned [.custody slot 0] := by simp [Zkc.Executable.CustodyTransfer.erased]

example (slot : String) (token : Structured.CustodyToken) :
    Zkc.Executable.CustodyTransfer.erased (F := F) (G := G) .consume slot [.custody slot token] =
      .returned [] := by simp [Zkc.Executable.CustodyTransfer.erased]

example (slot : String) (token : Structured.CustodyToken) :
    Zkc.Executable.CustodyTransfer.erased (F := F) (G := G) .create slot [.custody slot token] =
      .stopped .refused := by simp [Zkc.Executable.CustodyTransfer.erased]

example {expected actual : String} (different : expected ≠ actual)
    (token : Structured.CustodyToken) :
    Zkc.Executable.CustodyTransfer.erased (F := F) (G := G) .consume expected [.custody actual token] =
      .stopped .refused := by simp [Zkc.Executable.CustodyTransfer.erased, different]

example (slot : String) :
    Zkc.Executable.implements (.consumeUnit slot) (.custody .consume slot) = true := by
  simp [Zkc.Executable.implements]

example : Zkc.Executable.implements (.consumeUnit "a") (.custody .consume "b") = false := rfl
example : Zkc.Executable.implements (.consumeUnit "a") (.custody .pass "a") = false := rfl

end Tests.CustodyScalarTransport
