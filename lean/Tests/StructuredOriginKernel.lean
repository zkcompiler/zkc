module

public import Zkc.Source.Structured.Origin

@[expose] public section

/-! Source identities must reduce in certificate checks, including nested
record parameters. Native evaluation alone cannot test this requirement. -/
namespace Tests.StructuredOriginKernel
open Zkc.Source.Structured

def pending (size : String) : OriginTerm :=
  .nominal .record "example::Pending"
    [.field "koala-bear", .array (.tuple [.index, .builtin "vector" [.field "koala-bear"]]) size]

theorem reflexive : (pending "4" == pending "4") = true := by decide +kernel
theorem differentParameter : (pending "4" == pending "8") = false := by decide +kernel
theorem differentKind :
    ((.natural "4" : OriginTerm) == .field "4") = false := by decide +kernel
theorem deduplicated : [pending "4", pending "8", pending "4"].eraseDups =
    [pending "4", pending "8"] := by decide +kernel

#print axioms reflexive
#print axioms differentParameter
#print axioms deduplicated

end Tests.StructuredOriginKernel
