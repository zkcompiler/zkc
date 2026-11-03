module

public import Zkc.Source.Structured.SourceDeclarations

@[expose] public section

/-! Admission computations must reduce through the public module interface.
Runtime evaluation alone cannot detect an opaque imported helper. -/
namespace StructuredDeclarationReductionTests
open Zkc.Source.Structured

def ticket : OriginTerm := .nominal .record "probe::Ticket" []

def declarations : SourceDeclarations := {
  records := [⟨ticket, "linear", false, .fields [⟨"value", .index, none⟩], [],
    some "zkl_resource_ticket"⟩]
  protocols := [⟨"entry", [⟨"input", ticket, ["P"], 0, 2, .data ["P"]⟩], []⟩]
  authorities := [("probe::Ticket", some "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")]
}

example : declarations.checkShape = .ok () := by decide +kernel
example : SourceDeclarations.slotValid "zkl_resource_ticket" = true := by decide +kernel
example : SourceDeclarations.slotValid "zkl_resources_ticket" = false := by decide +kernel
example : SourceDeclarations.slotValid "zkl_resource_한" = false := by decide +kernel
example : SourceDeclarations.authorityOrder ["a", "b", "한"] = true := by decide +kernel

end StructuredDeclarationReductionTests
