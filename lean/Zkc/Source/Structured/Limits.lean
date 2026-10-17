module

@[expose] public section

/-! Admission limits of the structured import. The native
[format](../../../../docs/spec/formats/structured-source.md) states the same
limits; the exporter and this independent reader both refuse a unit that
exceeds one of them. -/

namespace Zkc.Source.Structured.Limits

/-- Entries in each top-level table: domains, relations, bindings, definitions
and protocol contracts. -/
abbrev tableEntries : Nat := 128

/-- Bytes of a native preparation identifier. -/
abbrev preparationNameBytes : Nat := 128

/-- Origin key/value pairs of one Local helper. -/
abbrev originBindings : Nat := 128

/-- Types in one signature list and operand references of one instruction. -/
abbrev listEntries : Nat := 512

/-- Stored instructions of one unit; also the largest operand reference. -/
abbrev instructions : Nat := 4096

/-- Bytes of one rendered effective protocol site label. -/
abbrev siteBytes : Nat := 4096

/-- Depth of stored blocks, helper and protocol references, applications and
repeats. -/
abbrev nesting : Nat := 64

/-- Visits of the application-metadata traversal over all roots. -/
abbrev applicationVisits : Nat := 100000

/-- Operand indices and selectors charged by application metadata. -/
abbrev applicationIndices : Nat := 1000000

/-- Cumulative rendered site-label bytes, and the byte size of an export. -/
abbrev applicationSiteBytes : Nat := 16777216

end Zkc.Source.Structured.Limits
