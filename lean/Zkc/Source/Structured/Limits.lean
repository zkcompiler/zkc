module

@[expose] public section

/-! Admission limits of the structured import. The native
[format](../../../../docs/spec/formats/structured-source.md) and the
[composition rules](../../../../docs/spec/ir/composition.md) state the
corresponding limits; this reader refuses a unit that exceeds one of them.
The reader's byte bound on parsed text is looser than the format's bound on a
complete export. Contract and repeat admission state their own bounds. -/

namespace Zkc.Source.Structured.Limits

/-- Entries in each top-level table of a decoded snapshot: domains, relations,
bindings and definitions, and the decoded protocol-contract list. -/
abbrev tableEntries : Nat := 128

/-- Bytes of a native preparation identifier. -/
abbrev preparationNameBytes : Nat := 128

/-- Origin key/value pairs of one Local helper. -/
abbrev originBindings : Nat := 128

/-- Types in one signature list and operand references of one instruction. -/
abbrev listEntries : Nat := 512

/-- Stored instructions of one unit; also the largest operand reference and
the default bound of every decoded natural number. -/
abbrev instructions : Nat := 4096

/-- Bytes of one rendered effective protocol site label. -/
abbrev siteBytes : Nat := 4096

/-- Depth of stored blocks, helper and protocol references, applications and
repeats, and of JSON brackets in parsed text. -/
abbrev nesting : Nat := 64

/-- Visits of the application-metadata traversal over all roots. -/
abbrev applicationVisits : Nat := 100000

/-- Operand indices and selectors charged by application metadata, as bounded
by the composition rules. -/
abbrev applicationIndices : Nat := 1000000

/-- Cumulative rendered site-label bytes charged by application metadata. -/
abbrev applicationSiteBytes : Nat := 16777216

/-- Bytes of JSON text this reader parses before decoding (16 MiB). The
writer bounds a complete exported file to 1 MiB; this reader accepts more. -/
abbrev parsedBytes : Nat := 16777216

end Zkc.Source.Structured.Limits
