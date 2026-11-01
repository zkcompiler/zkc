module

public import ZkcExamples.Structured.Generated.Presentations.Gkr
public import ZkcTools.StructuredSource.SourceCalls
public meta import ZkcTools.StructuredSource.SourceCalls

@[expose] public section

/-! The terminal application header comes from its unique retained occurrence.
The selector checks the complete callee signature; names carry no authority. -/
namespace ZkcSecurity.Realizations.Gkr.SourceCalls
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured

set_option maxRecDepth 50000 in
protocol_call inputCall from Generated.Presentations.Gkr.Root.gkrBody
  to GkrSourceBodies.sourceProtocol80Signature

end ZkcSecurity.Realizations.Gkr.SourceCalls
