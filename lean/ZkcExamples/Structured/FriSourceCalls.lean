module

public import ZkcExamples.Structured.FriSourceViews
public import ZkcTools.StructuredSource.SourceCalls
public meta import ZkcTools.StructuredSource.SourceCalls

@[expose] public section

/-! Each phase here has exactly one occurrence in its caller. Its checked
header supplies the label, arguments and role substitution. A missing or
ambiguous occurrence invalidates its selection during elaboration. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.FriSourceCalls
open Zkc.Source Zkc.Source.Structured FriSourceBodies

protocol_call lowDegree from runBody to protocol5Signature
protocol_call commitment from protocol5Body to protocol0Signature
protocol_call scalarQueries from protocol5Body to protocol1Signature
protocol_call binding from protocol5Body to protocol2Signature
protocol_call query from protocol5Body to protocol4Signature
protocol_call check from protocol4Body to protocol3Signature

end ZkcExamples.Structured.FriSourceCalls
