"""Keep the tiny two-call test entry associated with its complete native export."""

import copy

from bridges.structured import snapshot


def render(single, double):
    # The native checker re-emits the whole unit. Share the unchanged declarations
    # in Lean only after checking every column, including order and source metadata.
    entry = double[3]
    definitions = [i for i, row in enumerate(single[7]) if row[1] == entry]
    protocols = [i for i, row in enumerate(single[10][1]) if row[0] == entry]
    if len(definitions) != 1 or len(protocols) != 1:
        raise ValueError("expected one retained entry and its source declaration")
    definition, protocol = definitions[0], protocols[0]
    expected = copy.deepcopy(single)
    expected[2] = double[2]
    expected[7][definition] = double[7][definition]
    expected[10][1][protocol] = double[10][1][protocol]
    if expected != double:
        raise ValueError("the two-call fixture changed a shared declaration or its ordering")
    return f'''module

public import ZkcExamples.Structured.FriSourceData

@[expose] public section

/-! Complete native export of the two-call test root. The native regression
checks all shared declarations byte-for-byte as structured data. -/
namespace Tests.FriBindingSitesData
open Zkc.Source.Structured
abbrev single := ZkcExamples.Structured.FriSourceData.snapshot

def entry : Definition :=
  {snapshot.definition(double[7][definition])}

def ports : SourceProtocol :=
  {snapshot.source_protocol(double[10][1][protocol])}

def snapshot : Snapshot := {{single with
  source := {snapshot.text(double[2])}
  definitions := single.definitions.set {definition} entry
  sourceDeclarations := {{single.sourceDeclarations with
    protocols := single.sourceDeclarations.protocols.set {protocol} ports}}}}

end Tests.FriBindingSitesData
'''
