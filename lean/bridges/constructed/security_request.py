"""Explicit security experiments for checked constructed-program subjects.

Identifiers select reviewed interpretations and consumers. The native suite
remains part of the independently checked construction; selecting an ideal
model never certifies that suite's cryptographic implementation.
"""

from dataclasses import dataclass
import json
from pathlib import Path


VERSION = 'zkc.fs-verification-spec/0'
MODEL = 'ideal-indexed-transcript/0'


class Unresolved(ValueError):
    def __init__(self, code, detail):
        self.code = code
        self.detail = detail
        super().__init__(detail)


def require(condition, code, detail):
    if not condition:
        raise Unresolved(code, detail)


@dataclass(frozen=True)
class Experiment:
    contract: str
    property: str
    statement: str
    adversary: str
    observation: str
    query_budget: str
    premises: tuple[str, ...]


EXPERIMENTS = {
    'fs.schnorr.fixed-statement-cached-ro/0': Experiment(
        contract='schnorr.verifier/0',
        property='knowledge-extraction',
        statement='source, construction, application context, base and public key fixed before the prover',
        adversary='ordinary total oracle computation with private randomness and adaptive oracle queries',
        observation='acceptance and the named extractor witness relation',
        query_budget='Q bounds prover oracle calls; the theorem adds one final verification query',
        premises=(
            'one initially empty cached uniform-field oracle shared by prover and final verification',
            'finite field and compatible additive group/module interpretation',
            'the named adversary query bound; no efficiency conclusion follows from totality',
        ),
    ),
    'fs.sumcheck.full-prefix-cached-ro/0': Experiment(
        contract='sumcheck.quadratic-two-round/0',
        property='false-acceptance-bound',
        statement='public polynomial and claimed sum may be chosen adaptively within the fixed source and construction domain',
        adversary='ordinary total oracle computation with arbitrary full-prefix queries, including inconsistent and out-of-order prefixes',
        observation='false acceptance; early-stop and completed replay need not have equal final caches',
        query_budget='universally quantified adversary oracle-query bound, plus explicit reduction and verifier-completion accesses',
        premises=(
            'one initially empty cached uniform-field oracle shared by adversary and verification',
            'finite field and the named adversary and completion query bounds',
        ),
    ),
}


def validate(specification):
    """Check intent only; successful validation is never a proof receipt."""
    require(type(specification) is dict and set(specification) ==
            {'format', 'source', 'model', 'experiment', 'properties'},
            'fs-request-shape', 'Expected exactly format, source, model, experiment and properties')
    require(specification['format'] == VERSION,
            'fs-request-version', 'Unsupported FS verification specification version')
    require(specification['model'] == MODEL,
            'fs-model-unsupported',
            'Select the maintained ideal transcript interpretation; concrete provider security needs a separate proved adapter')
    identifier = specification['experiment']
    require(isinstance(identifier, str) and identifier in EXPERIMENTS,
            'fs-experiment-unsupported', 'No maintained consumer for this exact security experiment')
    experiment = EXPERIMENTS[identifier]
    require(specification['properties'] == [experiment.property],
            'fs-property-mismatch', 'The requested property does not match the selected experiment')
    source = specification['source']
    require(type(source) is dict and source.get('format') == 'zkc.proof-request/0',
            'fs-source-request', 'Supply the exact underlying common-source proof request')
    require(source.get('contract') == experiment.contract,
            'fs-contract-mismatch', 'The selected experiment requires another source contract')
    require(set(source) == {'format', 'contract', 'properties', 'experiment', 'role', 'inputs', 'wiring'},
            'fs-source-shape', 'Supply all and only the complete common-source proof-request fields')
    source_experiment, source_properties = SOURCE_PROPERTIES[experiment.contract]
    require(source['experiment'] == source_experiment and source['properties'] == source_properties,
            'fs-source-properties', 'The source request must select the reviewed complete contract properties')
    require(type(source['role']) is int and type(source['inputs']) is list and type(source['wiring']) is dict,
            'fs-source-selectors', 'Source role, input and effect selectors have invalid types')
    return experiment


SOURCE_PROPERTIES = {
    'schnorr.verifier/0': ('interactive.causal-transcripts/0',
                           ['perfect-completeness', 'special-soundness']),
    'sumcheck.quadratic-two-round/0': ('interactive.independent-uniform-field/0',
                                      ['perfect-completeness', 'interactive-soundness']),
}


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate-json-member', f'Duplicate JSON member: {key}')
        result[key] = value
    return result


def decode_json(raw, maximum=2_000_000):
    """Bound nesting before decoding, reject duplicate members and non-JSON floats."""
    require(len(raw) <= maximum, 'json-size', 'JSON exceeds the bounded input profile')
    if isinstance(raw, bytes):
        raw = raw.decode('utf-8')
    depth, quoted, escaped = 0, False, False
    for char in raw:
        if quoted:
            if escaped:
                escaped = False
            elif char == chr(92):
                escaped = True
            elif char == '"':
                quoted = False
        elif char == '"':
            quoted = True
        elif char in '[{':
            depth += 1
            require(depth <= 128, 'json-depth', 'JSON nesting exceeds the bounded input profile')
        elif char in ']}':
            depth -= 1
    def reject_constant(value):
        raise Unresolved('json-number', f'Non-JSON numeric constant: {value}')
    return json.loads(raw, object_pairs_hook=unique_object, parse_constant=reject_constant)


def read_json(path, maximum=2_000_000):
    with Path(path).open('rb') as stream:
        return decode_json(stream.read(maximum + 1), maximum)
