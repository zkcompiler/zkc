"""Maintained semantic contracts and independent property consumers.

Registry entries are reviewed code. A request selects entries; it never provides
Lean source, tactics, imports or theorem names. No source hashes occur here.
"""
from dataclasses import dataclass


@dataclass(frozen=True)
class Property:
    theorem: str
    experiment: str
    premises: tuple[str, ...]
    module: str | None = None
    context: str = ''
    consumer: str | None = None


@dataclass(frozen=True)
class Contract:
    namespace: str
    module: str
    binders: str
    arguments: str
    inputs: dict[str, tuple[str, str]]
    unfold: tuple[str, ...]
    properties: dict[str, Property]
    group: bool = False
    composed: bool = False


UNIFORM = 'interactive.independent-uniform-field/0'
CAUSAL = 'interactive.causal-transcripts/0'
ROUND = 'Zkc.Protocols.Sumcheck.Common'
FACTOR = 'Zkc.Protocols.Sumcheck.FactorOpening'
SCHNORR = 'Zkc.Protocols.Schnorr.Common'

# Premises describe the theorem, not facts established about native execution.
SUM_PROPERTIES = {
    'perfect-completeness': Property('perfect_completeness', UNIFORM,
        ('honest abstract strategy', 'two independent uniform full-field coins')),
    'interactive-soundness': Property('soundness', UNIFORM,
        ('false public sum claim', 'arbitrary fixed causal strategy',
         'two independent uniform full-field coins')),
}

ARKLIB_SOUNDNESS = Property('randomized_soundness', 'interactive.reached-uniform-queries/0',
    ('false public sum claim', 'arbitrary private distribution of causal two-round strategies',
     'fresh uniform full-field sampling at reached challenge queries', 'finite field'),
    'ZkcSecurity.ArkLib.Sumcheck.Soundness', '[Fintype F] [SampleableType F] ',
    'ZkcSecurity.ArkLib.Sumcheck.randomized_soundness')

SCHNORR_SIMULATION = Property('honest_verifier_zero_knowledge', 'interactive.honest-verifier-view/0',
    ('public key = secret scalar times base', 'uniform prover nonce and simulator response',
     'honest challenge fixed independently of nonce', 'public one-session transcript and verifier outcome'),
    'ZkcSecurity.VCVio.Schnorr', '[SampleableType F] ',
    'ZkcSecurity.VCVio.Schnorr.honest_verifier_zero_knowledge')

CONTRACTS = {
    'schnorr.verifier/0': Contract(SCHNORR, SCHNORR, '(base key : G) (service : Nat)',
        'base key service', {'base': ('base', 'group'), 'key': ('key', 'group'),
        'service': ('service', 'service')}, ('experiment',), {
            'perfect-completeness': Property('perfect_completeness', CAUSAL,
                ('honest abstract response and commitment', 'public key = secret scalar times base')),
            'special-soundness': Property('special_soundness', CAUSAL,
                ('same commitment', 'two distinct challenges', 'both transcripts accept')),
            'honest-verifier-zero-knowledge': SCHNORR_SIMULATION,
        }, group=True),
    'sumcheck.quadratic-two-round/0': Contract(ROUND, ROUND,
        '(coefficients : Coefficients F) (claim : F) (service : Nat)',
        'coefficients claim service', {
            **{f'{row}.{col}': (f'coefficients.{row}.{col}', 'field')
               for row in ('constant', 'linear', 'quadratic')
               for col in ('constant', 'linear', 'quadratic')},
            'claim': ('claim', 'field'), 'service': ('service', 'service')},
        ('experiment', 'experimentWith', 'standardArithmetic', 'wireBoundary', 'wireEvaluate', 'evaluate'),
        {**SUM_PROPERTIES, 'arklib-interactive-soundness': ARKLIB_SOUNDNESS}),
    'sumcheck.public-factor-openings/0': Contract(FACTOR, FACTOR + '.Security',
        '(statement : Statement F) (claim : F) (service : Nat)', 'statement claim service', {
            **{f'{side}.{part}': (f'statement.{side}.{part}', 'field')
               for side in ('left', 'right') for part in ('constant', 'second', 'first', 'mixed')},
            'claim': ('claim', 'field'), 'service': ('service', 'service')},
        ('experiment', 'experimentWith', 'terminal', 'publicChecks', 'value',
         ROUND + '.rounds', ROUND + '.roundsWith', ROUND + '.standardArithmetic',
         ROUND + '.wireBoundary', ROUND + '.wireEvaluate'), SUM_PROPERTIES, composed=True),
}
