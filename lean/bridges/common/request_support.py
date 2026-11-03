"""Shared proof-request refusal diagnostics."""

class Obligation(ValueError):
    def __init__(self, code, detail):
        self.code, self.detail = code, detail
        super().__init__(detail)



def require(condition, code, detail):
    if not condition:
        raise Obligation(code, detail)


def check_lean_resources(result, detail):
    """Keep tool termination and resource exhaustion out of semantic refusals."""
    require(result.returncode >= 0, 'proof-interrupted',
            f'Lean terminated by signal {-result.returncode}: {detail}')
    diagnostic = (result.stdout or '') + (getattr(result, 'stderr', None) or '')
    markers = ('maximum number of heartbeats', 'deterministic timeout', '(deterministic) timeout',
               'recursion depth', 'out of memory', 'excessive memory consumption', 'maximum memory')
    require(result.returncode == 0 or not any(marker in diagnostic.lower() for marker in markers),
            'proof-budget', 'Lean exhausted a proof resource limit: ' + detail)
