"""Shared proof-request refusal diagnostics."""

class Obligation(ValueError):
    def __init__(self, code, detail):
        self.code, self.detail = code, detail
        super().__init__(detail)



def require(condition, code, detail):
    if not condition:
        raise Obligation(code, detail)
