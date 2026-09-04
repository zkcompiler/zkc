"""Clean-room finite probe for the R2 FRI/grinding design witness."""


def build_report(*args, **kwargs):
    from .report import build_report as assemble

    return assemble(*args, **kwargs)


__all__ = ["build_report"]
