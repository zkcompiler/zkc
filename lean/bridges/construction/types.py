"""Constructed payload interpretation of strict logical type trees.

Only the existing formal data vocabulary is interpreted. Logical handles are
recursively excluded; neutral decoding alone grants no codec or realization.
"""
from bridges.common.schema import interpreted_type
from bridges.structured.snapshot import interpreted_ty


def data_type(value):
    return interpreted_type(value, payload=True)


def render_type(value):
    """Render an already interpreted descriptor, never a wire-format fallback."""
    return interpreted_ty(value)
