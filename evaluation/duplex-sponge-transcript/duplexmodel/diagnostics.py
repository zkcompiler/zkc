"""Typed failures for the finite evaluation instrument."""

from __future__ import annotations


class DuplexModelError(Exception):
    """Base class for expected finite-model failures."""


class MalformedInput(DuplexModelError):
    """A serialized or typed input has the wrong exact shape."""


class AdmissionRefusal(DuplexModelError):
    """A well-decoded construction does not satisfy formation laws."""


class SourceApplicabilityRefusal(DuplexModelError):
    """A structural construction fails this finite source-profile check."""


class CorrespondenceMismatch(DuplexModelError):
    """A construction or execution differs from the selected source shape."""


class ProvenanceError(DuplexModelError):
    """A replay root, source basis, or fixture binding is invalid."""


class ReplayContextMismatch(DuplexModelError):
    """Parsed proof context differs from the requested construction or Protocol."""


class InstanceBoundExceeded(DuplexModelError):
    """The projected runtime instance exceeds its construction bound."""


class DeterministicLimitExceeded(DuplexModelError):
    """A declared deterministic validation limit was exhausted."""
