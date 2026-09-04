"""Clean-room finite primitives for the native FRI/IOR validation package."""

from .commitment import (
    CommitmentTree,
    MerkleCap,
    PairOpening,
    build_commitment,
    verify_pair_opening,
)
from .field import (
    Fp,
    Fp2,
    POLYNOMIAL_COEFFICIENT_FIELD_OPERATIONS,
    binary_fold,
    canonical_polynomial,
    evaluate_polynomial,
    polynomial_degree,
)
from .profile import (
    D0,
    D1,
    D2,
    DEFAULT_VALIDATION_LIMITS,
    EXACT_PROFILE,
    EvaluationDomain,
    FriIorProfile,
)
from .terms import (
    CheckResult,
    ModelFailure,
    OutcomeClass,
    ResourceCounter,
    ResourceLimits,
    SEMANTIC_REGIME_ID,
    SemanticId,
    check_semantic_id,
)

__all__ = [
    "CheckResult",
    "CommitmentTree",
    "D0",
    "D1",
    "D2",
    "DEFAULT_VALIDATION_LIMITS",
    "EXACT_PROFILE",
    "EvaluationDomain",
    "Fp",
    "Fp2",
    "FriIorProfile",
    "MerkleCap",
    "ModelFailure",
    "OutcomeClass",
    "PairOpening",
    "POLYNOMIAL_COEFFICIENT_FIELD_OPERATIONS",
    "ResourceCounter",
    "ResourceLimits",
    "SEMANTIC_REGIME_ID",
    "SemanticId",
    "binary_fold",
    "build_commitment",
    "canonical_polynomial",
    "check_semantic_id",
    "evaluate_polynomial",
    "polynomial_degree",
    "verify_pair_opening",
]
