"""Closed, static diagnostic contract for the native FRI/IOR package.

The contract inventories diagnostic identifiers at their production emission
sites and separately records literal mentions in tests.  A test mention is not
execution evidence.  Even the ``direct-public-surface`` classification below
is an authored statement about the intended way to exercise a diagnostic, not
a claim that the current suite has reached it.

Every current identifier is explicitly classified.  Source discovery is
dynamic, so a new production module participates automatically, while a new
identifier fails closed until this table is reviewed.  Multiple literal sites
may share an identifier only when their statically recoverable owner, boundary,
and outcome agree.
"""

from __future__ import annotations

import ast
from collections import Counter
from dataclasses import dataclass
from enum import Enum
import hashlib
from itertools import product
import json
from pathlib import Path
import re
from types import MappingProxyType
from typing import Any, Iterable, Mapping

from .terms import (
    CheckResult,
    OutcomeClass,
    affirmative,
    checker_failure,
)
from .provenance import ValidationBasisId, validation_basis_id


_PACKAGE_ROOT = Path(__file__).resolve().parents[1]
_CODE_PATTERN = re.compile(
    r"^FRI-IOR-([A-Z0-9]+(?:-[A-Z0-9]+)*)-([0-9]{3})$"
)
_REPORT_TOKEN = object()

# The positional index of the diagnostic ``code`` argument.  ``None`` denotes
# a keyword-only parameter.  The scanner prefers an explicit ``code=`` keyword
# at every call site, so this table also admits callers that spell an ordinary
# positional parameter by keyword.
_BASE_CODE_POSITIONS: Mapping[str, int | None] = MappingProxyType(
    {
        "CheckResult": 2,
        "ModelFailure": 2,
        "_ContractViolation": 0,
        "_ReplayFailure": 2,
        "_outcome": 2,
        "affirmative": 1,
        "deterministic_limit_failure": 1,
        "kind_mismatch": 1,
        "malformed": 1,
        "missing_dependency": 1,
        "refusal": 1,
        "refused": 1,
        "unsupported": 1,
        "unsupported_failure": 1,
    }
)

# These calls copy an already formed diagnostic identifier from a typed
# failure carrier into its public result.  They are transports, not identifier
# origins.  Keeping the list exact prevents arbitrary ``object.code`` values
# from becoming an escape hatch in the static inventory.
_CODE_TRANSPORTS = frozenset(
    {
        (
            "friiormodel.constructions",
            "_expected_compilation_maps",
            "ModelFailure",
            "resolved",
        ),
        (
            "friiormodel.constructions",
            "check_committed_to_work_fresh",
            "CheckResult",
            "target_result",
        ),
        (
            "friiormodel.constructions",
            "verify_work_augmented_fresh_run",
            "CheckResult",
            "target_result",
        ),
        ("friiormodel.diagnostics", "_contract_failure", "CheckResult", "error"),
        ("friiormodel.terms", "to_result", "CheckResult", "self"),
        ("independent", "verify_public_fri", "_outcome", "error"),
        (
            "classical_independent",
            "verify_public_classical_fri",
            "_outcome",
            "error",
        ),
    }
)


class EvidenceClass(str, Enum):
    """Authored route by which a diagnostic may receive test evidence."""

    DIRECT_PUBLIC_SURFACE = "direct-public-surface"
    FORMATION = "formation"
    FAULT_INJECTION_DEFENSIVE = "fault-injection/defensive"
    RACE_ONLY = "race-only"
    INTENTIONALLY_UNREACHABLE = "intentionally-unreachable"


@dataclass(frozen=True, slots=True)
class DiagnosticClassification:
    """One explicit evidence class and its interpretation."""

    evidence_class: EvidenceClass
    reason: str

    def __post_init__(self) -> None:
        if not isinstance(self.evidence_class, EvidenceClass):
            raise TypeError("diagnostic evidence class must be typed")
        if not isinstance(self.reason, str):
            raise TypeError("diagnostic classification reason must be text")
        if self.evidence_class is not EvidenceClass.DIRECT_PUBLIC_SURFACE and not (
            self.reason.strip()
        ):
            raise ValueError("every non-direct classification requires a reason")

    def to_term(self) -> dict[str, str]:
        return {
            "evidence_class": self.evidence_class.value,
            "reason": self.reason,
        }


@dataclass(frozen=True, slots=True)
class DiagnosticSite:
    """One statically identified production emission site."""

    module: str
    function: str
    line: int
    boundary: str | None
    outcome: str | None

    def to_term(self) -> dict[str, Any]:
        return {
            "module": self.module,
            "function": self.function,
            "line": self.line,
            "boundary": self.boundary,
            "outcome": self.outcome,
        }


@dataclass(frozen=True, slots=True)
class StaticTestMention:
    """One literal test-source mention, never an execution observation."""

    module: str
    test_function: str
    line: int
    assertion_context: bool

    def to_term(self) -> dict[str, Any]:
        return {
            "module": self.module,
            "test_function": self.test_function,
            "line": self.line,
            "assertion_context": self.assertion_context,
            "establishes_reachability": False,
        }


@dataclass(frozen=True, slots=True)
class DiagnosticCoverageEntry:
    """Static ownership and classification for one exact identifier."""

    code: str
    owner_module: str
    boundaries: tuple[str, ...]
    outcomes: tuple[str, ...]
    sites: tuple[DiagnosticSite, ...]
    classification: DiagnosticClassification
    test_mentions: tuple[StaticTestMention, ...]

    def to_term(self) -> dict[str, Any]:
        return {
            "code": self.code,
            "owner_module": self.owner_module,
            "boundaries": list(self.boundaries),
            "boundary_recovery": (
                "static-exact" if self.boundaries else "runtime-supplied"
            ),
            "outcomes": list(self.outcomes),
            "outcome_recovery": "static-exact",
            "sites": [site.to_term() for site in self.sites],
            "test_evidence_classification": self.classification.to_term(),
            "static_test_mentions": [
                mention.to_term() for mention in self.test_mentions
            ],
            "static_test_mention_count": len(self.test_mentions),
            "static_assertion_mention_count": sum(
                mention.assertion_context for mention in self.test_mentions
            ),
            "reachability_status": "not-established-by-static-inventory",
        }


@dataclass(frozen=True, slots=True, init=False)
class CheckedDiagnosticCoverageReport:
    """A report issued only after closure and consistency checks pass."""

    production_sources: tuple[tuple[str, str], ...]
    test_sources: tuple[tuple[str, str], ...]
    entries: tuple[DiagnosticCoverageEntry, ...]

    def __init__(
        self,
        production_sources: tuple[tuple[str, str], ...],
        test_sources: tuple[tuple[str, str], ...],
        entries: tuple[DiagnosticCoverageEntry, ...],
        *,
        _token: object,
    ) -> None:
        if _token is not _REPORT_TOKEN:
            raise TypeError("checked diagnostic reports require the contract checker")
        object.__setattr__(self, "production_sources", production_sources)
        object.__setattr__(self, "test_sources", test_sources)
        object.__setattr__(self, "entries", entries)

    @property
    def by_code(self) -> Mapping[str, DiagnosticCoverageEntry]:
        return MappingProxyType({entry.code: entry for entry in self.entries})

    def to_term(self) -> dict[str, Any]:
        counts = Counter(
            entry.classification.evidence_class.value for entry in self.entries
        )
        return {
            "schema": "zkc.native-fri-ior.diagnostic-coverage.v1",
            "production_sources": [
                {"path": path, "sha256": digest}
                for path, digest in self.production_sources
            ],
            "test_sources": [
                {"path": path, "sha256": digest} for path, digest in self.test_sources
            ],
            "diagnostic_count": len(self.entries),
            "classification_counts": {
                classification.value: counts[classification.value]
                for classification in EvidenceClass
            },
            "entries": [entry.to_term() for entry in self.entries],
            "coverage_semantics": (
                "closed static inventory and authored evidence classification; "
                "literal test mentions and assertion syntax do not establish "
                "execution or reachability"
            ),
        }

    @property
    def validation_basis_id(self) -> ValidationBasisId:
        """Compact evidence identity for the full non-semantic inventory."""

        encoded = json.dumps(
            self.to_term(),
            ensure_ascii=True,
            allow_nan=False,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("ascii")
        return validation_basis_id(
            "diagnostic-inventory",
            {
                "schema": "zkc.native-fri-ior.diagnostic-inventory-binding.v1",
                "full_report_sha256": hashlib.sha256(encoded).hexdigest(),
                "full_report_byte_length": len(encoded),
                "diagnostic_count": len(self.entries),
                "production_source_count": len(self.production_sources),
                "test_source_count": len(self.test_sources),
                "authority": "validation-evidence-not-semantic-identity",
            },
        )


@dataclass(frozen=True, slots=True)
class DiagnosticContractAdmission:
    """Typed contract result, carrying a report only on affirmation."""

    result: CheckResult
    report: CheckedDiagnosticCoverageReport | None

    def __post_init__(self) -> None:
        if not isinstance(self.result, CheckResult):
            raise TypeError("diagnostic admission requires a CheckResult")
        if self.result.outcome is OutcomeClass.AFFIRMATIVE:
            if not isinstance(self.report, CheckedDiagnosticCoverageReport):
                raise TypeError("affirmative diagnostic admission requires a report")
        elif self.report is not None:
            raise TypeError("failed diagnostic admission cannot carry a report")

    def to_term(self) -> dict[str, Any]:
        return {
            "result": self.result.to_term(),
            "report": None if self.report is None else self.report.to_term(),
        }


class _ContractViolation(Exception):
    def __init__(self, code: str, detail: str, **evidence: Any) -> None:
        super().__init__(detail)
        self.code = code
        self.detail = detail
        self.evidence = evidence


def _numbers(family: str, values: Iterable[int]) -> frozenset[str]:
    return frozenset(f"FRI-IOR-{family}-{value:03d}" for value in values)


def _span(family: str, first: int, last: int) -> frozenset[str]:
    return _numbers(family, range(first, last + 1))


# This is an exact reviewed snapshot, not a family wildcard.  A newly added
# identifier remains absent even if it uses an existing namespace.
_CURRENT_CODES = frozenset().union(
    _span("ANALYSIS", 1, 36),
    _span("ANALYSIS", 100, 102),
    _numbers("CHECKER", (1,)),
    _span("COMMITMENT", 1, 32),
    _numbers("COMMITMENT", (100,)),
    _span("COMMITTED", 1, 4),
    _span("COMMITTED", 5, 9),
    _span("COMMITTED", 10, 15),
    _span("COMMITTED", 20, 23),
    _span("COMMITTED", 100, 102),
    _span("CONSTRUCTION", 1, 4),
    _span("CONSTRUCTION", 11, 59),
    _span("CONSTRUCTION", 100, 104),
    _span("FIELD", 1, 18),
    _span("FIXTURE", 1, 6),
    _span("FIXTURE", 10, 34),
    _span("GENERATION", 1, 40),
    _numbers("GENERATION", (100,)),
    _span("IDENTITY", 1, 11),
    _numbers("IDENTITY", (100,)),
    _span("INDEPENDENT", 1, 26),
    _span("INDEPENDENT", 30, 35),
    _span("INDEPENDENT", 40, 42),
    _span("INDEPENDENT", 50, 52),
    _span("INDEPENDENT", 90, 93),
    _numbers("INDEPENDENT", (99, 100)),
    _span("NATIVE", 1, 24),
    _span("NATIVE", 26, 39),
    _span("NATIVE", 41, 55),
    _numbers("NATIVE", (100,)),
    _span("PROFILE", 1, 13),
    _span("PROFILE", 15, 27),
    _span("PROFILE", 29, 33),
    _span("PROFILE", 37, 42),
    _numbers("PROFILE", (100,)),
    _span("PROOF", 1, 11),
    _span("PROVENANCE", 1, 65),
    _numbers("PROVENANCE", (100,)),
    _span("RELATION", 1, 29),
    _span("RELATION", 40, 51),
    _span("RELATION", 54, 58),
    _span("RELATION", 60, 76),
    _span("RELATION", 78, 82),
    _span("RELATION", 100, 102),
    _span("RESOURCE", 1, 10),
    _span("SUBJECT", 1, 36),
    _numbers("SUBJECT", (100, 101)),
    _span("TERM", 1, 5),
    _numbers("TRANSCRIPT", (1, 2)),
    _span("TRANSCRIPT", 10, 28),
    _span("TRANSCRIPT", 30, 47),
    _numbers("TRANSCRIPT", (48,)),
    _numbers("TRANSCRIPT", (100,)),
    _span("DIAGNOSTIC", 1, 7),
    _numbers("DIAGNOSTIC", (10, 12, 13, 14, 15, 16, 17, 18)),
    _numbers("DIAGNOSTIC", (100,)),
    _span("CLASSICAL-ANALYSIS", 1, 24),
    _numbers("CLASSICAL-ANALYSIS", (100, 101)),
    _span("CLASSICAL-CASE", 1, 5),
    _span("CLASSICAL-COMMITMENT", 1, 20),
    _span("CLASSICAL-COMMITTED", 1, 10),
    _span("CLASSICAL-COMMITTED", 21, 23),
    _numbers("CLASSICAL-COMMITTED", (100,)),
    _span("CLASSICAL-CONSTRUCTION", 1, 65),
    _numbers("CLASSICAL-CONSTRUCTION", (100, 101)),
    _span("CLASSICAL-CORE", 1, 6),
    _span("CLASSICAL-FIELD", 1, 9),
    _span("CLASSICAL-FORMATION", 1, 8),
    _span("CLASSICAL-FS", 1, 9),
    _numbers("CLASSICAL-FS", (11, 12, 13, 14)),
    _span("CLASSICAL-GENERATION", 1, 7),
    _span("CLASSICAL-INDEPENDENT", 1, 21),
    _span("CLASSICAL-INDEPENDENT", 30, 33),
    _numbers("CLASSICAL-INDEPENDENT", (40, 41, 50, 51, 52, 53)),
    _span("CLASSICAL-INDEPENDENT", 90, 92),
    _numbers("CLASSICAL-INDEPENDENT", (99, 100)),
    _span("CLASSICAL-NATIVE", 1, 9),
    _span("CLASSICAL-NATIVE", 20, 22),
    _numbers("CLASSICAL-NATIVE", (100,)),
    _span("CLASSICAL-ORACLE", 1, 4),
    _span("CLASSICAL-PROFILE", 1, 11),
    _span("CLASSICAL-PROOF", 1, 8),
    _span("CLASSICAL-PUBLIC", 1, 9),
    _span("CLASSICAL-QUERY", 1, 5),
    _span("CLASSICAL-RELATION", 1, 28),
    _numbers("CLASSICAL-RELATION", (100, 101, 102)),
    _numbers("CLASSICAL-RESOURCE", (1,)),
    _span("CLASSICAL-RUN", 1, 6),
    _span("CLASSICAL-SCHEDULE", 1, 3),
)


_FORMATION_CODES = frozenset().union(
    _span("ANALYSIS", 1, 36),
    _span("COMMITMENT", 1, 10),
    _numbers("COMMITMENT", (12, 13, 14, 15, 16, 17, 18)),
    _span("COMMITMENT", 26, 32),
    _span("COMMITTED", 1, 4),
    _numbers("CONSTRUCTION", (1, 2, 3, 13, 29, 34, 43, 53, 55, 56, 57)),
    _span("FIXTURE", 1, 4),
    _span("FIXTURE", 10, 34),
    _numbers("FIELD", (1, 3, 7, 8)),
    _span("FIELD", 13, 17),
    _span("GENERATION", 1, 16),
    _numbers("GENERATION", (39,)),
    _span("INDEPENDENT", 1, 24),
    _numbers("INDEPENDENT", (91, 92)),
    _span("NATIVE", 1, 24),
    _numbers("NATIVE", (26, 27, 28, 53)),
    _span("PROFILE", 1, 13),
    _numbers("PROFILE", (15, 16)),
    _span("PROFILE", 19, 27),
    _span("PROFILE", 29, 33),
    _span("PROFILE", 37, 42),
    _span("PROOF", 1, 11),
    _span("PROVENANCE", 1, 53),
    _span("RELATION", 1, 19),
    _span("RELATION", 40, 46),
    _span("RELATION", 60, 66),
    _numbers("RELATION", (70, 71, 81)),
    _span("SUBJECT", 1, 6),
    _numbers("SUBJECT", (9,)),
    _span("SUBJECT", 10, 17),
    _numbers("SUBJECT", (23, 24)),
    _numbers("SUBJECT", (33,)),
    _numbers("IDENTITY", (1, 2, 3, 4, 11)),
    _numbers("RESOURCE", (1, 2, 3, 4, 5, 9, 10)),
    _span("TERM", 1, 5),
    _numbers("TRANSCRIPT", (2, 20, 21)),
    _span("TRANSCRIPT", 38, 40),
    _span("TRANSCRIPT", 41, 47),
    _numbers("TRANSCRIPT", (48,)),
    _span("CLASSICAL-ANALYSIS", 1, 24),
    _span("CLASSICAL-CASE", 1, 5),
    _span("CLASSICAL-COMMITMENT", 1, 15),
    _span("CLASSICAL-CONSTRUCTION", 1, 10),
    _numbers("CLASSICAL-CONSTRUCTION", (20, 27)),
    _span("CLASSICAL-CONSTRUCTION", 28, 43),
    _span("CLASSICAL-CONSTRUCTION", 45, 48),
    _span("CLASSICAL-CONSTRUCTION", 57, 59),
    _numbers("CLASSICAL-CONSTRUCTION", (62, 63)),
    _span("CLASSICAL-CORE", 1, 6),
    _span("CLASSICAL-FIELD", 1, 9),
    _span("CLASSICAL-FORMATION", 1, 8),
    _span("CLASSICAL-FS", 1, 9),
    _span("CLASSICAL-GENERATION", 1, 7),
    _span("CLASSICAL-INDEPENDENT", 1, 21),
    _numbers("CLASSICAL-INDEPENDENT", (91, 92)),
    _span("CLASSICAL-ORACLE", 1, 4),
    _span("CLASSICAL-PROFILE", 1, 11),
    _span("CLASSICAL-PROOF", 1, 8),
    _span("CLASSICAL-PUBLIC", 1, 9),
    _span("CLASSICAL-QUERY", 1, 5),
    _span("CLASSICAL-RELATION", 1, 21),
    _numbers("CLASSICAL-RESOURCE", (1,)),
    _span("CLASSICAL-RUN", 1, 6),
    _span("CLASSICAL-SCHEDULE", 1, 3),
)

_FAULT_REASONS = MappingProxyType(
    {
        "FRI-IOR-CHECKER-001": (
            "the shared checker-failure code is emitted only by an unexpected "
            "implementation exception catch"
        ),
        "FRI-IOR-DIAGNOSTIC-017": (
            "DiagnosticClassification formation already rejects an empty reason; "
            "this branch protects a corrupted or forged row"
        ),
        "FRI-IOR-GENERATION-028": (
            "exact source reconstruction fixes the execution identity; reaching "
            "this mismatch requires internal drift or a semantic-ID collision"
        ),
        "FRI-IOR-GENERATION-030": (
            "the private occurrence-map producer fixes this source occurrence; "
            "ordinary formed inputs cannot change it"
        ),
        "FRI-IOR-RELATION-079": (
            "the checked-grounding carrier rejects direct construction without "
            "the package-private issuer token"
        ),
        "FRI-IOR-GENERATION-031": (
            "the private occurrence-map producer fixes this target occurrence; "
            "ordinary formed inputs cannot change it"
        ),
        "FRI-IOR-GENERATION-032": (
            "the private occurrence-map producer fixes the paired value identity; "
            "ordinary formed inputs cannot change it"
        ),
        "FRI-IOR-INDEPENDENT-025": (
            "the fixed SHA-256 rejection sampler can exhaust only under injected "
            "digest behavior or equivalent fault pressure"
        ),
        "FRI-IOR-INDEPENDENT-099": (
            "the independent replay emits this only when an unexpected host "
            "exception escapes its typed failure paths"
        ),
        "FRI-IOR-CLASSICAL-INDEPENDENT-099": (
            "the exact classical replay emits this only when an unexpected "
            "host exception escapes its typed failure paths"
        ),
        "FRI-IOR-RESOURCE-006": (
            "only the evaluator-private resource reservation helper can supply "
            "an unknown accounting dimension"
        ),
        "FRI-IOR-SUBJECT-019": (
            "the selected Core owns a formed acceptance-affecting occurrence "
            "inventory; this malformed-inventory guard is defensive"
        ),
        "FRI-IOR-SUBJECT-021": (
            "a formed Fiat-Shamir interpretation already owns a unique "
            "canonical transcript-plan occurrence sequence"
        ),
        "FRI-IOR-SUBJECT-031": (
            "a formed Fiat-Shamir interpretation already fixes the selected "
            "canonical construction plan"
        ),
        "FRI-IOR-SUBJECT-032": (
            "formed same-Core endpoints and the canonical plan determine these "
            "protocol identities before this repeat check"
        ),
        "FRI-IOR-SUBJECT-034": (
            "a formed FiatShamirConstruction declaration already establishes "
            "same-Core endpoints before admission repeats the check"
        ),
        "FRI-IOR-TRANSCRIPT-023": (
            "the u16 codec is fed only fixed-bound evaluator values at its current "
            "call sites"
        ),
        "FRI-IOR-TRANSCRIPT-025": (
            "typed framing lengths are already bounded by closed-term and fixed "
            "profile limits"
        ),
        "FRI-IOR-TRANSCRIPT-026": (
            "transcript state is evaluator-private fixed-width digest material"
        ),
        "FRI-IOR-TRANSCRIPT-027": (
            "the fixed SHA-256 field sampler can exhaust only under injected "
            "digest behavior or equivalent fault pressure"
        ),
        "FRI-IOR-TRANSCRIPT-028": (
            "query-domain and query-count values come from the admitted fixed "
            "profile rather than caller-selected shape"
        ),
        "FRI-IOR-TRANSCRIPT-032": (
            "one-shot replay supplies the evaluator-issued first-round carrier"
        ),
        "FRI-IOR-TRANSCRIPT-033": (
            "one-shot replay supplies the evaluator-issued second-round carrier"
        ),
        "FRI-IOR-TRANSCRIPT-034": (
            "the work seed is evaluator-issued fixed-width digest material before "
            "the work predicate is evaluated"
        ),
        "FRI-IOR-TRANSCRIPT-035": (
            "the intrinsic grinding-search exhaustion path is exercised only as "
            "bounded fault pressure, not an ordinary fixture expectation"
        ),
        "FRI-IOR-TRANSCRIPT-036": (
            "one-shot replay supplies the evaluator-issued work-seed carrier"
        ),
    }
)

_FAULT_CODES = frozenset(_FAULT_REASONS)

_RACE_CODES = _span("PROVENANCE", 61, 64)

_INTENTIONALLY_UNREACHABLE_CODES = frozenset(
    {
        # Both decisions were required to be Affirmative immediately before
        # this comparison, so they are necessarily both "Accept".
        "FRI-IOR-GENERATION-033",
    }
)


def _make_classifications() -> Mapping[str, DiagnosticClassification]:
    groups = (
        _FORMATION_CODES,
        _FAULT_CODES,
        _RACE_CODES,
        _INTENTIONALLY_UNREACHABLE_CODES,
    )
    counts = Counter(code for group in groups for code in group)
    overlaps = sorted(code for code, count in counts.items() if count != 1)
    if overlaps:
        raise RuntimeError(
            "overlapping diagnostic classifications: " + ",".join(overlaps)
        )
    if not set(counts).issubset(_CURRENT_CODES):
        raise RuntimeError("non-direct classification names an unknown code")

    direct_reason = (
        "authored as an ordinary public operation or result boundary; this "
        "static class does not establish that a test executes it"
    )
    table = {
        code: DiagnosticClassification(
            EvidenceClass.DIRECT_PUBLIC_SURFACE,
            direct_reason,
        )
        for code in _CURRENT_CODES
    }
    for code in _FORMATION_CODES:
        table[code] = DiagnosticClassification(
            EvidenceClass.FORMATION,
            (
                "emitted while constructing, freezing, or encoding an exact "
                "carrier; formation evidence is not a public checker run"
            ),
        )
    for code in _FAULT_CODES:
        table[code] = DiagnosticClassification(
            EvidenceClass.FAULT_INJECTION_DEFENSIVE,
            _FAULT_REASONS[code],
        )
    for code in _RACE_CODES:
        table[code] = DiagnosticClassification(
            EvidenceClass.RACE_ONLY,
            (
                "requires the opened source-ledger file to change during its "
                "bounded descriptor read; a stable file cannot drive it"
            ),
        )
    for code in _INTENTIONALLY_UNREACHABLE_CODES:
        table[code] = DiagnosticClassification(
            EvidenceClass.INTENTIONALLY_UNREACHABLE,
            (
                "the preceding source and target affirmative checks force both "
                "derived decisions to Accept before this comparison"
            ),
        )
    return MappingProxyType(dict(sorted(table.items())))


EXPLICIT_CLASSIFICATIONS = _make_classifications()


_FIXED_OUTCOME = {
    "affirmative": OutcomeClass.AFFIRMATIVE.value,
    "refused": OutcomeClass.REFUSED.value,
    "refusal": OutcomeClass.REFUSED.value,
    "unsupported": OutcomeClass.UNSUPPORTED.value,
    "unsupported_failure": OutcomeClass.UNSUPPORTED.value,
    "missing_dependency": OutcomeClass.MISSING_DEPENDENCY.value,
    "kind_mismatch": OutcomeClass.KIND_MISMATCH.value,
    "malformed": OutcomeClass.MALFORMED.value,
    "deterministic_limit_failure": OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED.value,
    "_malformed": OutcomeClass.MALFORMED.value,
    "_digest_text": OutcomeClass.MALFORMED.value,
    "_malformed_result": OutcomeClass.MALFORMED.value,
    "_refusal": OutcomeClass.REFUSED.value,
    "_object": OutcomeClass.MALFORMED.value,
    "_sequence": OutcomeClass.MALFORMED.value,
    "_integer": OutcomeClass.MALFORMED.value,
    "_text": OutcomeClass.MALFORMED.value,
    "_hex": OutcomeClass.MALFORMED.value,
    "_fp2": OutcomeClass.MALFORMED.value,
    "_reject": OutcomeClass.REFUSED.value,
    "_defect": OutcomeClass.REFUSED.value,
    "_require_semantic_id": OutcomeClass.MALFORMED.value,
    "_validate_identifier": OutcomeClass.MALFORMED.value,
    "_ContractViolation": OutcomeClass.CHECKER_FAILURE.value,
}

_BOUNDARY_POSITION = {
    "affirmative": 0,
    "refused": 0,
    "refusal": 0,
    "unsupported": 0,
    "unsupported_failure": 0,
    "missing_dependency": 0,
    "kind_mismatch": 0,
    "malformed": 0,
    "deterministic_limit_failure": 0,
    "CheckResult": 1,
    "ModelFailure": 1,
    "_failure": 1,
    "_outcome": 1,
}


def _module_name(root: Path, path: Path) -> str:
    relative = path.relative_to(root).with_suffix("")
    return ".".join(relative.parts)


def _digest_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _production_files(root: Path) -> tuple[Path, ...]:
    return tuple(
        sorted(
            (
                path
                for path in root.rglob("*.py")
                if "tests" not in path.relative_to(root).parts
                and "__pycache__" not in path.parts
            ),
            key=lambda path: path.relative_to(root).as_posix(),
        )
    )


def _test_files(root: Path) -> tuple[Path, ...]:
    tests = root / "tests"
    if not tests.is_dir():
        return ()
    return tuple(
        sorted(
            tests.rglob("test_*.py"),
            key=lambda path: path.relative_to(root).as_posix(),
        )
    )


def _source_snapshots(
    root: Path,
    files: tuple[Path, ...],
    *,
    code: str,
    kind: str,
) -> Mapping[Path, bytes]:
    try:
        return MappingProxyType({path: path.read_bytes() for path in files})
    except OSError as error:
        raise _ContractViolation(
            code,
            f"cannot read {kind} source: {error.filename}",
            source_kind=kind,
            source_path=(
                None
                if error.filename is None
                else Path(error.filename).relative_to(root).as_posix()
            ),
        ) from error


def _call_name(call: ast.Call) -> str:
    if isinstance(call.func, ast.Name):
        return call.func.id
    if isinstance(call.func, ast.Attribute):
        return call.func.attr
    return "<dynamic-call>"


def _parents(tree: ast.AST) -> dict[ast.AST, ast.AST]:
    return {
        child: parent
        for parent in ast.walk(tree)
        for child in ast.iter_child_nodes(parent)
    }


def _enclosing_function(
    node: ast.AST,
    parents: Mapping[ast.AST, ast.AST],
) -> ast.FunctionDef | ast.AsyncFunctionDef | None:
    current = node
    while current in parents:
        current = parents[current]
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return current
    return None


def _literal_strings(expression: ast.AST) -> tuple[str, ...]:
    """Evaluate only recursively constant string expressions."""

    if isinstance(expression, ast.Constant) and isinstance(expression.value, str):
        return (expression.value,)
    if isinstance(expression, ast.BinOp) and isinstance(expression.op, ast.Add):
        left = _literal_strings(expression.left)
        right = _literal_strings(expression.right)
        if left and right:
            return tuple(first + second for first, second in product(left, right))
    return ()


def _function_bindings(
    function: ast.FunctionDef | ast.AsyncFunctionDef | None,
) -> Mapping[str, tuple[str, ...]]:
    if function is None:
        return MappingProxyType({})
    bindings: dict[str, set[str]] = {}

    class _BindingVisitor(ast.NodeVisitor):
        def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
            if node is function:
                self.generic_visit(node)

        def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
            if node is function:
                self.generic_visit(node)

        def visit_Lambda(self, node: ast.Lambda) -> None:
            return

        def visit_ClassDef(self, node: ast.ClassDef) -> None:
            return

        def visit_Assign(self, node: ast.Assign) -> None:
            values = _literal_strings(node.value)
            if values:
                for target in node.targets:
                    if isinstance(target, ast.Name):
                        bindings.setdefault(target.id, set()).update(values)
            self.generic_visit(node)

        def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
            values = () if node.value is None else _literal_strings(node.value)
            if isinstance(node.target, ast.Name) and values:
                bindings.setdefault(node.target.id, set()).update(values)
            self.generic_visit(node)

        def visit_For(self, node: ast.For) -> None:
            if isinstance(node.target, ast.Tuple) and isinstance(
                node.iter, (ast.Tuple, ast.List)
            ):
                targets = node.target.elts
                for item in node.iter.elts:
                    if not isinstance(item, (ast.Tuple, ast.List)) or len(
                        item.elts
                    ) != len(targets):
                        continue
                    for target, value in zip(targets, item.elts, strict=True):
                        if (
                            isinstance(target, ast.Name)
                            and isinstance(value, ast.Constant)
                            and isinstance(value.value, str)
                        ):
                            bindings.setdefault(target.id, set()).add(value.value)
            self.generic_visit(node)

    _BindingVisitor().visit(function)
    return MappingProxyType(
        {name: tuple(sorted(values)) for name, values in bindings.items()}
    )


def _module_bindings(tree: ast.Module) -> Mapping[str, tuple[str, ...]]:
    """Collect exact module string constants available to function bodies."""

    bindings: dict[str, set[str]] = {}
    for node in tree.body:
        if isinstance(node, ast.Assign):
            values = _literal_strings(node.value)
            if values:
                for target in node.targets:
                    if isinstance(target, ast.Name):
                        bindings.setdefault(target.id, set()).update(values)
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
            values = () if node.value is None else _literal_strings(node.value)
            if values:
                bindings.setdefault(node.target.id, set()).update(values)
    return MappingProxyType(
        {name: tuple(sorted(values)) for name, values in bindings.items()}
    )


def _scoped_nodes(
    function: ast.FunctionDef | ast.AsyncFunctionDef,
) -> tuple[ast.AST, ...]:
    nodes: list[ast.AST] = []

    class _ScopeVisitor(ast.NodeVisitor):
        def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
            if node is function:
                nodes.append(node)
                self.generic_visit(node)

        def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
            if node is function:
                nodes.append(node)
                self.generic_visit(node)

        def visit_Lambda(self, node: ast.Lambda) -> None:
            return

        def visit_ClassDef(self, node: ast.ClassDef) -> None:
            return

        def generic_visit(self, node: ast.AST) -> None:
            if node is not function:
                nodes.append(node)
            super().generic_visit(node)

    _ScopeVisitor().visit(function)
    return tuple(nodes)


def _function_code_positions(tree: ast.Module) -> Mapping[str, int | None]:
    """Recover each module-local function's explicit ``code`` parameter."""

    positions: dict[str, int | None] = {}
    for function in tree.body:
        if not isinstance(function, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        positional = tuple(function.args.posonlyargs) + tuple(function.args.args)
        for index, argument in enumerate(positional):
            if argument.arg == "code":
                positions[function.name] = index
                break
        else:
            if any(argument.arg == "code" for argument in function.args.kwonlyargs):
                positions[function.name] = None
    return MappingProxyType(positions)


def _code_expression(call: ast.Call, position: int | None) -> ast.AST | None:
    keyword = _keyword(call, "code")
    if keyword is not None:
        return keyword
    if position is not None and len(call.args) > position:
        return call.args[position]
    return None


def _emitter_code_positions(tree: ast.Module) -> Mapping[str, int | None]:
    """Find exact static aliases and helpers that forward ``code``.

    This excludes mere metadata or logging mentions while retaining wrappers
    introduced by later modules.  A novel wrapper is discovered transitively
    when it forwards its explicit ``code`` parameter to a known typed emitter.
    Imported ``friiormodel.terms`` aliases and direct name-to-name assignments
    are followed to a fixed point; dynamic attribute or callable flow remains
    outside this deliberately bounded scanner.
    """

    emitters = dict(_BASE_CODE_POSITIONS)
    aliases: list[tuple[str, str]] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module in {
            "friiormodel.terms",
            "terms",
        }:
            aliases.extend(
                (alias.asname, alias.name)
                for alias in node.names
                if alias.asname is not None
            )
        elif isinstance(node, ast.Assign) and isinstance(node.value, ast.Name):
            aliases.extend(
                (target.id, node.value.id)
                for target in node.targets
                if isinstance(target, ast.Name)
            )
        elif (
            isinstance(node, ast.AnnAssign)
            and isinstance(node.target, ast.Name)
            and isinstance(node.value, ast.Name)
        ):
            aliases.append((node.target.id, node.value.id))
    local_positions = _function_code_positions(tree)
    functions = tuple(
        node
        for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    )
    changed = True
    while changed:
        changed = False
        for alias, source in aliases:
            if alias not in emitters and source in emitters:
                emitters[alias] = emitters[source]
                changed = True
        for function in functions:
            if function.name in emitters:
                continue
            if function.name not in local_positions:
                continue
            for call in (
                node for node in _scoped_nodes(function) if isinstance(node, ast.Call)
            ):
                called = _call_name(call)
                if called not in emitters:
                    continue
                expression = _code_expression(call, emitters[called])
                if isinstance(expression, ast.Name) and expression.id == "code":
                    emitters[function.name] = local_positions[function.name]
                    changed = True
                    break
    return MappingProxyType(emitters)


def _static_strings(
    expression: ast.AST,
    bindings: Mapping[str, tuple[str, ...]],
) -> tuple[str, ...]:
    literal = _literal_strings(expression)
    if literal:
        return literal
    if isinstance(expression, ast.Name):
        return bindings.get(expression.id, ())
    if isinstance(expression, ast.Attribute) and isinstance(expression.value, ast.Name):
        if expression.value.id == "OutcomeClass":
            try:
                return (OutcomeClass[expression.attr].value,)
            except KeyError:
                return ()
    if isinstance(expression, ast.JoinedStr):
        components: list[tuple[str, ...]] = []
        for part in expression.values:
            if isinstance(part, ast.Constant) and isinstance(part.value, str):
                components.append((part.value,))
            elif isinstance(part, ast.FormattedValue):
                values = _static_strings(part.value, bindings)
                if not values:
                    return ()
                components.append(values)
            else:
                return ()
        return tuple("".join(items) for items in product(*components))
    if isinstance(expression, ast.BinOp) and isinstance(expression.op, ast.Add):
        left = _static_strings(expression.left, bindings)
        right = _static_strings(expression.right, bindings)
        if left and right:
            return tuple(first + second for first, second in product(left, right))
    return ()


def _keyword(call: ast.Call, name: str) -> ast.AST | None:
    for keyword in call.keywords:
        if keyword.arg == name:
            return keyword.value
    return None


def _site_boundary(
    call: ast.Call,
    name: str,
    module: str,
    bindings: Mapping[str, tuple[str, ...]],
) -> tuple[str, ...]:
    if name == "_reject" and module == "friiormodel.native":
        return ("native:verification",)
    if name == "_defect" and module == "friiormodel.oracle_construction":
        return ("oracle-construction:admission",)
    if name == "_run_failure" and module == "friiormodel.oracle_construction":
        return ("oracle-construction:run-check",)
    if name == "_fail" and module == "classical_independent":
        if len(call.args) >= 2:
            return _static_strings(call.args[1], bindings)
        return ()
    if name == "_validate_identifier":
        return ("identity:formation",)
    if name == "_require_semantic_id":
        expression = _keyword(call, "boundary")
        return () if expression is None else _static_strings(expression, bindings)
    if name == "_ContractViolation":
        return ("diagnostics:contract",)
    if module == "friiormodel.constructions" and name in {
        "_malformed_result",
        "_refusal",
    }:
        return ("constructions:execution-check",)
    if module == "friiormodel.provenance" and name == "_digest_text":
        return ("provenance:formation",)
    if module == "friiormodel.fixtures" and name in {
        "_object",
        "_sequence",
        "_integer",
        "_text",
        "_hex",
        "_fp2",
    }:
        return ("fixtures:formation",)
    if name == "_malformed":
        expression = _keyword(call, "boundary")
        if expression is None and len(call.args) >= 3:
            expression = call.args[2]
        if expression is not None:
            return _static_strings(expression, bindings)
        return (
            "fixtures:formation"
            if module == "friiormodel.fixtures"
            else "provenance:formation",
        )
    position = _BOUNDARY_POSITION.get(name)
    if position is None or len(call.args) <= position:
        return ()
    return _static_strings(call.args[position], bindings)


def _site_outcome(
    call: ast.Call,
    name: str,
    bindings: Mapping[str, tuple[str, ...]],
) -> tuple[str, ...]:
    fixed = _FIXED_OUTCOME.get(name)
    if fixed is not None:
        return (fixed,)
    if name not in {
        "CheckResult",
        "ModelFailure",
        "_failure",
        "_fail",
        "_outcome",
        "_run_failure",
    }:
        return ()
    if not call.args:
        return ()
    return _static_strings(call.args[0], bindings)


def _is_forwarded_code_parameter(
    expression: ast.AST,
    function: ast.FunctionDef | ast.AsyncFunctionDef | None,
    emitter_positions: Mapping[str, int | None],
) -> bool:
    """Recognize an unchanged wrapper parameter whose callers own closure."""

    if (
        function is None
        or function.name not in emitter_positions
        or not isinstance(expression, ast.Name)
        or expression.id != "code"
    ):
        return False
    return not any(
        isinstance(node, ast.Name)
        and node.id == "code"
        and isinstance(node.ctx, ast.Store)
        for node in _scoped_nodes(function)
    )


def _is_code_transport(
    expression: ast.AST,
    *,
    module: str,
    function: ast.FunctionDef | ast.AsyncFunctionDef | None,
    emitter: str,
) -> bool:
    """Recognize one exact transport of an already inventoried identifier."""

    return (
        function is not None
        and isinstance(expression, ast.Attribute)
        and expression.attr == "code"
        and isinstance(expression.value, ast.Name)
        and (
            module,
            function.name,
            emitter,
            expression.value.id,
        )
        in _CODE_TRANSPORTS
    )


def _is_truthy_name_guarded(
    expression: ast.AST,
    node: ast.AST,
    parents: Mapping[ast.AST, ast.AST],
) -> bool:
    """Prove that an empty-string sentinel cannot reach this call."""

    if not isinstance(expression, ast.Name):
        return False
    current = node
    while current in parents:
        current = parents[current]
        if isinstance(current, ast.If) and isinstance(current.test, ast.Name):
            if current.test.id != expression.id:
                continue
            body_nodes = {
                descendant
                for statement in current.body
                for descendant in ast.walk(statement)
            }
            return node in body_nodes
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return False
    return False


def _assignment_target_names(
    node: ast.AST,
    parents: Mapping[ast.AST, ast.AST],
) -> frozenset[str]:
    current = node
    while current in parents:
        current = parents[current]
        if isinstance(current, ast.Assign):
            return frozenset(
                target.id for target in current.targets if isinstance(target, ast.Name)
            )
        if isinstance(current, ast.AnnAssign) and isinstance(current.target, ast.Name):
            return frozenset({current.target.id})
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return frozenset()
    return frozenset()


def _approved_non_emission_literal(
    node: ast.Constant,
    module: str,
    parents: Mapping[ast.AST, ast.AST],
) -> bool:
    function = _enclosing_function(node, parents)
    if module == "friiormodel.diagnostics" and function is None:
        return bool(
            _assignment_target_names(node, parents)
            & {"_FAULT_REASONS", "_INTENTIONALLY_UNREACHABLE_CODES"}
        )
    if module == "friiormodel.report":
        if function is not None and function.name in {
            "_report_policy_valid",
            "verify_public_report",
        }:
            return True
        return bool(
            _assignment_target_names(node, parents)
            & {"EXPECTED_POSITIVE_CODES", "EXPECTED_NEGATIVE_CODES"}
        )
    if module == "generate":
        return bool(
            _assignment_target_names(node, parents)
            & {"_OWNER_RESULT_CONTRACTS", "_NEGATIVE_RESULT_CONTRACTS"}
        )
    return False


def _scan_production(
    root: Path,
    files: tuple[Path, ...],
    snapshots: Mapping[Path, bytes] | None = None,
) -> Mapping[str, tuple[DiagnosticSite, ...]]:
    found: dict[str, list[DiagnosticSite]] = {}
    for path in files:
        try:
            source = (
                path.read_bytes() if snapshots is None else snapshots[path]
            ).decode("utf-8")
            tree = ast.parse(source, filename=str(path))
        except (OSError, UnicodeError, SyntaxError) as error:
            raise _ContractViolation(
                "FRI-IOR-DIAGNOSTIC-004",
                f"cannot parse production source: {path.relative_to(root)}",
            ) from error
        parents = _parents(tree)
        module = _module_name(root, path)
        module_bindings = _module_bindings(tree)
        emitter_positions = _emitter_code_positions(tree)
        emitted_function_codes: set[tuple[str, str]] = set()
        unresolved_emitters: list[dict[str, Any]] = []
        for call in (node for node in ast.walk(tree) if isinstance(node, ast.Call)):
            function = _enclosing_function(call, parents)
            bindings = MappingProxyType(
                {
                    **module_bindings,
                    **_function_bindings(function),
                }
            )
            name = _call_name(call)
            if name not in emitter_positions:
                continue
            expression = _code_expression(call, emitter_positions[name])
            if expression is None:
                unresolved_emitters.append(
                    {
                        "emitter": name,
                        "function": "<module>" if function is None else function.name,
                        "line": call.lineno,
                        "reason": "missing-explicit-code-expression",
                    }
                )
                continue
            values = _static_strings(expression, bindings)
            if not values:
                if _is_forwarded_code_parameter(
                    expression,
                    function,
                    emitter_positions,
                ) or _is_code_transport(
                    expression,
                    module=module,
                    function=function,
                    emitter=name,
                ):
                    continue
                unresolved_emitters.append(
                    {
                        "emitter": name,
                        "function": "<module>" if function is None else function.name,
                        "line": call.lineno,
                        "reason": "code-expression-is-not-statically-closed",
                    }
                )
                continue
            if "" in values and _is_truthy_name_guarded(expression, call, parents):
                values = tuple(value for value in values if value)
            invalid = sorted(
                value for value in values if _CODE_PATTERN.fullmatch(value) is None
            )
            if invalid:
                unresolved_emitters.append(
                    {
                        "emitter": name,
                        "function": "<module>" if function is None else function.name,
                        "line": call.lineno,
                        "reason": "static-code-expression-is-not-a-diagnostic-id",
                        "values": invalid,
                    }
                )
                continue
            codes = set(values)
            boundaries = _site_boundary(call, name, module, bindings) or (None,)
            outcomes = _site_outcome(call, name, bindings) or (None,)
            for code in sorted(codes):
                emitted_function_codes.add(
                    ("<module>" if function is None else function.name, code)
                )
                for boundary, outcome in product(boundaries, outcomes):
                    found.setdefault(code, []).append(
                        DiagnosticSite(
                            module,
                            "<module>" if function is None else function.name,
                            call.lineno,
                            boundary,
                            outcome,
                        )
                    )
        unrecognized = []
        for node in ast.walk(tree):
            if not (
                isinstance(node, ast.Constant)
                and isinstance(node.value, str)
                and _CODE_PATTERN.fullmatch(node.value) is not None
            ):
                continue
            function = _enclosing_function(node, parents)
            function_name = "<module>" if function is None else function.name
            if (function_name, node.value) in emitted_function_codes:
                continue
            if _approved_non_emission_literal(node, module, parents):
                continue
            unrecognized.append(
                {
                    "code": node.value,
                    "function": function_name,
                    "line": node.lineno,
                }
            )
        if unrecognized or unresolved_emitters:
            raise _ContractViolation(
                "FRI-IOR-DIAGNOSTIC-007",
                f"production diagnostic emission is not statically closed: {module}",
                module=module,
                literals=unrecognized,
                unresolved_emitters=unresolved_emitters,
            )
    return MappingProxyType(
        {
            code: tuple(
                sorted(
                    set(sites),
                    key=lambda site: (
                        site.module,
                        site.line,
                        site.boundary or "",
                        site.outcome or "",
                    ),
                )
            )
            for code, sites in sorted(found.items())
        }
    )


def _assertion_context(
    node: ast.AST,
    parents: Mapping[ast.AST, ast.AST],
) -> bool:
    current = node
    while current in parents:
        current = parents[current]
        if isinstance(current, ast.Assert):
            return True
        if isinstance(current, ast.Call):
            name = _call_name(current)
            if name == "fail" or name.startswith("assert"):
                return True
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return False
    return False


def _scan_tests(
    root: Path,
    files: tuple[Path, ...],
    snapshots: Mapping[Path, bytes] | None = None,
) -> Mapping[str, tuple[StaticTestMention, ...]]:
    found: dict[str, list[StaticTestMention]] = {}
    for path in files:
        try:
            source = (
                path.read_bytes() if snapshots is None else snapshots[path]
            ).decode("utf-8")
            tree = ast.parse(source, filename=str(path))
        except (OSError, UnicodeError, SyntaxError) as error:
            raise _ContractViolation(
                "FRI-IOR-DIAGNOSTIC-006",
                f"cannot parse test source: {path.relative_to(root)}",
            ) from error
        parents = _parents(tree)
        for node in ast.walk(tree):
            if not (
                isinstance(node, ast.Constant)
                and isinstance(node.value, str)
                and _CODE_PATTERN.fullmatch(node.value) is not None
            ):
                continue
            function = _enclosing_function(node, parents)
            found.setdefault(node.value, []).append(
                StaticTestMention(
                    _module_name(root, path),
                    "<module>" if function is None else function.name,
                    node.lineno,
                    _assertion_context(node, parents),
                )
            )
    return MappingProxyType(
        {
            code: tuple(
                sorted(
                    mentions,
                    key=lambda mention: (
                        mention.module,
                        mention.line,
                        mention.test_function,
                    ),
                )
            )
            for code, mentions in sorted(found.items())
        }
    )


def _contract_failure(error: _ContractViolation) -> DiagnosticContractAdmission:
    return DiagnosticContractAdmission(
        CheckResult(
            OutcomeClass.CHECKER_FAILURE,
            "diagnostics:contract",
            error.code,
            error.detail,
            evidence=error.evidence,
        ),
        None,
    )


def _classification_row_is_well_formed(
    code: object,
    classification: object,
) -> bool:
    """Validate a row again at the checker boundary.

    Ordinary construction already enforces these conditions.  Rechecking them
    here keeps corrupted or deliberately forged instances inside the typed
    diagnostic contract instead of letting attribute access escape as a host
    exception.
    """

    return (
        isinstance(code, str)
        and _CODE_PATTERN.fullmatch(code) is not None
        and isinstance(classification, DiagnosticClassification)
        and isinstance(getattr(classification, "evidence_class", None), EvidenceClass)
        and isinstance(getattr(classification, "reason", None), str)
    )


def check_diagnostic_contract(
    root: Path | None = None,
    *,
    classifications: Mapping[str, DiagnosticClassification] | None = None,
) -> DiagnosticContractAdmission:
    """Check current source/test closure and issue one machine-readable report."""

    try:
        selected_root = _PACKAGE_ROOT if root is None else root
        if not isinstance(selected_root, Path):
            raise _ContractViolation(
                "FRI-IOR-DIAGNOSTIC-001",
                "diagnostic source root must be an exact Path",
            )
        if not selected_root.is_dir():
            raise _ContractViolation(
                "FRI-IOR-DIAGNOSTIC-002",
                "diagnostic source root is unavailable",
            )
        production_files = _production_files(selected_root)
        if not production_files:
            raise _ContractViolation(
                "FRI-IOR-DIAGNOSTIC-003",
                "diagnostic source closure contains no production Python",
            )
        production_snapshots = _source_snapshots(
            selected_root,
            production_files,
            code="FRI-IOR-DIAGNOSTIC-004",
            kind="production",
        )
        sites_by_code = _scan_production(
            selected_root,
            production_files,
            production_snapshots,
        )
        if not sites_by_code:
            raise _ContractViolation(
                "FRI-IOR-DIAGNOSTIC-005",
                "diagnostic source closure contains no emitted identifiers",
            )
        test_files = _test_files(selected_root)
        test_snapshots = _source_snapshots(
            selected_root,
            test_files,
            code="FRI-IOR-DIAGNOSTIC-006",
            kind="test",
        )
        mentions_by_code = _scan_tests(
            selected_root,
            test_files,
            test_snapshots,
        )

        for code, sites in sites_by_code.items():
            owners = sorted({site.module for site in sites})
            if len(owners) != 1:
                raise _ContractViolation(
                    "FRI-IOR-DIAGNOSTIC-010",
                    f"diagnostic has inconsistent production owners: {code}",
                    diagnostic=code,
                    owners=owners,
                )
            boundaries = sorted(
                {site.boundary for site in sites if site.boundary is not None}
            )
            if len(boundaries) > 1:
                raise _ContractViolation(
                    "FRI-IOR-DIAGNOSTIC-012",
                    f"diagnostic has inconsistent static boundaries: {code}",
                    diagnostic=code,
                    boundaries=boundaries,
                )
            outcomes = sorted(
                {site.outcome for site in sites if site.outcome is not None}
            )
            if len(outcomes) != 1:
                raise _ContractViolation(
                    "FRI-IOR-DIAGNOSTIC-013",
                    f"diagnostic lacks one exact static outcome: {code}",
                    diagnostic=code,
                    outcomes=outcomes,
                )

        selected_classifications = (
            EXPLICIT_CLASSIFICATIONS if classifications is None else classifications
        )
        if not isinstance(selected_classifications, Mapping):
            raise _ContractViolation(
                "FRI-IOR-DIAGNOSTIC-014",
                "diagnostic classifications must be one exact mapping",
            )
        malformed_rows = sorted(
            [
                code
                for code, classification in selected_classifications.items()
                if not _classification_row_is_well_formed(code, classification)
            ],
            key=lambda code: repr(code),
        )
        if malformed_rows:
            raise _ContractViolation(
                "FRI-IOR-DIAGNOSTIC-014",
                "diagnostic classification rows are malformed",
                rows=malformed_rows,
            )
        declared = set(sites_by_code)
        classified = set(selected_classifications)
        missing = sorted(declared - classified)
        if missing:
            raise _ContractViolation(
                "FRI-IOR-DIAGNOSTIC-015",
                "newly emitted diagnostics lack an explicit classification",
                missing=missing,
            )
        stale = sorted(classified - declared)
        if stale:
            raise _ContractViolation(
                "FRI-IOR-DIAGNOSTIC-016",
                "classification table contains diagnostics no longer emitted",
                stale=stale,
            )
        missing_reasons = sorted(
            code
            for code, classification in selected_classifications.items()
            if classification.evidence_class is not EvidenceClass.DIRECT_PUBLIC_SURFACE
            and not classification.reason.strip()
        )
        if missing_reasons:
            raise _ContractViolation(
                "FRI-IOR-DIAGNOSTIC-017",
                "non-direct classifications require explicit reasons",
                diagnostics=missing_reasons,
            )
        unknown_test_ids = sorted(set(mentions_by_code) - declared)
        if unknown_test_ids:
            raise _ContractViolation(
                "FRI-IOR-DIAGNOSTIC-018",
                "tests mention diagnostic identifiers absent from production emissions",
                unknown_test_ids=unknown_test_ids,
            )

        entries = tuple(
            DiagnosticCoverageEntry(
                code,
                sites_by_code[code][0].module,
                tuple(
                    sorted(
                        {
                            site.boundary
                            for site in sites_by_code[code]
                            if site.boundary is not None
                        }
                    )
                ),
                tuple(
                    sorted(
                        {
                            site.outcome
                            for site in sites_by_code[code]
                            if site.outcome is not None
                        }
                    )
                ),
                sites_by_code[code],
                selected_classifications[code],
                mentions_by_code.get(code, ()),
            )
            for code in sorted(sites_by_code)
        )
        production_sources = tuple(
            (
                path.relative_to(selected_root).as_posix(),
                _digest_bytes(production_snapshots[path]),
            )
            for path in production_files
        )
        test_sources = tuple(
            (
                path.relative_to(selected_root).as_posix(),
                _digest_bytes(test_snapshots[path]),
            )
            for path in test_files
        )
        report = CheckedDiagnosticCoverageReport(
            production_sources,
            test_sources,
            entries,
            _token=_REPORT_TOKEN,
        )
        return DiagnosticContractAdmission(
            affirmative(
                "diagnostics:contract",
                "FRI-IOR-DIAGNOSTIC-100",
                "every emitted diagnostic has consistent ownership and one explicit evidence class",
                validation_basis_id=str(report.validation_basis_id),
                diagnostic_count=len(entries),
                production_source_count=len(production_sources),
                test_source_count=len(test_sources),
                static_test_mentions_are_reachability_evidence=False,
            ),
            report,
        )
    except _ContractViolation as error:
        return _contract_failure(error)
    except Exception as error:  # pragma: no cover - fault-injection boundary
        return DiagnosticContractAdmission(
            checker_failure(
                "diagnostics:contract",
                f"unexpected diagnostic-contract failure: {type(error).__name__}",
            ),
            None,
        )


__all__ = [
    "CheckedDiagnosticCoverageReport",
    "DiagnosticClassification",
    "DiagnosticContractAdmission",
    "DiagnosticCoverageEntry",
    "DiagnosticSite",
    "EXPLICIT_CLASSIFICATIONS",
    "EvidenceClass",
    "StaticTestMention",
    "check_diagnostic_contract",
]
