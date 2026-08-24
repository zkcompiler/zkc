"""Closed diagnostic taxonomy and first-boundary driver contract for P01.

This module classifies the diagnostic codes *declared by the current P01
evaluator sources*.  Classification is deliberately separate from execution
coverage:

* ``affirmative`` codes are successful judgment results;
* ``constructible-driver`` codes are intended results of finite malformed or
  negative inputs at a public checker boundary;
* ``internal-invariant/fault`` codes report a checker invariant failure or an
  assumption-only event rather than an ordinary caller-controlled input;
* ``environmental`` codes report unavailable or mismatched source material or
  owner-local evidence; and
* ``retired-dead/redundant`` codes are retained implementation branches that
  are shadowed, redundant after an earlier admission, or synthetic coverage
  sentinels rather than semantic judgments.

The table is closed on purpose.  Adding or deleting a ``P01-*`` literal in the
source closure without updating this module makes the audit fail.  A complete
classification therefore says nothing about whether a code has actually been
observed.  Likewise, the driver registry below is only a contract for later
test integration; this module registers and runs no drivers by itself.
"""

from __future__ import annotations

import ast
from collections import Counter
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
import re
from types import MappingProxyType
from typing import Any, Callable, Iterable, Mapping, TypeAlias

from .terms import Outcome, Result


class DiagnosticContractError(RuntimeError):
    """The declared-code taxonomy or a driver registry is not closed."""


class DriverContractError(DiagnosticContractError):
    """A registered negative driver violates its first-boundary contract."""


class DiagnosticClass(str, Enum):
    """The five disjoint roles assigned to every declared P01 code."""

    AFFIRMATIVE = "affirmative"
    CONSTRUCTIBLE_DRIVER = "constructible-driver"
    INTERNAL_INVARIANT_FAULT = "internal-invariant/fault"
    ENVIRONMENTAL = "environmental"
    RETIRED_DEAD_REDUNDANT = "retired-dead/redundant"


_CODE_LITERAL = re.compile(r"P01-[A-Z0-9]+(?:-[A-Z0-9]+)*\Z")
_PACKAGE_ROOT = Path(__file__).resolve().parent
_SELF_NAME = Path(__file__).name


def _codes(prefix: str, *suffixes: str) -> frozenset[str]:
    """Build an explicit, reviewable family fragment for the closed table."""

    return frozenset(f"P01-{prefix}-{suffix}" for suffix in suffixes)


# Positive results are not negative-test obligations.  The synthetic report
# report artifacts do not mint synthetic success diagnostics.
AFFIRMATIVE_CODES = frozenset().union(
    _codes("ALG", "OK"),
    _codes("BASIS", "OK"),
    _codes("CHECKED", "OK"),
    _codes("CORE", "OK"),
    _codes("CORR", "OK"),
    _codes("CTX", "OK"),
    _codes("EXT", "OK"),
    _codes("FACT", "OK"),
    _codes("FRESH", "OK"),
    _codes("FRESH", "PUBLIC-OK"),
    _codes("FS", "OK"),
    _codes("FS", "PROJECTION-OK"),
    _codes("GRD", "SHAPE-OK", "STATEMENT-OK"),
    _codes("HONEST", "OK"),
    _codes("IFACE", "OK"),
    _codes("INS", "OK"),
    _codes("INV", "OK"),
    _codes("LOCAL", "QUAL-OK"),
    _codes("PCOIN", "OK"),
    _codes("PROTO", "OK"),
    _codes("REL", "OK"),
    _codes("RHC", "OK"),
    _codes("SAT", "OK"),
    _codes("SHVZK", "OK"),
    _codes("SS", "ENUM-OK", "OK"),
    _codes("TRN", "OK"),
    _codes("VERIFY", "OK"),
    _codes("WIT", "OK"),
)


# These inputs are finite and caller-constructible at the boundary named by
# the result.  Listing every suffix is intentional: a newly introduced code,
# even in a known family, remains unknown until it is reviewed here.
CONSTRUCTIBLE_DRIVER_CODES = frozenset().union(
    _codes("ALG", "001", "002", "003", "004", "006", "007", "009"),
    _codes(
        "APP",
        "001",
        "101",
        "102",
        "103",
        "104",
        "105",
        "106",
    ),
    _codes("BASIS", "001", "003"),
    _codes("BUILD", "001"),
    _codes("CHECKED", "001"),
    _codes(
        "CORE",
        "001",
        "003",
        "004",
        "005",
        "006",
        "007",
        "008",
        "009",
        "010",
        "011",
        "012",
        "013",
    ),
    _codes("CORR", "001", "002", "003"),
    _codes("CTX", "001", "002"),
    _codes("EXT", "001", "002"),
    _codes("FIN", "001"),
    _codes("FRESH", "000", "001", "002", "003", "DERIVE-001"),
    _codes("FRESH", "PUBLIC-001"),
    _codes(
        "FS",
        "000",
        "001",
        "004",
        "005",
        "006",
        "007",
        "008",
        "010",
        "011",
        "012",
        "013",
        "017",
        "018",
        "019",
        "020",
        "021",
        "022",
        "023",
        "025",
        "DERIVE-001",
    ),
    _codes(
        "FS",
        "PROJECTION-001",
        "PROJECTION-002",
    ),
    _codes(
        "GRD",
        "001",
        "002",
        "003",
        "004",
        "005",
        "006",
        "007",
        "008",
        "009",
        "010",
    ),
    _codes("HONEST", "000", "001", "002"),
    _codes("IFACE", "001", "003"),
    _codes("INS", "001", "002", "003", "004"),
    _codes("INV", "001", "002", "003", "004"),
    _codes("LOCAL", "BIND-001", "BIND-002", "BIND-003"),
    _codes("LOCAL", "EXEC-001", "EXEC-002", "EXEC-003", "EXEC-004"),
    _codes("LOCAL", "QUAL-001"),
    _codes("PCOIN", "001"),
    _codes("PROOF", "001", "002", "004"),
    _codes(
        "PROTO",
        "000",
        "001",
        "002",
        "003",
        "005",
        "006",
        "008",
        "009",
    ),
    _codes("PUBLIC", "VERIFY-001"),
    _codes("REL", "001", "002", "003"),
    _codes("REPLAY", "001", "002", "003", "004"),
    _codes("RHC", "001", "002", "004"),
    _codes("SAT", "001"),
    _codes("SS", "001", "002", "003", "005", "006", "009"),
    _codes("TRACE", "001"),
    _codes("TRN", "001", "002", "003", "005", "006", "007", "008", "009"),
    _codes("VERIFY", "002", "003", "004"),
    _codes("WIT", "001", "002", "004", "005", "006"),
)


# These branches are not ordinary negative inputs.  Most require an admitted
# value to violate its own constructor invariant; COUPLE-003 additionally
# assumes a collision in the semantic-identity function.
INTERNAL_INVARIANT_FAULT_CODES = frozenset().union(
    _codes("CHECKED", "002"),
    _codes("FRESH", "DERIVE-002"),
    _codes("FS", "DERIVE-002", "DERIVE-003", "PROJECTION-003"),
    _codes("RHC", "003"),
    _codes("SHVZK", "001", "002", "ENUM-001"),
    _codes("SS", "008", "ENUM-001", "ENUM-002", "ENUM-003", "ENUM-004"),
    _codes("VERIFY", "001"),
)


# These results depend on checkout/source availability or owner-local evidence
# rather than a protocol object supplied to the semantic checker.
ENVIRONMENTAL_CODES = frozenset().union(
    _codes("BASIS", "002"),
)


# These branches must not inflate negative-driver coverage.  They are either
# shadowed by an earlier check, repeat a guarantee of an admitted wrapper, or
# redundant after an earlier admission.  Keeping them classified makes their
# continued presence visible until the owning code removes them.
RETIRED_DEAD_REDUNDANT_CODES = frozenset().union(
    _codes("ALG", "005"),
    _codes("BUILD", "002"),
    _codes("FACT", "001", "002", "003", "004", "005"),
    _codes("IFACE", "002"),
    _codes("PROOF", "003"),
    _codes("PROTO", "007"),
    _codes("SS", "004", "007"),
    _codes("TRN", "004"),
)


_CATEGORY_TABLE: tuple[tuple[DiagnosticClass, frozenset[str]], ...] = (
    (DiagnosticClass.AFFIRMATIVE, AFFIRMATIVE_CODES),
    (DiagnosticClass.CONSTRUCTIBLE_DRIVER, CONSTRUCTIBLE_DRIVER_CODES),
    (DiagnosticClass.INTERNAL_INVARIANT_FAULT, INTERNAL_INVARIANT_FAULT_CODES),
    (DiagnosticClass.ENVIRONMENTAL, ENVIRONMENTAL_CODES),
    (DiagnosticClass.RETIRED_DEAD_REDUNDANT, RETIRED_DEAD_REDUNDANT_CODES),
)


def _make_explicit_table() -> Mapping[str, DiagnosticClass]:
    table: dict[str, DiagnosticClass] = {}
    collisions: dict[str, list[str]] = {}
    for category, codes in _CATEGORY_TABLE:
        for code in codes:
            if code in table:
                collisions.setdefault(code, [table[code].value]).append(category.value)
            else:
                table[code] = category
    if collisions:
        rendered = ", ".join(
            f"{code}=>{'/'.join(categories)}"
            for code, categories in sorted(collisions.items())
        )
        raise DiagnosticContractError(
            f"diagnostic classification table overlaps: {rendered}"
        )
    return MappingProxyType(dict(sorted(table.items())))


EXPLICIT_CLASSIFICATIONS = _make_explicit_table()


def source_closure_files(root: Path | None = None) -> tuple[Path, ...]:
    """Return the deterministic Python source closure scanned for P01 codes.

    ``diagnostics.py`` is excluded because its explicit taxonomy necessarily
    repeats every declared code.  All other sibling Python modules, including
    a future module added to this package, participate automatically.
    """

    package_root = _PACKAGE_ROOT if root is None else Path(root)
    try:
        files = tuple(
            sorted(
                (
                    path
                    for path in package_root.iterdir()
                    if path.is_file()
                    and path.suffix == ".py"
                    and path.name != _SELF_NAME
                ),
                key=lambda path: path.name,
            )
        )
    except OSError as error:
        raise DiagnosticContractError(
            f"P01 source closure is unavailable: {package_root}"
        ) from error
    if not files:
        raise DiagnosticContractError("P01 source closure contains no Python files")
    return files


def scan_declared_codes(root: Path | None = None) -> Mapping[str, tuple[str, ...]]:
    """Scan exact string literals and return code-to-owner declarations.

    Parsing the AST excludes comments and substrings in longer prose.  A code
    is a declaration only when a complete string literal has the canonical
    ``P01-*`` form.
    """

    owners: dict[str, set[str]] = {}
    for path in source_closure_files(root):
        try:
            source = path.read_text(encoding="utf-8")
            tree = ast.parse(source, filename=str(path))
        except (OSError, SyntaxError, UnicodeError) as error:
            raise DiagnosticContractError(
                f"cannot parse P01 source closure member: {path.name}"
            ) from error
        for node in ast.walk(tree):
            if (
                isinstance(node, ast.Constant)
                and isinstance(node.value, str)
                and _CODE_LITERAL.fullmatch(node.value) is not None
            ):
                owners.setdefault(node.value, set()).add(path.name)
    if not owners:
        raise DiagnosticContractError("P01 source closure declares no diagnostic codes")
    return MappingProxyType(
        {
            code: tuple(sorted(code_owners))
            for code, code_owners in sorted(owners.items())
        }
    )


@dataclass(frozen=True)
class DiagnosticDeclaration:
    """One code, its single role, and every source file that declares it."""

    code: str
    classification: DiagnosticClass
    owners: tuple[str, ...]

    def term(self) -> dict[str, Any]:
        return {
            "code": self.code,
            "classification": self.classification.value,
            "owners": list(self.owners),
        }


@dataclass(frozen=True)
class ClassificationSummary:
    """Deterministic source-closure classification summary."""

    source_files: tuple[str, ...]
    declarations: tuple[DiagnosticDeclaration, ...]
    counts: tuple[tuple[DiagnosticClass, int], ...]

    @property
    def declared_count(self) -> int:
        return len(self.declarations)

    def term(self) -> dict[str, Any]:
        return {
            "source_files": list(self.source_files),
            "declared_count": self.declared_count,
            "counts": {
                category.value: count for category, count in self.counts
            },
            "declarations": [declaration.term() for declaration in self.declarations],
            "coverage_semantics": (
                "classification closure only; it is not diagnostic reachability "
                "or executed-driver coverage"
            ),
        }


def classification_summary(root: Path | None = None) -> ClassificationSummary:
    """Return the closed classification, rejecting unknown and stale entries.

    Unknown declarations fail closed instead of being defaulted to the
    constructible class.  Stale table entries also fail: deleting or retiring
    a source diagnostic requires an explicit taxonomy update.
    """

    declarations = scan_declared_codes(root)
    declared = set(declarations)
    classified = set(EXPLICIT_CLASSIFICATIONS)
    unknown = sorted(declared - classified)
    stale = sorted(classified - declared)
    if unknown or stale:
        fragments = []
        if unknown:
            fragments.append("unknown=" + ",".join(unknown))
        if stale:
            fragments.append("stale=" + ",".join(stale))
        raise DiagnosticContractError(
            "P01 diagnostic taxonomy is not closed (" + "; ".join(fragments) + ")"
        )

    rows = tuple(
        DiagnosticDeclaration(
            code=code,
            classification=EXPLICIT_CLASSIFICATIONS[code],
            owners=declarations[code],
        )
        for code in sorted(declarations)
    )
    count_by_category = Counter(row.classification for row in rows)
    counts = tuple(
        (category, count_by_category[category]) for category in DiagnosticClass
    )
    source_files = tuple(path.name for path in source_closure_files(root))
    return ClassificationSummary(source_files, rows, counts)


def classification_for(code: str, root: Path | None = None) -> DiagnosticClass:
    """Return one code's role after auditing the entire current closure."""

    summary = classification_summary(root)
    for declaration in summary.declarations:
        if declaration.code == code:
            return declaration.classification
    raise DiagnosticContractError(f"code is not declared by the P01 closure: {code}")


ResultDriver: TypeAlias = Callable[[], Result]


@dataclass(frozen=True)
class FirstBoundaryExpectation:
    """The exact result triple a constructible negative driver must produce."""

    case_name: str
    expected_outcome: Outcome
    expected_boundary: str
    expected_code: str
    rationale: str = ""

    def __post_init__(self) -> None:
        if not isinstance(self.case_name, str) or not self.case_name:
            raise DriverContractError("driver case_name must be nonempty text")
        if not isinstance(self.expected_outcome, Outcome):
            raise DriverContractError("driver expected_outcome must be an Outcome")
        if self.expected_outcome in (Outcome.AFFIRMATIVE, Outcome.NOT_EXERCISED):
            raise DriverContractError(
                "a negative driver must expect an exercised non-affirmative outcome"
            )
        if not isinstance(self.expected_boundary, str) or not self.expected_boundary:
            raise DriverContractError("driver expected_boundary must be nonempty text")
        if (
            not isinstance(self.expected_code, str)
            or _CODE_LITERAL.fullmatch(self.expected_code) is None
        ):
            raise DriverContractError("driver expected_code is not canonical")
        if not isinstance(self.rationale, str):
            raise DriverContractError("driver rationale must be text")

    def check(self, observed: Result) -> tuple[str, ...]:
        """Return deterministic mismatch descriptions for one observed result."""

        if not isinstance(observed, Result):
            return (f"result-type:{type(observed).__name__}",)
        mismatches = []
        if observed.outcome is not self.expected_outcome:
            mismatches.append(
                f"outcome:{self.expected_outcome.value}!={observed.outcome.value}"
            )
        if observed.boundary != self.expected_boundary:
            mismatches.append(
                f"boundary:{self.expected_boundary}!={observed.boundary}"
            )
        if observed.code != self.expected_code:
            mismatches.append(f"code:{self.expected_code}!={observed.code}")
        return tuple(mismatches)


@dataclass(frozen=True)
class DriverRegistration:
    """One expectation bound to a callable; no registrations live here."""

    expectation: FirstBoundaryExpectation
    driver: ResultDriver

    def __post_init__(self) -> None:
        if not isinstance(self.expectation, FirstBoundaryExpectation):
            raise DriverContractError(
                "registered expectation must be FirstBoundaryExpectation"
            )
        if not callable(self.driver):
            raise DriverContractError("registered driver must be callable")


@dataclass(frozen=True)
class DriverRun:
    """One successfully checked driver observation."""

    case_name: str
    expected_code: str
    observed: Result

    def term(self) -> dict[str, Any]:
        return {
            "case_name": self.case_name,
            "expected_code": self.expected_code,
            "observed": self.observed.term(),
        }


@dataclass(frozen=True)
class DriverCoverageSummary:
    """Registration coverage, explicitly distinct from executed coverage."""

    registered_cases: tuple[str, ...]
    registered_codes: tuple[str, ...]
    constructible_codes: tuple[str, ...]
    unregistered_codes: tuple[str, ...]

    @property
    def registration_complete(self) -> bool:
        return not self.unregistered_codes

    def term(self) -> dict[str, Any]:
        return {
            "registered_case_count": len(self.registered_cases),
            "registered_unique_code_count": len(self.registered_codes),
            "constructible_code_count": len(self.constructible_codes),
            "registered_cases": list(self.registered_cases),
            "registered_codes": list(self.registered_codes),
            "unregistered_codes": list(self.unregistered_codes),
            "registration_complete": self.registration_complete,
            "coverage_semantics": (
                "registry declarations only; execution is established only by "
                "successful DriverRun records"
            ),
        }


@dataclass(frozen=True)
class DriverRegistry:
    """Deterministic bindings for constructible first-boundary drivers."""

    registrations: tuple[DriverRegistration, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.registrations, tuple):
            raise DriverContractError("registry registrations must be a tuple")
        if any(
            not isinstance(registration, DriverRegistration)
            for registration in self.registrations
        ):
            raise DriverContractError(
                "registry entries must be DriverRegistration values"
            )
        ordered = tuple(
            sorted(self.registrations, key=lambda item: item.expectation.case_name)
        )
        if ordered != self.registrations:
            raise DriverContractError(
                "registry registrations must be ordered by case_name"
            )
        self._validate_current_registrations()

    def _validate_current_registrations(self) -> None:
        summary = classification_summary()
        classes = {
            declaration.code: declaration.classification
            for declaration in summary.declarations
        }
        seen_names: set[str] = set()
        for registration in self.registrations:
            if not isinstance(registration, DriverRegistration):
                raise DriverContractError(
                    "registry entries must be DriverRegistration values"
                )
            expectation = registration.expectation
            if expectation.case_name in seen_names:
                raise DriverContractError(
                    f"duplicate driver case name: {expectation.case_name}"
                )
            seen_names.add(expectation.case_name)
            category = classes.get(expectation.expected_code)
            if category is not DiagnosticClass.CONSTRUCTIBLE_DRIVER:
                rendered = "undeclared" if category is None else category.value
                raise DriverContractError(
                    "driver expected_code is not constructible-driver: "
                    f"{expectation.expected_code} ({rendered})"
                )

    @classmethod
    def build(
        cls,
        registrations: Iterable[DriverRegistration],
    ) -> "DriverRegistry":
        """Validate and canonically order driver bindings.

        Several cases may intentionally target the same diagnostic code, but
        case names are unique.  Every expected code must belong to the current
        constructible-driver class; internal, environmental, and dead branches
        cannot silently enter the ordinary negative matrix.
        """

        materialized = tuple(registrations)
        if any(
            not isinstance(registration, DriverRegistration)
            for registration in materialized
        ):
            raise DriverContractError(
                "registry entries must be DriverRegistration values"
            )
        ordered = tuple(
            sorted(materialized, key=lambda item: item.expectation.case_name)
        )
        return cls(ordered)

    def coverage(self) -> DriverCoverageSummary:
        """Describe registrations without implying that any driver was run."""

        self._validate_current_registrations()
        summary = classification_summary()
        constructible = tuple(
            declaration.code
            for declaration in summary.declarations
            if declaration.classification is DiagnosticClass.CONSTRUCTIBLE_DRIVER
        )
        registered_cases = tuple(
            registration.expectation.case_name for registration in self.registrations
        )
        registered_codes = tuple(
            sorted(
                {
                    registration.expectation.expected_code
                    for registration in self.registrations
                }
            )
        )
        unregistered = tuple(sorted(set(constructible) - set(registered_codes)))
        return DriverCoverageSummary(
            registered_cases,
            registered_codes,
            constructible,
            unregistered,
        )

    def require_complete(self) -> None:
        """Fail unless every constructible code has at least one registration."""

        coverage = self.coverage()
        if coverage.unregistered_codes:
            raise DriverContractError(
                "constructible-driver registry is incomplete: "
                + ",".join(coverage.unregistered_codes)
            )

    def run(self) -> tuple[DriverRun, ...]:
        """Run registered drivers and enforce exact first-boundary results."""

        self._validate_current_registrations()
        runs = []
        for registration in self.registrations:
            expectation = registration.expectation
            try:
                observed = registration.driver()
            except Exception as error:
                raise DriverContractError(
                    f"driver raised before returning Result: {expectation.case_name}"
                ) from error
            mismatches = expectation.check(observed)
            if mismatches:
                raise DriverContractError(
                    f"first-boundary mismatch for {expectation.case_name}: "
                    + ";".join(mismatches)
                )
            runs.append(
                DriverRun(
                    expectation.case_name,
                    expectation.expected_code,
                    observed,
                )
            )
        return tuple(runs)


__all__ = [
    "AFFIRMATIVE_CODES",
    "CONSTRUCTIBLE_DRIVER_CODES",
    "ClassificationSummary",
    "DiagnosticClass",
    "DiagnosticContractError",
    "DiagnosticDeclaration",
    "DriverContractError",
    "DriverCoverageSummary",
    "DriverRegistration",
    "DriverRegistry",
    "DriverRun",
    "ENVIRONMENTAL_CODES",
    "EXPLICIT_CLASSIFICATIONS",
    "FirstBoundaryExpectation",
    "INTERNAL_INVARIANT_FAULT_CODES",
    "RETIRED_DEAD_REDUNDANT_CODES",
    "ResultDriver",
    "classification_for",
    "classification_summary",
    "scan_declared_codes",
    "source_closure_files",
]
