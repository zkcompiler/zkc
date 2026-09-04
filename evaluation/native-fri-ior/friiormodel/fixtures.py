"""Strict frozen-fixture loading for the finite native FRI/IOR evaluation.

Public replay is rooted in the checkout that supplied this imported module.
The public report never loads owner-local generation material or expected
results; their parsers are exposed only for the generator and post-verification
comparison entry points.
"""

from __future__ import annotations

from dataclasses import dataclass
import os
from pathlib import Path, PurePosixPath
import stat
from typing import Any

from .commitment import EXACT_COMMITMENT_PROFILE, MerkleCap, PairOpening
from .field import Fp, Fp2
from .native import (
    DeclaredStrategyDependency,
    FreshChallenge,
    INITIAL_ORACLE_NAME,
    LogicalOracle,
    NativeEvent,
    NativeEventKind,
    NativeFriTrace,
    OracleEntry,
    OracleOrigin,
    OraclePublicationMode,
    RandomQueryDraw,
    TerminalPolynomial,
    canonical_event_log,
    canonical_structural_fold_chain,
)
from .profile import D0, D1, EXACT_PROFILE
from .proof import (
    CommittedFriPublicInputs,
    OccurrenceSelector,
    OpeningTableEntry,
    PublicFriProof,
)
from .provenance import (
    ArtifactContentId,
    CanonicalContentId,
    ValidationBasisId,
    artifact_content_id,
    canonical_json_content_id,
    load_bounded_json_bytes,
)
from .terms import ModelFailure, OutcomeClass, ResourceLimits
from .transcript import CANONICAL_CONSTRUCTION_PLAN


PACKAGE_ROOT = Path(__file__).resolve().parents[1]
LOADED_REPOSITORY_ROOT = PACKAGE_ROOT.parents[1]
MAX_FIXTURE_BYTES = 1 << 18


def _malformed(
    code: str, detail: str, boundary: str = "fixtures:formation"
) -> ModelFailure:
    return ModelFailure(OutcomeClass.MALFORMED, boundary, code, detail)


def _object(value: object, keys: tuple[str, ...], *, code: str) -> dict[str, Any]:
    if type(value) is not dict or set(value) != set(keys):
        raise _malformed(code, f"object requires exactly these keys: {', '.join(keys)}")
    return value


def _sequence(value: object, maximum: int, *, code: str) -> list[Any]:
    if type(value) is not list or len(value) > maximum:
        raise _malformed(code, "value must be a bounded JSON sequence")
    return value


def _integer(value: object, low: int, high: int, *, code: str) -> int:
    if type(value) is not int or not low <= value <= high:
        raise _malformed(code, "integer lies outside its admitted range")
    return value


def _text(value: object, maximum: int, *, code: str) -> str:
    if type(value) is not str or not value or len(value.encode("utf-8")) > maximum:
        raise _malformed(code, "text is empty or exceeds its byte bound")
    return value


def _hex(value: object, size: int, *, code: str) -> bytes:
    if type(value) is not str or len(value) != 2 * size:
        raise _malformed(code, "hexadecimal value has the wrong length")
    try:
        decoded = bytes.fromhex(value)
    except ValueError as error:
        raise _malformed(code, "hexadecimal value is malformed") from error
    if decoded.hex() != value:
        raise _malformed(code, "hexadecimal value is not canonical lowercase")
    return decoded


def _fp2(value: object, *, code: str) -> Fp2:
    parts = _sequence(value, 2, code=code)
    if len(parts) != 2:
        raise _malformed(code, "Fp2 requires exactly two limbs")
    return Fp2(
        Fp(_integer(parts[0], 0, 96, code=code)),
        Fp(_integer(parts[1], 0, 96, code=code)),
    )


def _closed_json(value: Any) -> Any:
    # The bounded JSON loader already excludes bytes, floats, duplicate keys,
    # excessive depth, and oversized integers/strings.
    return value


def bind_repository_root(root: Path) -> Path:
    if not isinstance(root, Path):
        raise _malformed("FRI-IOR-FIXTURE-001", "repository root must be a Path")
    try:
        resolved = root.resolve(strict=True)
    except OSError as error:
        raise _malformed(
            "FRI-IOR-FIXTURE-002", "repository root is unavailable"
        ) from error
    if resolved != LOADED_REPOSITORY_ROOT:
        raise _malformed(
            "FRI-IOR-FIXTURE-003",
            "fixture root differs from the checkout that supplied the loaded evaluator",
            "fixtures:root-binding",
        )
    return resolved


def _safe_relative_path(relative: str) -> PurePosixPath:
    path = PurePosixPath(relative)
    if (
        path.is_absolute()
        or not path.parts
        or any(part in ("", ".", "..") for part in path.parts)
    ):
        raise _malformed(
            "FRI-IOR-FIXTURE-004", "fixture path must be a closed relative POSIX path"
        )
    return path


def _read_regular_file(root: Path, relative: str, maximum: int) -> tuple[Path, bytes]:
    bound = bind_repository_root(root)
    rel = _safe_relative_path(relative)
    path = bound.joinpath(*rel.parts)
    try:
        cursor = bound
        for part in rel.parts[:-1]:
            cursor = cursor / part
            component = cursor.lstat()
            if stat.S_ISLNK(component.st_mode) or not stat.S_ISDIR(component.st_mode):
                raise OSError("an intermediate path component is not a real directory")
        if path.resolve(strict=True).parent != path.parent.resolve(strict=True):
            raise OSError("fixture path escapes through a symlink")
        before = path.lstat()
        if not stat.S_ISREG(before.st_mode) or stat.S_ISLNK(before.st_mode):
            raise OSError("not a regular non-symlink file")
        flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
        descriptor = os.open(path, flags)
        try:
            opened = os.fstat(descriptor)
            if (before.st_dev, before.st_ino) != (opened.st_dev, opened.st_ino):
                raise OSError("file changed during open")
            if opened.st_size > maximum:
                raise ModelFailure(
                    OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
                    "fixtures:load",
                    "FRI-IOR-FIXTURE-005",
                    "fixture exceeds its byte bound",
                )
            chunks: list[bytes] = []
            remaining = maximum + 1
            while remaining:
                chunk = os.read(descriptor, min(remaining, 1 << 16))
                if not chunk:
                    break
                chunks.append(chunk)
                remaining -= len(chunk)
            raw = b"".join(chunks)
            if len(raw) > maximum:
                raise ModelFailure(
                    OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
                    "fixtures:load",
                    "FRI-IOR-FIXTURE-005",
                    "fixture exceeds its byte bound",
                )
        finally:
            os.close(descriptor)
        after = path.lstat()
        if (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) != (
            after.st_dev,
            after.st_ino,
            after.st_size,
            after.st_mtime_ns,
        ):
            raise OSError("file changed during read")
    except ModelFailure:
        raise
    except OSError as error:
        raise _malformed(
            "FRI-IOR-FIXTURE-006", "fixture is unavailable or unstable", "fixtures:load"
        ) from error
    return path, raw


@dataclass(frozen=True, slots=True)
class LoadedFixture:
    role: str
    relative_path: str
    artifact_id: ArtifactContentId
    canonical_id: CanonicalContentId
    value: Any
    raw: bytes


def load_fixture(root: Path, relative: str, role: str) -> LoadedFixture:
    path, raw = _read_regular_file(root, relative, MAX_FIXTURE_BYTES)
    value = load_bounded_json_bytes(raw, maximum=MAX_FIXTURE_BYTES)
    return LoadedFixture(
        role,
        path.relative_to(bind_repository_root(root)).as_posix(),
        artifact_content_id(raw),
        canonical_json_content_id(value),
        value,
        raw,
    )


def parse_public_inputs(value: object) -> CommittedFriPublicInputs:
    obj = _object(
        value,
        ("schema", "profile", "transcript_plan", "statement", "application_context"),
        code="FRI-IOR-FIXTURE-010",
    )
    if (
        obj["schema"] != "zkc.fri-ior.committed-public-inputs.v1"
        or obj["profile"] != EXACT_PROFILE.to_term()
        or obj["transcript_plan"] != CANONICAL_CONSTRUCTION_PLAN.to_term()
    ):
        raise _malformed(
            "FRI-IOR-FIXTURE-011",
            "public inputs name a different schema, profile, or transcript plan",
        )
    formed = CommittedFriPublicInputs(
        EXACT_PROFILE,
        CANONICAL_CONSTRUCTION_PLAN,
        _closed_json(obj["statement"]),
        _closed_json(obj["application_context"]),
    )
    if formed.to_term() != value:
        raise _malformed(
            "FRI-IOR-FIXTURE-012", "public inputs are not the exact canonical term"
        )
    return formed


def _cap(value: object) -> MerkleCap:
    obj = _object(
        value,
        ("commitment_profile_id", "nodes"),
        code="FRI-IOR-FIXTURE-013",
    )
    nodes = _sequence(obj["nodes"], 2, code="FRI-IOR-FIXTURE-013")
    if (
        obj["commitment_profile_id"] != EXACT_COMMITMENT_PROFILE.identity.to_term()
        or len(nodes) != 2
    ):
        raise _malformed("FRI-IOR-FIXTURE-013", "cap does not match the exact profile")
    return MerkleCap(
        tuple(_hex(node, 32, code="FRI-IOR-FIXTURE-013") for node in nodes)
    )


def _opening(value: object) -> PairOpening:
    obj = _object(
        value,
        (
            "commitment_profile_id",
            "domain",
            "pair_index",
            "positive",
            "negative",
            "salt",
            "authentication_path",
        ),
        code="FRI-IOR-FIXTURE-014",
    )
    if obj["commitment_profile_id"] != EXACT_COMMITMENT_PROFILE.identity.to_term():
        raise _malformed(
            "FRI-IOR-FIXTURE-014",
            "opening names a different commitment profile",
        )
    domain = _text(obj["domain"], 96, code="FRI-IOR-FIXTURE-014")
    maximum = 7 if domain == D0.name else 3 if domain == D1.name else -1
    if maximum < 0:
        raise _malformed("FRI-IOR-FIXTURE-014", "opening names an unsupported domain")
    path = _sequence(obj["authentication_path"], 2, code="FRI-IOR-FIXTURE-014")
    return PairOpening(
        domain,
        _integer(obj["pair_index"], 0, maximum, code="FRI-IOR-FIXTURE-014"),
        _fp2(obj["positive"], code="FRI-IOR-FIXTURE-014"),
        _fp2(obj["negative"], code="FRI-IOR-FIXTURE-014"),
        _hex(obj["salt"], 16, code="FRI-IOR-FIXTURE-014"),
        tuple(_hex(item, 32, code="FRI-IOR-FIXTURE-014") for item in path),
    )


def parse_public_proof(value: object) -> PublicFriProof:
    obj = _object(
        value,
        (
            "schema",
            "cap0",
            "cap1",
            "terminal_polynomial",
            "grinding_nonce",
            "opening_table",
            "occurrence_selectors",
        ),
        code="FRI-IOR-FIXTURE-015",
    )
    if obj["schema"] != "zkc.fri-ior.public-proof.v1":
        raise _malformed("FRI-IOR-FIXTURE-015", "public proof schema is unsupported")
    terminal = _object(
        obj["terminal_polynomial"],
        ("coefficient_order", "coefficients"),
        code="FRI-IOR-FIXTURE-016",
    )
    coefficients = _sequence(terminal["coefficients"], 5, code="FRI-IOR-FIXTURE-016")
    if terminal["coefficient_order"] != "ascending" or not coefficients:
        raise _malformed(
            "FRI-IOR-FIXTURE-016", "terminal polynomial encoding is not canonical"
        )
    table = []
    for raw in _sequence(obj["opening_table"], 8, code="FRI-IOR-FIXTURE-017"):
        entry = _object(raw, ("layer", "opening"), code="FRI-IOR-FIXTURE-017")
        table.append(
            OpeningTableEntry(
                _integer(entry["layer"], 0, 1, code="FRI-IOR-FIXTURE-017"),
                _opening(entry["opening"]),
            )
        )
    selectors = []
    for raw in _sequence(obj["occurrence_selectors"], 4, code="FRI-IOR-FIXTURE-018"):
        item = _object(
            raw,
            ("ordinal", "layer0_opening_index", "layer1_opening_index"),
            code="FRI-IOR-FIXTURE-018",
        )
        selectors.append(
            OccurrenceSelector(
                _integer(item["ordinal"], 0, 3, code="FRI-IOR-FIXTURE-018"),
                _integer(
                    item["layer0_opening_index"], 0, 7, code="FRI-IOR-FIXTURE-018"
                ),
                _integer(
                    item["layer1_opening_index"], 0, 7, code="FRI-IOR-FIXTURE-018"
                ),
            )
        )
    formed = PublicFriProof(
        _cap(obj["cap0"]),
        _cap(obj["cap1"]),
        tuple(_fp2(item, code="FRI-IOR-FIXTURE-016") for item in coefficients),
        _integer(obj["grinding_nonce"], 0, (1 << 32) - 1, code="FRI-IOR-FIXTURE-015"),
        tuple(table),
        tuple(selectors),
    )
    if formed.to_term() != value:
        raise _malformed(
            "FRI-IOR-FIXTURE-019", "public proof is not the exact canonical term"
        )
    return formed


def parse_replay_policy(value: object) -> ResourceLimits:
    obj = _object(
        value, ("schema", "limits", "authority", "claims"), code="FRI-IOR-FIXTURE-020"
    )
    if (
        obj["schema"] != "zkc.native-fri-ior.public-replay-policy.v1"
        or obj["authority"]
        != "repository-frozen-report-local-operational-policy"
        or obj["claims"]
        != {
            "part_of_protocol_semantics": False,
            "proves_resource_optimality": False,
            "semantic_authority": False,
        }
    ):
        raise _malformed(
            "FRI-IOR-FIXTURE-020", "replay policy authority or claims drifted"
        )
    limits = _object(
        obj["limits"],
        tuple(ResourceLimits.__dataclass_fields__),
        code="FRI-IOR-FIXTURE-021",
    )
    return ResourceLimits(
        **{
            name: _integer(limits[name], 0, 1 << 20, code="FRI-IOR-FIXTURE-021")
            for name in limits
        }
    )


def _dependency(value: object) -> DeclaredStrategyDependency:
    obj = _object(
        value,
        ("subject", "authored_at", "declared_read_set"),
        code="FRI-IOR-FIXTURE-022",
    )
    reads = _sequence(obj["declared_read_set"], 8, code="FRI-IOR-FIXTURE-022")
    return DeclaredStrategyDependency(
        _text(obj["subject"], 96, code="FRI-IOR-FIXTURE-022"),
        _integer(obj["authored_at"], 0, 8, code="FRI-IOR-FIXTURE-022"),
        tuple(_text(item, 96, code="FRI-IOR-FIXTURE-022") for item in reads),
    )


def _oracle(value: object) -> LogicalOracle:
    obj = _object(
        value,
        (
            "name",
            "domain",
            "origin",
            "publication_mode",
            "entries",
            "declared_strategy_dependency",
        ),
        code="FRI-IOR-FIXTURE-023",
    )
    domain = (
        D0 if obj["domain"] == D0.name else D1 if obj["domain"] == D1.name else None
    )
    if domain is None:
        raise _malformed(
            "FRI-IOR-FIXTURE-023", "native vector names an unsupported domain"
        )
    entries = []
    for raw in _sequence(obj["entries"], domain.order, code="FRI-IOR-FIXTURE-023"):
        item = _object(raw, ("point", "value"), code="FRI-IOR-FIXTURE-023")
        entries.append(
            OracleEntry(
                Fp(_integer(item["point"], 0, 96, code="FRI-IOR-FIXTURE-023")),
                _fp2(item["value"], code="FRI-IOR-FIXTURE-023"),
            )
        )
    dependency = (
        None
        if obj["declared_strategy_dependency"] is None
        else _dependency(obj["declared_strategy_dependency"])
    )
    try:
        origin = OracleOrigin(obj["origin"])
        publication_mode = OraclePublicationMode(obj["publication_mode"])
    except (TypeError, ValueError) as error:
        raise _malformed(
            "FRI-IOR-FIXTURE-023", "native vector uses an unknown oracle enum"
        ) from error
    return LogicalOracle(
        _text(obj["name"], 32, code="FRI-IOR-FIXTURE-023"),
        domain,
        origin,
        tuple(entries),
        dependency,
        publication_mode,
    )


def parse_public_native_vector(value: object) -> NativeFriTrace:
    obj = _object(
        value,
        (
            "schema",
            "disclosure",
            "profile",
            "initial_oracle",
            "first_challenge",
            "prover_oracle",
            "second_challenge",
            "terminal",
            "query_draws",
            "events",
            "structural_chain",
            "native_trace_id",
        ),
        code="FRI-IOR-FIXTURE-024",
    )
    expected_disclosure = {
        "classification": "declassified-validation-only-complete-trace",
        "permitted_consumers": ["native-execution", "relations-grounding"],
        "forbidden_consumer": "committed-verifier",
        "establishes_confidentiality": False,
    }
    if (
        obj["schema"] != "zkc.native-fri-ior.public-native-vector.v1"
        or obj["disclosure"] != expected_disclosure
        or obj["profile"] != EXACT_PROFILE.to_term()
    ):
        raise _malformed(
            "FRI-IOR-FIXTURE-024",
            "native vector schema, disclosure, or profile drifted",
        )
    first = _object(
        obj["first_challenge"], ("name", "value"), code="FRI-IOR-FIXTURE-025"
    )
    second = _object(
        obj["second_challenge"], ("name", "value"), code="FRI-IOR-FIXTURE-025"
    )
    terminal = _object(
        obj["terminal"],
        ("coefficients", "declared_strategy_dependency"),
        code="FRI-IOR-FIXTURE-026",
    )
    draws = []
    for raw in _sequence(obj["query_draws"], 4, code="FRI-IOR-FIXTURE-027"):
        item = _object(
            raw, ("ordinal", "initial_domain_index"), code="FRI-IOR-FIXTURE-027"
        )
        draws.append(
            RandomQueryDraw(
                _integer(item["ordinal"], 0, 3, code="FRI-IOR-FIXTURE-027"),
                _integer(
                    item["initial_domain_index"], 0, 15, code="FRI-IOR-FIXTURE-027"
                ),
            )
        )
    events = []
    for raw in _sequence(obj["events"], 9, code="FRI-IOR-FIXTURE-028"):
        item = _object(raw, ("index", "kind", "subject"), code="FRI-IOR-FIXTURE-028")
        try:
            kind = NativeEventKind(item["kind"])
        except (TypeError, ValueError) as error:
            raise _malformed(
                "FRI-IOR-FIXTURE-028", "native vector uses an unknown event kind"
            ) from error
        events.append(
            NativeEvent(
                _integer(item["index"], 0, 8, code="FRI-IOR-FIXTURE-028"),
                kind,
                _text(item["subject"], 64, code="FRI-IOR-FIXTURE-028"),
            )
        )
    trace = NativeFriTrace(
        EXACT_PROFILE,
        _oracle(obj["initial_oracle"]),
        FreshChallenge(
            _text(first["name"], 32, code="FRI-IOR-FIXTURE-025"),
            _fp2(first["value"], code="FRI-IOR-FIXTURE-025"),
        ),
        _oracle(obj["prover_oracle"]),
        FreshChallenge(
            _text(second["name"], 32, code="FRI-IOR-FIXTURE-025"),
            _fp2(second["value"], code="FRI-IOR-FIXTURE-025"),
        ),
        TerminalPolynomial(
            tuple(
                _fp2(item, code="FRI-IOR-FIXTURE-026")
                for item in _sequence(
                    terminal["coefficients"], 5, code="FRI-IOR-FIXTURE-026"
                )
            ),
            _dependency(terminal["declared_strategy_dependency"]),
        ),
        tuple(draws),
        tuple(events),
        canonical_structural_fold_chain(),
    )
    if (
        trace.events != canonical_event_log()
        or obj["structural_chain"] != trace.structural_chain.to_term()
        or obj["native_trace_id"] != trace.identity.to_term()
    ):
        raise _malformed(
            "FRI-IOR-FIXTURE-029",
            "native vector event, structural, or identity anchor drifted",
        )
    return trace


@dataclass(frozen=True, slots=True)
class PrivateGenerationInput:
    coefficients: tuple[Fp2, ...]
    initial_layer_salts: tuple[bytes, ...]
    first_fold_layer_salts: tuple[bytes, ...]


def parse_relation_initial_oracle(value: object) -> LogicalOracle:
    """Load the relation-side material independently of construction receipts."""

    obj = _object(
        value,
        ("schema", "authority", "disclosure", "oracle", "nonclaims"),
        code="FRI-IOR-FIXTURE-034",
    )
    disclosure = _object(
        obj["disclosure"],
        ("classification", "contains_real_secret"),
        code="FRI-IOR-FIXTURE-034",
    )
    if (
        obj["schema"] != "zkc.native-fri-ior.relation-initial-oracle.v1"
        or obj["authority"]
        != "owner-relation-grounding-input-not-public-report-input"
        or disclosure
        != {
            "classification": "declassified-public-test-input",
            "contains_real_secret": False,
        }
        or obj["nonclaims"]
        != [
            "does-not-establish-the-statement-to-oracle-predicate",
            "separate-file-supply-does-not-establish-independent-provenance",
        ]
    ):
        raise _malformed(
            "FRI-IOR-FIXTURE-034",
            "relation initial-oracle authority or nonclaims drifted",
        )
    oracle = _oracle(obj["oracle"])
    if (
        oracle.name != INITIAL_ORACLE_NAME
        or oracle.domain != D0
        or oracle.origin is not OracleOrigin.INITIAL_ORACLE
        or oracle.publication_mode is not OraclePublicationMode.LOGICAL_ACCESS
        or oracle.declared_strategy_dependency is not None
    ):
        raise _malformed(
            "FRI-IOR-FIXTURE-034",
            "relation grounding requires the exact initial logical-oracle carrier",
        )
    return oracle


def parse_private_generation(value: object) -> PrivateGenerationInput:
    obj = _object(
        value,
        (
            "schema",
            "authority",
            "coefficients",
            "disclosure",
            "initial_layer_salts",
            "first_fold_layer_salts",
            "nonclaims",
        ),
        code="FRI-IOR-FIXTURE-030",
    )
    disclosure = _object(
        obj["disclosure"],
        ("classification", "contains_real_secret"),
        code="FRI-IOR-FIXTURE-030",
    )
    if (
        obj["schema"] != "zkc.native-fri-ior.private-generation.v1"
        or obj["authority"] != "owner-generation-input-not-public-report-input"
        or disclosure
        != {
            "classification": (
                "declassified-public-test-vector-populates-private-semantic-roles"
            ),
            "contains_real_secret": False,
        }
        or obj["nonclaims"]
        != ["does-not-establish-confidentiality-or-secure-randomness"]
    ):
        raise _malformed(
            "FRI-IOR-FIXTURE-030",
            "owner generation disclosure or authority drifted",
        )
    coefficients = tuple(
        _fp2(item, code="FRI-IOR-FIXTURE-030")
        for item in _sequence(obj["coefficients"], 8, code="FRI-IOR-FIXTURE-030")
    )
    salts0 = tuple(
        _hex(item, 16, code="FRI-IOR-FIXTURE-030")
        for item in _sequence(obj["initial_layer_salts"], 8, code="FRI-IOR-FIXTURE-030")
    )
    salts1 = tuple(
        _hex(item, 16, code="FRI-IOR-FIXTURE-030")
        for item in _sequence(
            obj["first_fold_layer_salts"], 4, code="FRI-IOR-FIXTURE-030"
        )
    )
    if len(coefficients) != 8 or len(salts0) != 8 or len(salts1) != 4:
        raise _malformed(
            "FRI-IOR-FIXTURE-030",
            "private generation vector has the wrong fixed extent",
        )
    return PrivateGenerationInput(coefficients, salts0, salts1)


def parse_negative_proofs(value: object) -> dict[str, PublicFriProof]:
    obj = _object(value, ("schema", "cases", "nonclaims"), code="FRI-IOR-FIXTURE-031")
    if obj["schema"] != "zkc.native-fri-ior.public-negative-proofs.v1" or obj[
        "nonclaims"
    ] != ["these examples do not establish completeness of the refusal taxonomy"]:
        raise _malformed("FRI-IOR-FIXTURE-031", "negative-proof envelope drifted")
    cases = _object(
        obj["cases"],
        ("authenticated-fold-inconsistency", "fold-consistent-terminal-degree-excess"),
        code="FRI-IOR-FIXTURE-032",
    )
    return {name: parse_public_proof(proof) for name, proof in cases.items()}


def parse_expected_projection(value: object) -> dict[str, Any]:
    obj = _object(
        value,
        ("schema", "authority", "projection"),
        code="FRI-IOR-FIXTURE-033",
    )
    if (
        obj["schema"] != "zkc.native-fri-ior.expected-report-projection.v3"
        or obj["authority"] != "regression-golden-not-semantic-or-provenance-authority"
    ):
        raise _malformed(
            "FRI-IOR-FIXTURE-033",
            "expected projection schema or authority is unsupported",
        )
    projection = _object(
        obj["projection"],
        (
            "report_content_id",
            "fixture_ids",
            "validation_source_basis_ids",
            "positive_outcomes",
            "negative_outcomes",
            "analysis_question_count",
        ),
        code="FRI-IOR-FIXTURE-033",
    )
    CanonicalContentId.parse(projection["report_content_id"])
    fixture_ids = _object(
        projection["fixture_ids"],
        (
            "negative_proofs",
            "public_inputs",
            "public_native_vector",
            "public_proof",
            "replay_policy",
            "exact_classical_public_inputs",
            "exact_classical_public_proof",
            "exact_classical_replay_policy",
            "source_ledger",
        ),
        code="FRI-IOR-FIXTURE-033",
    )
    for identity in fixture_ids.values():
        ArtifactContentId.parse(identity)
    bases = _object(
        projection["validation_source_basis_ids"],
        (
            "native",
            "committed",
            "analysis-formation",
            "independent-replay",
            "exact-classical-independent-replay",
            "report",
        ),
        code="FRI-IOR-FIXTURE-033",
    )
    for identity in bases.values():
        ValidationBasisId.parse(identity)
    positive = _object(
        projection["positive_outcomes"],
        (
            "native",
            "committed",
            "independent_replay",
            "reconciliation_equal",
            "exact_classical_independent_replay",
        ),
        code="FRI-IOR-FIXTURE-033",
    )
    if positive["reconciliation_equal"] is not True or any(
        type(positive[name]) is not str
        for name in (
            "native",
            "committed",
            "independent_replay",
            "exact_classical_independent_replay",
        )
    ):
        raise _malformed(
            "FRI-IOR-FIXTURE-033", "expected positive outcomes are malformed"
        )
    negatives = _object(
        projection["negative_outcomes"],
        (
            "authenticated-fold-inconsistency",
            "fold-consistent-terminal-degree-excess",
        ),
        code="FRI-IOR-FIXTURE-033",
    )
    if (
        any(type(code) is not str for code in negatives.values())
        or type(projection["analysis_question_count"]) is not int
    ):
        raise _malformed(
            "FRI-IOR-FIXTURE-033", "expected result coordinates are malformed"
        )
    return obj


__all__ = [
    "LoadedFixture",
    "PrivateGenerationInput",
    "bind_repository_root",
    "load_fixture",
    "parse_expected_projection",
    "parse_negative_proofs",
    "parse_private_generation",
    "parse_relation_initial_oracle",
    "parse_public_inputs",
    "parse_public_native_vector",
    "parse_public_proof",
    "parse_replay_policy",
]
