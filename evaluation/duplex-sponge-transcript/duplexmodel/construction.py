"""Closed finite duplex-sponge transcript-construction declaration."""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from itertools import product
from typing import Any

from .diagnostics import (
    AdmissionRefusal,
    DeterministicLimitExceeded,
    MalformedInput,
    SourceApplicabilityRefusal,
)
from .terms import exact_keys, exact_nat, semantic_id
from .transition import (
    ALPHABET_SIZE,
    CAPACITY,
    RATE,
    STATE_WIDTH,
    ForwardOracle,
    affine_forward_oracle,
    all_states,
    symbols,
)


CONSTRUCTION_SCHEMA = "zkc.duplex-sponge-transcript.construction.v1"
CORE_SCHEMA = "zkc.duplex-sponge-transcript.core-view.v1"
ABSORB_LAW = (
    "Absorb resets iS to rate, permutes only before a symbol at full iA, "
    "then overwrites"
)
SQUEEZE_LAW = (
    "Squeeze(0) is identity; positive Squeeze resets iA and continues one output stream"
)

CONSTRUCTION_KEYS = {
    "kind",
    "core_id",
    "alphabet_size",
    "rate",
    "capacity",
    "salt_length",
    "instance_bit_bound",
    "instance_codec",
    "provider_interface",
    "provider_semantics",
    "absorption_mode",
    "start_law",
    "absorb_law",
    "squeeze_law",
    "message_codecs",
    "challenge_decoders",
}

OCCURRENCE_KINDS = {"ProverMessage", "Challenge"}
MESSAGE_TYPES = {"SigmaPair", "Unit", "SigmaTriple"}
CHALLENGE_TYPES = {"SigmaPair", "SigmaScalar", "SigmaQuad"}

MESSAGE_CODEC_ALGORITHMS = {
    "PairIdentity": "TupleSymbolsInOrder",
    "UnitEmpty": "UnitToEmptySymbols",
    "TripleIdentity": "TupleSymbolsInOrder",
    "PairFirstDuplicate": "DuplicateFirstTupleSymbol",
    "PairDropZero": "DropLeadingZeroSymbol",
}
CHALLENGE_DECODER_ALGORITHMS = {
    "PairIdentity": "SymbolsToTupleInOrder",
    "ScalarIdentity": "OnlySymbol",
    "QuadIdentity": "SymbolsToTupleInOrder",
    "PartialScalar": "OnlySymbolExceptLastUndefined",
    "ConstantScalar": "ConstantZero",
    "EmptyToConstantScalar": "EmptySymbolsToConstantZero",
    "PairAsScalar": "FirstSymbolOnly",
}
MAX_FINITE_DECODER_INPUTS = ALPHABET_SIZE**6


@dataclass(frozen=True)
class Occurrence:
    kind: str
    name: str
    value_type: str

    def to_term(self) -> dict[str, str]:
        return {"kind": self.kind, "name": self.name, "value_type": self.value_type}


@dataclass(frozen=True)
class InitialBinding:
    kind: str
    name: str
    value_type: str

    def to_term(self) -> dict[str, str]:
        return {"kind": self.kind, "name": self.name, "value_type": self.value_type}


@dataclass(frozen=True)
class CoreView:
    initial_bindings: tuple[InitialBinding, ...]
    schedule: tuple[Occurrence, ...]

    def to_term(self) -> dict[str, object]:
        return {
            "schema": CORE_SCHEMA,
            "initial_bindings": [item.to_term() for item in self.initial_bindings],
            "schedule": [item.to_term() for item in self.schedule],
        }


@dataclass(frozen=True)
class MessageCodec:
    occurrence: str
    codec: str
    encoded_length: int

    def to_term(self) -> dict[str, object]:
        return {
            "occurrence": self.occurrence,
            "codec": self.codec,
            "algorithm": MESSAGE_CODEC_ALGORITHMS[self.codec],
            "encoded_length": self.encoded_length,
        }


@dataclass(frozen=True)
class ChallengeDecoder:
    occurrence: str
    decoder: str
    squeeze_length: int

    def to_term(self) -> dict[str, object]:
        return {
            "occurrence": self.occurrence,
            "decoder": self.decoder,
            "algorithm": CHALLENGE_DECODER_ALGORITHMS[self.decoder],
            "squeeze_length": self.squeeze_length,
        }


@dataclass(frozen=True)
class InstanceCodec:
    fields: tuple[str, ...]

    def to_term(self) -> dict[str, object]:
        return {
            "kind": "OrderedStatementOctets",
            "source_type": "StatementPair",
            "binding": "statement",
            "fields": list(self.fields),
            "output_length_octets": 2,
        }


@dataclass(frozen=True)
class ProviderSemantics:
    start_matrix: tuple[tuple[int, ...], ...]
    start_offset: tuple[int, ...]
    permutation_matrix: tuple[tuple[int, ...], ...]
    permutation_offset: tuple[int, ...]

    def to_term(self) -> dict[str, object]:
        return {
            "kind": "AffineModuloAlphabet",
            "start_hash": {
                "input_width_octets": 2,
                "matrix": [list(row) for row in self.start_matrix],
                "offset": list(self.start_offset),
            },
            "permutation": {
                "state_width": STATE_WIDTH,
                "matrix": [list(row) for row in self.permutation_matrix],
                "offset": list(self.permutation_offset),
            },
        }

    def forward_oracle(self) -> ForwardOracle:
        return affine_forward_oracle(
            self.start_matrix,
            self.start_offset,
            self.permutation_matrix,
            self.permutation_offset,
        )


@dataclass(frozen=True)
class TranscriptConstruction:
    core: CoreView
    salt_length: int
    instance_bit_bound: int
    instance_codec: InstanceCodec
    provider_interface: tuple[str, ...]
    provider_semantics: ProviderSemantics
    message_codecs: tuple[MessageCodec, ...]
    challenge_decoders: tuple[ChallengeDecoder, ...]

    def body(self) -> dict[str, object]:
        return {
            "kind": "DuplexSpongeTranscriptConstruction",
            "core_id": core_id(self.core),
            "alphabet_size": ALPHABET_SIZE,
            "rate": RATE,
            "capacity": CAPACITY,
            "salt_length": self.salt_length,
            "instance_bit_bound": self.instance_bit_bound,
            "instance_codec": self.instance_codec.to_term(),
            "provider_interface": list(self.provider_interface),
            "provider_semantics": self.provider_semantics.to_term(),
            "absorption_mode": "Overwrite",
            "start_law": "Start_h(x)=((zero^rate,h(x)),0,rate)",
            "absorb_law": ABSORB_LAW,
            "squeeze_law": SQUEEZE_LAW,
            "message_codecs": [item.to_term() for item in self.message_codecs],
            "challenge_decoders": [item.to_term() for item in self.challenge_decoders],
        }


def _nonempty_name(value: Any, *, where: str) -> str:
    if type(value) is not str or not value or len(value) > 96:
        raise MalformedInput(f"{where} must be a bounded nonempty name")
    return value


def _parse_occurrence(value: Any, index: int) -> Occurrence:
    obj = exact_keys(value, {"kind", "name", "value_type"}, where=f"schedule[{index}]")
    kind = _nonempty_name(obj["kind"], where=f"schedule[{index}].kind")
    name = _nonempty_name(obj["name"], where=f"schedule[{index}].name")
    value_type = _nonempty_name(
        obj["value_type"], where=f"schedule[{index}].value_type"
    )
    if kind not in OCCURRENCE_KINDS:
        raise AdmissionRefusal("unsupported occurrence kind in construction Core view")
    if kind == "ProverMessage" and value_type not in MESSAGE_TYPES:
        raise AdmissionRefusal(
            "prover-message occurrence has an unsupported value type"
        )
    if kind == "Challenge" and value_type not in CHALLENGE_TYPES:
        raise AdmissionRefusal("challenge occurrence has an unsupported value type")
    return Occurrence(kind, name, value_type)


def parse_core(value: Any) -> CoreView:
    obj = exact_keys(
        value,
        {"schema", "initial_bindings", "schedule"},
        where="Core view",
    )
    if obj["schema"] != CORE_SCHEMA or type(obj["schedule"]) is not list:
        raise MalformedInput("Core view schema or schedule differs")
    if type(obj["initial_bindings"]) is not list or len(obj["initial_bindings"]) != 1:
        raise AdmissionRefusal("finite source Core requires one Statement binding")
    binding_obj = exact_keys(
        obj["initial_bindings"][0],
        {"kind", "name", "value_type"},
        where="initial Statement binding",
    )
    if binding_obj != {
        "kind": "Statement",
        "name": "statement",
        "value_type": "StatementPair",
    }:
        raise AdmissionRefusal("finite source Core Statement binding differs")
    bindings = (InitialBinding("Statement", "statement", "StatementPair"),)
    schedule = tuple(
        _parse_occurrence(item, index) for index, item in enumerate(obj["schedule"])
    )
    if not schedule or len(schedule) > 16:
        raise AdmissionRefusal(
            "Core view schedule is empty or exceeds its finite bound"
        )
    names = [item.name for item in schedule]
    if len(names) != len(set(names)):
        raise AdmissionRefusal("Core occurrence names must be unique")
    if tuple(item.kind for item in schedule) != tuple(
        "ProverMessage" if index % 2 == 0 else "Challenge"
        for index in range(len(schedule))
    ):
        raise AdmissionRefusal(
            "finite source Core must alternate prover messages and challenges"
        )
    if schedule[-1].kind != "Challenge":
        raise AdmissionRefusal(
            "finite source Core must include its final verifier challenge"
        )
    return CoreView(bindings, schedule)


def _parse_message_codec(value: Any, index: int) -> MessageCodec:
    obj = exact_keys(
        value,
        {"occurrence", "codec", "algorithm", "encoded_length"},
        where=f"message_codecs[{index}]",
    )
    codec = _nonempty_name(obj["codec"], where="message codec name")
    if MESSAGE_CODEC_ALGORITHMS.get(codec) != obj["algorithm"]:
        raise AdmissionRefusal("message codec algorithm declaration differs")
    return MessageCodec(
        _nonempty_name(obj["occurrence"], where="message codec occurrence"),
        codec,
        exact_nat(obj["encoded_length"], maximum=16, where="message encoded length"),
    )


def _parse_challenge_decoder(value: Any, index: int) -> ChallengeDecoder:
    obj = exact_keys(
        value,
        {"occurrence", "decoder", "algorithm", "squeeze_length"},
        where=f"challenge_decoders[{index}]",
    )
    decoder = _nonempty_name(obj["decoder"], where="challenge decoder name")
    if CHALLENGE_DECODER_ALGORITHMS.get(decoder) != obj["algorithm"]:
        raise AdmissionRefusal("challenge decoder algorithm declaration differs")
    return ChallengeDecoder(
        _nonempty_name(obj["occurrence"], where="challenge decoder occurrence"),
        decoder,
        exact_nat(obj["squeeze_length"], maximum=16, where="challenge squeeze length"),
    )


def _matrix(
    value: Any, rows: int, columns: int, *, where: str
) -> tuple[tuple[int, ...], ...]:
    if type(value) is not list or len(value) != rows:
        raise MalformedInput(f"{where} has the wrong row count")
    parsed: list[tuple[int, ...]] = []
    for row_index, row in enumerate(value):
        if type(row) is not list or len(row) != columns:
            raise MalformedInput(f"{where}[{row_index}] has the wrong column count")
        parsed.append(
            tuple(
                exact_nat(
                    item,
                    maximum=ALPHABET_SIZE - 1,
                    where=f"{where}[{row_index}][{column_index}]",
                )
                for column_index, item in enumerate(row)
            )
        )
    return tuple(parsed)


def _vector(value: Any, length: int, *, where: str) -> tuple[int, ...]:
    if type(value) is not list or len(value) != length:
        raise MalformedInput(f"{where} has the wrong length")
    return tuple(
        exact_nat(item, maximum=ALPHABET_SIZE - 1, where=f"{where}[{index}]")
        for index, item in enumerate(value)
    )


def _parse_instance_codec(value: Any) -> InstanceCodec:
    obj = exact_keys(
        value,
        {"kind", "source_type", "binding", "fields", "output_length_octets"},
        where="instance codec",
    )
    if (
        obj["kind"] != "OrderedStatementOctets"
        or obj["source_type"] != "StatementPair"
        or obj["binding"] != "statement"
        or obj["output_length_octets"] != 2
    ):
        raise AdmissionRefusal("instance projection algorithm differs")
    if (
        type(obj["fields"]) is not list
        or len(obj["fields"]) != 2
        or obj["fields"] != ["first", "second"]
        or any(type(field) is not str for field in obj["fields"])
    ):
        raise AdmissionRefusal("instance projection fields must be an exact ordering")
    return InstanceCodec(tuple(obj["fields"]))


def _parse_provider_semantics(value: Any) -> ProviderSemantics:
    obj = exact_keys(
        value,
        {"kind", "start_hash", "permutation"},
        where="provider semantics",
    )
    if obj["kind"] != "AffineModuloAlphabet":
        raise AdmissionRefusal("provider algorithm kind differs")
    start_hash = exact_keys(
        obj["start_hash"],
        {"input_width_octets", "matrix", "offset"},
        where="provider start hash",
    )
    if start_hash["input_width_octets"] != 2:
        raise AdmissionRefusal("provider Start hash input width differs")
    permutation = exact_keys(
        obj["permutation"],
        {"state_width", "matrix", "offset"},
        where="provider permutation",
    )
    if permutation["state_width"] != STATE_WIDTH:
        raise AdmissionRefusal("provider permutation state width differs")
    provider = ProviderSemantics(
        _matrix(start_hash["matrix"], CAPACITY, 2, where="Start matrix"),
        _vector(start_hash["offset"], CAPACITY, where="Start offset"),
        _matrix(
            permutation["matrix"],
            STATE_WIDTH,
            STATE_WIDTH,
            where="permutation matrix",
        ),
        _vector(
            permutation["offset"],
            STATE_WIDTH,
            where="permutation offset",
        ),
    )
    return provider


def message_domain(value_type: str) -> tuple[object, ...]:
    alphabet = range(ALPHABET_SIZE)
    if value_type == "SigmaPair":
        return tuple(product(alphabet, repeat=2))
    if value_type == "Unit":
        return (None,)
    if value_type == "SigmaTriple":
        return tuple(product(alphabet, repeat=3))
    raise AdmissionRefusal("unknown message value type")


def challenge_domain(value_type: str) -> tuple[object, ...]:
    alphabet = range(ALPHABET_SIZE)
    if value_type == "SigmaPair":
        return tuple(product(alphabet, repeat=2))
    if value_type == "SigmaScalar":
        return tuple(alphabet)
    if value_type == "SigmaQuad":
        return tuple(product(alphabet, repeat=4))
    raise AdmissionRefusal("unknown challenge value type")


def encode_message(codec: str, value_type: str, value: object) -> tuple[int, ...]:
    if value not in message_domain(value_type):
        raise MalformedInput("prover message is outside its declared finite type")
    if codec == "PairIdentity" and value_type == "SigmaPair":
        return tuple(value)  # type: ignore[arg-type]
    if codec == "UnitEmpty" and value_type == "Unit":
        return ()
    if codec == "TripleIdentity" and value_type == "SigmaTriple":
        return tuple(value)  # type: ignore[arg-type]
    if codec == "PairFirstDuplicate" and value_type == "SigmaPair":
        pair = tuple(value)  # type: ignore[arg-type]
        return pair[0], pair[0]
    if codec == "PairDropZero" and value_type == "SigmaPair":
        pair = tuple(value)  # type: ignore[arg-type]
        return (pair[1],) if pair[0] == 0 else pair
    raise AdmissionRefusal("message codec is unsupported for the declared type")


def decode_challenge(decoder: str, value_type: str, data: tuple[int, ...]) -> object:
    data = symbols(data, where="challenge decoder input")
    if decoder == "EmptyToConstantScalar" and value_type == "SigmaScalar" and not data:
        return 0
    if decoder == "PairIdentity" and value_type == "SigmaPair" and len(data) == 2:
        return data
    if decoder == "ScalarIdentity" and value_type == "SigmaScalar" and len(data) == 1:
        return data[0]
    if decoder == "QuadIdentity" and value_type == "SigmaQuad" and len(data) == 4:
        return data
    if decoder == "PartialScalar" and value_type == "SigmaScalar" and len(data) == 1:
        if data[0] == ALPHABET_SIZE - 1:
            raise MalformedInput("partial decoder is undefined at its last symbol")
        return data[0]
    if decoder == "ConstantScalar" and value_type == "SigmaScalar" and len(data) == 1:
        return 0
    if decoder == "PairAsScalar" and value_type == "SigmaPair" and len(data) == 2:
        return data[0]
    raise AdmissionRefusal("challenge decoder is unsupported for the declared type")


def _admit_total_fixed_message_codec(
    decl: MessageCodec,
    occurrence: Occurrence,
) -> None:
    for value in message_domain(occurrence.value_type):
        encoded = encode_message(decl.codec, occurrence.value_type, value)
        if len(encoded) != decl.encoded_length:
            raise AdmissionRefusal("message codec violates its exact encoded length")


def decoder_bias(decl: ChallengeDecoder, occurrence: Occurrence) -> dict[str, int]:
    source_size = ALPHABET_SIZE**decl.squeeze_length
    if source_size > MAX_FINITE_DECODER_INPUTS:
        raise DeterministicLimitExceeded(
            "finite challenge-decoder enumeration limit exhausted"
        )
    target = challenge_domain(occurrence.value_type)
    counts: Counter[object] = Counter()
    for data in product(range(ALPHABET_SIZE), repeat=decl.squeeze_length):
        try:
            decoded = decode_challenge(decl.decoder, occurrence.value_type, data)
        except (AdmissionRefusal, MalformedInput) as error:
            raise SourceApplicabilityRefusal(
                "challenge decoder is not total"
            ) from error
        if decoded not in target:
            raise SourceApplicabilityRefusal(
                "challenge decoder returned the wrong value type"
            )
        counts[decoded] += 1
    # Total variation distance is represented exactly as numerator/denominator.
    # 1/2 sum_y |count_y/|source| - 1/|target||.
    numerator = sum(abs(counts[value] * len(target) - source_size) for value in target)
    denominator = 2 * source_size * len(target)
    return {"numerator": numerator, "denominator": denominator}


def finite_source_applicability(
    construction: TranscriptConstruction,
) -> dict[str, object]:
    """Check finite assumptions required by the selected duplex source.

    These checks do not define generic PIR structural admission.  They are
    exhaustive only for this closed finite carrier.
    """

    oracle = construction.provider_semantics.forward_oracle()
    provider_outputs = {oracle.permutation(tuple(state)) for state in all_states()}
    expected_states = ALPHABET_SIZE**STATE_WIDTH
    if len(provider_outputs) != expected_states:
        raise SourceApplicabilityRefusal(
            "declared provider is not a permutation on the finite carrier"
        )
    occurrences = {item.name: item for item in construction.core.schedule}
    codec_checks: dict[str, dict[str, int | bool]] = {}
    for declaration in construction.message_codecs:
        occurrence = occurrences[declaration.occurrence]
        images = {
            encode_message(declaration.codec, occurrence.value_type, value)
            for value in message_domain(occurrence.value_type)
        }
        domain_size = len(message_domain(occurrence.value_type))
        if len(images) != domain_size:
            raise SourceApplicabilityRefusal(
                "message codec is not injective for the finite source profile"
            )
        codec_checks[declaration.occurrence] = {
            "domain_size": domain_size,
            "image_size": len(images),
            "injective": True,
        }
    decoder_biases = {
        declaration.occurrence: decoder_bias(
            declaration, occurrences[declaration.occurrence]
        )
        for declaration in construction.challenge_decoders
    }
    return {
        "provider_states_checked": expected_states,
        "message_codecs": codec_checks,
        "challenge_decoder_biases": decoder_biases,
    }


def parse_construction(value: Any) -> TranscriptConstruction:
    outer = exact_keys(
        value, {"schema", "core", "construction"}, where="construction fixture"
    )
    if outer["schema"] != CONSTRUCTION_SCHEMA:
        raise MalformedInput("construction fixture schema differs")
    core = parse_core(outer["core"])
    obj = exact_keys(outer["construction"], CONSTRUCTION_KEYS, where="construction")
    expected_scalars = {
        "kind": "DuplexSpongeTranscriptConstruction",
        "alphabet_size": ALPHABET_SIZE,
        "rate": RATE,
        "capacity": CAPACITY,
        "absorption_mode": "Overwrite",
        "start_law": "Start_h(x)=((zero^rate,h(x)),0,rate)",
        "absorb_law": ABSORB_LAW,
        "squeeze_law": SQUEEZE_LAW,
    }
    for key, expected in expected_scalars.items():
        if obj[key] != expected:
            raise AdmissionRefusal(
                f"construction {key} differs from the selected source law"
            )
    if obj["core_id"] != core_id(core):
        raise AdmissionRefusal(
            "construction names a Core other than its exact supplied view"
        )
    salt_length = exact_nat(obj["salt_length"], maximum=16, where="salt length")
    if salt_length == 0:
        raise AdmissionRefusal("finite source profile requires a nonempty salt")
    instance_bit_bound = exact_nat(
        obj["instance_bit_bound"], maximum=16, where="instance bit bound"
    )
    instance_codec = _parse_instance_codec(obj["instance_codec"])
    if instance_bit_bound < 2 * 8:
        raise AdmissionRefusal(
            "instance_bit_bound is smaller than the fixed instance projection"
        )
    if obj["provider_interface"] != ["StartHash", "ForwardPermutation"]:
        raise AdmissionRefusal("execution provider exposes the wrong exact interface")
    provider_semantics = _parse_provider_semantics(obj["provider_semantics"])
    if (
        type(obj["message_codecs"]) is not list
        or type(obj["challenge_decoders"]) is not list
    ):
        raise MalformedInput("construction mappings must be ordered lists")
    message_codecs = tuple(
        _parse_message_codec(item, index)
        for index, item in enumerate(obj["message_codecs"])
    )
    challenge_decoders = tuple(
        _parse_challenge_decoder(item, index)
        for index, item in enumerate(obj["challenge_decoders"])
    )
    messages = tuple(item for item in core.schedule if item.kind == "ProverMessage")
    challenges = tuple(item for item in core.schedule if item.kind == "Challenge")
    if tuple(item.occurrence for item in message_codecs) != tuple(
        item.name for item in messages
    ):
        raise AdmissionRefusal(
            "message-codec map is not exact, total, and schedule ordered"
        )
    if tuple(item.occurrence for item in challenge_decoders) != tuple(
        item.name for item in challenges
    ):
        raise AdmissionRefusal(
            "challenge-decoder map is not exact, total, and schedule ordered"
        )
    for declaration, occurrence in zip(message_codecs, messages, strict=True):
        _admit_total_fixed_message_codec(declaration, occurrence)
    construction = TranscriptConstruction(
        core,
        salt_length,
        instance_bit_bound,
        instance_codec,
        tuple(obj["provider_interface"]),
        provider_semantics,
        message_codecs,
        challenge_decoders,
    )
    # The reconstructed body must reproduce the decoded declaration exactly.
    if construction.body() != obj:
        raise AdmissionRefusal(
            "construction declaration is not its canonical reconstructed body"
        )
    return construction


def core_id(core: CoreView) -> str:
    return semantic_id("pir.interactive-core", core.to_term())


def construction_id(construction: TranscriptConstruction) -> str:
    return semantic_id("pir.transcript-construction", construction.body())


def protocol_id(construction: TranscriptConstruction, interpretation: str) -> str:
    if interpretation == "Fresh":
        body = {"core_id": core_id(construction.core), "interpretation": "Fresh"}
    elif interpretation == "DuplexSponge":
        body = {
            "core_id": core_id(construction.core),
            "interpretation": "FiatShamir",
            "construction_id": construction_id(construction),
        }
    else:
        raise AdmissionRefusal("unsupported finite challenge interpretation")
    return semantic_id("pir.protocol", body)


def construction_codec_biases(
    construction: TranscriptConstruction,
) -> dict[str, dict[str, int]]:
    occurrences = {item.name: item for item in construction.core.schedule}
    return {
        declaration.occurrence: decoder_bias(
            declaration, occurrences[declaration.occurrence]
        )
        for declaration in construction.challenge_decoders
    }
