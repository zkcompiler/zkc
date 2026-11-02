"""The strict reader of `zkc.native-proof-policy/0` shared by every bridge.

The [deployment policy](../../../docs/spec/formats/proof.md#deployment-policy-and-descriptor)
is one exact twelve-field array:

    ["zkc.native-proof-policy/0", entry, producer, validator, acceptance,
     suite, services, public_inputs, [[query_site, delivery_site], ...], format,
     construction, [[query_site, difficulty], ...]]

`decode` checks the version, the arity, the kind of every field, canonical
decimal indices below 1024, strictly increasing service and public input
indices, the draw and gate rows, and the construction profile the fields
select. A consumer then states which profiles it supports and refuses the
others; it never indexes the raw array.
"""

from dataclasses import dataclass
import re

from bridges.common.lean_render import require

VERSION = "zkc.native-proof-policy/0"
FORMATS = ("zkc.framed/0", "raw.bytes/0")
INDEX = re.compile(r"0|[1-9][0-9]{0,3}")
INDEX_LIMIT = 1024
DRAW_LIMIT = 64
GATE_LIMIT = 64

# The construction profiles a policy selects.
AUTHORED = "authored"
NATIVE = "native"
PROGRAMMABLE = "programmable"


@dataclass(frozen=True)
class Policy:
    """A decoded policy: its fields and the construction profile they select."""
    entry: str
    producer: str
    validator: str
    acceptance: int
    suite: str
    services: tuple
    public: tuple
    draws: tuple
    format: str
    construction: str
    gates: tuple
    profile: str


def index(value, what):
    require(isinstance(value, str) and INDEX.fullmatch(value) is not None and int(value) < INDEX_LIMIT,
            f"policy {what}: expected a canonical decimal index below {INDEX_LIMIT}")
    return int(value)


def increasing(values, what):
    require(isinstance(values, list), f"policy {what}: expected an array")
    decoded = [index(value, what) for value in values]
    require(all(a < b for a, b in zip(decoded, decoded[1:])), f"policy {what}: expected strictly increasing indices")
    return tuple(decoded)


def site(value, what):
    require(isinstance(value, str) and value, f"policy {what}: expected a nonempty site")
    return value


def decode(value):
    """Check a policy array and return its decoded fields and profile."""
    require(isinstance(value, list) and len(value) == 12 and value[0] == VERSION,
            f"expected a {VERSION} array of size 12")
    (_, entry, producer, validator, acceptance, suite, services, public, draws, framing, construction,
     gates) = value
    for name, item in (("entry", entry), ("producer", producer), ("validator", validator)):
        require(isinstance(item, str) and item, f"policy {name}: expected a nonempty string")
    require(isinstance(suite, str), "policy suite: expected a string")
    require(isinstance(construction, str), "policy construction: expected a string")
    require(framing in FORMATS, "policy format: expected zkc.framed/0 or raw.bytes/0")
    require(isinstance(draws, list) and len(draws) <= DRAW_LIMIT, "policy draws: expected at most 64 rows")
    pairs = []
    for row in draws:
        require(isinstance(row, list) and len(row) == 2, "policy draws: expected [query, delivery] rows")
        pairs.append((site(row[0], "draw query"), site(row[1], "draw delivery")))
    require(isinstance(gates, list) and len(gates) <= GATE_LIMIT, "policy gates: expected an array")
    queries = [query for query, _ in pairs]
    rows = []
    for row in gates:
        require(isinstance(row, list) and len(row) == 2, "policy gates: expected [query, difficulty] rows")
        query = site(row[0], "gate query")
        require(query in queries, "policy gates: a gate selects no draw query")
        difficulty = row[1]
        require(isinstance(difficulty, str) and INDEX.fullmatch(difficulty) is not None and int(difficulty) <= 64,
                "policy gates: expected a canonical decimal difficulty from 0 through 64")
        rows.append((query, int(difficulty)))
    require(len({query for query, _ in rows}) == len(rows), "policy gates: duplicate gate site")
    selected = increasing(services, "services")
    published = increasing(public, "public inputs")
    if construction:
        profile = PROGRAMMABLE
        require(selected, "policy: a programmable construction selects a service")
    elif suite:
        profile = NATIVE
        require(len(selected) == 1 and pairs, "policy: a native construction selects one service and 1-64 draws")
    else:
        profile = AUTHORED
        require(not selected and not pairs, "policy: an authored policy selects a challenge replacement")
    require(profile == NATIVE or not rows, "policy gates: only a native construction selects gates")
    return Policy(entry, producer, validator, index(acceptance, "acceptance"), suite, selected, published,
                  tuple(pairs), framing, construction, tuple(rows), profile)
