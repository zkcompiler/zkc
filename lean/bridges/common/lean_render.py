"""Shared rendering and driver support for the Lean bridges.

Every bridge that writes Lean constructor data or runs the compiler and Lean
uses these helpers, so that one escaping policy, one set of bounds checks and
one command log apply everywhere:

* bounded readers for exported JSON (`record`, `nat`, `decimal`, `seq`) and
  the Lean string literal of a UTF-8 string (`text`), with the size limit of
  the format being rendered;
* type renderers for the structured source vocabulary and the constructor
  names of its operations;
* the canonical occurrence-template codec (`decode_tree`, `encode_tree`,
  `origin`) shared by the constructed-participant and program renderers;
* the namespace check, the module-header filter used when several renderings
  share one Lean file, and the command-line skeleton of a renderer;
* the subprocess wrapper with its command log, digests, timestamps, the axiom
  set every kernel check may depend on and the parser of `#print axioms`.

Nothing here assigns meaning to exported data: a renderer is a tested
serialization edge and Lean checks what it produces.
"""

import argparse
import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[3]

# The axioms a kernel-checked bridge theorem may depend on.
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

NAMESPACE = r"(?:[A-Za-z][A-Za-z0-9_]*\.)*[A-Za-z][A-Za-z0-9_]*"

# Lean string escapes. JSON's backspace and form-feed escapes are not Lean
# escapes: every other control character is spelled as a code point.
ESCAPES = {'"': r'\"', '\\': r'\\', '\n': r'\n', '\r': r'\r', '\t': r'\t'}


class Refused(ValueError):
    """Exported data outside the rendered profile; nothing is written."""


def require(condition, message):
    if not condition:
        raise Refused(message)


def record(value, size=None):
    """A JSON array, of exactly `size` items when given."""
    require(isinstance(value, list) and (size is None or len(value) == size),
            "expected an array" if size is None else f"expected array of size {size}")
    return value


def text(value, limit=4096, printable_ascii=False):
    """The Lean string literal of `value`, at most `limit` UTF-8 bytes.

    Each character is rendered once, so a literal backslash cannot become an
    escape prefix. `printable_ascii` restricts the profile to nonempty
    printable ASCII, whose rendering is also its JSON spelling.
    """
    if printable_ascii:
        require(isinstance(value, str) and 1 <= len(value) <= limit
                and all(32 <= ord(char) <= 126 for char in value),
                f"renderer requires nonempty printable ASCII strings of at most {limit} bytes")
    else:
        require(isinstance(value, str) and len(value.encode("utf-8")) <= limit,
                f"expected a UTF-8 string of at most {limit} bytes")

    def character(char):
        if char in ESCAPES:
            return ESCAPES[char]
        if ord(char) < 32 or ord(char) == 127:
            return f"\\u{ord(char):04x}"
        return char
    return '"' + ''.join(character(char) for char in value) + '"'


def nat(value, limit=4096):
    require(type(value) is int and 0 <= value <= limit, "invalid bounded natural")
    return str(value)


def decimal(value, limit=1024):
    """A canonical decimal string below `limit`, as a Lean natural."""
    require(isinstance(value, str) and re.fullmatch(r"0|[1-9][0-9]*", value) is not None
            and int(value) < limit, "invalid canonical decimal")
    return str(int(value))


def seq(values, render=nat, limit=4096):
    require(isinstance(values, list) and len(values) <= limit, "invalid bounded array")
    return "[" + ", ".join(render(value) for value in values) + "]"


def optional(value, render):
    return "none" if value is None else f"some ({render(value)})"


def namespace(name):
    require(isinstance(name, str) and re.fullmatch(NAMESPACE, name) is not None, "invalid Lean namespace")
    return name


# ---------------------------------------------------------------------------
# The structured source vocabulary

# Value types of the structured source format, `["bool"]`, `["index"]` or
# `[tag, domain]`.
TYPE_TAGS = ("field", "vector", "group", "service")


def ty(value, tags=TYPE_TAGS, index=True, string=lambda value: text(value, 512)):
    """The Lean `Ty` of a structured value type. `tags`, `index` and `string`
    select the profile: the scalar profile has no vectors or indices and spells
    domains in printable ASCII."""
    if value == ["bool"]:
        return ".boolean"
    if index and value == ["index"]:
        return ".index"
    tag, domain = record(value, 2)
    require(tag in tags, "unsupported type")
    return f".{tag} {string(domain)}"


# Constructor names of the structured operations, shared by the scalar and the
# structured source formats. One-argument operations name their domain.
UNARY_OPERATIONS = {
    "field.add": "fieldAdd", "field.subtract": "fieldSubtract",
    "field.multiply": "fieldMultiply", "field.equal": "fieldEqual",
    "group.identity": "groupIdentity", "group.add": "groupAdd", "group.equal": "groupEqual",
    "bounded_at": "boundedAt", "call": "call", "apply": "apply", "guard": "guard",
}
NULLARY_OPERATIONS = {
    "bool.and": "booleanAnd", "bool.or": "booleanOr", "bool.xor": "booleanXor",
    "bool.equal": "booleanEqual", "bool.not_equal": "booleanNotEqual",
    "if": "branch", "for": "loop", "for_condition": "loopCondition", "index.equal": "indexEqual",
}
# Operations with two domain or name arguments.
BINARY_OPERATIONS = {
    "field.constant": "fieldConstant", "group.scale": "groupScale",
    "exchange": "exchange", "draw": "draw", "local_call": "localCall",
}
# Every named operation constructor, for profiles that select a subset.
OPERATIONS = {**UNARY_OPERATIONS, **NULLARY_OPERATIONS, **BINARY_OPERATIONS,
              "bool.constant": "booleanConstant", "index.constant": "indexConstant"}

# Scalar calculations of the constructed participant: exported operation name,
# Lean constructor and the sort of both operands.
CALCULATIONS = {
    "algebra.field_add": ("fieldAdd", "field"),
    "algebra.field_subtract": ("fieldSubtract", "field"),
    "algebra.field_multiply": ("fieldMultiply", "field"),
    "algebra.field_equal": ("fieldEqual", "field"),
    "algebra.group_add": ("groupAdd", "group"),
    "algebra.group_equal": ("groupEqual", "group"),
}

# The BLS12-381 scalar modulus bounds canonical field constants.
FIELD_MODULUS = 52435875175126190479447740508185965837690552500527637822603658699938581184513


# ---------------------------------------------------------------------------
# Canonical occurrence templates

TEMPLATE = "zkc.native-origin-template/0"


def decode_tree(data, offset=0, depth=0):
    """Read one tree of the canonical encoding: text (tag 0) or list (tag 1),
    each with an 8-byte little-endian length or count."""
    require(depth <= 16 and offset + 9 <= len(data), "truncated origin")
    tag, count = data[offset], int.from_bytes(data[offset + 1:offset + 9], "little")
    offset += 9
    if tag == 0:
        require(offset + count <= len(data), "truncated origin text")
        return data[offset:offset + count].decode("utf-8"), offset + count
    require(tag == 1 and count <= 64, "invalid origin tag")
    items = []
    for _ in range(count):
        item, offset = decode_tree(data, offset, depth + 1)
        items.append(item)
    return items, offset


def encode_tree(tree):
    if isinstance(tree, str):
        raw = tree.encode("utf-8")
        return b"\0" + len(raw).to_bytes(8, "little") + raw
    return b"\1" + len(tree).to_bytes(8, "little") + b"".join(encode_tree(item) for item in tree)


def template(hex_text):
    """Decode an occurrence template, requiring its canonical encoding."""
    require(isinstance(hex_text, str) and re.fullmatch(r"(?:[0-9a-f]{2})+", hex_text) is not None
            and len(hex_text) <= 4096, "origin must be lowercase even-length hex")
    data = bytes.fromhex(hex_text)
    tree, end = decode_tree(data)
    require(end == len(data), "trailing origin bytes")
    require(encode_tree(tree).hex() == hex_text, "noncanonical origin encoding")
    require(isinstance(tree, list) and len(tree) == 5 and tree[0] == TEMPLATE, "not an origin template")
    return tree


def origin_step(value):
    require(isinstance(value, list) and len(value) == 3 and value[0] in ("apply", "repeat")
            and all(isinstance(item, str) for item in value), "invalid origin step")
    return f"⟨{text(value[0])}, {text(value[1])}, {text(value[2])}⟩"


def origin(hex_text):
    """The Lean occurrence template of a canonical template encoding."""
    _, entry, steps, coordinates, event = template(hex_text)
    require(isinstance(entry, str) and isinstance(steps, list) and len(steps) <= 64 and coordinates == [],
            "invalid origin path")
    require(isinstance(event, list) and event and all(isinstance(item, str) for item in event), "invalid origin event")
    return f"⟨{text(entry)}, {seq(steps, origin_step)}, {seq(event, text)}⟩"


# ---------------------------------------------------------------------------
# Modules and command lines

def strip_header(source):
    """Drop a rendered module's header, so several renderings share one Lean file."""
    return "\n".join(line for line in source.splitlines()
                     if line not in ("module", "@[expose] public section")
                     and not line.startswith("public import "))


def render_main(render, description, read=None):
    """The command line of a renderer: INPUT OUTPUT --namespace NAME."""
    parser = argparse.ArgumentParser(description=description)
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--namespace", required=True)
    args = parser.parse_args()
    data = json.loads(args.input.read_text(encoding="utf-8")) if read is None else read(args.input)
    args.output.write_text(render(data, args.namespace), encoding="utf-8")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def file_digest(path):
    return digest(Path(path).read_bytes())


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


class CheckFailed(RuntimeError):
    """A named check of a bridge driver failed."""


class Runner:
    """Runs commands and records each one, and records named checks.

    A command's record keeps its arguments, directory, exit status, times, the
    digest of its output and the tail of its diagnostics. A failed check stops
    the driver; the log of what ran so far is kept for the report.
    """

    def __init__(self):
        self.commands = []
        self.checks = []

    def run(self, arguments, *, cwd=ROOT, expect=0, name=None):
        started = now()
        arguments = [str(argument) for argument in arguments]
        result = subprocess.run(arguments, cwd=cwd, capture_output=True, text=True, check=False)
        output = result.stdout
        self.commands.append(dict(name=name, arguments=arguments, cwd=str(cwd), exit=result.returncode,
                                  started=started, finished=now(),
                                  stdout_sha256=digest(output.encode()),
                                  stderr=result.stderr[-4000:]))
        if expect is not None and result.returncode != expect:
            raise CheckFailed(f"{name or arguments[0]} exited {result.returncode}:\n"
                              f"{output[-2000:]}{result.stderr[-2000:]}")
        return result

    def check(self, name, passed, detail=""):
        self.checks.append(dict(name=name, passed=bool(passed), detail="" if passed else detail))
        if not passed:
            raise CheckFailed(f"check failed: {name} {detail}")


def printed_axioms(stdout):
    """The axioms of each declaration in `#print axioms` output."""
    found = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", stdout):
        found[name] = sorted(axiom.strip() for axiom in axioms.split(",") if axiom.strip())
    for name in re.findall(r"'([^']+)' does not depend on any axioms", stdout):
        found[name] = []
    return found


def axioms_allowed(stdout, name):
    """Whether `#print axioms name` was printed and stays within `ALLOWED_AXIOMS`."""
    found = printed_axioms(stdout)
    return name in found and set(found[name]) <= ALLOWED_AXIOMS


def regenerate(runner, path, generated, write, owned=True):
    """Compare (or with `write`, first rewrite) one generated file."""
    path = Path(path)
    if write and owned:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(generated, encoding="utf-8")
    current = path.read_text(encoding="utf-8") if path.exists() else None
    label = path.relative_to(ROOT) if path.is_relative_to(ROOT) else path
    runner.check(f"regenerated:{label}", current == generated, "committed file differs from the fresh output")
