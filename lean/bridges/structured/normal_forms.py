#!/usr/bin/env python3
"""Generate participant normal forms of an admitted structured unit as Lean source.

A request (TOML) names a retained snapshot, the typed bodies to read and, for
each role, which inputs it holds. The generator walks the exported
instructions at that role, following the participant rules, and writes:

  * site constants named from the source labels;
  * positional input builders and role-local state embeddings;
  * one normal-form process per role: the ordered actions, the values computed
    on the way, guards as conditionals and missing inputs as stops;
  * the process equation of each normal form, with its proof;
  * reply scripts and the observed run of each root role;
  * for a selected contract clause, the relation binding, its argument
    builder, the formula's process and the observed decision;
  * for a body that applies other protocols, the callee's generated normal
    form at the application's child context with its input and output masks,
    and the role's invocation at any caller context;
  * named positions of carried repeat slots and of the return order;
  * a typed body whose repeats, nested ones included, run named callbacks
    (`[bodies]` with `callbacks`: each callback's name and a source label one
    of its own actions carries), with each repeat's static maximum named and
    the admitted declaration's raw equation.

The output is ordinary Lean source. Every definition and equation is
elaborated and checked by the kernel, so a generator error, a stale request or
a changed program is reported as a failed equation rather than trusted. Root
equations are definitional. Equations over a shared typed body (for every unit
whose checked body it is) are proved by explicit operation steps that use the
helper laws named in the request. A request may instead ask for normal-form
proofs: each equation is then an instance of the normalizer's soundness
theorem, with the form the compiled normalizer prints as a literal that the
kernel checks.

Within a body, a repeat whose callback the request states over (a `[[shared]]`
entry whose `repeat` names it) may stand anywhere: its returned state is bound
like an owned call's tuple. Applications may stand inside a repeat callback. A
strict use of a component read from a bound tuple splits on its presence as on
an optional input. A role's `strict` list (or `*` for every owned call without
a law) keeps those owned calls as the helper's own invocation on present
arguments, so their results are present and later uses need no split; an
application entry's `results` names the callee's results by position. A
callback role with `fold = true` also gets `<role>_fold`: the repeat on an
admitted count is the fold of the role's normal form over the iteration indices.

Usage, from the repository root:
  python3 lean/bridges/structured/normal_forms.py REQUEST.toml [--check]

`--check` compares the generated module with the existing output file and
fails when they differ, without writing it.
"""

import argparse
import json
import os
import re
import subprocess
import sys
import tomllib
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]


class GeneratorError(Exception):
    """The request or the retained unit is outside the supported fragment."""


# ---------------------------------------------------------------------------
# Types

def lean_domain(domain):
    return {"bls12-381.fr": "scalarDomain", "bls12-381.g1": "groupDomain"}.get(domain, json.dumps(domain))


def lean_ty(wire, literal=False):
    """The Lean `Ty` of a wire type, parenthesized; `literal` spells domains as strings."""
    head = wire[0]
    if head == "bool":
        return ".boolean"
    if head == "index":
        return ".index"
    if head in ("field", "vector", "group", "service"):
        domain = json.dumps(wire[1]) if literal else lean_domain(wire[1])
        return f"(.{head} {domain})"
    raise GeneratorError(f"unsupported value type {wire}")


def bare_ty(wire, literal=False):
    text = lean_ty(wire, literal)
    return text[1:-1] if text.startswith("(") else text


def value_type(wire):
    """The Lean type of a present value, `assignment F G ty`."""
    return {"bool": "Bool", "index": "Nat", "field": "F", "vector": "List F",
            "group": "G", "service": "Nat"}[wire[0]]


def ty_list(wires, literal=False):
    return "[" + ", ".join(bare_ty(wire, literal) for wire in wires) + "]"


# ---------------------------------------------------------------------------
# Names

def camel(text):
    parts = [part for part in re.split(r"[^0-9A-Za-z]+", text) if part]
    if not parts:
        return "value"
    head = parts[0][0].lower() + parts[0][1:]
    return head + "".join(part[0].upper() + part[1:] for part in parts[1:])


def decode_label(site):
    """Source labels `label_<hex>` or `label_<hex>_<position>`; other sites are positional."""
    match = re.fullmatch(r"label_([0-9a-f]+)(?:_(\d+))?", site)
    if not match:
        return None
    try:
        return bytes.fromhex(match.group(1)).decode("utf-8"), match.group(2)
    except ValueError:
        return None


class Names:
    """Fresh Lean identifiers."""

    RESERVED = {"F", "G", "U", "ctx", "self", "role", "separate", "index", "result", "value", "m",
                "fun", "match", "with", "if", "then", "else", "let", "have", "show", "by", "at", "in",
                "from", "do", "where", "end", "open", "section", "namespace", "true", "false"}

    def __init__(self, taken=()):
        self.taken = set(self.RESERVED) | set(taken)

    def fresh(self, base):
        base = camel(base)
        if not base[0].isalpha():
            base = "value" + base
        name, counter = base, 1
        while name in self.taken:
            counter += 1
            name = f"{base}{counter}"
        self.taken.add(name)
        return name


# ---------------------------------------------------------------------------
# The retained unit

@dataclass
class Function:
    name: str
    kind: str
    inputs: list
    outputs: list
    roles: list | None
    input_scopes: list | None
    output_scopes: list | None
    body: list


class Unit:
    def __init__(self, data):
        if data[0] != "zkc.structured-source/0":
            raise GeneratorError(f"unsupported snapshot format {data[0]}")
        self.entry = data[3]
        self.relations = {row[1]: row for row in data[5]}
        self.functions = {}
        for row in data[7]:
            if row[0] != "function":
                continue
            meta = row[6]
            roles = scopes_in = scopes_out = None
            if meta and meta[0] == "protocol":
                roles = meta[1]
                scopes_in = [[roles.index(role) for role in scope] for scope in meta[2]]
                scopes_out = [[roles.index(role) for role in scope] for scope in meta[3]]
            self.functions[row[1]] = Function(row[1], row[2], row[4], row[5], roles, scopes_in,
                                              scopes_out, row[9])
        self.contracts = {row[0]: row[1] for row in data[8]}

    def function(self, name):
        if name not in self.functions:
            raise GeneratorError(f"no retained definition {name}")
        return self.functions[name]


def find_repeat(block, site):
    for instruction in block[1]:
        if instruction[0][0] == "protocol_repeat":
            if instruction[4] == site:
                return instruction
            found = find_repeat(instruction[3][0][2], site)
            if found:
                return found
    return None


def repeat_with_label(block, label):
    """The repeat whose own callback directly performs an action or application with this
    source label, so a request can name a loop by what it does rather than by the
    compiler's positional site."""
    for instruction in block[1]:
        if instruction[0][0] != "protocol_repeat":
            continue
        callback = instruction[3][0][2]
        for inner in callback[1]:
            decoded = decode_label(inner[4]) if inner[4] else None
            if decoded and decoded[0] == label:
                return instruction
        found = repeat_with_label(callback, label)
        if found:
            return found
    return None


def locate_repeat(block, key):
    """A repeat named by its site or by a source label its callback carries."""
    instruction = find_repeat(block, key) or repeat_with_label(block, key)
    if instruction is None:
        raise GeneratorError(f"no repeat has site {key!r} or a callback action labelled {key!r}")
    return instruction


def action_sites(block, sites=None):
    """Sites of actions in source order, including nested callbacks."""
    sites = [] if sites is None else sites
    for instruction in block[1]:
        head = instruction[0][0]
        if head in ("exchange", "draw") and instruction[4] not in sites:
            sites.append(instruction[4])
        if head == "protocol_repeat":
            action_sites(instruction[3][0][2], sites)
    return sites


def application_sites(block, found=None):
    """The protocol applications of a block in source order, including nested callbacks."""
    found = [] if found is None else found
    for instruction in block[1]:
        head = instruction[0][0]
        if head == "protocol_apply":
            found.append(instruction)
        if head == "protocol_repeat":
            application_sites(instruction[3][0][2], found)
    return found


def scope_literal(scopes):
    return "[" + ", ".join(list_literal(scope) for scope in scopes) + "]"


def list_literal(items):
    return "[" + ", ".join(str(item) for item in items) + "]"


def binder_groups(text):
    """The parenthesized binder groups of a Lean binder string, in order."""
    groups, depth, start = [], 0, None
    for position, character in enumerate(text or ""):
        if character == "(":
            if depth == 0:
                start = position
            depth += 1
        elif character == ")":
            depth -= 1
            if depth == 0 and start is not None:
                groups.append(text[start:position + 1])
    return groups


def binders_used(text, statement):
    """The binder groups of `text` some of whose names the statement mentions."""
    kept = []
    for group in binder_groups(text):
        if any(re.search(rf"(?<![\w.]){re.escape(name)}(?![\w'])", statement) for name in binder_names(group)):
            kept.append(group)
    return " ".join(kept)


def binder_names(text):
    """The names a Lean binder string such as `(a b : T) (c : U)` introduces."""
    names = []
    for group in re.findall(r"[({\[]\s*([\w\s']+?)\s*:", text or ""):
        names.extend(group.split())
    return names


# ---------------------------------------------------------------------------
# Symbolic values

@dataclass(frozen=True)
class Sym:
    kind: str           # "present", "absent", "optional" or "component"
    wire: tuple
    expr: str = ""      # present: a Lean term; optional: the variable holding it;
                        # component: an `Option` term read from a bound tuple
    label: str = ""     # a component's stem for the name its present value gets

    def component(self):
        if self.kind == "present":
            return f"some {paren(self.expr)}"
        if self.kind == "absent":
            return "none"
        return self.expr          # "optional" or "component": an `Option` term


def present(wire, expr):
    return Sym("present", tuple(wire), expr)


def absent(wire):
    return Sym("absent", tuple(wire))


def optional(wire, variable):
    return Sym("optional", tuple(wire), variable)


def outer_parenthesized(text):
    if not text.startswith("("):
        return False
    depth = 0
    for position, character in enumerate(text):
        if character == "(":
            depth += 1
        elif character == ")":
            depth -= 1
            if depth == 0 and position != len(text) - 1:
                return False
    return depth == 0


def paren(text):
    text = text.strip()
    if re.fullmatch(r"[\w.']+|\[[^\[\]]*\]", text) or outer_parenthesized(text):
        return text
    return f"({text})"


def values_literal(items):
    """A `Values` literal of the given element terms."""
    text = ".nil"
    for item in reversed(items):
        text = f"(.cons {paren(item)} {text})"
    return text[1:-1] if text.startswith("(") and text != ".nil" else text


def tuple_literal(items):
    return items[0] if len(items) == 1 else "(" + ", ".join(items) + ")"


# Process trees -------------------------------------------------------------

@dataclass
class Event:
    """One action as the normal form states it: `send`, `receive` or `query`."""
    kind: str
    site: str           # Lean term of the qualified site
    ty: str             # Lean `Ty` of the value
    peer: str = ""      # the other role of an exchange
    value: str = ""     # the sent value
    field: str = ""     # the queried field domain
    handles: str = ""   # the queried service handles

    def action(self):
        if self.kind == "send":
            return f"(.send (ty := {self.ty}) {self.site} {self.peer} {paren(self.value)})"
        if self.kind == "receive":
            return f"(.receive {paren(self.ty)} {self.site} {self.peer})"
        return f"(.query {self.site} {self.field} {paren(self.handles)})"


@dataclass
class Call:
    event: Event
    binder: str
    binder_type: str
    next: object

    @property
    def action(self):
        return self.event.action()


@dataclass
class Halt:
    reason: str


@dataclass
class Done:
    expr: str


@dataclass
class Match:
    variable: str       # the `Option` variable or term the match scrutinizes
    none: object
    some: object
    binder: str = ""    # the present value's name, when the scrutinee is a term


@dataclass
class Bind:
    process: str
    binder: str
    binder_type: str
    next: object


@dataclass
class If:
    prop: str
    then: object
    otherwise: object


def render_process(node, indent):
    pad = " " * indent
    if isinstance(node, Call):
        binder = "_" if node.binder == "_" else f"({node.binder} : {node.binder_type})"
        return f"{pad}.call {node.action} fun {binder} =>\n" + render_process(node.next, indent)
    if isinstance(node, Halt):
        return f"{pad}.halt .{node.reason}"
    if isinstance(node, Done):
        return f"{pad}.done {paren(node.expr)}"
    if isinstance(node, Match):
        some = render_process(node.some, indent + 2)
        binder = node.binder or node.variable
        if node.binder and re.search(rf"(?<![\w.]){re.escape(binder)}(?![\w'])", some) is None:
            binder = "_"
        return (f"{pad}match {node.variable} with\n{pad}| none =>\n" + render_process(node.none, indent + 2)
                + f"\n{pad}| some {binder} =>\n" + some)
    if isinstance(node, Bind):
        rest = render_process(node.next, indent)
        used = re.search(rf"(?<![\w.]){re.escape(node.binder)}(?![\w'])", rest) is not None
        return (f"{pad}({node.process}).bind fun ({node.binder if used else '_'} : {node.binder_type}) =>\n"
                + rest)
    if isinstance(node, If):
        return (f"{pad}if {node.prop} then\n" + render_process(node.then, indent + 2)
                + f"\n{pad}else\n" + render_process(node.otherwise, indent + 2))
    raise GeneratorError(f"unknown process node {node}")


def has_bind(node):
    """Whether a process tree binds an opaque process (a repeat, an application or a kept call)."""
    if isinstance(node, Bind):
        return True
    if isinstance(node, Call):
        return has_bind(node.next)
    if isinstance(node, Match):
        return has_bind(node.none) or has_bind(node.some)
    if isinstance(node, If):
        return has_bind(node.then) or has_bind(node.otherwise)
    return False


def associate(node):
    """Bound processes nested under the role's outer bind need reassociation first."""
    return ", PIR.Process.bind_assoc" if has_bind(node) else ""


def linear_actions(node):
    """The actions and final value of a branch-free process, or None."""
    actions = []
    while isinstance(node, Call):
        actions.append(node)
        node = node.next
    return (actions, node) if isinstance(node, (Done, Halt)) else None


# ---------------------------------------------------------------------------
# Operations: the typed operation each raw instruction elaborates to.

BINARY = {
    "field.add": ("fieldAdd", lambda a, b: f"{paren(a)} + {paren(b)}"),
    "field.subtract": ("fieldSubtract", lambda a, b: f"{paren(a)} - {paren(b)}"),
    "field.multiply": ("fieldMultiply", lambda a, b: f"{paren(a)} * {paren(b)}"),
    "field.equal": ("fieldEqual", lambda a, b: f"decide ({a} = {b})"),
    "group.add": ("groupAdd", lambda a, b: f"{paren(a)} + {paren(b)}"),
    "group.equal": ("groupEqual", lambda a, b: f"decide ({a} = {b})"),
    "group.scale": ("groupScale", lambda point, scalar: f"{paren(scalar)} • {paren(point)}"),
    "index.equal": ("indexEqual", lambda a, b: f"decide ({a} = {b})"),
    "bool.and": ("booleanAnd", lambda a, b: f"{paren(a)} && {paren(b)}"),
    "bool.or": ("booleanOr", lambda a, b: f"{paren(a)} || {paren(b)}"),
    "bool.xor": ("booleanXor", lambda a, b: f"xor {paren(a)} {paren(b)}"),
    "bool.equal": ("booleanEqual", lambda a, b: f"{paren(a)} == {paren(b)}"),
    "bool.not_equal": ("booleanNotEqual", lambda a, b: f"{paren(a)} != {paren(b)}"),
}
CONSTANTS = ("field.constant", "index.constant", "bool.constant", "group.identity")


def calculation_op(descriptor):
    head = descriptor[0]
    if head in ("field.add", "field.subtract", "field.multiply", "field.equal", "group.add", "group.equal"):
        return f"(.{BINARY[head][0]} {json.dumps(descriptor[1])})"
    if head == "group.scale":
        return f"(.groupScale {json.dumps(descriptor[1])} {json.dumps(descriptor[2])})"
    if head in BINARY:
        return f".{BINARY[head][0]}"
    if head == "field.constant":
        return f"(.fieldConstant {json.dumps(descriptor[1])} {int(descriptor[2])})"
    if head == "index.constant":
        return f"(.indexConstant {int(descriptor[1])})"
    if head == "bool.constant":
        return f"(.booleanConstant {'true' if descriptor[1] else 'false'})"
    if head == "group.identity":
        return f"(.groupIdentity {json.dumps(descriptor[1])})"
    raise GeneratorError(f"unsupported calculation {descriptor}")


def evaluate_calculation(descriptor, args, wire):
    head = descriptor[0]
    if any(arg.kind == "absent" for arg in args):
        return absent(wire)
    if head == "field.constant":
        value = int(descriptor[2])
        return present(wire, str(value) if value in (0, 1) else f"({value} : F)")
    if head == "index.constant":
        return present(wire, str(int(descriptor[1])))
    if head == "bool.constant":
        return present(wire, "true" if descriptor[1] else "false")
    if head == "group.identity":
        return present(wire, "(0 : G)")
    folded = fold_literals(head, [arg.expr for arg in args])
    if folded is not None:
        return present(wire, folded)
    return present(wire, BINARY[head][1](*[arg.expr for arg in args]))


def fold_literals(head, exprs):
    """Comparisons and connectives of literals, which reduce by definitional unfolding."""
    def literal(text):
        if text in ("true", "false"):
            return text == "true"
        return int(text) if re.fullmatch(r"\d+", text) else None
    values = [literal(text) for text in exprs]
    if any(value is None for value in values):
        return None
    a, b = values
    result = {"index.equal": a == b, "bool.equal": a == b, "bool.not_equal": a != b,
              "bool.and": a and b, "bool.or": a or b, "bool.xor": a != b}.get(head)
    return None if result is None else ("true" if result else "false")


# ---------------------------------------------------------------------------
# Evaluation frames

@dataclass
class Law:
    """A helper law: a Lean term proving the helper's invocation equation, the
    result expressions it yields, or the stop it reaches. Templates refer to
    the call's operands as {0}, {1}, ..."""
    term: str
    results: list = field(default_factory=list)
    stop: str | None = None
    components: bool = False      # templates read and yield optional components


@dataclass
class Frame:
    unit: Unit
    roles: list                  # retained role names of the evaluated protocol
    role: int
    mode: str                    # "root" (definitional) or "shared" (explicit steps)
    sites: dict                  # site -> Lean name of its constant
    helpers: dict                # retained helper name -> Lean term
    laws: dict                   # helper key -> Law
    guards: dict                 # guard site -> proof term of its condition
    separate: str = "separate"
    closed: str = ""
    components: str = ""
    rewrites: list = field(default_factory=list)
    callback: str = ""
    repeat_spec: str = ""
    repeats: dict = field(default_factory=dict)        # repeat site -> (spec term, callback function)
    slot_names: dict = field(default_factory=dict)     # repeat site -> slot position -> this role's name
    outer_bind: bool = False     # the stated process is followed by the role's embedding
    applications: dict = field(default_factory=dict)   # site -> Application
    opaque: tuple = ()           # helpers whose owned calls stay as they are
    strict: tuple = ()           # helpers whose owned calls stay as invocations on present arguments
    role_name: str = ""
    law_uses: list = field(default_factory=list)   # (retained helper, call arguments) of each law use
    application_uses: dict = field(default_factory=dict)   # site -> callee binder name -> argument term


@dataclass
class Application:
    """A protocol application and the callee's generated normal forms it substitutes."""
    name: str                    # Lean stem, from the source label
    site: str
    roles: list                  # caller role index of each callee role
    signature: str               # Lean term of the callee signature
    context: str                 # Lean name of the child-context abbreviation
    unit: str                    # the admitted unit and the callee's checked declaration
    definition: str
    member: str
    same: str
    body: str
    raw: str
    arguments: dict              # callee normal-form parameters -> Lean terms
    callee_roles: dict           # callee role index -> callee role information
    values: dict                 # callee role index -> request table of binder and premise terms
    results: list = field(default_factory=list)   # names of the callee's results, by position
    callee: str = ""             # the callee's retained name


class Evaluator:
    """Symbolic participant execution of one block at one role.

    The process tree and, in shared mode, the proof script come from the same
    traversal, so the stated normal form is exactly what the steps derive."""

    def __init__(self, frame, names, finish):
        self.frame = frame
        self.names = names
        self.finish = finish
        self.shared = frame.mode == "shared"
        self.branches = 0

    def after(self):
        """Whether a bound process here is followed by the role's outer bind. The process
        equation's initial `simp` reassociates that bind into every bind it reaches; only a
        match or a conditional stops it, so it stays separate under a branch."""
        return self.frame.outer_bind and self.branches > 0

    def branch(self, instructions, terminator, env, proof, indent):
        self.branches += 1
        try:
            return self.run(instructions, terminator, env, proof, indent)
        finally:
            self.branches -= 1

    # -- terms ---------------------------------------------------------
    def role_term(self, index):
        return str(index) if not self.shared else f"(ctx.roles {index})"

    def site_term(self, site):
        if site not in self.frame.sites:
            raise GeneratorError(f"no site constant for {site!r}")
        name = self.frame.sites[site]
        return name if not self.shared else f"({name} ctx)"

    def qualified_site(self, site):
        return f"(qualifyProtocolSite ctx.applicationPrefix {json.dumps(site)})"

    def helper_term(self, name):
        if name in self.frame.helpers:
            return self.frame.helpers[name]
        helper = self.frame.unit.function(name)
        kind = {"local": ".local", "math": ".math"}[helper.kind]
        return (f"(⟨{json.dumps(name)}, {kind}, {ty_list(helper.inputs, True)}, "
                f"{ty_list(helper.outputs, True)}⟩ : Helper)")

    def law(self, name):
        term = self.helper_term(name)
        for key in (term, name, term.split(".")[-1]):
            if key in self.frame.laws:
                return self.frame.laws[key]
        known = "" if name in self.frame.helpers else (
            "; if a typed-body module declares it, list that module in helper_modules")
        raise GeneratorError(f"no law for helper {name} ({term.split('.')[-1] if name in self.frame.helpers else 'unnamed'}) "
                             f"at role {self.frame.role}; name one in the request's laws table{known}")

    def inline(self, name, args, results):
        """A Math helper evaluated through its own retained body. Root equations are
        definitional, so the kernel checks the inlined values by unfolding the helper."""
        helper = self.frame.unit.function(name)
        if helper.kind != "math":
            return None
        frame = Frame(self.frame.unit, [], 0, "root", {}, self.frame.helpers, {}, {})

        def finish(values, proof, pad):
            return values

        values = Evaluator(frame, self.names, finish).run(helper.body[1], helper.body[2], list(args), [], 0)
        if not isinstance(values, list) or len(values) != len(results):
            raise GeneratorError(f"Math helper {name} does not return its declared results")
        return values

    def fill(self, template, args, components=False):
        if components:
            return template.format(*[paren(arg.component()) for arg in args])
        return template.format(*[paren(arg.expr) for arg in args])

    def from_component(self, wire, text):
        text = text.strip()
        while outer_parenthesized(text):
            text = text[1:-1].strip()
        if text == "none":
            return absent(wire)
        if text.startswith("some "):
            return present(wire, text[5:].strip())
        return Sym("component", tuple(wire), text)

    def rewrite(self, values, proof, pad):
        """Apply the request's value facts to new values; the proof rewrites the goal alike."""
        result = []
        for value in values:
            for fact in self.frame.rewrites:
                if value.kind == "present" and fact["expr"] in value.expr:
                    if self.shared:
                        proof.append(f"{pad}simp only [show {fact['expr']} = {fact['value']} from {fact['proof']}]")
                    value = present(value.wire, value.expr.replace(fact["expr"], fact["value"]))
            result.append(value)
        return result

    def received_name(self, site, fallback):
        label = decode_label(site) if site else None
        if label:
            text, position = label
            sibling = re.sub(r"_\d+$", "_1", site)
            base = f"{text}_{position}" if position is not None and sibling in self.frame.sites else text
            return self.names.fresh(base)
        if site in self.frame.sites:
            return self.names.fresh(self.frame.sites[site].removesuffix("Site"))
        return self.names.fresh(fallback)

    # -- traversal -----------------------------------------------------
    def run(self, instructions, terminator, env, proof, indent):
        pad = " " * indent
        if not instructions:
            kind, indices = terminator
            if kind not in ("return", "yield"):
                raise GeneratorError(f"unsupported terminator {kind}")
            return self.finish([env[index] for index in indices], proof, pad)
        instruction, rest = instructions[0], instructions[1:]
        descriptor, operands, results, _, site = instruction
        args = [env[index] for index in operands]
        # A strict use of an undetermined optional value splits on its presence first; a
        # component read from a bound tuple splits the same way, on the term that reads it.
        for position in self.demands(descriptor, args, site):
            if args[position].kind == "optional":
                return self.split(args[position].expr, instructions, terminator, env, proof, indent)
            if args[position].kind == "component":
                return self.split_component(args[position], instructions, terminator, env, proof, indent)
        step = Step(self, proof, pad)
        step.mark(site)
        head = descriptor[0]
        if head in BINARY or head in CONSTANTS:
            value = evaluate_calculation(descriptor, args, results[0])
            op = f"(.calculate {calculation_op(descriptor)} rfl)"
            if head == "field.constant" and self.shared:
                cast = present(results[0], f"(({int(descriptor[2])} : ℕ) : F)")
                step.done(op, [cast], None)
                lemma = {0: "Nat.cast_zero", 1: "Nat.cast_one"}.get(int(descriptor[2]), "Nat.cast_ofNat")
                proof.append(f"{pad}simp only [{lemma}]")
            else:
                step.done(op, [value], None)
            return self.run(rest, terminator, [value] + env, proof, indent)
        if head == "call":
            return self.math_call(descriptor, args, results, rest, terminator, env, proof, indent, step)
        if head == "local_call":
            return self.local_call(descriptor, args, results, site, rest, terminator, env, proof, indent,
                                   step)
        if head == "exchange":
            return self.exchange(descriptor, args, results, site, rest, terminator, env, proof, indent, step)
        if head == "restrict":
            roles = [self.frame.roles.index(role) for role in descriptor[1]]
            value = args[0] if self.frame.role in roles else absent(results[0])
            op = f"(.restrict {lean_ty(results[0], literal=True)} [{', '.join(map(str, roles))}])"
            listed = ", ".join(self.role_term(role) for role in roles)
            step.done(op, [value], ("restrict", listed, args[0]))
            return self.run(rest, terminator, [value] + env, proof, indent)
        if head == "draw":
            return self.draw(descriptor, args, results, site, rest, terminator, env, proof, indent, step)
        if head == "guard":
            return self.guard(descriptor, args, site, rest, terminator, env, proof, indent, step)
        if head == "protocol_repeat":
            return self.repeat(descriptor, args, results, site, rest, terminator, env, proof, indent, step)
        if head == "protocol_apply":
            return self.application(descriptor, args, site, rest, terminator, env, proof, indent)
        raise GeneratorError(f"unsupported instruction {head} at site {site!r}")

    def repeat(self, descriptor, args, results, site, rest, terminator, env, proof, indent, step):
        """A repeat at a role in its roster: the actual repeat of its callback, then the
        retained return of its state or, in the middle of a body, the continuation on the
        repeat's returned state."""
        _, state_count, _, roles, _ = descriptor
        if self.frame.roles[self.frame.role] not in roles:
            raise GeneratorError("normal forms of a role outside a repeat's roster are not supported")
        if site in self.frame.repeats:
            spec, callback = self.frame.repeats[site]
        elif self.frame.callback and self.frame.repeat_spec:
            spec, callback = self.frame.repeat_spec, self.frame.callback
        else:
            raise GeneratorError(f"the repeat at site {site!r} needs its callback: name it in the request's "
                                 f"[bodies] callbacks and give it a [[shared]] entry whose repeat names it")
        count, state, captures = args[0], args[1:1 + state_count], args[1 + state_count:]
        me = self.role_term(self.frame.role)
        typed_state = (f"({values_literal([value.component() for value in state])} : "
                       f"Values (Component (assignment F G)) {ty_list(results, True)})")
        typed_captures = (f"({values_literal([value.component() for value in captures])} : "
                          f"Values (Component (assignment F G)) {ty_list([value.wire for value in captures], True)})")
        process = (f"denoteRepeat ({spec}) ctx {me} {paren(count.component())} {typed_state}\n"
                   f"    {typed_captures} ({callback} ctx {me})")
        if rest or terminator[0] != "return":
            return self.repeat_then(spec, callback, process, results, site, rest, terminator, env, proof,
                                    indent)
        pad = " " * indent
        if self.shared:
            proof.append(f"{pad}refine (Region.denote_letOp_values m (.repeat ({spec}) "
                         f"{json.dumps(site)}) _ _ _ _).trans ?_")
            proof.append(f"{pad}change ({process}).bind _ = _")
            proof.append(f"{pad}congr 1")
            proof.append(f"{pad}funext state")
            for position in range(state_count):
                proof.append(f"{pad}{'  ' * position}cases state with | cons slot{position} state =>")
            proof.append(f"{pad}{'  ' * state_count}cases state")
        inner = [Sym("component", tuple(wire), f"state.get {variable(position)}")
                 for position, wire in enumerate(results)]
        kind, indices = terminator
        node = self.finish([inner[index] if index < state_count else None for index in indices], None, pad)
        if self.shared:
            proof.append(f"{pad}{'  ' * state_count}rfl")
        return Bind(process, "state", f"Values (Component (assignment F G)) {ty_list(results, True)}", node)

    def repeat_then(self, spec, callback, process, results, site, rest, terminator, env, proof, indent):
        """A repeat in the middle of a body: its returned state is bound like an owned call's
        tuple, and the rest of the body reads the bound components."""
        stem = callback.removesuffix("Fn") or "repeat"
        binder = self.names.fresh(stem + "Returned")
        typed = f"Values (Component (assignment F G)) {ty_list(results, True)}"
        slots = self.frame.slot_names.get(site, {})
        values = [Sym("component", tuple(wire), f"{binder}.get {variable(position)}",
                      slots.get(position, stem if len(results) == 1 else f"{stem}{position}"))
                  for position, wire in enumerate(results)]
        if self.shared:
            pad = " " * indent
            op = f"(.repeat ({spec}) {json.dumps(site)})"
            expanded = values_literal([value.expr for value in values])
            lemma = "denote_letOp_bind_after" if self.after() else "denote_letOp_bind"
            proof.append(f"{pad}refine NormalFormSteps.{lemma} m {op} _ _ _ _")
            proof.append(f"{pad}  ({process})")
            proof.append(f"{pad}  (fun {binder} => {expanded}) _{' _' if self.after() else ''} ?_ ?_")
            proof.append(f"{pad}· refine (PIR.Process.bind_done _).symm.trans (congrArg (PIR.Process.bind _) "
                         f"(funext fun {binder} => ?_))")
            cases = "".join(f"cases {binder} with | cons value{position} {binder} => "
                            for position in range(len(results)))
            proof.append(f"{pad}  {cases}cases {binder}; rfl")
            proof.append(f"{pad}intro {binder}")
        return Bind(process, binder, typed, self.run(rest, terminator, values + env, proof, indent))

    def demands(self, descriptor, args, site=None):
        """Operand positions whose presence decides this operation's behaviour here."""
        head = descriptor[0]
        if head == "protocol_apply":
            callee = self.callee_role(descriptor, site)
            if callee is None:
                return []
            index, info, masked = callee
            return [position for position, item in enumerate(info["inputs"])
                    if masked[position] and item.get("mode", "present") == "present" and "value" not in item]
        if head == "local_call" and self.opaque(descriptor[1]):
            return []
        if head == "call":
            if not self.shared and not any(key in self.frame.laws for key in
                                           (descriptor[1], self.helper_term(descriptor[1]))):
                return range(len(args))
            return [] if self.law(descriptor[1]).components else range(len(args))
        # An absent operand already decides a calculation (absent), an owned call or a draw
        # (both stop), whatever the other operands hold.
        decided = any(arg.kind == "absent" for arg in args)
        if head in BINARY:
            return [] if decided else range(len(args))
        if head == "local_call":
            return range(len(args)) if self.frame.roles.index(descriptor[2]) == self.frame.role and not decided \
                else []
        if head == "exchange":
            return [0] if self.frame.roles.index(descriptor[1]) == self.frame.role else []
        if head in ("draw", "guard"):
            return range(len(args)) if self.frame.roles.index(descriptor[1]) == self.frame.role and not decided \
                else []
        return []

    def split(self, variable, instructions, terminator, env, proof, indent):
        pad = " " * indent
        none_env = [absent(value.wire) if value.kind == "optional" and value.expr == variable else value
                    for value in env]
        some_env = [present(value.wire, variable) if value.kind == "optional" and value.expr == variable
                    else value for value in env]
        none_proof, some_proof = [], []
        none_node = self.branch(instructions, terminator, none_env, none_proof, indent + 2)
        some_node = self.branch(instructions, terminator, some_env, some_proof, indent + 2)
        if self.shared:
            proof.append(f"{pad}cases {variable} with")
            proof.append(f"{pad}| none =>")
            proof.extend(none_proof)
            proof.append(f"{pad}| some {variable} =>")
            proof.extend(some_proof)
        return Match(variable, none_node, some_node)

    def split_component(self, value, instructions, terminator, env, proof, indent):
        """Split on a component of a bound tuple: its term is generalized, and each branch
        continues with that component absent or present under a fresh name."""
        pad = " " * indent
        name = self.names.fresh(value.label or "value")
        none_env = [absent(item.wire) if item.kind == "component" and item.expr == value.expr else item
                    for item in env]
        some_env = [present(item.wire, name) if item.kind == "component" and item.expr == value.expr
                    else item for item in env]
        none_proof, some_proof = [], []
        none_node = self.branch(instructions, terminator, none_env, none_proof, indent + 2)
        some_node = self.branch(instructions, terminator, some_env, some_proof, indent + 2)
        if self.shared:
            proof.append(f"{pad}cases {value.expr} with")
            proof.append(f"{pad}| none =>")
            proof.extend(none_proof)
            proof.append(f"{pad}| some {name} =>")
            proof.extend(some_proof)
        return Match(value.expr, none_node, some_node, name)

    def math_call(self, descriptor, args, results, rest, terminator, env, proof, indent, step):
        if not self.shared and not any(key in self.frame.laws for key in
                                       (descriptor[1], self.helper_term(descriptor[1]))):
            if all(arg.kind in ("present", "absent") for arg in args):
                # Math calls propagate each input's availability through the body.
                values = self.inline(descriptor[1], args, results)
                if values is not None:
                    return self.run(rest, terminator, values + env, proof, indent)
        law = self.law(descriptor[1])
        op = f"(.calculate (.invoke {self.helper_term(descriptor[1])}) rfl)"
        helper = self.helper_term(descriptor[1])
        if law.stop:
            step.halt(op, law.stop, ("math", law, helper, args))
            return Halt(law.stop)
        if law.components:
            values = [self.from_component(wire, self.fill(text, args, True))
                      for wire, text in zip(results, law.results)]
        else:
            values = [present(wire, self.fill(text, args)) for wire, text in zip(results, law.results)]
        step.done(op, values, ("math", law, helper, args))
        values = self.rewrite(values, proof, step.pad)
        return self.run(rest, terminator, values + env, proof, indent)

    def local_call(self, descriptor, args, results, site, rest, terminator, env, proof, indent, step):
        owner = self.frame.roles.index(descriptor[2])
        helper = self.helper_term(descriptor[1])
        op = f"(.localCall {helper} rfl {owner} {json.dumps(site)})"
        if owner != self.frame.role:
            values = [absent(wire) for wire in results]
            step.done(op, values, ("other", owner, helper, args))
            return self.run(rest, terminator, values + env, proof, indent)
        if any(arg.kind == "absent" for arg in args):
            step.halt(op, "incomplete", ("missing", helper, args))
            return Halt("incomplete")
        if self.opaque(descriptor[1]):
            return self.opaque_call(descriptor, args, results, site, rest, terminator, env, proof, indent, step)
        if self.strict(descriptor[1]):
            return self.strict_call(descriptor, args, results, site, rest, terminator, env, proof, indent)
        law = self.law(descriptor[1])
        self.frame.law_uses.append((descriptor[1], list(args)))
        if law.stop:
            step.halt(op, law.stop, ("owned", law, helper, args))
            return Halt(law.stop)
        values = [present(wire, self.fill(text, args)) for wire, text in zip(results, law.results)]
        step.done(op, values, ("owned", law, helper, args))
        values = self.rewrite(values, proof, step.pad)
        return self.run(rest, terminator, values + env, proof, indent)

    def exchange(self, descriptor, args, results, site, rest, terminator, env, proof, indent, step):
        sender = self.frame.roles.index(descriptor[1])
        receiver = self.frame.roles.index(descriptor[2])
        wire = results[0]
        op = f"(.exchange {lean_ty(wire, literal=True)} {sender} {receiver} {json.dumps(site)})"
        how = ("exchange", sender, receiver, site, wire, args[0])
        if sender == self.frame.role:
            if args[0].kind == "absent":
                step.halt(op, "incomplete", how)
                return Halt("incomplete")
            value = args[0]
            event = Event("send", self.site_term(site), bare_ty(wire), self.role_term(receiver), value.expr)
            step.call(op, (f"(.send (ty := {bare_ty(wire, literal=True)}) {self.qualified_site(site)} "
                           f"{self.role_term(receiver)} {paren(value.expr)})"),
                      "_", value_type(wire), [value], how)
            return Call(event, "_", "", self.run(rest, terminator, [value] + env, proof, indent))
        if receiver == self.frame.role:
            name = self.received_name(site, "received")
            value = present(wire, name)
            event = Event("receive", self.site_term(site), bare_ty(wire), self.role_term(sender))
            step.call(op, (f"(.receive {lean_ty(wire, literal=True)} {self.qualified_site(site)} "
                           f"{self.role_term(sender)})"), name, value_type(wire), [value], how)
            return Call(event, name, value_type(wire), self.run(rest, terminator, [value] + env, proof, indent))
        value = absent(wire)
        step.done(op, [value], how)
        return self.run(rest, terminator, [value] + env, proof, indent)

    def draw(self, descriptor, args, results, site, rest, terminator, env, proof, indent, step):
        owner = self.frame.roles.index(descriptor[1])
        field_name = descriptor[2]
        wire = results[0]
        op = f"(.draw {owner} {json.dumps(field_name)} {json.dumps(site)})"
        how = ("draw", owner, site, field_name, args)
        if owner != self.frame.role:
            value = absent(wire)
            step.done(op, [value], how)
            return self.run(rest, terminator, [value] + env, proof, indent)
        if any(arg.kind == "absent" for arg in args):
            step.halt(op, "incomplete", how)
            return Halt("incomplete")
        name = self.received_name(site, "sample")
        value = present(wire, name)
        handles = values_literal([arg.expr for arg in args])
        event = Event("query", self.site_term(site), bare_ty(wire), field=lean_domain(field_name), handles=handles)
        step.call(op, f"(.query {self.qualified_site(site)} {json.dumps(field_name)} {paren(handles)})",
                  name, value_type(wire), [value], how)
        return Call(event, name, value_type(wire), self.run(rest, terminator, [value] + env, proof, indent))

    def guard(self, descriptor, args, site, rest, terminator, env, proof, indent, step):
        owner = self.frame.roles.index(descriptor[1])
        op = f"(.guard {owner} {json.dumps(site)})"
        condition = args[0]
        if owner != self.frame.role:
            step.done(op, [], ("guard", owner, condition, None))
            return self.run(rest, terminator, env, proof, indent)
        if condition.kind == "absent":
            step.halt(op, "incomplete", ("guard", owner, condition, None))
            return Halt("incomplete")
        if site in self.frame.guards or condition.expr == "true":
            step.done(op, [], ("guard", owner, condition, self.frame.guards.get(site)))
            return self.run(rest, terminator, env, proof, indent)
        if condition.expr == "false":
            step.halt(op, "reject", ("guard", owner, condition, None))
            return Halt("reject")
        decided = re.fullmatch(r"decide \((.*)\)", condition.expr)
        if not decided or not outer_parenthesized("(" + decided.group(1) + ")"):
            raise GeneratorError(f"guard {site!r} condition {condition.expr!r} is not a decided proposition; "
                                 f"name its fact in the request's guards table")
        prop = decided.group(1)
        pad = " " * step.pad_width
        holds = self.names.fresh("holds")
        holds_proof, fails_proof = [], []
        Step(self, holds_proof, pad + "  ").done(op, [], ("guard", owner, present(condition.wire, "true"), None))
        # The proof rewrites the decided proposition to `True` throughout the goal.
        decided_env = [present(value.wire, value.expr.replace(condition.expr, "true"))
                       if value.kind == "present" else value for value in env]
        then = self.branch(rest, terminator, decided_env, holds_proof, indent + 2)
        Step(self, fails_proof, pad + "  ").halt(op, "reject",
                                                 ("guard", owner, present(condition.wire, "false"), None))
        if self.shared:
            proof.append(f"{pad}by_cases {holds} : {prop}")
            proof.append(f"{pad}· simp only [eq_true {holds}, decide_true, ↓reduceIte, PIR.Process.bind]")
            proof.extend(holds_proof)
            proof.append(f"{pad}· simp only [eq_false {holds}, decide_false, ↓reduceIte, PIR.Process.bind]")
            proof.extend(fails_proof)
        return If(prop, then, Halt("reject"))

    # -- protocol applications and opaque owned calls ----------------------
    def callee_role(self, descriptor, site):
        """The callee role this participant plays at an application, its generated normal
        form, and which callee inputs survive the callee's input scopes; None if inactive."""
        frame = self.frame
        app = frame.applications.get(site)
        if app is None:
            if not self.shared:
                raise GeneratorError(f"protocol_apply at site {site!r}: a root with applications needs a "
                                     f"[[shared]] entry naming the callee's normal forms")
            raise GeneratorError(f"protocol_apply at site {site!r}: name its callee in the request's "
                                 f"applications table")
        callee = frame.unit.function(descriptor[1])
        roles = [frame.roles.index(role) for role in descriptor[2]]
        if frame.role not in roles:
            return None
        index = roles.index(frame.role)
        info = app.callee_roles.get(index)
        if info is None:
            raise GeneratorError(f"application {app.name}: no callee normal form is named for callee role "
                                 f"{index}")
        if len(info["inputs"]) != len(callee.inputs):
            raise GeneratorError(f"application {app.name}: the callee has {len(callee.inputs)} inputs; its "
                                 f"normal form lists {len(info['inputs'])}")
        return index, info, [index in scope for scope in callee.input_scopes]

    def application(self, descriptor, args, site, rest, terminator, env, proof, indent):
        """The callee's generated normal form at its child context, with the caller's masked
        operands, followed by the caller's continuation on the callee's masked results."""
        frame = self.frame
        app = frame.applications[site] if site in frame.applications else None
        found = self.callee_role(descriptor, site)
        if found is None:
            raise GeneratorError(f"application {app.name}: normal forms of a role outside the "
                                 f"application's roster are not supported")
        index, info, kept = found
        callee = frame.unit.function(descriptor[1])
        roles = [frame.roles.index(role) for role in descriptor[2]]
        masked = [arg if keep else absent(arg.wire) for arg, keep in zip(args, kept)]
        values = {}
        for position, (item, arg) in enumerate(zip(info["inputs"], masked)):
            mode = item.get("mode", "present")
            if mode == "absent":
                if arg.kind != "absent":
                    raise GeneratorError(f"application {app.name}: callee input {position} is {arg.kind} here; "
                                         f"the callee's normal form takes it absent")
            elif "value" in item:
                if arg.kind != "present" or arg.expr != str(item["value"]):
                    raise GeneratorError(f"application {app.name}: callee input {position} is "
                                         f"{arg.expr or arg.kind} here, not the fixed value {item['value']}")
            elif mode == "optional":
                values[item["name"]] = arg.component()
            elif arg.kind != "present":
                raise GeneratorError(f"application {app.name}: callee input {position} is {arg.kind} here; "
                                     f"the callee's normal form takes it present")
            else:
                values[item["name"]] = arg.expr
        frame.application_uses[site] = dict(values)
        child = f"({app.context} ctx)"
        me = self.role_term(frame.role)

        def argument(name):
            if name == "ctx":
                return child
            if name in app.arguments:
                return app.arguments[name]
            if name in values:
                return values[name]
            raise GeneratorError(f"application {app.name}: no value for the callee's {name}")

        process = " ".join([info["process"]] + [paren(argument(name)) for name in info["process_binders"]])
        binder = self.names.fresh(app.name + "Returned")
        def label(position):
            named = app.results[position] if position < len(app.results) else ""
            return app.name + (named[0].upper() + named[1:] if named else str(position))

        added = [Sym("component", tuple(wire), f"{binder}.get {variable(position)}", label(position))
                 if index in scope else absent(wire)
                 for position, (wire, scope) in enumerate(zip(callee.outputs, callee.output_scopes))]
        if self.shared:
            pad = " " * indent
            other = [role for role in range(len(roles)) if role != index]
            if len(other) != 1 or len(frame.roles) != 2 or roles[other[0]] == frame.role:
                raise GeneratorError(f"application {app.name}: only two-role applications are supported")
            arguments = [info["theorem"]]
            arguments += [f"({name} := {app.arguments[name]})" for name in info["parameters"]]
            supplied = app.values.get(index, {})
            for name in info["binders"] + info["premises"]:
                if name not in supplied:
                    raise GeneratorError(f"application {app.name}: give the callee's {name} in the request")
            arguments += [f"({name} := {supplied[name]})" for name in info["binders"]]
            arguments += [f"(ctx := {child})", f"(self := {me})", "(role := rfl)"]
            if info["uses_separate"]:
                arguments.append(f"(separate := {frame.separate})")
            arguments += [f"({name} := {value})" for name, value in values.items()]
            arguments += [f"({name} := {supplied[name]})" for name in info["premises"]]
            typed = f"Values (Component (assignment F G)) {ty_list(callee.inputs, True)}"
            before = f"({values_literal([arg.component() for arg in args])} : {typed})"
            after = f"({values_literal([arg.component() for arg in masked])} : {typed})"
            returned = values_literal([value.component() for value in added])
            lemma = "apply_step_after" if self.after() else "apply_step"
            proof.append(f"{pad}refine NormalFormSteps.{lemma} {app.unit} {app.definition} {app.member} "
                         f"{app.signature} {app.same} ({app.body}) {app.raw}")
            proof.append(f"{pad}  [{', '.join(map(str, roles))}] {json.dumps(site)} ctx {me} _ _ _")
            proof.append(f"{pad}  ((ProtocolContext.contains_iff _ _ _).mpr ⟨{index}, by decide, rfl⟩)")
            proof.append(f"{pad}  {after} ?_")
            proof.append(f"{pad}  ({process}) ?_")
            typed_results = f"Values (Component (assignment F G)) {ty_list(callee.outputs, True)}"
            # A later presence split generalizes a component of the returned tuple; the tuple's
            # type is then spelled as the normal form spells it, so every occurrence matches.
            continuation = []
            node = self.run(rest, terminator, added + env, continuation, indent)
            splits = f"cases {binder}.get " in "\n".join(continuation)
            typed_binder = f"({binder} : {typed_results})" if splits else binder
            proof.append(f"{pad}  (fun {typed_binder} => {returned}) ?_ _{' _' if self.after() else ''} ?_")
            proof.append(f"{pad}· change maskValues {me} ((ctx.enter {json.dumps(site)} {list_literal(roles)}).mapScopes "
                         f"{scope_literal(callee.input_scopes)}) {before} = _")
            proof.append(f"{pad}  iterate {len(callee.inputs) + 1} unfold maskValues")
            proof.append(f"{pad}  simp [ProtocolContext.mapScopes, ProtocolContext.enter, roleSubstitution,")
            proof.append(f"{pad}    Participant.restrict, {frame.separate}, Ne.symm {frame.separate}]")
            proof.append(f"{pad}· exact {' '.join(arguments)}")
            hides = any(index not in scope for scope in callee.output_scopes)
            proof.append(f"{pad}· exact {app.name}_{frame.role_name}_outputs ctx"
                         f"{' ' + frame.separate if hides else ''}")
            proof.append(f"{pad}intro {binder}")
            if splits:
                proof.append(f"{pad}change {typed_results} at {binder}")
            proof.extend(continuation)
            return Bind(process, binder, typed_results, node)
        typed_results = f"Values (Component (assignment F G)) {ty_list(callee.outputs, True)}"
        return Bind(process, binder, typed_results, self.run(rest, terminator, added + env, proof, indent))

    def opaque(self, name):
        term = self.helper_term(name)
        return any(key in self.frame.opaque for key in (name, term, term.split(".")[-1]))

    def strict(self, name):
        """Whether an owned call is kept as the helper's own invocation on present arguments:
        the request lists the helper among its strict calls, or lists `*` there and names no
        law for it."""
        term = self.helper_term(name)
        keys = (name, term, term.split(".")[-1])
        if any(key in self.frame.strict for key in keys):
            return True
        return "*" in self.frame.strict and not any(key in self.frame.laws for key in keys)

    def strict_call(self, descriptor, args, results, site, rest, terminator, env, proof, indent):
        """An owned Local call on present arguments, kept as the helper's invocation: the
        participant rule runs it on the arguments and returns its results present, so later
        uses read present values and need no presence split."""
        helper = self.helper_term(descriptor[1])
        typed_args = (f"({values_literal([arg.expr for arg in args])} : Values (assignment F G) "
                      f"{ty_list([arg.wire for arg in args], True)})")
        process = f"invoke {self.frame.closed} {helper} {typed_args}"
        stem = helper.split(".")[-1].removesuffix("Helper") or "helper"
        binder = self.names.fresh(stem + "Results")
        typed = f"Values (assignment F G) {ty_list(results, True)}"
        values = [present(wire, f"{binder}.get {variable(position)}") for position, wire in enumerate(results)]
        if self.shared:
            pad = " " * indent
            me = self.role_term(self.frame.role)
            op = f"(.localCall {helper} rfl {self.frame.role} {json.dumps(site)})"
            expanded = values_literal([f"some ({value.expr})" for value in values])
            lemma = "denote_letOp_bind_after" if self.after() else "denote_letOp_bind"
            proof.append(f"{pad}refine NormalFormSteps.{lemma} m {op} _ _ _ _")
            proof.append(f"{pad}  ({process}) (fun {binder} => {expanded}) _{' _' if self.after() else ''} ?_ ?_")
            proof.append(f"{pad}· change Participant.owned {me} {me} (invoke {self.frame.closed} {helper}) "
                         f"{typed_args}.present = _")
            proof.append(f"{pad}  refine (Participant.owned_present _ _ _).trans (congrArg (PIR.Process.bind _) "
                         f"(funext fun {binder} => ?_))")
            cases = "".join(f"cases {binder} with | cons value{position} {binder} => "
                            for position in range(len(results)))
            proof.append(f"{pad}  {cases}cases {binder}; rfl")
            proof.append(f"{pad}intro {binder}")
        return Bind(process, binder, typed, self.run(rest, terminator, values + env, proof, indent))

    def opaque_call(self, descriptor, args, results, site, rest, terminator, env, proof, indent, step):
        """An owned Local call kept as the participant rule states it: its returned tuple
        is bound, and every later use reads the bound tuple."""
        helper = self.helper_term(descriptor[1])
        owner = self.role_term(self.frame.role)
        process = (f"Participant.owned {owner} {owner} (invoke {self.frame.closed} {helper}) "
                   f"{paren(values_literal([arg.component() for arg in args]))}")
        stem = helper.split(".")[-1].removesuffix("Helper") or "helper"
        binder = self.names.fresh(stem + "Returned")
        typed = f"Values (Component (assignment F G)) {ty_list(results, True)}"
        values = [Sym("component", tuple(wire), f"{binder}.get {variable(position)}",
                      stem if len(results) == 1 else f"{stem}{position}")
                  for position, wire in enumerate(results)]
        if self.shared:
            pad = " " * indent
            op = f"(.localCall {helper} rfl {self.frame.role} {json.dumps(site)})"
            expanded = values_literal([value.expr for value in values])
            lemma = "denote_letOp_bind_after" if self.after() else "denote_letOp_bind"
            proof.append(f"{pad}refine NormalFormSteps.{lemma} m {op} _ _ _ _")
            proof.append(f"{pad}  ({process}) (fun {binder} => {expanded}) _{' _' if self.after() else ''} ?_ ?_")
            proof.append(f"{pad}· refine (PIR.Process.bind_done _).symm.trans (congrArg (PIR.Process.bind _) "
                         f"(funext fun {binder} => ?_))")
            cases = "".join(f"cases {binder} with | cons value{position} {binder} => "
                            for position in range(len(results)))
            proof.append(f"{pad}  {cases}cases {binder}; rfl")
            proof.append(f"{pad}intro {binder}")
        return Bind(process, binder, typed, self.run(rest, terminator, values + env, proof, indent))


class Step:
    """Proof lines for one instruction in shared mode: its site mark and its operation."""

    def __init__(self, evaluator, proof, pad):
        self.evaluator = evaluator
        self.proof = proof
        self.pad = pad
        self.pad_width = len(pad)
        self.enabled = evaluator.shared

    def mark(self, site):
        if self.enabled:
            self.proof.append(f"{self.pad}refine (Region.denote_letOp_done m (.mark {json.dumps(site)}) "
                              f"_ _ _ _ .nil rfl).trans ?_")

    def typed(self, values):
        if not values:
            return ".nil"
        literal = values_literal([value.component() for value in values])
        return f"({literal} : Values (Component (assignment F G)) {ty_list([value.wire for value in values], True)})"

    def done(self, op, values, how):
        if not self.enabled:
            return
        added = self.typed(values)
        side = self.side(how)
        if side is None:
            self.proof.append(f"{self.pad}refine (Region.denote_letOp_done m {op} _ _ _ _ {paren(added)} rfl).trans ?_")
        else:
            self.proof.append(f"{self.pad}refine (Region.denote_letOp_done m {op} _ _ _ _ {paren(added)} ?_).trans ?_")
            self.bullet(side)

    def halt(self, op, reason, how):
        if not self.enabled:
            return
        self.proof.append(f"{self.pad}apply Region.denote_letOp_halt m {op} _ _ _ _ .{reason}")
        for line in self.side(how, stop=True):
            self.proof.append(f"{self.pad}{line}")

    def call(self, op, action, binder, binder_type, values, how):
        if not self.enabled:
            return
        reply = "_" if binder == "_" else "value"
        replied = values if binder == "_" else [present(value.wire, "value") for value in values]
        self.proof.append(f"{self.pad}refine Region.denote_letOp_call m {op} _ _ _ _ {action} "
                          f"(fun {reply} => {self.typed(replied)}) _ ?_ ?_")
        self.bullet(self.side(how))
        self.proof.append(f"{self.pad}intro {binder}")
        if binder != "_":
            self.proof.append(f"{self.pad}change {binder_type} at {binder}")

    def bullet(self, lines):
        for index, line in enumerate(lines):
            self.proof.append(f"{self.pad}{'· ' if index == 0 else '  '}{line}")

    # The operation's meaning at this role, through the participant rule it reduces to.
    def side(self, how, stop=False):
        if how is None:
            return None
        evaluator = self.evaluator
        frame = evaluator.frame
        me = evaluator.role_term(frame.role).strip("()")
        separate = frame.separate
        kind = how[0]
        if kind == "restrict":
            _, listed, value = how
            facts = "" if f"({me})" in listed.split(", ") or me in listed.split(", ") else f", Ne.symm {separate}"
            return [f"change PIR.Process.done (I := participantInterface F G) "
                    f"(one (F := F) (G := G) (ty := {bare_ty(value.wire, True)}) "
                    f"(Participant.restrict ([{listed}].contains ({me})) {paren(value.component())})) = _",
                    f"simp [Participant.restrict{facts}]",
                    "rfl"]
        if kind == "other":
            _, owner, helper, args = how
            return [f"change Participant.owned ({me}) {evaluator.role_term(owner)} (invoke {frame.closed} {helper}) "
                    f"{paren(values_literal([arg.component() for arg in args]))} = _",
                    f"rw [Participant.owned_other _ _ {frame.separate}]",
                    "rfl"]
        if kind == "missing":
            _, helper, args = how
            return [f"change Participant.owned ({me}) ({me}) (invoke {frame.closed} {helper}) "
                    f"{paren(values_literal([arg.component() for arg in args]))} = _",
                    "simp only [Participant.owned, ↓reduceIte]",
                    "rfl"]
        if kind == "owned":
            _, law, helper, args = how
            arguments = (f"({values_literal([arg.expr for arg in args])} : Values (assignment F G) "
                         f"{ty_list([arg.wire for arg in args], True)})")
            lemma = "owned_halt" if stop else "owned_done"
            return [f"change Participant.owned ({me}) ({me}) (invoke {frame.closed} {helper}) {arguments}.present = _",
                    f"exact NormalFormSteps.{lemma} _ _ {paren(evaluator.fill(law.term, args))}"]
        if kind == "math":
            _, law, helper, args = how
            arguments = paren(values_literal([arg.component() for arg in args]))
            return [f"change invoke {frame.components} {helper} {arguments} = _",
                    f"rw [{evaluator.fill(law.term, args, law.components)}]",
                    "rfl"]
        if kind == "exchange":
            _, sender, receiver, site, wire, value = how
            facts = "" if sender == frame.role else f"{separate}, "
            return [f"change ((Participant.exchange (services := services) (Value := assignment F G) "
                    f"({me}) {evaluator.role_term(sender)} {evaluator.role_term(receiver)} "
                    f"{evaluator.qualified_site(site)} (ty := {bare_ty(wire, literal=True)}) "
                    f"{paren(value.component())}).interpret (participantActions F G)).bind "
                    f"(fun value => .done (one (F := F) (G := G) (ty := {bare_ty(wire, True)}) value)) = _",
                    f"simp only [Participant.exchange, {facts}↓reduceIte, "
                    f"PIR.Process.interpret, participantActions, PIR.Process.bind]",
                    "rfl"]
        if kind == "draw":
            _, owner, site, field_name, args = how
            handles = paren(values_literal([arg.component() for arg in args]))
            facts = "" if owner == frame.role else f"{separate}, "
            return [f"change ((Participant.query (services := services) (Value := assignment F G) "
                    f"({me}) {evaluator.role_term(owner)} {evaluator.qualified_site(site)} "
                    f"{json.dumps(field_name)} {handles}).interpret (participantActions F G)).bind "
                    f"(fun value => .done (one (F := F) (G := G) (ty := .field {json.dumps(field_name)}) value)) = _",
                    f"simp only [Participant.query, {facts}↓reduceIte, PIR.Process.interpret, PIR.Process.bind]",
                    "rfl"]
        if kind == "guard":
            _, owner, condition, fact = how
            facts = "" if owner == frame.role else f"{separate}, "
            if owner == frame.role and condition.kind == "present" and condition.expr == "false":
                facts = "Bool.false_eq_true, "
            lines = [f"change ((Participant.guard (services := services) (Value := assignment F G) "
                     f"({me}) {evaluator.role_term(owner)} {paren(condition.component())}).interpret "
                     f"(participantActions F G)).bind "
                     f"(fun _ => .done (Values.nil : Values (Component (assignment F G)) [])) = _"]
            if fact:
                lines.append(f"rw [show {condition.expr} = true from {fact}]")
            lines += [f"simp only [Participant.guard, {facts}↓reduceIte, PIR.Process.interpret, PIR.Process.bind]",
                      "rfl"]
            return lines
        raise GeneratorError(f"no side condition for {how}")


def variable(index):
    return "(.there " * index + ".here" + ")" * index


def operands(indices):
    return values_literal([variable(index) for index in indices])


def typed_op(evaluator, descriptor, results, site, roles):
    """The typed operation a retained instruction elaborates to."""
    head = descriptor[0]
    if head in BINARY or head in CONSTANTS:
        return f"(.calculate {calculation_op(descriptor)} rfl)"
    if head == "call":
        return f"(.calculate (.invoke {evaluator.helper_term(descriptor[1])}) rfl)"
    if head == "local_call":
        return f"(.localCall {evaluator.helper_term(descriptor[1])} rfl {roles.index(descriptor[2])} {json.dumps(site)})"
    if head == "exchange":
        return (f"(.exchange {lean_ty(results[0], literal=True)} {roles.index(descriptor[1])} "
                f"{roles.index(descriptor[2])} {json.dumps(site)})")
    if head == "restrict":
        return (f"(.restrict {lean_ty(results[0], literal=True)} "
                f"[{', '.join(str(roles.index(role)) for role in descriptor[1])}])")
    if head == "draw":
        return f"(.draw {roles.index(descriptor[1])} {json.dumps(descriptor[2])} {json.dumps(site)})"
    if head == "guard":
        return f"(.guard {roles.index(descriptor[1])} {json.dumps(site)})"
    raise GeneratorError(f"no typed operation for {head}")


def split_top(text, operator):
    """Split at top-level occurrences of `operator`, outside parentheses."""
    parts, depth, start, index = [], 0, 0, 0
    while index < len(text):
        character = text[index]
        if character == "(":
            depth += 1
        elif character == ")":
            depth -= 1
        elif depth == 0 and text.startswith(operator, index):
            parts.append(text[start:index].strip())
            index += len(operator)
            start = index
            continue
        index += 1
    parts.append(text[start:].strip())
    return parts


def bool_to_prop(text):
    """The proposition a generated Boolean states: `decide p` is `p`, `&&` is `∧`, `||` is `∨`."""
    text = text.strip()
    while outer_parenthesized(text):
        text = text[1:-1].strip()
    for operator, connective in ((" || ", " ∨ "), (" && ", " ∧ ")):
        parts = split_top(text, operator)
        if len(parts) > 1:
            return connective.join(paren(bool_to_prop(part)) if connective == " ∨ " else bool_to_prop(part)
                                   for part in parts)
    decided = re.fullmatch(r"decide \((.*)\)", text)
    if decided and outer_parenthesized("(" + decided.group(1) + ")"):
        return decided.group(1)
    if text == "true":
        return "True"
    return f"{paren(text)} = true"


def substitute(text, names):
    for name, replacement in sorted(names.items(), key=lambda item: -len(item[0])):
        text = re.sub(rf"(?<![\w.]){re.escape(name)}(?![\w'])", replacement, text)
    return text


def merge_pairs(*groups):
    """Concatenate (name, type) pairs, dropping names already present."""
    seen, out = set(), []
    for group in groups:
        for name, kind in group:
            if name not in seen:
                seen.add(name)
                out.append((name, kind))
    return out


def merge_binders(*groups):
    """Concatenate binder groups, dropping binders already present."""
    seen, out = set(), []
    for group in groups:
        for binder in re.findall(r"\(([^()]*)\)", group):
            names, kind = binder.split(" : ")
            kept = [name for name in names.split() if name not in seen]
            seen.update(kept)
            if kept:
                out.append(f"({' '.join(kept)} : {kind})")
    return " ".join(out) + (" " if out else "")



# ---------------------------------------------------------------------------
# Requests and module emission

def load_laws(table):
    laws = {}
    for key, entry in (table or {}).items():
        laws[key] = Law(entry["term"], list(entry.get("results", [])), entry.get("stop"),
                        bool(entry.get("components", False)))
    return laws


def law_pin(arg, fixed_inputs):
    """What a law asks of an argument at every use: the input it is, or the literal."""
    if arg.kind != "present":
        return None
    if arg.expr in fixed_inputs:
        return ("input", fixed_inputs[arg.expr])
    code = literal_code(arg.expr)
    if code is not None:
        return ("literal", code, arg.expr)
    return None


def pin_lean(pin):
    if pin is None:
        return ".free"
    if pin[0] == "input":
        return f".input {pin[1]}"
    return f".literal {pin[1]}"


def pin_json(pin):
    if pin is None:
        return None
    if pin[0] == "input":
        return str(pin[1])
    return ["literal", str(pin[1])]


def literal_code(template):
    """A literal result template as the normalizer reads it: false, true or a natural."""
    text = template.strip()
    if text == "false":
        return 0
    if text == "true":
        return 1
    if re.fullmatch(r"\d+", text):
        return int(text)
    return None


def law_shape(law):
    """A law's shape for the normalizer, as request JSON and as a Lean literal: a stop, a
    passing law on components (results that are arguments), literal results, or results
    the law's result function gives."""
    if law.stop:
        return ["stops", law.stop], f".stops .{law.stop}"
    if law.components:
        positions = []
        for template in law.results:
            match = re.fullmatch(r"\{(\d+)\}", template.strip())
            if match is None:
                raise GeneratorError(f"a law on components must return its arguments, not {template}")
            positions.append(int(match.group(1)))
        return ["passes", [str(position) for position in positions]], f".passes {list_literal(positions)}"
    outputs, lean = [], []
    for template in law.results:
        argument = re.fullmatch(r"\{(\d+)\}", template.strip())
        code = literal_code(template)
        if argument is not None:
            outputs.append(["argument", argument.group(1)])
            lean.append(f".argument {argument.group(1)}")
        elif code is not None:
            outputs.append(["literal", str(code)])
            lean.append(f".literal {code}")
        else:
            outputs.append(["result"])
            lean.append(".result")
    if all(output == ["result"] for output in outputs):
        return "returns", ".returns []"
    return ["returns", outputs], f".returns [{', '.join(lean)}]"


def site_names(unit_function_blocks, renames):
    """Lean names of the action sites, from source labels where present."""
    sites, used = {}, set()
    labels = {}
    for site in unit_function_blocks:
        label = decode_label(site)
        if label:
            labels.setdefault(label[0], []).append(site)
    for site in unit_function_blocks:
        if site in renames:
            name = renames[site]
        else:
            label = decode_label(site)
            if label:
                text, position = label
                many = len(labels[text]) > 1
                name = camel(f"{text}_{position}" if many and position is not None else text) + "Site"
            else:
                name = camel(site) + "Site"
        if name in used:
            raise GeneratorError(f"two sites are both named {name}; rename one in the request's sites table")
        used.add(name)
        sites[site] = name
    return sites


# ---------------------------------------------------------------------------
# Forms of the Lean normalizer
#
# With `proof = "normal-form"`, a role's equation is an instance of the
# normalizer's soundness theorem: the compiled normalizer (the `normal-form`
# mode of `structured-source`) prints the role's form as JSON, this module
# prints it as a Lean literal, and the kernel checks that the normalizer
# returns exactly that literal and that its denotation is the readable process.
# The compiled run is not trusted.

STRUCTURED_SOURCE = Path(os.environ.get("ZKC_STRUCTURED_SOURCE", ROOT / "lean/.lake/build/bin/structured-source"))
NORMALIZER_MODULE = "Zkc.Source.Structured.NormalForm.Presentation"


def run_normalizer(fixture, request, name):
    """The form the compiled normalizer computes for a role's request."""
    if not STRUCTURED_SOURCE.is_file():
        raise GeneratorError(f"{STRUCTURED_SOURCE} is missing; build it with `lake build structured-source`")
    path = ROOT / "build/normal-forms" / (re.sub(r"[^0-9A-Za-z]+", "-", json.dumps(request))[:120] + ".json")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(request), encoding="utf-8")
    try:
        completed = subprocess.run([str(STRUCTURED_SOURCE), "normal-form", str(ROOT / fixture), str(path)],
                                   capture_output=True, text=True, check=False)
    finally:
        path.unlink()
    try:
        result = json.loads(completed.stdout)
    except json.JSONDecodeError:
        raise GeneratorError(f"the normalizer printed no form: {completed.stdout}{completed.stderr}")
    if result.get("status") != "normalized":
        raise GeneratorError(f"{name}: the normalizer refused the request: {result.get('code')}")
    return result


def lean_wire(wire):
    return lean_ty(wire, literal=True)


def lean_op(op):
    head, args = op[0], op[1:]
    if head == "unsupported":
        raise GeneratorError("the form contains an operation the printer does not support")
    if not args:
        return f".{head}"
    rendered = []
    for arg in args:
        if isinstance(arg, bool):
            rendered.append("true" if arg else "false")
        elif isinstance(arg, int):
            rendered.append(str(arg))
        elif isinstance(arg, list):
            rendered.append(lean_wire(arg))
        else:
            rendered.append(json.dumps(arg))
    return f"(.{head} {' '.join(rendered)})"


def lean_term(term):
    head = term[0]
    if head == "var":
        return f"(.var {variable(term[1])})"
    if head == "result":
        return f"(.result {variable(term[1])} {variable(term[2])})"
    if head == "index":
        return f"(.index {term[1]})"
    if head == "bool":
        return f"(.bool {'true' if term[1] else 'false'})"
    if head == "field":
        return f"(.field {json.dumps(term[1])} {term[2]})"
    if head == "groupZero":
        return f"(.groupZero {json.dumps(term[1])})"
    if head == "calc":
        return f"(.calc {lean_op(term[1])} rfl {lean_terms(term[2])} {variable(term[3])})"
    if head == "law":
        return f"(.law ⟨{term[1]}, by decide⟩ {lean_terms(term[2])} {variable(term[3])})"
    raise GeneratorError(f"unknown term {head}")


def lean_terms(terms):
    text = ".nil"
    for term in reversed(terms):
        text = f"(.cons {lean_term(term)} {text})"
    return text


def lean_comp(comp):
    head = comp[0]
    if head == "absent":
        return ".absent"
    if head == "present":
        return f"(.present {lean_term(comp[1])})"
    if head == "input":
        return f"(.input {variable(comp[1])})"
    if head == "read":
        return f"(.read {variable(comp[1])} {variable(comp[2])})"
    raise GeneratorError(f"unknown component {head}")


def lean_equality(equality):
    return f"(.{equality[0]} {json.dumps(equality[1])})" if len(equality) > 1 else f".{equality[0]}"


def qualified(text, inductive):
    """A constructor application whose head names its inductive, for positions whose
    expected type does not determine it."""
    if text.startswith("(."):
        return f"({inductive}." + text[2:]
    if text.startswith("."):
        return f"{inductive}." + text[1:]
    return text


def lean_form(form, indent, helpers, repeats=None, callees=None):
    """A form literal; each node's continuation follows on the next line. `repeats` gives
    each repeat site's spec and callback region as Lean terms, and `callees` each callee's
    signature term and whether each of its binders is a present value."""
    pad = " " * indent
    head = form[0]
    if head == "done":
        return f"{pad}.done {paren(values_literal([lean_comp(comp) for comp in form[1]])) if form[1] else '.nil'}"
    if head == "halt":
        return f"{pad}.halt .{form[1]}"
    if head == "send":
        _, ty, site, peer, value, rest = form
        return (f"{pad}.send {lean_wire(ty)} {json.dumps(site)} {peer} {lean_term(value)} <|\n"
                + lean_form(rest, indent, helpers, repeats, callees))
    if head == "receive":
        _, ty, site, peer, rest = form
        return f"{pad}.receive {lean_wire(ty)} {json.dumps(site)} {peer} <|\n" + lean_form(rest, indent, helpers, repeats, callees)
    if head == "query":
        _, site, request, args, rest = form
        return (f"{pad}.query {json.dumps(site)} {json.dumps(request)} {lean_terms(args)} <|\n"
                + lean_form(rest, indent, helpers, repeats, callees))
    if head == "split":
        _, subject, absent_form, present_form = form
        return (f"{pad}.split {lean_comp(subject)}\n{pad}  (\n" + lean_form(absent_form, indent + 4, helpers, repeats, callees)
                + f")\n{pad}  (\n" + lean_form(present_form, indent + 4, helpers, repeats, callees) + ")")
    if head == "guard":
        _, equality, left, right, rest = form
        return (f"{pad}.guard {lean_equality(equality)} {lean_term(left)} {lean_term(right)} <|\n"
                + lean_form(rest, indent, helpers, repeats, callees))
    if head == "strict":
        _, helper, args, rest = form
        return (f"{pad}.strict {helpers(helper)} {lean_terms(args)} <|\n" + lean_form(rest, indent, helpers, repeats, callees))
    if head == "byLaw":
        _, entry, helper, rest = form
        return (f"{pad}.byLaw ⟨{entry}, by decide⟩ {helpers(helper)} <|\n"
                + lean_form(rest, indent, helpers, repeats, callees))
    if head == "owned":
        _, owner, helper, args, rest = form
        return (f"{pad}.owned {owner} {helpers(helper)} {paren(values_literal([lean_comp(c) for c in args]))} <|\n"
                + lean_form(rest, indent, helpers, repeats, callees))
    if head == "repeat":
        _, site, count, state, captures, rest = form
        if site not in (repeats or {}):
            raise GeneratorError(f"the form repeats at {site}; name its spec and callback region")
        spec, callback = repeats[site]
        return (f"{pad}.repeat {paren(spec)} {json.dumps(site)} {paren(callback)} {lean_comp(count)}\n"
                f"{pad}  {paren(values_literal([lean_comp(c) for c in state]))}\n"
                f"{pad}  {paren(values_literal([lean_comp(c) for c in captures]))} <|\n"
                + lean_form(rest, indent, helpers, repeats, callees))
    if head == "apply":
        _, callee, roles, site, args, rest = form
        if callees is None or callee >= len(callees):
            raise GeneratorError(f"the form applies callee {callee}; name the callees")
        signature, values = callees[callee]
        rendered = [qualified(lean_term(arg), "NormalForm.Term") if present else qualified(lean_comp(arg), "NormalForm.Comp")
                    for arg, (present, _) in zip(args, values)]
        slots = list_literal([f"{'.value' if present else '.component'} {lean_wire(wire)}" for present, wire in values])
        arguments = (f"({values_literal(rendered)} : Values (NormalForm.Argument _ _) {slots})"
                     if rendered else ".nil")
        return (f"{pad}.apply ⟨{callee}, by decide⟩ {signature} {list_literal(roles)} {json.dumps(site)}\n"
                f"{pad}  {arguments} <|\n"
                + lean_form(rest, indent, helpers, repeats, callees))
    raise GeneratorError(f"unsupported form node {head}")


def binders_literal(names):
    """A tuple of binder values, first binder first."""
    text = ".nil"
    for name in reversed(names):
        text = f"(.cons {name} {text})"
    return text[1:-1] if text != ".nil" else text


class Module:
    def __init__(self, request, path):
        self.request = request
        self.path = path
        self.unit = Unit(json.loads((ROOT / request["fixture"]).read_text(encoding="utf-8")))
        self.carrier = request.get("carrier", "CommRing")
        self.parts = []
        self.roles_info = {}
        self.declared = False
        self.helper_names = None
        self.emitted_sites = set()
        self.role_infos = {}
        self.signature_names = None
        self.applied = set()

    # -- shared pieces ---------------------------------------------------
    def variables(self):
        if self.declared:
            return ""
        self.declared = True
        if self.carrier == "Field":
            return ("variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] "
                    "[DecidableEq G]")
        return ("variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]\n"
                "  [DecidableEq F] [DecidableEq G]")

    def header(self):
        names = list(self.request["imports"])
        # Normal-form proofs cite the normalizer's soundness and its presentation lemmas.
        if any(role.get("proof") == "normal-form" for spec in self.request.get("shared", [])
               for role in spec.get("roles", [])) and NORMALIZER_MODULE not in names:
            names.append(NORMALIZER_MODULE)
        imports = "\n".join(f"public import {name}" for name in names)
        opens = " ".join(["Zkc.Source", "Zkc.Source.Structured", *self.request.get("open", [])])
        request = self.path.relative_to(ROOT) if self.path.is_relative_to(ROOT) else self.path
        options = "".join(f"set_option {option}\n" for option in self.request.get("options", []))
        summary = self.request.get("summary", "Participant normal forms")
        return (f"module\n\n{imports}\n\n@[expose] public section\n\n"
                f"/-! {summary}, generated by `lean/bridges/structured/normal_forms.py`\n"
                f"from `{request}` and the retained unit\n`{self.request['fixture']}`.\n"
                f"Regenerate after the unit or the request changes; do not edit by hand. Every\n"
                f"definition and equation below is checked by the kernel. -/\n"
                f"namespace {self.request['namespace']}\nopen {opens}\n\n{options}")

    # -- root participants -------------------------------------------------
    def root(self, spec):
        unit = self.unit
        entry = unit.function(spec.get("protocol", unit.entry))
        program = spec.get("program", "program")
        names = spec["inputs"]
        if len(names) != len(entry.inputs):
            raise GeneratorError(f"the root has {len(entry.inputs)} inputs; the request names {len(names)}")
        sites = site_names(action_sites(entry.body), self.request.get("sites", {}))
        out = ["/-! Action sites of the root, named from their source labels. -/"]
        for site, name in sites.items():
            out.append(f"def {name} : String := {json.dumps(site)}")
        out.append("")
        out.append(self.variables())
        out.append("")
        role_names = spec["roles"]
        for role, role_name in enumerate(role_names):
            held = [index for index, scope in enumerate(entry.input_scopes) if role in scope]
            binders = self.binders([(names[index], value_type(entry.inputs[index])) for index in held])
            arguments = " ".join(names[index] for index in held)
            components = [f"some {names[index]}" if index in held else "none" for index in range(len(names))]
            inputs_name = f"{role_name}Inputs"
            out.append(f"/-- The {role_name}'s own inputs, in port order; the others are absent. -/")
            out.append(f"def {inputs_name} {binders}:\n    Values (Component (assignment F G)) "
                       f"{program}.payload.entry.inputs :=\n  {values_literal(components)}\n")
            frame = Frame(unit, entry.roles, role, "root", sites, self.helpers(), {}, {})
            taken = Names(names + list(sites.values()))
            env = [present(wire, names[index]) if index in held else absent(wire)
                   for index, wire in enumerate(entry.inputs)]

            def finish(values, proof, pad):
                return Done(values_literal([value.component() for value in values]))

            node = Evaluator(frame, taken, finish).run(entry.body[1], entry.body[2], env, [], 2)
            process = f"{role_name}Process"
            text = render_process(node, 2)
            used = [index for index in held if re.search(rf"(?<![\w.]){re.escape(names[index])}(?![\w'])", text)]
            used_binders = self.binders([(names[index], value_type(entry.inputs[index])) for index in used])
            application = f"{process} {' '.join(names[index] for index in used)}".strip()
            out.append(f"/-- The {role_name}'s normal form: its ordered actions and its returned tuple. -/")
            out.append(f"def {process} {used_binders}:\n    PIR.Process (participantInterface F G)\n"
                       f"      (Values (Component (assignment F G)) {program}.payload.entry.outputs) :=\n"
                       f"{text}\n")
            proof = spec.get("proof", "rfl")
            if proof not in ("rfl", "kernel"):
                raise GeneratorError("root equations are definitional: their proof is rfl or kernel")
            tactic = "kernel_rfl" if proof == "kernel" else "rfl"
            out.append(f"theorem {role_name}_process {binders}:\n    {program}.participant F G {role} "
                       f"({inputs_name} {arguments}) =\n      {application} := by\n  {tactic}\n")
            replies = self.run_equation(out, program, role, role_name, inputs_name, arguments, binders, node)
            self.roles_info[role] = {"name": role_name, "inputs": inputs_name, "held": held,
                                     "arguments": arguments, "binders": binders, "replies": replies,
                                     "node": node}
        self.parts.append("\n".join(out))
        self.root_spec = (entry, sites, names, role_names, program)

    def helper_term_of(self, name):
        return Evaluator(Frame(self.unit, [], 0, "root", {}, self.helpers(), {}, {}), Names(), None).helper_term(name)

    def callback_sites(self):
        """Repeat site -> callback name for the callbacks `[bodies]` names; each is given by
        a source label its callback carries, or by the repeat's site."""
        bodies = self.request.get("bodies", {})
        if "callbacks" not in bodies:
            return {}
        protocol = self.unit.function(bodies.get("protocol", self.unit.entry))
        return {locate_repeat(protocol.body, key)[4]: name for name, key in bodies["callbacks"].items()}

    def repeat_site(self, spec):
        """The site of the repeat a `[[shared]]` entry states over: a callback `[bodies]`
        names, a source label its callback carries, or the repeat's site."""
        key = spec["repeat"]
        callbacks = self.request.get("bodies", {}).get("callbacks", {})
        key = callbacks.get(key, key)
        protocol = self.unit.function(spec.get("protocol", self.unit.entry))
        return locate_repeat(protocol.body, key)[4]

    def repeat_terms(self):
        """Repeat site -> (spec, callback function) for the callbacks this request names in
        `[bodies]` and states over in a `[[shared]]` entry with that repeat."""
        callbacks = self.callback_sites()
        terms = {}
        for spec in self.request.get("shared", []):
            if not spec.get("repeat"):
                continue
            site = self.repeat_site(spec)
            if site in callbacks:
                terms[site] = (f"{callbacks[site]}Spec", spec["function"])
        return terms

    def repeat_regions(self, spec):
        """Repeat site -> (spec, callback region) as Lean terms, for printing repeat nodes:
        from callback entries that name both, and from a whole-body entry's `repeat_spec`
        and `callback_body` for the repeats directly in its body."""
        regions = {}
        named = self.repeat_terms()
        for other in self.request.get("shared", []):
            if not other.get("repeat"):
                continue
            site = self.repeat_site(other)
            repeat_spec = other.get("repeat_spec") or named.get(site, (None, None))[0]
            if repeat_spec:
                regions[site] = (repeat_spec, other["body"])
        if spec.get("repeat_spec") and spec.get("callback_body"):
            protocol = self.unit.function(spec.get("protocol", self.unit.entry))
            for instruction in protocol.body[1]:
                if instruction[0][0] == "protocol_repeat":
                    regions[instruction[4]] = (spec["repeat_spec"], spec["callback_body"])
        return regions

    def slot_names(self, role):
        """Repeat site -> {slot position: name} for the slots this request names at `role`."""
        names = {}
        for spec in self.request.get("shared", []):
            if not spec.get("repeat"):
                continue
            site = self.repeat_site(spec)
            instruction = find_repeat(self.unit.function(spec.get("protocol", self.unit.entry)).body, site)
            protocol_roles = self.unit.function(spec.get("protocol", self.unit.entry)).roles
            scopes = [[protocol_roles.index(owner) for owner in scope] for scope in instruction[0][4]]
            owned = [index for index, scope in enumerate(scopes) if role in scope]
            for role_spec in spec.get("roles", []):
                if role_spec["role"] == role:
                    names[site] = {index: slot["name"] for index, slot in zip(owned, role_spec["slots"])}
        return names

    def binders(self, pairs):
        if not pairs:
            return ""
        groups = []
        for name, kind in pairs:
            if groups and groups[-1][1] == kind:
                groups[-1][0].append(name)
            else:
                groups.append(([name], kind))
        return " ".join(f"({' '.join(group)} : {kind})" for group, kind in groups) + " "

    def helpers(self):
        """Lean names of retained helpers: discovered in the listed body modules, then the request's table."""
        if self.helper_names is None:
            names = {}
            parent = self.request["namespace"].rsplit(".", 1)[0] + "."
            for module in self.request.get("helper_modules", []):
                text = (ROOT / module).read_text(encoding="utf-8")
                namespace = re.search(r"^namespace (\S+)", text, re.MULTILINE).group(1)
                prefix = namespace.removeprefix(parent) if namespace.startswith(parent) else namespace
                for local, raw in re.findall(r"abbrev (\w+) : Helper :=\s*⟨\"([^\"]+)\"", text):
                    names.setdefault(raw, f"{prefix}.{local}")
            names.update(self.request.get("helpers", {}))
            self.helper_names = names
        return self.helper_names

    def signatures(self):
        """Lean names of retained protocol signatures, declared in the listed body modules."""
        if self.signature_names is None:
            names = {}
            parent = self.request["namespace"].rsplit(".", 1)[0] + "."
            for module in self.request.get("helper_modules", []):
                text = (ROOT / module).read_text(encoding="utf-8")
                namespace = re.search(r"^namespace (\S+)", text, re.MULTILINE).group(1)
                prefix = namespace.removeprefix(parent) if namespace.startswith(parent) else namespace
                for local, raw in re.findall(r"def (\w+) : ProtocolSignature where\s+name := \"([^\"]+)\"", text):
                    names.setdefault(raw, f"{prefix}.{local}")
                for local, raw in re.findall(r"def (\w+) : ProtocolSignature :=\s*⟨\"([^\"]+)\"", text):
                    names.setdefault(raw, f"{prefix}.{local}")
            names.update(self.request.get("signatures", {}))
            self.signature_names = names
        return self.signature_names

    def run_equation(self, out, program, role, role_name, inputs_name, arguments, binders, node):
        """Reply script and observed run of a branch-free root process."""
        linear = linear_actions(node)
        if linear is None:
            return None
        actions, last = linear
        replied = [call for call in actions if call.binder != "_"]
        reply_binders = self.binders([(call.binder, call.binder_type) for call in replied])
        by_type = {}
        for call in replied:
            if call.event.kind == "receive":
                head = call.event.ty.split()[0]
                by_type.setdefault(head, []).append((call.event.site, call.binder))
        drawn = [(call.event.site, call.binder) for call in replied if call.event.kind == "query"]
        out.append(f"/-- The replies of one {role_name} run: received values by type and site, and\n"
                   f"drawn values by site. Other requests are refused. -/")
        out.append(f"def {role_name}Replies {reply_binders}: ReplyScript F G where")
        out.append("  receive")
        for head, entries in by_type.items():
            chain = "".join(f"if site = {site} then some {binder} else " for site, binder in entries)
            out.append(f"    | {head}{'' if head in ('.boolean', '.index') else ' _'}, site => {chain}none")
        out.append("    | _, _ => none")
        chain = "".join(f"if site = {site} then some {binder} else " for site, binder in drawn)
        out.append(f"  draw site := {chain}none\n")
        returned = f".returned {paren(last.expr)}" if isinstance(last, Done) else f".stopped .{last.reason}"
        events = ",\n         ".join(call.action[1:-1] for call in actions)
        reply_arguments = " ".join(call.binder for call in replied)
        out.append(f"/-- The {role_name}'s run on those replies: its outcome and its ordered actions. -/")
        out.append(f"theorem {role_name}_run {binders}{reply_binders}:\n    ({role_name}Replies {reply_arguments}).run "
                   f"({program}.participant F G {role} ({inputs_name} {arguments})) =\n"
                   f"      ⟨{returned}, (),\n        [{events}]⟩ := by\n"
                   f"  rw [{role_name}_process]\n  rfl\n")
        return [(call.binder, call.binder_type) for call in replied]

    # -- typed bodies ------------------------------------------------------
    def bodies(self, spec):
        """The typed body of one retained protocol, with its repeat callback named and its
        repeat maximum a parameter, so units that differ only in that maximum share it."""
        if "callbacks" in spec:
            return self.unit_bodies(spec)
        protocol = self.unit.function(spec["protocol"])
        name = spec["name"]
        callback_name = spec["callback"]
        maximum = spec.get("maximum", "maximum")
        instructions, terminator = protocol.body[1], protocol.body[2]
        repeats = [index for index, row in enumerate(instructions) if row[0][0] == "protocol_repeat"]
        if len(repeats) != 1 or repeats[0] != len(instructions) - 1:
            raise GeneratorError("the protocol must end with exactly one repeat followed by its return")
        repeat = instructions[-1]
        _, state_count, _, repeat_roles, scopes = repeat[0]
        callback_inputs, state, callback = repeat[3][0]
        captures = callback_inputs[1 + state_count:]
        if terminator[0] != "return" or any(index >= state_count for index in terminator[1]):
            raise GeneratorError("the return after the repeat must read its state only")
        roles = protocol.roles
        out = [f"abbrev {name}Inputs : List Ty :=\n  {ty_list(protocol.inputs, True)}\n",
               f"abbrev {name}Outputs : List Ty :=\n  {ty_list(protocol.outputs, True)}\n",
               "/-- The repeat-carried slots, which precede the unchanged outer SSA environment. -/",
               f"abbrev repeatState : List Ty :=\n  {ty_list(state, True)}\n"]
        role_indices = "[" + ", ".join(str(roles.index(role)) for role in repeat_roles) + "]"
        scope_indices = "[" + ", ".join("[" + ", ".join(str(roles.index(role)) for role in scope) + "]"
                                        for scope in scopes) + "]"
        out.append(f"abbrev repeatSpec ({maximum} : Nat) : RepeatSpec :=\n"
                   f"  ⟨repeatState, {ty_list(captures, True)}, {role_indices},\n    {scope_indices}, {maximum}⟩\n")
        returned = values_literal([f"state.get {variable(index)}" for index in terminator[1]])
        out.append("/-- The state positions the retained return reads, in output order. -/")
        out.append(f"abbrev {name}ReturnIndices : List Nat := {list_literal(terminator[1])}\n")
        out.append("/-- The retained return permutation of the repeat's state, for any value family. -/")
        out.append(f"def {name}ReturnValues {{Value : Ty → Type}} (state : Values Value repeatState) :\n"
                   f"    Values Value {name}Outputs :=\n  {returned}\n")
        out.append("/-- The retained return of the repeat's state. -/")
        out.append(f"def {name}Return (tail : List Ty) : Region protocolDialect (repeatState ++ tail)\n"
                   f"    {name}Outputs :=\n  .ret {paren(operands(terminator[1]))}\n")
        out.append("/-- One iteration of the repeat: every retained operation, with its site mark. -/")
        out.append(f"def {callback_name}Body : Region protocolDialect\n"
                   f"    (.index :: (repeatState ++ {ty_list(captures, True)})) repeatState :=\n"
                   f"{self.chain(callback, roles, '  ')}\n")
        prelude = ["block", instructions[:-1], None]
        repeat_op = f"(.repeat (repeatSpec {maximum}) {json.dumps(repeat[4])})"
        last = (f"  .letOp (.mark {json.dumps(repeat[4])}) .nil .nil <|\n"
                f"  .letOp {repeat_op} {paren(operands(repeat[1]))} (.cons {callback_name}Body .nil) <|\n"
                f"  {name}Return _")
        out.append("/-- The whole body, with the repeat maximum as a parameter. -/")
        out.append(f"def {name}Body ({maximum} : Nat) : Region protocolDialect {ty_list(protocol.inputs, True)}\n"
                   f"    {ty_list(protocol.outputs, True)} :=\n"
                   f"{self.chain(prelude, roles, '  ', last)}\n")
        if "declaration" in spec:
            # The admitted declaration's checked tree is this body at its own maximum.
            views, declaration = spec["views"], spec["declaration"]
            out.append(f"/-- The admitted `{declaration}` declaration is this body at maximum {spec['value']}. -/")
            out.append(f"theorem {name}Body_raw : {views}.{declaration}Definition.raw =\n"
                       f"    ({name}Body {spec['value']}).erase := by\n"
                       f"  refine {views}.{declaration}_raw.trans ?_\n"
                       f"  unfold {name}Body {callback_name}Body {name}Return\n  rfl\n")
        self.parts.append("\n".join(out))

    def unit_bodies(self, spec):
        """The typed body of one retained protocol of this unit with every repeat callback
        named, nested ones included, and protocol applications through the callee's declared
        signature. Each repeat's static maximum is read from the export and named, so a
        statement over the body need not spell it."""
        protocol = self.unit.function(spec.get("protocol", self.unit.entry))
        name = spec["name"]
        callbacks = self.callback_sites()
        roles = protocol.roles
        repeats = []

        def collect(block):
            # Post-order: a nested callback precedes the callback that repeats it.
            for instruction in block[1]:
                if instruction[0][0] == "protocol_repeat":
                    collect(instruction[3][0][2])
                    repeats.append(instruction)

        collect(protocol.body)
        sites = [instruction[4] for instruction in repeats]
        if sorted(sites) != sorted(callbacks):
            raise GeneratorError(f"the body repeats at sites {sites}; the request names callbacks for "
                                 f"{sorted(callbacks)}")
        out = [f"abbrev {name}Inputs : List Ty :=\n  {ty_list(protocol.inputs, True)}\n",
               f"abbrev {name}Outputs : List Ty :=\n  {ty_list(protocol.outputs, True)}\n"]
        for instruction in repeats:
            (_, state_count, maximum, repeat_roles, scopes), site = instruction[0], instruction[4]
            callback = callbacks[site]
            callback_inputs, state, block = instruction[3][0]
            captures = callback_inputs[1 + state_count:]
            role_indices = list_literal([roles.index(role) for role in repeat_roles])
            scope_indices = scope_literal([[roles.index(role) for role in scope] for scope in scopes])
            out.append(f"/-- The slots the `{callback}` repeat carries, which precede its captures. -/")
            out.append(f"abbrev {callback}State : List Ty :=\n  {ty_list(state, True)}\n")
            out.append(f"/-- The values the `{callback}` callback captures unchanged. -/")
            out.append(f"abbrev {callback}Captures : List Ty :=\n  {ty_list(captures, True)}\n")
            out.append(f"/-- The static maximum of the `{callback}` repeat in this unit. -/")
            out.append(f"abbrev {callback}Maximum : Nat := {int(maximum)}\n")
            out.append(f"/-- The `{callback}` repeat: its state, captures, roster, state scopes and maximum. -/")
            out.append(f"abbrev {callback}Spec : RepeatSpec :=\n"
                       f"  ⟨{callback}State, {callback}Captures, {role_indices},\n"
                       f"    {scope_indices}, {callback}Maximum⟩\n")
            out.append(f"/-- One iteration of the `{callback}` repeat: every retained operation, with its "
                       f"site mark. -/")
            out.append(f"def {callback}Body : Region protocolDialect\n"
                       f"    (.index :: ({callback}State ++ {callback}Captures)) {callback}State :=\n"
                       f"{self.chain(block, roles, '  ', callbacks=callbacks)}\n")
        out.append("/-- The whole body, every repeat through its named callback. -/")
        out.append(f"def {name}Body : Region protocolDialect {ty_list(protocol.inputs, True)}\n"
                   f"    {ty_list(protocol.outputs, True)} :=\n"
                   f"{self.chain(protocol.body, roles, '  ', callbacks=callbacks)}\n")
        if "declaration" in spec:
            views, declaration = spec["views"], spec["declaration"]
            unfolds = " ".join([f"{name}Body"] + [f"{callbacks[site]}Body" for site in reversed(sites)])
            out.append(f"/-- The admitted `{declaration}` declaration is this body. -/")
            out.append(f"theorem {name}Body_raw : {views}.{declaration}Definition.raw =\n"
                       f"    {name}Body.erase := by\n"
                       f"  refine {views}.{declaration}_raw.trans ?_\n"
                       f"  unfold {unfolds}\n  rfl\n")
        self.parts.append("\n".join(out))

    def chain(self, block, roles, pad, last=None, callbacks=None):
        lines = []
        frame = Frame(self.unit, roles, 0, "root", {}, self.helpers(), {}, {})
        evaluator = Evaluator(frame, Names(), None)
        for descriptor, operand_list, results, _, site in block[1]:
            lines.append(f"{pad}.letOp (.mark {json.dumps(site)}) .nil .nil <|")
            regions = ".nil"
            if callbacks is not None and descriptor[0] == "protocol_repeat":
                op = f"(.repeat {callbacks[site]}Spec {json.dumps(site)})"
                regions = f"(.cons {callbacks[site]}Body .nil)"
            elif callbacks is not None and descriptor[0] == "protocol_apply":
                callee = self.unit.function(descriptor[1])
                op = (f"(.protocolApply {self.signature_term(callee)} "
                      f"{list_literal([roles.index(role) for role in descriptor[2]])} {json.dumps(site)})")
            else:
                op = typed_op(evaluator, descriptor, results, site, roles)
            lines.append(f"{pad}.letOp {op} {paren(operands(operand_list))} {regions} <|")
        if last is not None:
            lines.append(last)
        else:
            kind, indices = block[2]
            if kind not in ("return", "yield"):
                raise GeneratorError(f"unsupported terminator {kind}")
            lines.append(f"{pad}.ret {paren(operands(indices))}")
        return "\n".join(lines)

    # -- the selected contract clause -------------------------------------
    def contract(self, spec):
        """Relation binding, formula process and observed decision of one clause."""
        entry, sites, names, role_names, program = self.root_spec
        clause = next((row for row in self.unit.contracts.get(entry.name, []) if row[1] == spec["clause"]), None)
        if clause is None:
            raise GeneratorError(f"the root has no contract clause {spec['clause']!r}")
        kind, clause_name, (relation_name, selectors), residual, decision = clause
        if kind != "target" or residual is not None or decision is None:
            raise GeneratorError("only target clauses with a decision and no residual are supported")
        relation = self.unit.relations[relation_name]
        inputs, outputs, kinds, formula = relation[6], relation[7], relation[8], relation[9]
        if outputs != [["bool"]]:
            raise GeneratorError("the relation must return one Boolean")
        arguments = []
        for position, selector in enumerate(selectors):
            if selector[0] != "input":
                raise GeneratorError("relation arguments must be read from root inputs")
            arguments.append((names[selector[1]], inputs[position], kinds[position], selector))
        decision_role = entry.roles.index(decision[2])
        if decision[0] != "output":
            raise GeneratorError("the decision must be a root output")
        info = self.roles_info.get(decision_role)
        if info is None or info["replies"] is None:
            raise GeneratorError("the deciding role needs a branch-free normal form")
        verifier = info["name"]
        out = ["/-! The selected contract clause: its relation binding, the formula's process and",
               "the decision observed at the deciding role. -/",
               "def owner : ContractBinding imported := by bind_contract\n",
               f"def clauseIndex : Fin owner.contract.clauses.length := owner.namedClause {json.dumps(clause_name)}\n",
               "def clause : ContractClause := owner.clause clauseIndex\n",
               f"theorem owner_is_entry : owner.protocol = {program}.payload.entry := rfl\n",
               "def application : ApplicationBinding owner clause.subject := by bind_contract\n"]
        for position, (name, wire, _, _) in enumerate(arguments):
            path = "(.there " * position + ".here" + ")" * position
            out.append(f"def {name}Selector : BoundarySelector owner.protocol.signature {lean_ty(wire)} :=\n"
                       f"  application.selectors.get {paren(path)}\n")
        out.append(f"def decisionSelector : BoundarySelector owner.protocol.signature .boolean :=\n"
                   f"  ⟨.output {paren('(.there ' * decision[1] + '.here' + ')' * decision[1])}, "
                   f"⟨{decision_role}, by decide +kernel⟩, by decide +kernel⟩\n")
        out.append(f"theorem exact_clause : clause.kind = .target ∧ clause.name = {json.dumps(clause_name)} ∧\n"
                   f"    clause.residual = none ∧ clause.decision = some decisionSelector.erase := by\n"
                   f"  decide +kernel\n")
        out.append("theorem all_clauses : owner.contract.clauses = [clause] := rfl\n"
                   if len(self.unit.contracts.get(entry.name, [])) == 1 else "")
        out.append("def formulaBinding : FormulaBinding imported application.relation := by bind_contract\n")
        out.append("theorem no_formula_preconditions : formulaBinding.preconditions = [] := rfl\n")
        out.append(self.variables() + "\n")
        binders = self.binders([(name, value_type(wire)) for name, wire, _, _ in arguments])
        argument_names = " ".join(name for name, _, _, _ in arguments)
        out.append("/-- The relation's arguments, in its declared order. -/")
        out.append(f"def arguments {binders}:\n    Values (assignment F G) formulaBinding.definition.inputs :=\n"
                   f"  {values_literal([name for name, _, _, _ in arguments])}\n")
        out.append("/-- The target holds when the retained formula returns `true`. -/")
        out.append(f"def Relation {binders}: Prop :=\n  formulaBinding.process (arguments {argument_names}) =\n"
                   f"    .done (.cons true .nil)\n")
        helper = self.unit.function(formula)
        frame = Frame(self.unit, [], 0, "root", {}, self.helpers(), {}, {})
        env = [present(wire, name) for name, wire, _, _ in arguments]

        def finish(values, proof, pad):
            return Done(values[0].expr)
        formula_node = Evaluator(frame, Names(argument_names.split()), finish).run(
            helper.body[1], helper.body[2], env, [], 2)
        if not isinstance(formula_node, Done):
            raise GeneratorError("the formula must compute its decision without stops")
        decision_bool = formula_node.expr
        decision_prop = bool_to_prop(decision_bool)
        out.append(f"theorem formula_process {binders}:\n    formulaBinding.process (arguments {argument_names}) =\n"
                   f"      .done (.cons {paren(decision_bool)} .nil) := by\n  rfl\n")
        out.append(f"theorem relation_iff {binders}:\n    Relation {argument_names} ↔ {decision_prop} := by\n"
                   f"  unfold Relation\n  rw [formula_process]\n"
                   f"  change (PIR.Process.done (I := closedInterface) (.cons {paren(decision_bool)} .nil :\n"
                   f"    Values (assignment F G) [.boolean]) = .done (.cons true .nil)) ↔ _\n  simp\n")
        gets = {name: "args.get " + paren("(.there " * position + ".here" + ")" * position)
                for position, (name, _, _, _) in enumerate(arguments)}
        substituted = substitute(decision_prop, gets)
        out.append("/-- The subject's only relation is this formula. -/")
        out.append("def environment : RelationEnvironment imported F G where\n  meanings index args := by\n"
                   "    have same : index = application.relation.index := by\n      apply Fin.ext\n"
                   "      have bound : index.val < 1 := index.isLt\n      change index.val = 0\n      omega\n"
                   "    subst index\n"
                   f"    exact Relation {' '.join(paren(gets[name]) for name, _, _, _ in arguments)}\n")
        out.append("def target : InterpretedApplication owner clause.subject F G environment where\n"
                   "  binding := application\n"
                   f"  interpretation := .formula formulaBinding rfl (fun _ => True)\n"
                   f"    (fun args => {substituted})\n    inferInstance\n")
        cases = "".join(f"  cases args with | cons {name} args =>\n" for name, _, _, _ in arguments)
        lemmas = [lemma for operator, lemma in ((" && ", "Bool.decide_and"), (" || ", "Bool.decide_or"))
                  if operator in decision_bool]
        closing = f"  simp only [{', '.join(lemmas)}]\n  rfl\n" if lemmas else "  rfl\n"
        out.append("theorem target_formula_law : (target (F := F) (G := G)).interpretation.FormulaLaw := by\n"
                   f"  intro args _\n{cases}  cases args\n{closing}")
        out.append("def rootInvocation : InvocationCoordinate := ⟨0, []⟩\n")
        logical = [(name, wire, role_kind) for name, wire, role_kind, _ in arguments
                   if role_kind in ("parameter", "witness")]
        logical_binders = self.binders([(name, value_type(wire)) for name, wire, _ in logical])
        logical_names = " ".join(name for name, _, _ in logical)
        lines = ["/-- Parameter and witness values, keyed by the actual typed selectors. -/",
                 f"def assignments {logical_binders}:\n    LogicalAssignments (assignment F G) owner rootInvocation where"]
        for role_kind, field_name in (("parameter", "parameters"), ("witness", "witnesses")):
            chosen = [(name, wire) for name, wire, kind_ in logical if kind_ == role_kind]
            if not chosen:
                lines.append(f"  {field_name} _ _ := none")
                continue
            lines.append(f"  {field_name} type selector := match type with")
            by_head = {}
            for name, wire in chosen:
                by_head.setdefault(wire[0], []).append(name)
            for head, group in by_head.items():
                pattern = {"group": ".group _", "field": ".field _", "vector": ".vector _", "index": ".index",
                           "bool": ".boolean"}[head]
                chain = "".join(f"if selector.erase = {name}Selector.erase then some {name} else "
                                for name in group)
                lines.append(f"    | {pattern} => {chain}none")
            lines.append("    | _ => none")
        out.append("\n".join(lines) + "\n")
        reply_binders = self.binders(info["replies"])
        reply_names = " ".join(name for name, _ in info["replies"])
        held_binders = info["binders"]
        held_arguments = info["arguments"]
        observed = f"observedBoundary {held_arguments} {reply_names}"
        out.append(f"/-- Only the {verifier}'s own inputs and its actual returned tuple are projected. -/")
        out.append(f"def observedBoundary {held_binders}{reply_binders}: ContractBoundaryValues owner F G :=\n"
                   f"  BoundaryValuation.ofOutcome {decision_role} ({info['inputs']} {held_arguments})\n"
                   f"    (({verifier}Replies {reply_names}).run\n"
                   f"      ({program}.participant F G {decision_role} ({info['inputs']} {held_arguments}))).outcome\n")
        linear = linear_actions(info["node"])
        _, last = linear
        returned = re.fullmatch(r"\.cons some \((.*)\) \.nil|\.cons \(some \((.*)\)\) \.nil", last.expr)
        if returned is None:
            raise GeneratorError(f"the deciding role must return one present Boolean, not {last.expr}")
        accepted_bool = returned.group(1) or returned.group(2)
        accepted_prop = bool_to_prop(accepted_bool)
        out.append(f"/-- The selected decision is the {verifier}'s actual returned value. -/")
        out.append(f"theorem observed_accepts_iff {held_binders}{reply_binders}:\n"
                   f"    decisionSelector.read {{}} ({observed}) = some true ↔\n      {accepted_prop} := by\n"
                   f"  change (some {paren(accepted_bool)} = some true) ↔ _\n  simp\n")
        out.append(f"theorem observed_read {merge_binders(held_binders, logical_binders, reply_binders)}:\n"
                   f"    application.read {{}} ({observed}) ({'assignments ' + logical_names}) =\n"
                   f"      some (arguments {argument_names}) := by\n  rfl\n")
        out.append(f"theorem observed_target_iff {merge_binders(held_binders, logical_binders, reply_binders)}:\n"
                   f"    (target (F := F) (G := G)).Holds {{}} ({observed}) ({'assignments ' + logical_names}) ↔\n"
                   f"      Relation {argument_names} := by\n"
                   f"  change (∃ args, application.read {{}} _ _ = some args ∧\n"
                   f"    formulaBinding.invokeRelation args = .done (.cons true .nil)) ↔ _\n"
                   f"  constructor\n"
                   f"  · rintro ⟨args, read, truth⟩\n    rw [observed_read] at read\n"
                   f"    cases Option.some.inj read\n    exact truth\n"
                   f"  · intro truth\n    exact ⟨_, observed_read .., truth⟩\n")
        self.parts.append("\n".join(part for part in out if part))

    # -- a typed body shared by several units ------------------------------
    def unit_terms(self):
        """Lean terms of the admitted unit a whole-body entry is stated over (the request's `[unit]`)."""
        table = self.request.get("unit")
        if table is None:
            raise GeneratorError("a body with protocol applications or an invocation theorem needs a "
                                 "[unit] table naming the admitted unit and its views")
        name = table.get("name", "unit")
        return {"name": name, "views": table["views"], "helpers": table["helpers"],
                "program": table.get("program", "program"),
                "meaning": (f"participantMeaningWith (.silent _) (participantActions F G) ({table['helpers']}) "
                            f"self ({name}.plainProtocolTable F G) ctx")}

    def signature_term(self, function):
        names = self.signatures()
        if function.name not in names:
            raise GeneratorError(f"no signature declaration names {function.name}; list its body module in "
                                 f"helper_modules or name it in the request's signatures table")
        return names[function.name]

    def omit_line(self):
        if self.carrier == "Field":
            return "omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in"
        return "omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in"

    def view(self, out, name, function, declaration, body, raw=None):
        """The invocation of one retained protocol in the unit's plain table: its checked body
        at the given context, between its input and output masks."""
        terms = self.unit_terms()
        views = terms["views"]
        raw = raw or f"{views}.{declaration}_raw"
        scopes_in = scope_literal(function.input_scopes)
        scopes_out = scope_literal(function.output_scopes)
        typed = f"Values (Component (assignment F G)) {ty_list(function.inputs, True)}"
        out.append(f"/-- The checked body of `{declaration}` at any context, between its input and output\n"
                   f"masks, with this unit's plain tables. -/")
        out.append(f"theorem {name}_view (ctx : ProtocolContext) (self : Nat) (args masked : {typed})\n"
                   f"    (mask : maskValues self (ctx.mapScopes {scopes_in}) args = masked) :\n"
                   f"    invokeProtocol ({terms['name']}.plainProtocolTable F G) {self.signature_term(function)} "
                   f"ctx self args =\n"
                   f"      ({paren(body)}.denote\n        ({terms['meaning']}) masked.get).bind\n"
                   f"        (fun out => .done (maskValues self (ctx.mapScopes {scopes_out}) out)) := by\n"
                   f"  rw [← mask]\n"
                   f"  exact protocol_invoke_body_view (.silent _) (participantActions F G) ({terms['helpers']})\n"
                   f"    {terms['name']}.protocols {terms['name']}.protocolsLinked {views}.{declaration}Definition\n"
                   f"    {views}.{declaration}_member ({body}) {raw} ctx self args\n")

    def masked_outputs(self, out, theorem, function, context, role, other, scope_role=None):
        """The output masks of a returned tuple at caller role `role`, which is the callee's
        `scope_role`: in-scope components are kept, the others are masked away."""
        binder = "values"
        scope_role = role if scope_role is None else scope_role
        kept = values_literal([f"{binder}.get {variable(position)}" if scope_role in scope else "none"
                               for position, scope in enumerate(function.output_scopes)])
        cases = "".join(f"{'  ' * position}cases {binder} with | cons value{position} {binder} =>\n  "
                        for position in range(len(function.outputs)))
        cases += "  " * len(function.outputs) + f"cases {binder}\n"
        pad = "  " * len(function.outputs)
        out.append("set_option linter.unusedSimpArgs false in")
        out.append(self.omit_line())
        out.append(f"/-- The returned components kept at role {role}; the others are masked away. -/")
        hides = any(scope_role not in scope for scope in function.output_scopes)
        separate = f" (separate : ctx.roles {other} ≠ ctx.roles {role})" if hides else ""
        out.append(f"theorem {theorem} (ctx : ProtocolContext){separate}\n"
                   f"    ({binder} : Values (Component (assignment F G)) {ty_list(function.outputs, True)}) :\n"
                   f"    maskValues (ctx.roles {role}) ({context}.mapScopes {scope_literal(function.output_scopes)}) "
                   f"{binder} =\n      {kept} := by\n"
                   f"  {cases}"
                   f"  {pad}simp [maskValues, ProtocolContext.mapScopes, ProtocolContext.enter, roleSubstitution,\n"
                   f"  {pad}  Participant.restrict{', separate, Ne.symm separate' if hides else ''}, Values.get]\n")
        return kept, hides

    def callee(self, entry, function):
        """The generated normal forms of an application's callee, by callee role index."""
        path = ROOT / entry["callee"]
        key = (str(path.resolve()), entry["function"])
        if key not in CALLEES:
            request = tomllib.loads(path.read_text(encoding="utf-8"))
            module = Module(request, path.resolve())
            build(module, request)
            CALLEES[key] = module
        module = CALLEES[key]
        parent = self.request["namespace"].rsplit(".", 1)[0] + "."
        namespace = module.request["namespace"]
        prefix = namespace.removeprefix(parent) if namespace.startswith(parent) else namespace
        by_index, values = {}, {}
        for role_name, supplied in entry.get("roles", {}).items():
            info = module.role_infos.get((entry["function"], role_name))
            if info is None:
                raise GeneratorError(f"{entry['callee']} has no role {role_name!r} of {entry['function']}")
            if info["role"] in by_index:
                raise GeneratorError(f"two callee normal forms are named for callee role {info['role']}")
            if info["outputs"] != function.outputs or len(info["inputs"]) != len(function.inputs):
                raise GeneratorError(f"{entry['callee']}: {entry['function']} is not over the applied "
                                     f"protocol's signature")
            by_index[info["role"]] = dict(info, process=f"{prefix}.{info['process']}",
                                          theorem=f"{prefix}.{info['theorem']}", name=role_name)
            values[info["role"]] = dict(supplied)
        return by_index, values

    def applications(self, out, spec, protocol, block):
        """Child contexts, invocation views and output masks of the body's protocol applications."""
        found = [instruction for instruction in block[1] if instruction[0][0] == "protocol_apply"]
        entries = spec.get("applications", [])
        if not found:
            return {}
        if len(entries) != len(found):
            raise GeneratorError(f"the body has {len(found)} protocol applications; the request names "
                                 f"{len(entries)}")
        applications = {}
        out.append("/-! Protocol applications: the child context (application prefix and role mapping)\n"
                   "and the callee's invocation in this unit. -/")
        for instruction, entry in zip(found, entries):
            site = instruction[4]
            if entry.get("site", site) != site:
                raise GeneratorError(f"application {entry.get('site')!r} is not the body's next application "
                                     f"{site!r}")
            # Named from the callee's declaration, not from the (possibly positional) site.
            name = entry.get("name") or camel(entry["declaration"])
            callee = self.unit.function(instruction[0][1])
            roles = [protocol.roles.index(role) for role in instruction[0][2]]
            context = f"{name}Context"
            out.append(f"/-- The child context of the `{name}` application: its sites are qualified by the\n"
                       f"application site and its roles map to the caller's roles {roles}. -/")
            out.append(f"abbrev {context} (ctx : ProtocolContext) : ProtocolContext :=\n"
                       f"  ctx.enter {json.dumps(site)} {list_literal(roles)}\n")
            # The callee's static repeat maximum in this unit, read from the retained export, so
            # statements about this unit's application need not spell it.
            repeats = [row for row in callee.body[1] if row[0][0] == "protocol_repeat"]
            stem = camel(entry["declaration"])
            if stem not in self.applied:
                self.applied.add(stem)
                if len(repeats) == 1:
                    out.append(f"/-- The repeat maximum of the applied `{stem}` body in this unit. -/")
                    out.append(f"abbrev {stem}Maximum : Nat := {int(repeats[0][0][2])}\n")
                self.view(out, stem, callee, entry["declaration"], entry["body"], entry.get("raw"))
            callee_roles, values = self.callee(entry, callee)
            for role_spec in spec.get("roles", []):
                role = role_spec["role"]
                if role in roles:
                    other = [index for index in range(len(protocol.roles)) if index != role]
                    if len(other) != 1:
                        raise GeneratorError("protocol applications are supported in two-role bodies")
                    self.masked_outputs(out, f"{name}_{role_spec['name']}_outputs", callee,
                                        f"({context} ctx)", role, other[0], roles.index(role))
            views = self.unit_terms()["views"]
            declaration = entry["declaration"]
            applications[site] = Application(
                name, site, roles, self.signature_term(callee), context, self.unit_terms()["name"],
                f"{views}.{declaration}Definition", f"{views}.{declaration}_member",
                f"{views}.{declaration}_signature", entry["body"], entry.get("raw", f"{views}.{declaration}_raw"),
                dict(entry.get("arguments", {})), callee_roles, values, list(entry.get("results", [])),
                instruction[0][1])
        return applications

    def shared(self, spec):
        unit = self.unit
        protocol = unit.function(spec.get("protocol", unit.entry))
        if spec.get("repeat"):
            instruction = find_repeat(protocol.body, self.repeat_site(spec))
            inputs, outputs, block = instruction[3][0]
            state_scopes = [[protocol.roles.index(role) for role in scope] for scope in instruction[0][4]]
            state_count = instruction[0][1]
        else:
            inputs, outputs, block = protocol.inputs, protocol.outputs, protocol.body
            state_scopes, state_count = None, None
        sites = site_names(action_sites(block), self.request.get("sites", {}))
        fresh = {site: name for site, name in sites.items() if site not in self.emitted_sites}
        out = []
        if fresh:
            out.append("/-! Action sites of the body, qualified by the application prefix. -/")
            for site, name in fresh.items():
                out.append(f"abbrev {name} (ctx : ProtocolContext) : String :=\n"
                           f"  qualifyProtocolSite ctx.applicationPrefix {json.dumps(site)}")
                self.emitted_sites.add(site)
            out.append("")
        if not self.declared:
            out.append(self.variables())
            out.append("")
            out.append("private abbrev one {ty : Ty} (value : Option (assignment F G ty)) :\n"
                       "    Values (Component (assignment F G)) [ty] := .cons value .nil\n")
        if spec.get("applications") or spec.get("declaration") or "unit" in self.request:
            terms = self.unit_terms()
            spec = dict(spec)
            spec.setdefault("meaning", terms["meaning"])
            spec.setdefault("closed", f"({terms['helpers']}).closed")
            spec.setdefault("components", f"({terms['helpers']}).components")
            spec.setdefault("tables", terms["helpers"])
            spec.setdefault("protocols", f"{terms['name']}.plainProtocolTable F G")
        applications = self.applications(out, spec, protocol, block)
        function = spec["function"]
        parameters = spec.get("parameters", "")
        parameter_names = " ".join(re.findall(r"\((\w+)\s*:", parameters))
        meaning = spec["meaning"]
        out.append("/-- The typed body's process at one participant, with this unit's tables. -/")
        out.append(f"def {function} {parameters} (ctx : ProtocolContext) (self : Nat) :\n"
                   f"    RegionFunction (Component (assignment F G)) (participantInterface F G)\n"
                   f"      ({ty_list(inputs, True)}, {ty_list(outputs, True)}) :=\n"
                   f"  fun args => {paren(spec['body'])}.denote\n    ({meaning}) args.get\n")
        if spec.get("declaration"):
            self.view(out, spec["declaration"], protocol, spec["declaration"], spec["body"], spec.get("raw"))
        captures = inputs[1 + state_count:] if state_count is not None else []
        for role_spec in spec.get("roles", []):
            if state_scopes is None:
                self.shared_protocol_role(out, spec, role_spec, protocol, block, sites, function,
                                          parameter_names, applications)
            else:
                self.shared_role(out, spec, role_spec, protocol, inputs, outputs, block, state_scopes,
                                 captures, sites, function, parameter_names, applications)
        self.parts.append("\n".join(out))

    def shared_role(self, out, spec, role_spec, protocol, inputs, outputs, block, state_scopes, captures,
                    sites, function, parameter_names, applications=None):
        role = role_spec["role"]
        name = role_spec["name"]
        slots = role_spec["slots"]
        state = inputs[1:1 + len(state_scopes)]
        if state_scopes is None:
            raise GeneratorError("normal forms of a whole protocol body need a repeat site")
        owned = [index for index, scope in enumerate(state_scopes) if role in scope]
        if len(slots) != len(owned):
            raise GeneratorError(f"{name}: the role holds {len(owned)} carried slots; the request names "
                                 f"{len(slots)}")
        # Slots are named in the role's own order, so a layout change of the other role's
        # slots, or a reordering that keeps this role's order, needs no request change.
        slots = [dict(slot, slot=index) for slot, index in zip(slots, owned)]
        def slot_type(slot):
            base = value_type(state[slot["slot"]])
            return f"Option {paren(base)}" if slot.get("mode", "present") == "optional" else base
        embed = role_spec.get("state", f"{name}State")
        # Role-local embedding of the carried state.
        if not role_spec.get("reuse_state"):
            pairs = [(slot["name"], slot_type(slot)) for slot in slots]
            components = []
            for index in range(len(state)):
                slot = next((slot for slot in slots if slot["slot"] == index), None)
                if slot is None:
                    components.append("none")
                elif slot.get("mode", "present") == "optional":
                    components.append(slot["name"])
                else:
                    components.append(f"some {slot['name']}")
            out.append(f"/-- The {name}'s components of the carried state; the other slots are absent. -/")
            out.append(f"def {embed} {self.binders(pairs)}:\n    Values (Component (assignment F G)) "
                       f"{ty_list(state, True)} :=\n  {values_literal(components)}\n")
            scopes = "[" + ", ".join("[" + ", ".join(map(str, scope)) + "]" for scope in state_scopes) + "]"
            arguments = " ".join(slot["name"] for slot in slots)
            if role_spec.get("proof") == "normal-form":
                finish_name = f"{name}Finish"
                out.append(f"/-- The positions of the carried state the {name} presents. -/")
                out.append(f"def {finish_name} : Values (fun (_ : Ty) => NormalForm.Carried) {ty_list(state, True)} :=\n"
                           f"  {values_literal(self.finish_modes(slots, len(state)))}\n")
            out.append(f"omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in\n"
                       f"/-- Masking the carried state to its declared scopes keeps the {name}'s components. -/")
            if role_spec.get("proof") == "normal-form":
                masked_proof = (f"  subst self\n  exact NormalForm.maskValues_embed (Value := assignment F G) ctx {role} "
                                f"{finish_name} _ rfl\n    {paren(binders_literal([slot['name'] for slot in slots]))}\n")
            else:
                masked_proof = (f"  subst self\n  unfold {embed}\n  iterate {len(state) + 1} unfold maskValues\n"
                                f"  simp [ProtocolContext.mapScopes, Participant.restrict]\n")
            out.append(f"theorem {embed}_masked (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles {role})\n"
                       f"    {self.binders(pairs)}:\n"
                       f"    maskValues self (ctx.mapScopes {scopes}) ({f'{embed} (F := F) (G := G) {arguments}'.strip()}) =\n"
                       f"      {embed} {arguments} := by\n" + masked_proof)
            # Stable names for the role's carried slots: statements about the state use
            # these instead of positions, so a reordered layout changes only this module.
            out.append(f"/-! Positions of the {name}'s carried slots in the repeat state, named by the request. -/")
            for slot in slots:
                stem = slot["name"][0].upper() + slot["name"][1:]
                index = slot["slot"]
                out.append(f"abbrev {name}{stem}Position : Nat := {index}")
                out.append(f"abbrev {name}{stem}Slot : Var ({ty_list(state, True)} : List Ty) {lean_ty(state[index], True)} :=\n"
                           f"  {variable(index)}")
            out.append("")
        # Input values: the induction index, the state slots and the captures.
        values_by_slot = {}
        state_args = []
        for slot in slots:
            wire = state[slot["slot"]]
            if "value" in slot:
                values_by_slot[slot["slot"]] = present(wire, slot["value"])
                state_args.append(slot["value"])
            elif slot.get("mode", "present") == "optional":
                values_by_slot[slot["slot"]] = optional(wire, slot["name"])
                state_args.append(slot["name"])
            else:
                values_by_slot[slot["slot"]] = present(wire, slot["name"])
                state_args.append(slot["name"])
        env = [present(inputs[0], "index")]
        for index, wire in enumerate(state):
            env.append(values_by_slot.get(index, absent(wire)))
        capture_specs = role_spec.get("captures", [])
        capture_binders, capture_components = [], []
        for position, wire in enumerate(captures):
            capture = capture_specs[position] if position < len(capture_specs) else {"name": f"capture{position}"}
            mode = capture.get("mode", "optional")
            capture_binders.append((capture["name"], f"Option {paren(value_type(wire))}" if mode == "optional"
                                    else value_type(wire)))
            capture_components.append(capture["name"] if mode == "optional" else f"some {capture['name']}")
            env.append(optional(wire, capture["name"]) if mode == "optional" else present(wire, capture["name"]))
        frame = Frame(self.unit, protocol.roles, role, "shared", sites, self.helpers(),
                      load_laws(role_spec.get("laws")), dict(role_spec.get("guards", {})),
                      separate="separate", closed=spec["closed"], components=spec.get("components", ""),
                      opaque=tuple(role_spec.get("opaque", [])), role_name=name, outer_bind=True,
                      strict=tuple(role_spec.get("strict", [])), slot_names=self.slot_names(role),
                      applications=applications or {}, repeats=self.repeat_terms())
        free = [slot for slot in slots if "value" not in slot]
        result_names = [slot["name"] for slot in slots]
        names = Names(result_names + [capture["name"] for capture in capture_specs] + list(sites.values()))

        def finish(values, proof, pad):
            for index, value in enumerate(values):
                if index not in [slot["slot"] for slot in slots] and value.kind != "absent":
                    raise GeneratorError(f"{name}: slot {index} is present at this role but is not one of its slots")
            parts = []
            for slot in slots:
                value = values[slot["slot"]]
                if slot.get("mode", "present") == "optional":
                    parts.append(value.component())
                elif value.kind != "present":
                    raise GeneratorError(f"{name}: slot {slot['slot']} is not present at the end of the body")
                else:
                    parts.append(value.expr)
            if proof is not None and frame.mode == "shared":
                proof.append(f"{pad}rfl")
            # A role that carries no slot of this repeat returns the unit value.
            return Done(tuple_literal(parts) if parts else "()")

        proof = []
        node = Evaluator(frame, names, finish).run(block[1], block[2], env, proof, 2)
        process = role_spec.get("process", f"{name}Process")
        text = render_process(node, 2)
        free_pairs = [(slot["name"], slot_type(slot)) for slot in free]
        used_pairs = [(variable, kind) for variable, kind in
                      [("ctx", "ProtocolContext"), ("index", "Nat")] + capture_binders + free_pairs
                      if re.search(rf"(?<![\w.]){re.escape(variable)}(?![\w'])", text)]
        process_binders = self.binders(used_pairs)
        process_arguments = " ".join(variable for variable, _ in used_pairs)
        theorem_binders = self.binders(capture_binders + free_pairs)
        script = "\n".join(proof)
        uses_separate = re.search(r"(?<![\w.])separate(?![\w'])", script) is not None
        result_type = " × ".join(paren(slot_type(slot)) if " " in slot_type(slot) else slot_type(slot)
                                 for slot in slots) or "Unit"
        out.append(f"/-- The {name}'s normal form of one body run: its ordered actions, the values it\n"
                   f"computes, guards as conditionals and missing inputs as stops. -/")
        out.append(f"def {process} {process_binders}:\n"
                   f"    PIR.Process (participantInterface F G) ({result_type}) :=\n{text}\n")
        projections = self.projections(len(slots)) if slots else []
        embedded = f"{embed} {' '.join(projections)}".strip()
        ends = f"(fun {'result' if slots else '_'} => .done ({embedded}))"
        others = [other for other in range(len(protocol.roles)) if other != role]
        if len(others) != 1:
            raise GeneratorError("shared normal forms support two-role protocols")
        theorem = role_spec.get("theorem", f"{name}_process")
        premises = role_spec.get("premises", "")
        binders = role_spec.get("binders", "")
        if role_spec.get("proof") == "normal-form":
            application = f"{process} {process_arguments}".strip()
            self.shared_form(out, spec, role_spec, protocol, inputs, outputs, state, slots, captures,
                             capture_specs, frame, process, role, uses_separate, others[0], theorem, function,
                             parameter_names, embed, state_args, capture_components, theorem_binders, premises,
                             binders, application, result_type, projections)
            if role_spec.get("fold"):
                self.fold(out, spec, role_spec, role, others[0], name, embed, process, theorem, function,
                          parameter_names, state, slots, capture_binders, capture_components, used_pairs,
                          uses_separate, result_type)
            return
        out.append("set_option linter.unusedSimpArgs false in")
        out.append(f"/-- The process equation of `{process}` over the typed body. -/")
        separate_binder = f"\n    (separate : ctx.roles {others[0]} ≠ self)" if uses_separate else ""
        application = f"{process} {process_arguments}".strip()
        unfolds = " ".join([function, *spec.get("unfold", [spec["body"]])])
        out.append(f"theorem {theorem} {spec.get('parameters', '')} {binders}\n"
                   f"    (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles {role}){separate_binder}\n"
                   f"    (index : Nat) {theorem_binders}{premises}{' ' if premises else ''}:\n"
                   f"    {function} (F := F) (G := G) {parameter_names} ctx self (.cons (some index)\n"
                   f"      (({f'{embed} ' + ' '.join(state_args) if state_args else embed}).append {paren(values_literal(capture_components))})) =\n"
                   f"      ({application}).bind {ends} := by\n"
                   f"  subst self\n"
                   f"  let m := {spec['meaning'].replace(' self ', ' (ctx.roles ' + str(role) + ') ')}\n"
                   f"  unfold {unfolds}\n"
                   f"  simp only [{process}, PIR.Process.bind{associate(node)}]\n"
                   + script + "\n")
        if role_spec.get("fold"):
            self.fold(out, spec, role_spec, role, others[0], name, embed, process, theorem, function,
                      parameter_names, state, slots, capture_binders, capture_components, used_pairs,
                      uses_separate, result_type)

    @staticmethod
    def finish_modes(slots, count):
        modes = []
        for index in range(count):
            slot = next((slot for slot in slots if slot["slot"] == index), None)
            if slot is None:
                modes.append(".absent")
            elif slot.get("mode", "present") == "optional":
                modes.append(".optional")
            else:
                modes.append(".present")
        return modes

    def law_table(self, role_spec, frame, inputs, fixed_inputs):
        """The role's laws as the normalizer reads them: retained helper, shape and pins.
        A pin ties an argument to a present or fixed input; it holds at every use of the law."""
        names = {term.split(".")[-1]: raw for raw, term in self.helpers().items()}
        laws = []
        for key, law in load_laws(role_spec.get("laws")).items():
            raw = names.get(key, key)
            helper = self.unit.function(raw)
            uses = [args for used, args in frame.law_uses if used == raw]
            pins = None
            for args in uses:
                current = [law_pin(arg, fixed_inputs) for arg in args]
                pins = current if pins is None else [a if a == b else None for a, b in zip(pins, current)]
            shape_json, shape_lean = law_shape(law)
            if shape_json != "returns" and shape_json[0] == "passes":
                pins = []
            laws.append({"key": key, "raw": raw, "law": law, "helper": helper, "pins": pins or [],
                         "term": self.helper_term_of(raw), "shape_json": shape_json, "shape_lean": shape_lean})
        return laws

    def kept_helpers(self, role_spec):
        """The retained names and Lean terms of the helpers whose owned calls stay owned."""
        names = {term.split(".")[-1]: raw for raw, term in self.helpers().items()}
        raws = [names.get(key, key) for key in role_spec.get("opaque", [])]
        return raws, [self.helper_term_of(raw) for raw in raws]

    def signature_literal(self, laws, names, kept_terms, strict=False, callees=()):
        keys = ", ".join(f"⟨{law['term']}, {law['shape_lean']}, {list_literal([pin_lean(pin) for pin in law['pins']])}⟩"
                         for law in laws)
        callee_keys = ", ".join(f"⟨{callee['signature']}, {callee['index']}, {callee['pattern_lean']}, "
                                f"{list_literal(['none' if pin is None else f'some {pin}' for pin in callee['pins']])}⟩"
                                for callee in callees)
        return (f"⟨[{keys}], {'true' if strict else 'false'}, {'true' if names else 'false'}, "
                f"{list_literal(kept_terms)}, [{callee_keys}]⟩")

    def law_request(self, laws):
        return [[law["raw"], law["shape_json"], [pin_json(pin) for pin in law["pins"]]] for law in laws]

    def results_body(self, laws, signature):
        """The law results function: the request's templates for laws whose results it gives,
        any value of the output sort for the others."""
        defaults = {"field": "0", "index": "0", "bool": "false", "vector": "[]", "group": "0", "service": "0"}
        cases = []
        for entry, law in enumerate(laws):
            helper = law["helper"]
            arguments = [f"(args.get {variable(index)})" for index in range(len(helper.inputs))]
            if law["shape_json"] == "returns" or law["shape_json"][0] == "returns":
                values = [paren(template.format(*arguments)) for template in law["law"].results]
            else:
                values = [defaults[wire[0]] for wire in helper.outputs]
            cases.append(f"    | ⟨{entry}, _⟩ => fun (args : Values (assignment F G) {ty_list(helper.inputs, True)}) =>\n"
                         f"      ({values_literal(values)} : Values (assignment F G) {ty_list(helper.outputs, True)})")
        if laws:
            cases.append(f"    | ⟨_ + {len(laws)}, outside⟩ => absurd outside (by simp [{signature}])")
            return "⟨fun entry => match entry with\n" + "\n".join(cases) + "⟩"
        return "⟨fun entry => entry.elim0⟩"

    def shared_form(self, out, spec, role_spec, protocol, inputs, outputs, state, slots, captures, capture_specs,
                    frame, process, role, uses_separate, other, theorem, function, parameter_names, embed,
                    state_args, capture_components, theorem_binders, premises, binders, application, result_type,
                    projections):
        """A callback role's equation as an instance of the normalizer's soundness theorem."""
        name = role_spec["name"]
        # The callback's inputs: the index, the carried state and the captures.
        pattern, scope_names, fixed_inputs = ["present"], ["index"], {}
        for index, wire in enumerate(state):
            slot = next((slot for slot in slots if slot["slot"] == index), None)
            position = 1 + index
            if slot is None:
                pattern.append("absent")
            elif "value" in slot:
                kind = wire[0]
                if kind not in ("index", "field", "bool"):
                    raise GeneratorError(f"{name}: fixed slots of sort {kind} are not supported")
                pattern.append([kind, slot["value"]])
                fixed_inputs[slot["value"]] = position
            elif slot.get("mode", "present") == "optional":
                pattern.append("optional")
                scope_names.append(slot["name"])
            else:
                pattern.append("present")
                scope_names.append(slot["name"])
                fixed_inputs[slot["name"]] = position
        for index, wire in enumerate(captures):
            capture = capture_specs[index] if index < len(capture_specs) else {"name": f"capture{index}"}
            position = 1 + len(state) + index
            if capture.get("mode", "optional") == "optional":
                pattern.append("optional")
            else:
                pattern.append("present")
                fixed_inputs[capture["name"]] = position
            scope_names.append(capture["name"])
        laws = self.law_table(role_spec, frame, inputs, fixed_inputs)
        kept_raws, kept_terms = self.kept_helpers(role_spec)
        strict = bool(role_spec.get("strict"))
        roster = len(protocol.roles) if uses_separate else 1
        if not uses_separate and role != 0:
            raise GeneratorError(f"{name}: a role other than the first needs the separate roster premise")
        callees = self.callee_keys(out, frame, role, role_spec, fixed_inputs)
        request = [protocol.name, self.repeat_site(spec), str(role), str(roster), pattern,
                   self.law_request(laws), strict, kept_raws,
                   [[callee["raw"], str(callee["index"]), callee["pattern_json"],
                     [None if pin is None else str(pin) for pin in callee["pins"]]] for callee in callees]]
        result = run_normalizer(self.request["fixture"], request, name)
        types = ty_list(inputs, True)
        signature, pattern_name, finish_name = f"{name}Signature", f"{name}Pattern", f"{name}Finish"
        results_name, form_name = f"{name}Results", f"{name}Form"
        if role_spec.get("reuse_state"):
            finish_name = f"{role_spec.get('finish', name + 'Finish')}"
            out.append(f"/-- The positions of the carried state the {name} presents. -/")
            out.append(f"def {finish_name} : Values (fun (_ : Ty) => NormalForm.Carried) {ty_list(state, True)} :=\n"
                       f"  {values_literal(self.finish_modes(slots, len(state)))}\n")
        out.append(f"/-- The {name}'s laws as the normalizer reads them, keyed by helper. -/")
        out.append(f"def {signature} : NormalForm.Signature :=\n"
                   f"  {self.signature_literal(laws, result.get('names'), kept_terms, strict, callees)}\n")
        result_body = self.results_body(laws, signature)
        out.append(f"/-- The results the {name}'s laws present, from the request's templates. -/")
        out.append(f"def {results_name} : NormalForm.LawResults (ringModel F G) {signature}.laws :=\n  {result_body}\n")
        processes, _ = self.callee_processes(out, name, signature, callees, spec)
        out.append(f"/-- The {name}'s inputs as the normalizer reads them. -/")
        pattern_literal = values_literal([self.pattern_entry(item) for item in pattern])
        out.append(f"def {pattern_name} : NormalForm.InputPattern {types} :=\n  {pattern_literal}\n")
        out.append(f"/-- The {name}'s form, printed from the compiled normalizer; the kernel checks it. -/")
        out.append(f"noncomputable def {form_name} : NormalForm.Form {signature}.laws {signature}.callees {pattern_name}.scope {ty_list(outputs, True)} :=\n"
                   + lean_form(result["form"], 2, self.helper_term_of, self.repeat_regions(spec),
                               [(callee["signature"], [(present, wire) for _, _, present, wire in callee["scope"]])
                                for callee in callees]) + "\n")
        out.append(f"theorem {name}_normalized :\n    NormalForm.normalize {signature} {spec['body']} {role} {roster} "
                   f"{pattern_name} = .ok {form_name} := by\n  kernel_rfl\n")
        out.append(f"theorem {name}_lawsMatch : {form_name}.CallsMatch := by\n  kernel_rfl\n")
        out.append(f"theorem {name}_finishes : {form_name}.finishes {finish_name} = true := by\n  kernel_rfl\n")
        binders_value = binders_literal(scope_names)
        scope_binders = self.scope_binders(scope_names, state, slots, captures, capture_specs)
        environment = (f".cons (some index)\n      (({f'{embed} ' + ' '.join(state_args) if state_args else embed}).append "
                       f"{paren(values_literal(capture_components))})")
        out.append(f"theorem {name}_environment {scope_binders}:\n"
                   f"    {pattern_name}.environment (ringModel F G) ({binders_value}) =\n"
                   f"      ({environment} : Values (Component (assignment F G)) {types}) := by\n  kernel_rfl\n")
        out.append("/-- The form's presented process is the readable process. -/")
        tables, protocols = spec["tables"], spec["protocols"]
        out.append(f"theorem {name}_presentation {spec.get('parameters', '')} (ctx : ProtocolContext)\n"
                   f"    {scope_binders}:\n"
                   f"    {form_name}.denoteWith (ringModel F G) ({tables}).toOn {results_name} ctx\n"
                   f"        (NormalForm.Runs.uniform ({tables}) ({protocols}) ctx (ctx.roles {role}))\n"
                   f"        {processes}\n"
                   f"        (NormalForm.finishLeaf (ringModel F G) {results_name} {finish_name}) ({binders_value}) =\n"
                   f"      {application} := by\n  kernel_rfl\n")
        tuple_type = paren(result_type) if " " in result_type else result_type
        embedded = f"{embed} {' '.join(projections)}".strip()
        out.append(f"theorem {name}_embedding (result : {tuple_type}) :\n"
                   f"    NormalForm.embed (assignment F G) {finish_name} (NormalForm.Tuple.toValues result) =\n"
                   f"      {embedded} := by\n  kernel_rfl\n")
        laws_binders = f"{spec.get('parameters', '')} {binders} (index : Nat) {theorem_binders}{premises}"
        laws_arguments = " ".join(binder_names(laws_binders))
        self.law_proofs(out, name, laws, results_name, spec, laws_binders, environment, types, fixed_inputs)
        callees_call = self.callee_proofs(out, name, signature, callees, processes, spec, role_spec,
                                          scope_binders, environment, types, [other])
        separate_binder = f"\n    (separate : ctx.roles {other} ≠ self)" if uses_separate else ""
        distinct = "(.ofSeparate separate (by decide))" if uses_separate else "(NormalForm.RosterDistinct.only ctx)"
        names_in_order = " ".join(scope_names)
        laws_call = f"{name}_laws {laws_arguments}"
        out.append(f"/-- The process equation of `{process}`, an instance of the normalizer's soundness. -/")
        out.append(f"theorem {theorem} {spec.get('parameters', '')} {binders}\n"
                   f"    (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles {role}){separate_binder}\n"
                   f"    (index : Nat) {theorem_binders}{premises}{' ' if premises else ''}:\n"
                   f"    {function} (F := F) (G := G) {parameter_names} ctx self (.cons (some index)\n"
                   f"      (({f'{embed} ' + ' '.join(state_args) if state_args else embed}).append {paren(values_literal(capture_components))})) =\n"
                   f"      ({application}).bind (fun {'result' if slots else '_'} => .done ({embedded})) := by\n"
                   f"  subst self\n"
                   f"  exact (NormalForm.callback_sound_uniform {signature} {spec['body']} {role} {roster} {pattern_name}\n"
                   f"    {finish_name} {form_name} {name}_normalized {name}_lawsMatch {name}_finishes ctx {distinct}\n"
                   f"    ({spec['tables']}) ({spec['protocols']}) {results_name} {processes} ({binders_value}) _\n"
                   f"    ({name}_environment {names_in_order}) ({laws_call}) {callees_call}).trans\n"
                   f"    (congrArg₂ PIR.Process.bind ({name}_presentation {parameter_names} ctx {names_in_order})\n"
                   f"      (funext fun result => congrArg PIR.Process.done ({name}_embedding result)))\n")

    @staticmethod
    def pattern_entry(item):
        if isinstance(item, str):
            return f".{item}"
        kind, value = item
        if kind == "bool":
            return f"(.bool {value})"
        if kind == "field":
            return f"(.field _ {value})"
        return f"(.index {value})"

    def scope_binders(self, scope_names, state, slots, captures, capture_specs):
        kinds = {"index": "Nat"}
        for slot in slots:
            base = value_type(state[slot["slot"]])
            kinds[slot["name"]] = f"Option {paren(base)}" if slot.get("mode", "present") == "optional" else base
        for index, wire in enumerate(captures):
            capture = capture_specs[index] if index < len(capture_specs) else {"name": f"capture{index}"}
            base = value_type(wire)
            kinds[capture["name"]] = f"Option {paren(base)}" if capture.get("mode", "optional") == "optional" else base
        return self.binders([(name, kinds[name]) for name in scope_names])

    def law_proofs(self, out, name, laws, results_name, spec, laws_binders, environment, types, fixed_inputs):
        """One premise per law, each discharged by the admitted helper's own law from the request."""
        position_names = {position: input_name for input_name, position in fixed_inputs.items()}
        cases = []
        for entry, law in enumerate(laws):
            helper = law["helper"]
            args = [f"a{index}" for index in range(len(helper.inputs))]
            typed_outputs = f"Values (Component (assignment F G)) {ty_list(helper.outputs, True)}"
            if law["shape_json"] != "returns" and law["shape_json"][0] == "passes":
                arguments_pattern = values_literal(args) if args else ".nil"
                passed = [template.format(*args) for template in law["law"].results]
                cases.append(f"  | ⟨{entry}, _⟩ => fun args => match args with\n"
                             f"    | {arguments_pattern} => fun values found => by\n"
                             f"      obtain rfl : values = ({values_literal(passed)} : {typed_outputs}) :=\n"
                             f"        Option.some.inj (found.symm.trans (by kernel_rfl))\n"
                             f"      exact {law['law'].term.format(*args)}")
                continue
            pins = law["pins"] + [None] * (len(helper.inputs) - len(law["pins"]))
            pinned = [f"p{index}" if pin is not None else "_" for index, pin in enumerate(law["pins"])]
            def pinned_term(pin, index):
                if pin is None:
                    return args[index]
                return position_names[pin[1]] if pin[0] == "input" else pin[2]
            filled = [pinned_term(pin, index) for index, pin in enumerate(pins)]
            term = law["law"].term.format(*filled)
            rewrites = []
            for index, pin in enumerate(pins):
                if pin is None:
                    continue
                if pin[0] == "input":
                    rewrites.append(f"← (Option.some.inj p{index} : {position_names[pin[1]]} = a{index})")
                else:
                    rewrites.append(f"← (Option.some.inj (p{index} : some {paren(pin[2])} = some a{index}) : "
                                    f"{pin[2]} = a{index})")
            substitutions = f"      rw [{', '.join(rewrites)}]\n" if rewrites else ""
            arguments_pattern = values_literal(args) if args else ".nil"
            pinned_pattern = "⟨" + ", ".join(pinned + ["_"]) + "⟩" if law["pins"] else "_"
            if law["shape_json"] == "returns" or law["shape_json"][0] == "returns":
                shown = [template.format(*args) for template in law["law"].results]
                cases.append(f"  | ⟨{entry}, _⟩ => fun args pinned => match args, pinned with\n"
                             f"    | {arguments_pattern}, {pinned_pattern} => fun values found => by\n"
                             f"      obtain rfl : values = ({values_literal(shown)} : "
                             f"Values (assignment F G) {ty_list(helper.outputs, True)}) :=\n"
                             f"        Option.some.inj (found.symm.trans (by kernel_rfl))\n{substitutions}"
                             f"      show invoke ({spec['tables']}).closed {law['term']} _ = .done "
                             f"({values_literal([template.format(*filled) for template in law['law'].results])} : "
                             f"Values (assignment F G) {ty_list(helper.outputs, True)})\n"
                             f"      exact {term}")
                continue
            cases.append(f"  | ⟨{entry}, _⟩ => fun args pinned => match args, pinned with\n"
                         f"    | {arguments_pattern}, {pinned_pattern} => by\n{substitutions}"
                         f"      exact {term}")
        if laws:
            cases.append(f"  | ⟨_ + {len(laws)}, outside⟩ => absurd outside (by simp [{name}Signature])")
            body = "fun entry => match entry with\n" + "\n".join(cases)
        else:
            body = "fun entry => entry.elim0"
        tables = spec["tables"]
        out.append(f"/-- The {name}'s laws hold at its inputs, by the admitted helpers' laws. -/")
        out.append(f"theorem {name}_laws {laws_binders}:\n"
                   f"    NormalForm.LawsHold ({tables}).toOn {results_name}\n"
                   f"      ({environment} : Values (Component (assignment F G)) {types}) :=\n  {body}\n")

    def fold(self, out, spec, role_spec, role, other, name, embed, process, theorem, function,
             parameter_names, state, slots, capture_binders, capture_components, used_pairs, uses_separate,
             result_type):
        """The repeat of a callback at one role of its roster, on an admitted count: the fold
        of the role's normal form over the iteration indices, by the generic embedding law."""
        site = self.repeat_site(spec)
        repeat = self.repeat_terms().get(site, (spec.get("repeat_spec"), None))[0]
        if not repeat:
            raise GeneratorError(f"{name}: a fold needs the repeat's spec; name the callback in [bodies] "
                                 f"callbacks or give the entry a repeat_spec")
        if role_spec.get("premises") or role_spec.get("binders") or spec.get("parameters"):
            raise GeneratorError(f"{name}: folds are stated for callbacks without parameters, binders or premises")
        if any("value" in slot for slot in slots):
            raise GeneratorError(f"{name}: folds are stated for callbacks whose slots are all free")
        projections = self.projections(len(slots)) if slots else []
        initial = [projection.replace("result", "initial", 1) for projection in projections]
        embedded = f"{embed} {' '.join(projections)}".strip()
        names = {slot["name"]: projection for slot, projection in zip(slots, projections)}
        arguments = " ".join(names.get(variable, variable) for variable, _ in used_pairs)
        me = f"(ctx.roles {role})"
        typed_state = f"Values (Component (assignment F G)) {ty_list(state, True)}"
        named = [f"({variable} := {variable})" for variable, _ in capture_binders]
        named += [f"({slot['name']} := {projection})" for slot, projection in zip(slots, projections)]
        separate_binder = f" (separate : ctx.roles {other} ≠ ctx.roles {role})" if uses_separate else ""
        separate_argument = " (separate := separate)" if uses_separate else ""
        callback = f"{function} {parameter_names} ctx {me}".replace("  ", " ")
        index = "index" if any(variable == "index" for variable, _ in used_pairs) else "_"
        value = "result" if slots else "_"
        out.append(f"/-- The repeat of `{function}` at the {name} on an admitted count: the fold of its normal\n"
                   f"form over the iteration indices, from any state whose masked slots are `initial`. -/")
        out.append(f"theorem {name}_fold (ctx : ProtocolContext){separate_binder}\n"
                   f"    {self.binders(capture_binders)}(count : Nat) (bounded : count ≤ {paren(repeat)}.maximum)\n"
                   f"    (state : {typed_state}) (initial : {result_type})\n"
                   f"    (start : maskValues {me} (ctx.mapScopes {paren(repeat)}.stateScopes) state =\n"
                   f"      {f'{embed} ' + ' '.join(initial) if initial else embed}) :\n"
                   + f"    denoteRepeat {paren(repeat)} ctx {me} (some count) state\n"
                   f"      {paren(values_literal(capture_components))} ({callback}) =\n"
                   f"      (Finite.fold (fun {value} {index} => {process} {arguments}) "
                   f"(List.range' 0 count) initial).bind\n"
                   f"        (fun {'result' if slots else '_'} => .done ({embedded})) :=\n"
                   f"  NormalFormSteps.repeat_embed {paren(repeat)} ctx {me} (by simp) _ _\n"
                   f"    (fun {'result' if slots else '_'} => {embedded})\n"
                   f"    (fun {value} => {f'{embed}_masked ctx _ rfl ' + ' '.join(projections) if projections else f'{embed}_masked ctx _ rfl'})\n"
                   f"    _ (fun {'result' if slots else '_'} index => {theorem} (ctx := ctx) (self := {me}) (role := rfl)"
                   f"{separate_argument}\n"
                   f"      (index := index) {' '.join(named)})\n"
                   f"    count bounded state initial start\n")

    def shared_protocol_role(self, out, spec, role_spec, protocol, block, sites, function, parameter_names,
                             applications=None):
        """A whole protocol body at one role: input presence as declared, outputs as components."""
        role = role_spec["role"]
        name = role_spec["name"]
        specs = role_spec["inputs"]
        if len(specs) != len(protocol.inputs):
            raise GeneratorError(f"{name}: the protocol has {len(protocol.inputs)} inputs; "
                                 f"the request lists {len(specs)}")
        env, components, binders = [], [], []
        for wire, item in zip(protocol.inputs, specs):
            mode = item.get("mode", "present")
            if mode == "absent":
                env.append(absent(wire))
                components.append("none")
            elif "value" in item:
                env.append(present(wire, item["value"]))
                components.append(f"some {paren(item['value'])}")
            elif mode == "optional":
                env.append(optional(wire, item["name"]))
                components.append(item["name"])
                binders.append((item["name"], f"Option {paren(value_type(wire))}"))
            else:
                env.append(present(wire, item["name"]))
                components.append(f"some {item['name']}")
                binders.append((item["name"], value_type(wire)))
        frame = Frame(self.unit, protocol.roles, role, "shared", sites, self.helpers(),
                      load_laws(role_spec.get("laws")), dict(role_spec.get("guards", {})),
                      separate="separate", closed=spec["closed"], components=spec.get("components", ""),
                      rewrites=list(role_spec.get("rewrites", [])), callback=spec.get("callback", ""),
                      repeat_spec=spec.get("repeat_spec", ""), applications=applications or {},
                      opaque=tuple(role_spec.get("opaque", [])), role_name=name, repeats=self.repeat_terms(),
                      strict=tuple(role_spec.get("strict", [])), slot_names=self.slot_names(role))
        names = Names([binder for binder, _ in binders] + list(sites.values())
                      + binder_names(role_spec.get("binders", "")) + binder_names(role_spec.get("premises", "")))

        def finish(values, proof, pad):
            if proof is not None:
                proof.append(f"{pad}rfl")
            return Done(f"({values_literal([value.component() for value in values])} : "
                        f"Values (Component (assignment F G)) {ty_list(protocol.outputs, True)})")

        proof = []
        node = Evaluator(frame, names, finish).run(block[1], block[2], env, proof, 2)
        process = role_spec.get("process", f"{name}Process")
        text = render_process(node, 2)
        parameters = [(variable, kind) for variable, kind in
                      re.findall(r"\((\w+)\s*:\s*([^()]*(?:\([^()]*\))?[^()]*)\)", spec.get("parameters", ""))]
        used = [(variable, kind) for variable, kind in parameters + [("ctx", "ProtocolContext")] + binders
                if re.search(rf"(?<![\w.]){re.escape(variable)}(?![\w'])", text)]
        process_binders = self.binders(used)
        process_arguments = " ".join(variable for variable, _ in used)
        script = "\n".join(proof)
        uses_separate = re.search(r"(?<![\w.])separate(?![\w'])", script) is not None
        others = [other for other in range(len(protocol.roles)) if other != role]
        separate_binder = f"\n    (separate : ctx.roles {others[0]} ≠ self)" if uses_separate else ""
        out.append(f"/-- The {name}'s normal form of the whole body. -/")
        out.append(f"def {process} {process_binders}:\n    PIR.Process (participantInterface F G)\n"
                   f"      (Values (Component (assignment F G)) {ty_list(protocol.outputs, True)}) :=\n{text}\n")
        theorem = role_spec.get("theorem", f"{name}_process")
        if role_spec.get("proof") == "normal-form":
            self.protocol_form(out, spec, role_spec, protocol, frame, specs, binders, components, process,
                               process_arguments, theorem, function, parameter_names, uses_separate,
                               separate_binder)
            self.role_infos[(function, name)] = {
                "role": role, "process": process, "process_binders": [variable for variable, _ in used],
                "theorem": theorem, "parameters": binder_names(spec.get("parameters", "")),
                "binders": binder_names(role_spec.get("binders", "")),
                "premises": binder_names(role_spec.get("premises", "")), "uses_separate": uses_separate,
                "inputs": specs, "outputs": protocol.outputs}
            if spec.get("declaration"):
                self.invocation(out, spec, role_spec, protocol, process, used, theorem, binders, components,
                                uses_separate)
            return
        default_unfold = [spec["body"]] if re.fullmatch(r"[\w.']+", spec["body"]) else []
        unfolds = " ".join([function, *spec.get("unfold", default_unfold)])
        out.append("set_option linter.unusedSimpArgs false in")
        out.append(f"/-- The process equation of `{process}` over the typed body. -/")
        out.append(f"theorem {theorem} {spec.get('parameters', '')} {role_spec.get('binders', '')}\n"
                   f"    (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles {role}){separate_binder}\n"
                   f"    {self.binders(binders)}{role_spec.get('premises', '')}"
                   f"{' ' if role_spec.get('premises') else ''}:\n"
                   f"    {function} (F := F) (G := G) {parameter_names} ctx self\n"
                   f"      {paren(values_literal(components))} =\n"
                   f"      {process} {process_arguments} := by\n"
                   f"  subst self\n"
                   f"  let m := {spec['meaning'].replace(' self ', ' (ctx.roles ' + str(role) + ') ')}\n"
                   f"  unfold {unfolds}\n"
                   f"  simp only [{process}, PIR.Process.bind{associate(node)}]\n"
                   + script + "\n")
        self.role_infos[(function, name)] = {
            "role": role, "process": process, "process_binders": [variable for variable, _ in used],
            "theorem": theorem, "parameters": binder_names(spec.get("parameters", "")),
            "binders": binder_names(role_spec.get("binders", "")),
            "premises": binder_names(role_spec.get("premises", "")), "uses_separate": uses_separate,
            "inputs": specs, "outputs": protocol.outputs}
        if spec.get("declaration"):
            self.invocation(out, spec, role_spec, protocol, process, used, theorem, binders, components,
                            uses_separate)

    def protocol_form(self, out, spec, role_spec, protocol, frame, specs, binders, components, process,
                      process_arguments, theorem, function, parameter_names, uses_separate, separate_binder):
        """A whole-body role's equation as an instance of the normalizer's soundness theorem."""
        role = role_spec["role"]
        name = role_spec["name"]
        pattern, fixed_inputs = [], {}
        for position, (wire, item) in enumerate(zip(protocol.inputs, specs)):
            mode = item.get("mode", "present")
            if mode == "absent":
                pattern.append("absent")
            elif "value" in item:
                kind = wire[0]
                if kind not in ("index", "field", "bool"):
                    raise GeneratorError(f"{name}: fixed inputs of sort {kind} are not supported")
                pattern.append([kind, str(item["value"])])
                fixed_inputs[str(item["value"])] = position
            elif mode == "optional":
                pattern.append("optional")
            else:
                pattern.append("present")
                fixed_inputs[item["name"]] = position
        laws = self.law_table(role_spec, frame, protocol.inputs, fixed_inputs)
        kept_raws, kept_terms = self.kept_helpers(role_spec)
        strict = bool(role_spec.get("strict"))
        others = [other for other in range(len(protocol.roles)) if other != role]
        roster = len(protocol.roles) if uses_separate else 1
        if not uses_separate and role != 0:
            raise GeneratorError(f"{name}: a role other than the first needs the separate roster premise")
        callees = self.callee_keys(out, frame, role, role_spec, fixed_inputs)
        request = [protocol.name, None, str(role), str(roster), pattern, self.law_request(laws), strict, kept_raws,
                   [[callee["raw"], str(callee["index"]), callee["pattern_json"],
                     [None if pin is None else str(pin) for pin in callee["pins"]]] for callee in callees]]
        result = run_normalizer(self.request["fixture"], request, name)
        signature, pattern_name, results_name, form_name = (f"{name}Signature", f"{name}Pattern",
                                                            f"{name}Results", f"{name}Form")
        types = ty_list(protocol.inputs, True)
        out.append(f"/-- The {name}'s laws as the normalizer reads them, keyed by helper. -/")
        out.append(f"def {signature} : NormalForm.Signature :=\n"
                   f"  {self.signature_literal(laws, result.get('names'), kept_terms, strict, callees)}\n")
        out.append(f"/-- The results the {name}'s laws present, from the request's templates. -/")
        out.append(f"def {results_name} : NormalForm.LawResults (ringModel F G) {signature}.laws :=\n"
                   f"  {self.results_body(laws, signature)}\n")
        processes, processes_parameters = self.callee_processes(out, name, signature, callees, spec)
        out.append(f"/-- The {name}'s inputs as the normalizer reads them. -/")
        out.append(f"def {pattern_name} : NormalForm.InputPattern {types} :=\n"
                   f"  {values_literal([self.pattern_entry(item) for item in pattern])}\n")
        form_text = lean_form(result["form"], 2, self.helper_term_of, self.repeat_regions(spec),
                              [(callee["signature"], [(present, wire) for _, _, present, wire in callee["scope"]])
                               for callee in callees])
        form_parameters = binders_used(spec.get("parameters", ""), form_text)
        form_term = paren(f"{form_name} {' '.join(binder_names(form_parameters))}".strip())
        out.append(f"/-- The {name}'s form, printed from the compiled normalizer; the kernel checks it. -/")
        out.append(f"noncomputable def {form_name} {form_parameters} : NormalForm.Form {signature}.laws {signature}.callees "
                   f"{pattern_name}.scope {ty_list(protocol.outputs, True)} :=\n" + form_text + "\n")
        normalized_parameters = binders_used(spec.get("parameters", ""), f"{spec['body']} {form_term}")
        out.append(f"theorem {name}_normalized {normalized_parameters} :\n"
                   f"    NormalForm.normalize {signature} {paren(spec['body'])} {role} {roster} "
                   f"{pattern_name} = .ok {form_term} := by\n  kernel_rfl\n")
        out.append(f"theorem {name}_lawsMatch {form_parameters} : {form_term}.CallsMatch := by\n  kernel_rfl\n")
        scope_names = [binder for binder, _ in binders]
        binders_value = binders_literal(scope_names)
        scope_binders = self.binders(binders)
        out.append(f"theorem {name}_environment {scope_binders}:\n"
                   f"    {pattern_name}.environment (ringModel F G) ({binders_value}) =\n"
                   f"      ({values_literal(components)} : Values (Component (assignment F G)) {types}) := by\n"
                   f"  kernel_rfl\n")
        tables, protocols = spec["tables"], spec["protocols"]
        out.append("/-- The form's process is the readable process. -/")
        out.append(f"theorem {name}_presentation {spec.get('parameters', '')} (ctx : ProtocolContext)\n"
                   f"    {scope_binders}:\n"
                   f"    {form_term}.denote (ringModel F G) ({tables}).toOn {results_name} ctx\n"
                   f"        (NormalForm.Runs.uniform ({tables}) ({protocols}) ctx (ctx.roles {role})) "
                   f"{processes}\n        ({binders_value}) =\n"
                   f"      {process} {process_arguments} := by\n  kernel_rfl\n")
        environment = values_literal(components)
        laws_text = f"{tables} {environment} " + " ".join(law["law"].term for law in laws)
        laws_binders = (f"{binders_used(spec.get('parameters', ''), laws_text)} "
                        f"{binders_used(role_spec.get('binders', ''), laws_text)} "
                        f"{scope_binders}{binders_used(role_spec.get('premises', ''), laws_text)}")
        laws_arguments = " ".join(binder_names(laws_binders))
        self.law_proofs(out, name, laws, results_name, spec, laws_binders, environment, types, fixed_inputs)
        callees_call = self.callee_proofs(out, name, signature, callees, processes, spec, role_spec,
                                          scope_binders, environment, types, others)
        distinct = "(.ofSeparate separate (by decide))" if uses_separate else "(NormalForm.RosterDistinct.only ctx)"
        names_in_order = " ".join(scope_names)
        out.append(f"/-- The process equation of `{process}`, an instance of the normalizer's soundness. -/")
        out.append(f"theorem {theorem} {spec.get('parameters', '')} {role_spec.get('binders', '')}\n"
                   f"    (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles {role}){separate_binder}\n"
                   f"    {self.binders(binders)}{role_spec.get('premises', '')}"
                   f"{' ' if role_spec.get('premises') else ''}:\n"
                   f"    {function} (F := F) (G := G) {parameter_names} ctx self\n"
                   f"      {paren(values_literal(components))} =\n"
                   f"      {process} {process_arguments} := by\n"
                   f"  subst self\n"
                   f"  exact (NormalForm.sound_uniform {signature} {paren(spec['body'])} {role} {roster} {pattern_name}\n"
                   f"    {form_term} ({name}_normalized {' '.join(binder_names(normalized_parameters))}) "
                   f"({name}_lawsMatch {' '.join(binder_names(form_parameters))}) ctx {distinct}\n"
                   f"    ({tables}) ({protocols}) {results_name} {processes} ({binders_value}) _\n"
                   f"    ({name}_environment {names_in_order}) ({name}_laws {laws_arguments}) {callees_call}).trans\n"
                   f"    ({name}_presentation {parameter_names} ctx {names_in_order})\n")

    def callee_keys(self, out, frame, role, role_spec, fixed_inputs):
        """The callee forms that present this role's applications, keyed by callee signature and
        role, with each callee's summary: its invocation in this unit at any child context."""
        callees = []
        for site, app in frame.applications.items():
            if role not in app.roles:
                continue
            index = app.roles.index(role)
            info = app.callee_roles.get(index)
            if info is None:
                raise GeneratorError(f"application {app.name}: no callee normal form for callee role {index}")
            function = self.unit.function(app.callee)
            uses = frame.application_uses.get(site, {})
            pattern_json, scope = [], []
            for wire, item in zip(function.inputs, info["inputs"]):
                mode = item.get("mode", "present")
                if mode == "absent":
                    pattern_json.append("absent")
                elif "value" in item:
                    pattern_json.append([wire[0], str(item["value"])])
                elif mode == "optional":
                    pattern_json.append("optional")
                    scope.append((item["name"], f"Option {paren(value_type(wire))}", False, wire))
                else:
                    pattern_json.append("present")
                    scope.append((item["name"], value_type(wire), True, wire))
            pinned = bool(info["premises"])
            pins = []
            for binder, _, present_binder, _ in scope:
                term = uses.get(binder)
                pins.append(fixed_inputs.get(term) if pinned and present_binder and term in fixed_inputs else None)
            # Applications of one callee role on the same pattern and pins share one callee form.
            if any(known["signature"] == app.signature and known["index"] == index
                   and known["pattern_json"] == pattern_json and known["pins"] == pins for known in callees):
                continue
            callee = {"app": app, "index": index, "info": info, "function": function, "raw": app.callee,
                      "signature": app.signature, "pattern_json": pattern_json, "scope": scope, "pins": pins,
                      "pattern_lean": paren(values_literal([self.pattern_entry(item) for item in pattern_json])),
                      "uses": uses}
            self.callee_summary(out, callee, role_spec, fixed_inputs)
            callees.append(callee)
        return callees

    def callee_summary(self, out, callee, role_spec, fixed_inputs):
        """A callee's invocation in this unit at any child context: the input masks, the callee's
        process theorem and the participant's view of the returned tuple."""
        app, index, info, function = callee["app"], callee["index"], callee["info"], callee["function"]
        others = [other for other in range(len(app.roles)) if other != index]
        if len(others) != 1:
            raise GeneratorError(f"application {app.name}: callee summaries are stated for two-role callees")
        other = others[0]
        # Named by the callee's declaration: the summary holds at any child context.
        declaration = camel(app.definition.rsplit(".", 1)[1].removesuffix("Definition"))
        stem = f"{declaration}_{info['name']}"
        if stem in self.applied:
            return
        self.applied.add(stem)
        kept, hides = self.masked_outputs(out, f"{stem}_returned", function, "ctx", index, other, index)
        pinned = any(pin is not None for pin in callee["pins"])
        # Binder values: the caller's arguments where pinned, else the callee's binder names.
        values = {}
        for (binder, _, _, _), pin in zip(callee["scope"], callee["pins"]):
            values[binder] = callee["uses"][binder] if pin is not None else binder
        declared, unpinned = {}, set()
        for (binder, kind, _, _), pin in zip(callee["scope"], callee["pins"]):
            declared.setdefault(values[binder], kind)
            if pin is None:
                unpinned.add(binder)
        arguments, masked, absent_names = [], [], []
        for position, (wire, item) in enumerate(zip(function.inputs, info["inputs"])):
            mode = item.get("mode", "present")
            if mode == "absent":
                variable_name = f"input{position}"
                absent_names.append((variable_name, f"Option {paren(value_type(wire))}"))
                arguments.append(variable_name)
                masked.append("none")
            elif "value" in item:
                arguments.append(f"some {paren(str(item['value']))}")
                masked.append(f"some {paren(str(item['value']))}")
            elif mode == "optional":
                arguments.append(values[item["name"]])
                masked.append(values[item["name"]])
            else:
                arguments.append(f"some {paren(values[item['name']])}")
                masked.append(f"some {paren(values[item['name']])}")
        def argument(name):
            if name == "ctx":
                return "ctx"
            if name in app.arguments:
                return app.arguments[name]
            if name in values:
                return values[name]
            raise GeneratorError(f"application {app.name}: no value for the callee's {name}")
        process = " ".join([info["process"]] + [paren(argument(name)) for name in info["process_binders"]])
        supplied = app.values.get(index, {})
        theorem_arguments = [info["theorem"]]
        theorem_arguments += [f"({name} := {app.arguments[name]})" for name in info["parameters"]]
        theorem_arguments += [f"({name} := {supplied[name]})" for name in info["binders"]]
        theorem_arguments += ["(ctx := ctx)", f"(self := ctx.roles {index})", "(role := rfl)"]
        if info["uses_separate"]:
            theorem_arguments.append("(separate := separate)")
        theorem_arguments += [f"({binder} := {values[binder]})" for binder, _, _, _ in callee["scope"]]
        theorem_arguments += [f"({name} := {supplied[name]})" for name in info["premises"]]
        typed = f"Values (Component (assignment F G)) {ty_list(function.inputs, True)}"
        premise_text = " ".join(supplied.get(name, "") for name in info["premises"] + info["binders"])
        role_binders = binders_used(role_spec.get("binders", ""), premise_text)
        premises = binders_used(role_spec.get("premises", ""), premise_text) if pinned else ""
        separate = f" (separate : ctx.roles {other} ≠ ctx.roles {index})" if (hides or info["uses_separate"]) else ""
        binder_declarations = self.binders(list(declared.items()) + absent_names)
        callee["summary"] = f"{stem}_invoke"
        callee["summary_binders"] = (role_binders, separate != "",
                                     [(term, term in unpinned) for term in declared],
                                     [n for n, _ in absent_names], premises)
        view = camel(app.definition.rsplit(".", 1)[1].removesuffix("Definition")) + "_view"
        out.append("set_option linter.unusedSimpArgs false in")
        out.append(f"/-- The `{app.name}` callee at role {index}: its invocation in this unit at any child context. -/")
        out.append(f"theorem {stem}_invoke {role_binders} (ctx : ProtocolContext){separate}\n"
                   f"    {binder_declarations}{premises}{' ' if premises else ''}:\n"
                   f"    invokeProtocol ({app.unit}.plainProtocolTable F G) {app.signature} ctx (ctx.roles {index})\n"
                   f"      ({values_literal(arguments)} : {typed}) =\n"
                   f"      ({process}).bind (fun out => .done {paren(kept.replace('values.get', 'out.get'))}) := by\n"
                   f"  refine ({view} ctx (ctx.roles {index}) _ ({values_literal(masked)} : {typed}) ?_).trans ?_\n"
                   f"  · iterate {len(function.inputs) + 1} unfold maskValues\n"
                   f"    simp [ProtocolContext.mapScopes, Participant.restrict"
                   f"{', separate, Ne.symm separate' if separate else ''}]\n"
                   f"  refine (congrArg (fun process => PIR.Process.bind process _)\n"
                   f"    ({' '.join(theorem_arguments)})).trans ?_\n"
                   f"  apply congrArg (PIR.Process.bind _)\n"
                   f"  funext out\n"
                   f"  exact congrArg PIR.Process.done ({stem}_returned ctx{' separate' if hides else ''} out)\n")

    def callee_processes(self, out, name, signature, callees, spec):
        """The callees' presented processes, by callee index, at a child context and on the
        callee's binders."""
        if not callees:
            return "(NormalForm.noCallees _)", ""
        cases = []
        for position, callee in enumerate(callees):
            info, app = callee["info"], callee["app"]
            names = [binder for binder, _, _, _ in callee["scope"]]
            def argument(binder):
                if binder == "ctx":
                    return "ctx"
                if binder in app.arguments:
                    return app.arguments[binder]
                if binder in names:
                    return f"(NormalForm.entryAt binders {variable(names.index(binder))})"
                raise GeneratorError(f"application {app.name}: no value for the callee's {binder}")
            process = " ".join([info["process"]] + [paren(argument(binder)) for binder in info["process_binders"]])
            cases.append(f"  | ⟨{position}, _⟩ => fun ctx binders => {process}")
        cases.append(f"  | ⟨_ + {len(callees)}, outside⟩ => absurd outside (by simp [{signature}])")
        text = "\n".join(cases)
        parameters = binders_used(spec.get("parameters", ""), text)
        out.append(f"/-- The {name}'s callees' processes, by callee. -/")
        out.append(f"def {name}Callees {parameters} : NormalForm.CalleeProcesses (ringModel F G) {signature}.callees :=\n"
                   f"  fun callee => match callee with\n{text}\n")
        return paren(f"{name}Callees {' '.join(binder_names(parameters))}".strip()), parameters

    def callee_proofs(self, out, name, signature, callees, processes, spec, role_spec, scope_binders,
                      environment, types, others):
        """The callees' premise: each callee's summary, at the binders and child contexts the
        soundness theorem names."""
        if not callees:
            return "(NormalForm.noCallees_hold _ _)"
        cases = []
        all_binders = ""
        for position, callee in enumerate(callees):
            role_binders, separated, declared, absent_names, premises = callee["summary_binders"]
            names = ["callee" + binder[0].upper() + binder[1:] for binder, _, _, _ in callee["scope"]]
            pinned = [f"p{index}" if pin is not None else "_" for index, pin in enumerate(callee["pins"])]
            binders_pattern = values_literal(names) if names else ".nil"
            others_pattern = values_literal(absent_names) if absent_names else ".nil"
            pinned_pattern = "⟨" + ", ".join(pinned + ["_"]) + "⟩" if any(pin is not None for pin in callee["pins"]) else "_"
            rewrites = []
            scope_names = [binder for binder, _, _, _ in callee["scope"]]
            for index, pin in enumerate(callee["pins"]):
                if pin is not None:
                    caller = callee["uses"][scope_names[index]]
                    rewrites.append(f"← (Option.some.inj (p{index} : some {caller} = some {names[index]}) : "
                                    f"{caller} = {names[index]})")
            other = [o for o in range(len(callee['app'].roles)) if o != callee['index']][0]
            separate = (f" (distinct {other} (show {other} < {len(callee['app'].roles)} by decide) "
                        f"(show ({other} : Nat) ≠ {callee['index']} by decide))") if separated else ""
            summary_arguments = " ".join(binder_names(role_binders))
            fresh = dict(zip(scope_names, names))
            declared_arguments = " ".join(paren(fresh[term] if is_binder else term) for term, is_binder in declared)
            premise_arguments = " ".join(binder_names(premises))
            body = (f"    | {binders_pattern}, {others_pattern}, {pinned_pattern} => by\n"
                    + (f"      rw [{', '.join(rewrites)}]\n" if rewrites else "")
                    + f"      exact {callee['summary']} {summary_arguments} ctx{separate} {declared_arguments} "
                      f"{' '.join(absent_names)} {premise_arguments}")
            cases.append(f"  | ⟨{position}, _⟩ => fun ctx binders others pinned distinct =>\n"
                         f"    match binders, others, pinned with\n{body}")
            all_binders += f" {role_binders} {premises}"
        cases.append(f"  | ⟨_ + {len(callees)}, outside⟩ => absurd outside (by simp [{signature}])")
        text = "\n".join(cases)
        parameters = binders_used(spec.get("parameters", ""), f"{processes} {spec['protocols']}")
        theorem_binders = f"{parameters} {binders_used(role_spec.get('binders', ''), text)} {scope_binders}" \
                          f"{binders_used(role_spec.get('premises', ''), text)}"
        out.append(f"/-- The {name}'s callees present their applications: each callee's invocation in this unit. -/")
        out.append(f"theorem {name}_callees {theorem_binders}:\n"
                   f"    NormalForm.CalleesHold ({spec['protocols']}) {processes}\n"
                   f"      ({environment} : Values (Component (assignment F G)) {types}) :=\n"
                   f"  fun callee => match callee with\n{text}\n")
        return paren(f"{name}_callees {' '.join(binder_names(theorem_binders))}")

    def invocation(self, out, spec, role_spec, protocol, process, used, theorem, binders, components,
                   uses_separate):
        """The role's invocation of the protocol at any caller context and, for the unit's
        entry, its participant: the input masks, the body's normal form and the output masks."""
        role = role_spec["role"]
        name = role_spec["name"]
        terms = self.unit_terms()
        others = [other for other in range(len(protocol.roles)) if other != role]
        if len(others) != 1:
            raise GeneratorError("invocation theorems are supported for two-role protocols")
        other = others[0]
        # Outer inputs: the role's own inputs as its normal form takes them; the others are
        # arbitrary optional values that the input masks remove.
        outer, outer_binders = [], []
        for position, (wire, item, scope) in enumerate(zip(protocol.inputs, role_spec["inputs"],
                                                            protocol.input_scopes)):
            if role in scope:
                outer.append(components[position])
                continue
            if item.get("mode", "present") != "absent":
                raise GeneratorError(f"{name}: input {position} is outside the role's scope; declare it absent")
            variable = item.get("name", f"input{position}")
            outer.append(variable)
            outer_binders.append((variable, f"Option {paren(value_type(wire))}"))
        all_binders = self.binders(merge_pairs(binders, outer_binders))
        premises = role_spec.get("premises", "")
        named = [f"({variable} := {variable})" for variable in
                 binder_names(spec.get("parameters", "")) + binder_names(role_spec.get("binders", ""))]
        named += [f"({variable} := {variable})" for variable, _ in binders]
        named += [f"({variable} := {variable})" for variable in binder_names(premises)]
        kept, hides = self.masked_outputs(out, f"{name}_outputs", protocol, "ctx", role, other)
        kept = kept.replace("values.get", "out.get")
        bound = "out" if "out.get" in kept else "_"
        signature = self.signature_term(protocol)
        arguments = " ".join(variable for variable, _ in used)
        separate = "(separate := separate) " if uses_separate else ""
        out.append("set_option linter.unusedSimpArgs false in")
        out.append(f"/-- The {name}'s invocation at any caller context: the input masks, the normal form of\n"
                   f"the body and the output masks, with this unit's protocol table. -/")
        out.append(f"theorem {name}_invoke {spec.get('parameters', '')} {role_spec.get('binders', '')}\n"
                   f"    (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles {role})\n"
                   f"    (separate : ctx.roles {other} ≠ self)\n"
                   f"    {all_binders}{premises}{' ' if premises else ''}:\n"
                   f"    invokeProtocol ({terms['name']}.plainProtocolTable F G) {signature} ctx self\n"
                   f"      {paren(values_literal(outer))} =\n"
                   f"      ({process} {arguments}).bind (fun {bound} => .done {paren(kept)}) := by\n"
                   f"  refine ({spec['declaration']}_view ctx self _ {paren(values_literal(components))} ?_).trans ?_\n"
                   f"  · subst self\n"
                   f"    iterate {len(protocol.inputs) + 1} unfold maskValues\n"
                   f"    simp [ProtocolContext.mapScopes, Participant.restrict, separate, Ne.symm separate]\n"
                   f"  subst self\n"
                   f"  refine (congrArg (fun process => PIR.Process.bind process _)\n"
                   f"    ({theorem} {' '.join(named)} (ctx := ctx) (self := ctx.roles {role}) (role := rfl)\n"
                   f"      {separate})).trans ?_\n"
                   f"  apply congrArg (PIR.Process.bind _)\n"
                   f"  funext out\n"
                   f"  exact congrArg PIR.Process.done ({name}_outputs ctx{' separate' if hides else ''} out)\n")
        if protocol.name != self.unit.entry:
            return
        root_arguments = " ".join("({} : ProtocolContext)" if variable == "ctx" else variable
                                  for variable, _ in used)
        named_root = " ".join(named + [f"({variable} := {variable})" for variable, _ in outer_binders])
        out.append(f"/-- The {name}'s participant of the admitted unit. -/")
        out.append(f"theorem {name}_participant {spec.get('parameters', '')} {role_spec.get('binders', '')}\n"
                   f"    {all_binders}{premises}{' ' if premises else ''}:\n"
                   f"    {terms['program']}.participant F G {role} {paren(values_literal(outer))} =\n"
                   f"      ({process} {root_arguments}).bind (fun {bound} => .done {paren(kept)}) :=\n"
                   f"  ({terms['name']}.protocolTable_forgetSites (F := F) (G := G) {signature} {{}} {role}\n"
                   f"    {paren(values_literal(outer))}).trans\n"
                   f"    ({name}_invoke {named_root} (ctx := {{}}) (self := {role}) (role := rfl)\n"
                   f"      (separate := by decide))\n")

    def projections(self, count):
        """Projections of the components of a right-nested tuple named `result`."""
        if count == 1:
            return ["result"]
        return ["result" + ".2" * index + (".1" if index < count - 1 else "") for index in range(count)]

    def write(self):
        text = self.header() + "\n".join(self.parts) + f"\nend {self.request['namespace']}\n"
        text = re.sub(r"(\S)  +(?=\S)", r"\1 ", text)
        return re.sub(r"[ \t]+\n", "\n", text)


# Generated callee modules, by request path and function, for protocol applications.
CALLEES = {}


def build(module, request):
    if "bodies" in request:
        module.bodies(request["bodies"])
    if "root" in request:
        module.root(request["root"])
    if "contract" in request:
        module.contract(request["contract"])
    for spec in request.get("shared", []):
        module.shared(spec)


def generate(path):
    request = tomllib.loads(path.read_text(encoding="utf-8"))
    module = Module(request, path.resolve())
    build(module, request)
    return module.write(), ROOT / request["output"]


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("request", type=Path)
    parser.add_argument("--check", action="store_true",
                        help="fail if the output file differs from the generated module")
    parser.add_argument("--output", type=Path, help="write here instead of the request's output path")
    args = parser.parse_args()
    try:
        text, output = generate(args.request)
    except GeneratorError as error:
        sys.exit(f"normal_forms: {error}")
    if args.output:
        output = args.output
    if args.check:
        if not output.is_file() or output.read_text(encoding="utf-8") != text:
            sys.exit(f"normal_forms: {output} is not the generated module; regenerate it")
        return
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
