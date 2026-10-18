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
    builder, the formula's process and the observed decision.

The output is ordinary Lean source. Every definition and equation is
elaborated and checked by the kernel, so a generator error, a stale request or
a changed program is reported as a failed equation rather than trusted. Root
equations are definitional. Equations over a shared typed body (for every unit
whose checked body it is) are proved by explicit operation steps that use the
helper laws named in the request.

Usage, from the repository root:
  python3 lean/bridges/structured/normal_forms.py REQUEST.toml [--check]

`--check` compares the generated module with the existing output file and
fails when they differ, without writing it.
"""

import argparse
import json
import re
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


# ---------------------------------------------------------------------------
# Symbolic values

@dataclass(frozen=True)
class Sym:
    kind: str           # "present", "absent" or "optional"
    wire: tuple
    expr: str = ""      # present: a Lean term; optional: the variable holding it

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
    variable: str
    none: object
    some: object


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
        return (f"{pad}match {node.variable} with\n{pad}| none =>\n" + render_process(node.none, indent + 2)
                + f"\n{pad}| some {node.variable} =>\n" + render_process(node.some, indent + 2))
    if isinstance(node, Bind):
        return (f"{pad}({node.process}).bind fun ({node.binder} : {node.binder_type}) =>\n"
                + render_process(node.next, indent))
    if isinstance(node, If):
        return (f"{pad}if {node.prop} then\n" + render_process(node.then, indent + 2)
                + f"\n{pad}else\n" + render_process(node.otherwise, indent + 2))
    raise GeneratorError(f"unknown process node {node}")


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


class Evaluator:
    """Symbolic participant execution of one block at one role.

    The process tree and, in shared mode, the proof script come from the same
    traversal, so the stated normal form is exactly what the steps derive."""

    def __init__(self, frame, names, finish):
        self.frame = frame
        self.names = names
        self.finish = finish
        self.shared = frame.mode == "shared"

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
        # A strict use of an undetermined optional value splits on its presence first.
        for position in self.demands(descriptor, args):
            if args[position].kind == "optional":
                return self.split(args[position].expr, instructions, terminator, env, proof, indent)
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
            return self.repeat(descriptor, args, results, site, rest, terminator, proof, indent, step)
        raise GeneratorError(f"unsupported instruction {head} at site {site!r}")

    def repeat(self, descriptor, args, results, site, rest, terminator, proof, indent, step):
        """A repeat at a role in its roster: the actual repeat of the body's own callback, then
        the retained return of its state."""
        _, state_count, _, roles, _ = descriptor
        if self.frame.roles[self.frame.role] not in roles:
            raise GeneratorError("normal forms of a role outside a repeat's roster are not supported")
        if rest:
            raise GeneratorError("only the return may follow a repeat")
        if not self.frame.callback or not self.frame.repeat_spec:
            raise GeneratorError("a body with a repeat needs `callback` and `repeat_spec` in the request")
        count, state, captures = args[0], args[1:1 + state_count], args[1 + state_count:]
        me = self.role_term(self.frame.role)
        typed_state = (f"({values_literal([value.component() for value in state])} : "
                       f"Values (Component (assignment F G)) {ty_list(results, True)})")
        typed_captures = (f"({values_literal([value.component() for value in captures])} : "
                          f"Values (Component (assignment F G)) {ty_list([value.wire for value in captures], True)})")
        process = (f"denoteRepeat ({self.frame.repeat_spec}) ctx {me} {paren(count.component())} {typed_state}\n"
                   f"    {typed_captures} ({self.frame.callback} ctx {me})")
        pad = " " * indent
        if self.shared:
            proof.append(f"{pad}refine (Region.denote_letOp_values m (.repeat ({self.frame.repeat_spec}) "
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
        if kind != "return":
            raise GeneratorError("a repeat must be followed by the body's return")
        node = self.finish([inner[index] if index < state_count else None for index in indices], None, pad)
        if self.shared:
            proof.append(f"{pad}{'  ' * state_count}rfl")
        return Bind(process, "state", f"Values (Component (assignment F G)) {ty_list(results, True)}", node)

    def demands(self, descriptor, args):
        """Operand positions whose presence decides this operation's behaviour here."""
        head = descriptor[0]
        if head == "call":
            if not self.shared and not any(key in self.frame.laws for key in
                                           (descriptor[1], self.helper_term(descriptor[1]))):
                return range(len(args))
            return [] if self.law(descriptor[1]).components else range(len(args))
        if head in BINARY:
            return range(len(args))
        if head == "local_call":
            return range(len(args)) if self.frame.roles.index(descriptor[2]) == self.frame.role else []
        if head == "exchange":
            return [0] if self.frame.roles.index(descriptor[1]) == self.frame.role else []
        if head in ("draw", "guard"):
            return range(len(args)) if self.frame.roles.index(descriptor[1]) == self.frame.role else []
        return []

    def split(self, variable, instructions, terminator, env, proof, indent):
        pad = " " * indent
        none_env = [absent(value.wire) if value.kind == "optional" and value.expr == variable else value
                    for value in env]
        some_env = [present(value.wire, variable) if value.kind == "optional" and value.expr == variable
                    else value for value in env]
        none_proof, some_proof = [], []
        none_node = self.run(instructions, terminator, none_env, none_proof, indent + 2)
        some_node = self.run(instructions, terminator, some_env, some_proof, indent + 2)
        if self.shared:
            proof.append(f"{pad}cases {variable} with")
            proof.append(f"{pad}| none =>")
            proof.extend(none_proof)
            proof.append(f"{pad}| some {variable} =>")
            proof.extend(some_proof)
        return Match(variable, none_node, some_node)

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
        law = self.law(descriptor[1])
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
        then = self.run(rest, terminator, decided_env, holds_proof, indent + 2)
        Step(self, fails_proof, pad + "  ").halt(op, "reject",
                                                 ("guard", owner, present(condition.wire, "false"), None))
        if self.shared:
            proof.append(f"{pad}by_cases {holds} : {prop}")
            proof.append(f"{pad}· simp only [eq_true {holds}, decide_true, ↓reduceIte, PIR.Proc.bind]")
            proof.extend(holds_proof)
            proof.append(f"{pad}· simp only [eq_false {holds}, decide_false, ↓reduceIte, PIR.Proc.bind]")
            proof.extend(fails_proof)
        return If(prop, then, Halt("reject"))


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
            return [f"change PIR.Proc.done (I := participantInterface F G) "
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
                    f"PIR.Proc.interpret, participantActions, PIR.Proc.bind]",
                    "rfl"]
        if kind == "draw":
            _, owner, site, field_name, args = how
            handles = paren(values_literal([arg.component() for arg in args]))
            facts = "" if owner == frame.role else f"{separate}, "
            return [f"change ((Participant.query (services := services) (Value := assignment F G) "
                    f"({me}) {evaluator.role_term(owner)} {evaluator.qualified_site(site)} "
                    f"{json.dumps(field_name)} {handles}).interpret (participantActions F G)).bind "
                    f"(fun value => .done (one (F := F) (G := G) (ty := .field {json.dumps(field_name)}) value)) = _",
                    f"simp only [Participant.query, {facts}↓reduceIte, PIR.Proc.interpret, PIR.Proc.bind]",
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
            lines += [f"simp only [Participant.guard, {facts}↓reduceIte, PIR.Proc.interpret, PIR.Proc.bind]",
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
        imports = "\n".join(f"public import {name}" for name in self.request["imports"])
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
            out.append(f"def {process} {used_binders}:\n    PIR.Proc (participantInterface F G)\n"
                       f"      (Values (Component (assignment F G)) {program}.payload.entry.outputs) :=\n"
                       f"{text}\n")
            out.append(f"theorem {role_name}_process {binders}:\n    {program}.participant F G {role} "
                       f"({inputs_name} {arguments}) =\n      {application} := by\n  rfl\n")
            replies = self.run_equation(out, program, role, role_name, inputs_name, arguments, binders, node)
            self.roles_info[role] = {"name": role_name, "inputs": inputs_name, "held": held,
                                     "arguments": arguments, "binders": binders, "replies": replies,
                                     "node": node}
        self.parts.append("\n".join(out))
        self.root_spec = (entry, sites, names, role_names, program)

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
        self.parts.append("\n".join(out))

    def chain(self, block, roles, pad, last=None):
        lines = []
        frame = Frame(self.unit, roles, 0, "root", {}, self.helpers(), {}, {})
        evaluator = Evaluator(frame, Names(), None)
        for descriptor, operand_list, results, _, site in block[1]:
            lines.append(f"{pad}.letOp (.mark {json.dumps(site)}) .nil .nil <|")
            op = typed_op(evaluator, descriptor, results, site, roles)
            lines.append(f"{pad}.letOp {op} {paren(operands(operand_list))} .nil <|")
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
                   f"  change (PIR.Proc.done (I := closedInterface) (.cons {paren(decision_bool)} .nil :\n"
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
    def shared(self, spec):
        unit = self.unit
        protocol = unit.function(spec["protocol"])
        if spec.get("repeat"):
            instruction = find_repeat(protocol.body, spec["repeat"])
            if instruction is None:
                raise GeneratorError(f"no repeat with site {spec['repeat']!r} in {protocol.name}")
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
        function = spec["function"]
        parameters = spec.get("parameters", "")
        parameter_names = " ".join(re.findall(r"\((\w+)\s*:", parameters))
        meaning = spec["meaning"]
        out.append("/-- The typed body's process at one participant, with this unit's tables. -/")
        out.append(f"def {function} {parameters} (ctx : ProtocolContext) (self : Nat) :\n"
                   f"    RegionFunction (Component (assignment F G)) (participantInterface F G)\n"
                   f"      ({ty_list(inputs, True)}, {ty_list(outputs, True)}) :=\n"
                   f"  fun args => {paren(spec['body'])}.denote\n    ({meaning}) args.get\n")
        captures = inputs[1 + state_count:] if state_count is not None else []
        for role_spec in spec["roles"]:
            if state_scopes is None:
                self.shared_protocol_role(out, spec, role_spec, protocol, block, sites, function,
                                          parameter_names)
            else:
                self.shared_role(out, spec, role_spec, protocol, inputs, outputs, block, state_scopes,
                                 captures, sites, function, parameter_names)
        self.parts.append("\n".join(out))

    def shared_role(self, out, spec, role_spec, protocol, inputs, outputs, block, state_scopes, captures,
                    sites, function, parameter_names):
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
            out.append(f"omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in\n"
                       f"/-- Masking the carried state to its declared scopes keeps the {name}'s components. -/")
            out.append(f"theorem {embed}_masked (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles {role})\n"
                       f"    {self.binders(pairs)}:\n"
                       f"    maskValues self (ctx.mapScopes {scopes}) ({embed} (F := F) (G := G) {arguments}) =\n"
                       f"      {embed} {arguments} := by\n"
                       f"  subst self\n  unfold {embed}\n  iterate {len(state) + 1} unfold maskValues\n"
                       f"  simp [ProtocolContext.mapScopes, Participant.restrict]\n")
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
            capture_binders.append((capture["name"], f"Option {value_type(wire)}" if mode == "optional"
                                    else value_type(wire)))
            capture_components.append(capture["name"] if mode == "optional" else f"some {capture['name']}")
            env.append(optional(wire, capture["name"]) if mode == "optional" else present(wire, capture["name"]))
        frame = Frame(self.unit, protocol.roles, role, "shared", sites, self.helpers(),
                      load_laws(role_spec.get("laws")), dict(role_spec.get("guards", {})),
                      separate="separate", closed=spec["closed"], components=spec.get("components", ""))
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
            return Done(tuple_literal(parts))

        proof = []
        node = Evaluator(frame, names, finish).run(block[1], block[2], env, proof, 2)
        process = role_spec.get("process", f"{name}Process")
        text = render_process(node, 2)
        free_pairs = [(slot["name"], slot_type(slot)) for slot in free]
        used_pairs = [(variable, kind) for variable, kind in [("ctx", "ProtocolContext")] + capture_binders + free_pairs
                      if re.search(rf"(?<![\w.]){re.escape(variable)}(?![\w'])", text)]
        process_binders = self.binders(used_pairs)
        process_arguments = " ".join(variable for variable, _ in used_pairs)
        theorem_binders = self.binders(capture_binders + free_pairs)
        script = "\n".join(proof)
        uses_separate = re.search(r"(?<![\w.])separate(?![\w'])", script) is not None
        result_type = " × ".join(paren(slot_type(slot)) if " " in slot_type(slot) else slot_type(slot)
                                 for slot in slots)
        out.append(f"/-- The {name}'s normal form of one body run: its ordered actions, the values it\n"
                   f"computes, guards as conditionals and missing inputs as stops. -/")
        out.append(f"def {process} {process_binders}:\n"
                   f"    PIR.Proc (participantInterface F G) ({result_type}) :=\n{text}\n")
        projections = self.projections(len(slots))
        embedded = f"{embed} {' '.join(projections)}"
        ends = f"(fun result => .done ({embedded}))"
        others = [other for other in range(len(protocol.roles)) if other != role]
        if len(others) != 1:
            raise GeneratorError("shared normal forms support two-role protocols")
        theorem = role_spec.get("theorem", f"{name}_process")
        premises = role_spec.get("premises", "")
        binders = role_spec.get("binders", "")
        out.append("set_option linter.unusedSimpArgs false in")
        out.append(f"/-- The process equation of `{process}` over the typed body. -/")
        separate_binder = f"\n    (separate : ctx.roles {others[0]} ≠ self)" if uses_separate else ""
        application = f"{process} {process_arguments}".strip()
        unfolds = " ".join([function, *spec.get("unfold", [spec["body"]])])
        out.append(f"theorem {theorem} {spec.get('parameters', '')} {binders}\n"
                   f"    (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles {role}){separate_binder}\n"
                   f"    (index : Nat) {theorem_binders}{premises}{' ' if premises else ''}:\n"
                   f"    {function} (F := F) (G := G) {parameter_names} ctx self (.cons (some index)\n"
                   f"      (({embed} {' '.join(state_args)}).append {paren(values_literal(capture_components))})) =\n"
                   f"      ({application}).bind {ends} := by\n"
                   f"  subst self\n"
                   f"  let m := {spec['meaning'].replace(' self ', ' (ctx.roles ' + str(role) + ') ')}\n"
                   f"  unfold {unfolds}\n"
                   f"  simp only [{process}, PIR.Proc.bind]\n"
                   + script + "\n")

    def shared_protocol_role(self, out, spec, role_spec, protocol, block, sites, function, parameter_names):
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
                      repeat_spec=spec.get("repeat_spec", ""))
        names = Names([binder for binder, _ in binders] + list(sites.values()))

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
        out.append(f"def {process} {process_binders}:\n    PIR.Proc (participantInterface F G)\n"
                   f"      (Values (Component (assignment F G)) {ty_list(protocol.outputs, True)}) :=\n{text}\n")
        theorem = role_spec.get("theorem", f"{name}_process")
        unfolds = " ".join([function, *spec.get("unfold", [])])
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
                   f"  simp only [{process}, PIR.Proc.bind]\n"
                   + script + "\n")

    def projections(self, count):
        """Projections of the components of a right-nested tuple named `result`."""
        if count == 1:
            return ["result"]
        return ["result" + ".2" * index + (".1" if index < count - 1 else "") for index in range(count)]

    def write(self):
        text = self.header() + "\n".join(self.parts) + f"\nend {self.request['namespace']}\n"
        return re.sub(r"[ \t]+\n", "\n", text)


def generate(path):
    request = tomllib.loads(path.read_text(encoding="utf-8"))
    module = Module(request, path.resolve())
    if "bodies" in request:
        module.bodies(request["bodies"])
    if "root" in request:
        module.root(request["root"])
    if "contract" in request:
        module.contract(request["contract"])
    for spec in request.get("shared", []):
        module.shared(spec)
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
