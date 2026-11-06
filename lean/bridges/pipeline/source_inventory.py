"""Exact-artifact source identity lookup for bridge generators.

Read the native correspondence inventory once, bind it to the independently
exported original/interface/snapshot, and check its row and occurrence joins.
This is transport validation, not an elaboration or execution proof. Written
nodes remain proposals; generated origins remain unordered provenance. Actual
call/region traversal and independently checked Lean bodies supply meaning.
"""

from copy import deepcopy
from dataclasses import dataclass

from bridges.common import interface as language_interface
from bridges.common.lean_render import require
from bridges.pipeline.source_claims import canonical, decode, digest
from bridges.structured.snapshot import origin_term


def fields(value, names, label):
    require(isinstance(value, dict) and set(value) == set(names.split()),
            f"source inventory: unexpected {label} fields")
    return value


def sequence(value, label):
    require(isinstance(value, list), f"source inventory: {label} must be an array")
    return value


def string(value, label):
    require(isinstance(value, str) and value, f"source inventory: empty or invalid {label}")
    return value


def natural(value, label):
    require(type(value) is int and value >= 0, f"source inventory: invalid {label}")
    return value


def hexadecimal(value):
    return isinstance(value, str) and len(value) == 64 and all(c in "0123456789abcdef" for c in value)


def path_key(value):
    result = []
    for item in sequence(value, "written path"):
        require(isinstance(item, list) and len(item) == 2, "source inventory: invalid path step")
        result.append((string(item[0], "path category"), natural(item[1], "path ordinal")))
    return tuple(result)


def block_sites(block):
    """Static block preorder, including region bodies and stop terminators."""
    require(isinstance(block, list) and len(block) == 3 and block[0] == "block",
            "source inventory: malformed block")
    for instruction in sequence(block[1], "instructions"):
        require(isinstance(instruction, list) and len(instruction) == 5,
                "source inventory: malformed instruction")
        site = instruction[4]
        require(isinstance(site, str), "source inventory: malformed site")
        if site:
            yield site
        for region in sequence(instruction[3], "regions"):
            require(isinstance(region, list) and len(region) == 3, "source inventory: malformed region")
            yield from block_sites(region[2])
    terminal = block[2]
    require(isinstance(terminal, list) and terminal, "source inventory: malformed terminator")
    if terminal[0] == "stop":
        require(len(terminal) == 3, "source inventory: malformed stop")
        yield string(terminal[2], "stop site")


@dataclass(frozen=True)
class Identity:
    """Lookup metadata in one bound inventory; never a proof receipt."""
    symbol: str
    kind: str
    declaration: dict | list
    rows: tuple


class Inventory:
    def __init__(self, export, *, source, interface_text, original_text):
        # Do not let callers mutate an already checked association in place.
        self.document = deepcopy(export)
        document = fields(self.document,
            "format admission source_ast bindings snapshot instances instance_rows generated generated_rows occurrences rows",
            "correspondence")
        require(document["format"] == "zkc.source-correspondence/0", "source inventory: unsupported format")
        admission = fields(document["admission"],
            "format original_sha256 interface_sha256 protocol_symbol capture installation", "admission")
        require(all(hexadecimal(admission[key]) for key in ("capture", "installation")),
                "source inventory: invalid capture or installation")
        interface = language_interface.loads(interface_text)
        self.snapshot = decode(original_text)
        require(isinstance(self.snapshot, list) and len(self.snapshot) == 11,
                "source inventory: malformed snapshot")
        require(canonical(document["snapshot"]) == canonical(self.snapshot), "source inventory: different snapshot")
        require(admission["original_sha256"] == digest(source) == self.snapshot[2]
                and interface["original"] == digest(source).removeprefix("sha256:"),
                "source inventory: different original")
        require(admission["interface_sha256"] == digest(interface_text.removesuffix("\n").encode()),
                "source inventory: different interface")
        require(admission["format"] == self.snapshot[0] == "zkc.structured-source/0"
                and self.snapshot[1] == "original", "source inventory: different stage")
        require(admission["protocol_symbol"] == self.snapshot[3] == interface["protocol"],
                "source inventory: different protocol")
        self.admission = admission
        self.nodes = self._written_nodes(document["source_ast"])
        bindings = fields(document["bindings"],
            "format capture installation locals unassociated_locals declarations units", "bindings")
        self._context(bindings, "zkc.source-bindings/0")
        # Binding observations are retained intact. This reader does not resolve
        # lexical scope, selected callees, notation or source revision values.
        for key in ("locals", "unassociated_locals", "declarations", "units"):
            sequence(bindings[key], key)
        instances = fields(document["instances"], "format capture installation instances", "instances")
        self._context(instances, "zkc.source-instances/0")
        self.identities = {}
        self.symbol_rows = {}
        self.definitions = {}
        self.body_owners = set()
        expected_sites = []
        for table in (4, 5, 6, 7):
            for index, row in enumerate(sequence(self.snapshot[table], "snapshot table")):
                require(isinstance(row, list) and len(row) >= 2, "source inventory: malformed symbol row")
                symbol = string(row[1], "row symbol")
                self.symbol_rows.setdefault(symbol, []).append([table, index])
                if table == 7 and row[0] == "function":
                    require(len(row) == 10 and symbol not in self.definitions,
                            "source inventory: malformed or repeated definition")
                    self.definitions[symbol] = row
                if isinstance(row[-1], list) and row[-1][:1] == ["block"]:
                    self.body_owners.add(symbol)
                    sites = list(block_sites(row[-1]))
                    require(len(sites) == len(set(sites)), "source inventory: repeated definition site")
                    expected_sites.extend((symbol, site) for site in sites)
        for kind, entries, associations in (
            ("instance", sequence(instances["instances"], "instances"), document["instance_rows"]),
            ("generated", sequence(document["generated"], "generated"), document["generated_rows"]),
        ):
            sequence(associations, kind + " associations")
            require(len(entries) == len(associations), "source inventory: incomplete identity associations")
            for ordinal, (entry, association) in enumerate(zip(entries, associations)):
                if kind == "instance":
                    self._instance(entry)
                else:
                    self._generated(entry)
                symbol = string(entry["symbol"], "identity symbol")
                require(symbol not in self.identities, "source inventory: repeated identity symbol")
                fields(association, kind + " rows", "identity association")
                require(type(association[kind]) is int and association[kind] == ordinal,
                        "source inventory: reordered identity association")
                require(canonical(association["rows"]) == canonical(self.symbol_rows.get(symbol, [])),
                        "source inventory: wrong identity row association")
                self.identities[symbol] = Identity(symbol, kind, entry,
                                                   tuple(tuple(row) for row in association["rows"]))
        generated = [identity.declaration for identity in self.identities.values() if identity.kind == "generated"]
        keys = [canonical([entry["purpose"], entry["part"], entry["origins"]]) for entry in generated]
        require(len(keys) == len(set(keys)), "source inventory: repeated generated provenance")
        for symbol, definition in self.definitions.items():
            identity = self.identities.get(symbol)
            if definition[2] == "protocol" and identity is not None and identity.kind == "instance":
                entry = identity.declaration
                if entry["template"]["kind"] == "declaration":
                    require(canonical(definition[8]) == canonical([entry["template"]["owner"], entry["statics"]]),
                            "source inventory: protocol origin differs from instance")
        self._row_associations(document["rows"])
        self.occurrences = {}
        actual_sites = []
        for item in sequence(document["occurrences"], "occurrences"):
            fields(item, "definition site nodes", "occurrence")
            key = (string(item["definition"], "definition"), string(item["site"], "site"))
            actual_sites.append(key)
            self._addresses(item["nodes"])
            self.occurrences[key] = item["nodes"]
        require(actual_sites == expected_sites, "source inventory: incomplete or reordered occurrences")

    def _context(self, value, format):
        require(value["format"] == format and all(value[key] == self.admission[key]
                for key in ("capture", "installation")), "source inventory: mixed source context")

    def _written_nodes(self, ast):
        fields(ast, "format capture installation sources declarations", "written source")
        self._context(ast, "zkc.source-ast/0")
        sources = {}
        for source in sequence(ast["sources"], "sources"):
            fields(source, "module origin bytes sha256", "source")
            name = string(source["module"], "module")
            require(source["origin"] == "captured" and hexadecimal(source["sha256"])
                    and name not in sources, "source inventory: invalid source unit")
            sources[name] = natural(source["bytes"], "source byte length")
        self.sources = sources
        nodes, owners = {}, set()
        for declaration in sequence(ast["declarations"], "declarations"):
            fields(declaration, "owner nodes", "written declaration")
            owner = string(declaration["owner"], "owner")
            require(owner not in owners, "source inventory: repeated written owner")
            owners.add(owner)
            for node in sequence(declaration["nodes"], "written nodes"):
                # Node-specific syntax is owned by the source AST interpreter.
                # This consumer checks only addresses and spans, not elaboration.
                require(isinstance(node, dict) and {"kind", "path", "span"} <= node.keys(),
                        "source inventory: malformed written node")
                string(node["kind"], "written kind")
                key = (owner, path_key(node["path"]))
                require(key not in nodes, "source inventory: repeated written address")
                self._span(node["span"])
                nodes[key] = node
            require((owner, ()) in nodes, "source inventory: missing written declaration root")
        return nodes

    def _span(self, value):
        fields(value, "module begin end", "source span")
        name = string(value["module"], "span module")
        begin, end = natural(value["begin"], "span begin"), natural(value["end"], "span end")
        require(name in self.sources and begin <= end <= self.sources[name],
                "source inventory: span outside captured unit")

    def _addresses(self, values, span=None):
        keys = []
        for value in sequence(values, "written addresses"):
            fields(value, "owner path", "written address")
            key = (string(value["owner"], "written owner"), path_key(value["path"]))
            require(key in self.nodes, "source inventory: missing written address")
            if span is not None:
                require(self.nodes[key]["span"] == span, "source inventory: candidate span differs")
            keys.append(key)
        require(len(keys) == len(set(keys)), "source inventory: repeated written address")

    def _instance(self, entry):
        names = "symbol template statics scoped domains layout oracle_obligations"
        if isinstance(entry, dict) and "oracle_definition" in entry:
            names += " oracle_definition"
        fields(entry, names, "instance")
        template = entry["template"]
        require(isinstance(template, dict), "source inventory: malformed template")
        if template.get("kind") == "declaration":
            fields(template, "kind owner generated source candidates", "declaration template")
            require(type(template["generated"]) is bool, "source inventory: invalid generated flag")
            self._addresses(template["candidates"], template["source"])
        else:
            fields(template, "kind owner source nodes", "scoped template")
            require(template["kind"] == "scoped", "source inventory: unknown template kind")
            self._addresses(template["nodes"])
        string(template["owner"], "template owner")
        if template["source"] is None:
            require(template["kind"] == "declaration" and not template["generated"]
                    and not template["candidates"], "source inventory: invalid installed template")
        else:
            self._span(template["source"])
        parameters = set()
        for binding in sequence(entry["statics"], "static substitutions"):
            require(isinstance(binding, list) and len(binding) == 2,
                    "source inventory: invalid static binding")
            parameter = string(binding[0], "static parameter")
            require(parameter not in parameters, "source inventory: repeated static parameter")
            parameters.add(parameter)
            origin_term(binding[1])
        for symbol in sequence(entry["scoped"], "scoped selections"):
            string(symbol, "scoped symbol")
        fields(entry["layout"], "inputs captures", "instance layout")
        for slots in entry["layout"].values():
            for slot in sequence(slots, "source callable slots"):
                natural(slot, "source callable slot")
        # These typed descriptors are passed intact to later semantic consumers;
        # lookup never interprets their body, bounds, effects or obligations.
        sequence(entry["domains"], "finite domains")
        sequence(entry["oracle_obligations"], "oracle obligations")
        if "oracle_definition" in entry:
            require(isinstance(entry["oracle_definition"], dict), "source inventory: malformed oracle plan")

    def _generated(self, entry):
        fields(entry, "symbol purpose part origins", "generated identity")
        require(entry["purpose"] in ("control", "custody", "finite", "map"),
                "source inventory: unknown generated purpose")
        string(entry["part"], "generated part")
        origins = []
        for origin in sequence(entry["origins"], "generated origins"):
            fields(origin, "definition site", "generated origin")
            key = (string(origin["definition"], "origin definition"), string(origin["site"], "origin site"))
            require(key[0] in self.body_owners, "source inventory: origin outside snapshot bodies")
            origins.append(key)
        # Pure mathematical sites may be absent from the structured snapshot.
        # They are still provenance, never an executable occurrence address.
        require(origins and origins == sorted(set(origins)), "source inventory: invalid origin order")

    def _row_associations(self, rows):
        computed, seen = set(), set()
        for row in sequence(rows, "row associations"):
            fields(row, "row operation derivation original sources", "row association")
            path = tuple(natural(index, "row index") for index in sequence(row["row"], "row path"))
            require(path and path not in seen, "source inventory: repeated or empty row association")
            seen.add(path)
            target = self.snapshot
            for index in path:
                require(isinstance(target, list) and index < len(target), "source inventory: row outside snapshot")
                target = target[index]
            string(row["operation"], "associated operation")
            require(row["derivation"] in ("direct", "scoped_execution", "computation"),
                    "source inventory: unknown row derivation")
            if row["original"] is not None:
                fields(row["original"], "begin end line column", "original range")
                for coordinate in row["original"].values():
                    natural(coordinate, "original coordinate")
                require(row["original"]["begin"] <= row["original"]["end"],
                        "source inventory: reversed original range")
            if row["derivation"] == "computation":
                computed.add(path)
            for source in sequence(row["sources"], "row sources"):
                fields(source, "span candidates", "row source")
                self._span(source["span"])
                self._addresses(source["candidates"], source["span"])
        for table in (4, 7):
            for index, row in enumerate(self.snapshot[table]):
                if table == 4 or row[0] in ("function", "oracle"):
                    require(row[1] in self.identities, "source inventory: definition has no identity")
                else:
                    require(row[0] in ("realize", "finite", "collect", "map") and (table, index) in computed,
                            "source inventory: derived definition lacks computation association")

    def identity(self, symbol):
        require(symbol in self.identities, "source inventory: unknown identity symbol")
        return deepcopy(self.identities[symbol])

    def authored(self, owner, *, statics, scoped, domains):
        """Select an exact closed declaration, never a first same-named match."""
        matches = [identity for identity in self.identities.values()
                   if identity.kind == "instance" and identity.declaration["template"]["kind"] == "declaration"
                   and identity.declaration["template"]["owner"] == owner
                   and identity.declaration["statics"] == statics
                   and identity.declaration["scoped"] == scoped and identity.declaration["domains"] == domains]
        require(len(matches) == 1, "source inventory: missing or ambiguous authored selection")
        return deepcopy(matches[0])

    def row(self, table, index):
        """Classify an exact snapshot row without decoding any printed symbol."""
        require(type(table) is int and table in (4, 5, 6, 7) and type(index) is int
                and 0 <= index < len(self.snapshot[table]), "source inventory: invalid row selection")
        value = self.snapshot[table][index]
        identity = self.identities.get(value[1])
        if identity is not None:
            return deepcopy(identity)
        if table in (5, 6):
            return Identity(value[1], "relation" if table == 5 else "binding", deepcopy(value), ((table, index),))
        require(table == 7 and value[0] in ("realize", "finite", "collect", "map"),
                "source inventory: row has no identity")
        return Identity(value[1], "derived", deepcopy(value), ((table, index),))

    def definition(self, symbol):
        rows = [row for row in self.symbol_rows.get(symbol, []) if row[0] == 7]
        require(len(rows) == 1, "source inventory: missing or ambiguous definition")
        return self.row(*rows[0])

    def single_target(self, symbol, operation, operand=1):
        """One syntactic callee in this exact body, not a dynamic call path."""
        require(symbol in self.definitions, "source inventory: target lookup needs a function")
        def targets(block):
            for descriptor, _, _, regions, _ in block[1]:
                if descriptor[0] == operation:
                    require(len(descriptor) > operand, "source inventory: missing target operand")
                    yield descriptor[operand]
                for region in regions:
                    yield from targets(region[2])
        found = list(targets(self.definitions[symbol][9]))
        require(len(found) == 1, "source inventory: missing or ambiguous instruction target")
        return self.definition(found[0])
