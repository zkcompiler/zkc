"""Compare exact declaration records across an explicitly mapped module move.

A difference is never approved because both axiom sets are on an allowlist, or
because a theorem's statement hash stayed equal. Intentional changes remain
review findings for a separately checked correspondence and review receipt.
"""

from dataclasses import dataclass
from functools import lru_cache
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

FORMAT = 'zkc.migration-declarations/0'
NAME_ENCODING = 'lean-name-components/0'
AXIOM_PROVENANCE = 'owning-module-environment/0'
FIELDS = {'name', 'display_name', 'module', 'kind', 'universes', 'type', 'body', 'shape', 'axioms',
          'type_dependencies', 'body_dependencies'}
SEMANTIC_FIELDS = ('kind', 'universes', 'type', 'body', 'shape', 'axioms')
HEADER_FIELDS = {'format', 'name_encoding', 'axiom_provenance', 'modules', 'declarations'}


def record_header(modules, count):
    return {'format': FORMAT, 'name_encoding': NAME_ENCODING,
            'axiom_provenance': AXIOM_PROVENANCE, 'modules': modules, 'declarations': count}


def read_header(stream):
    try:
        header = json.loads(next(stream))
    except StopIteration as error:
        raise ValueError('empty declaration record') from error
    if (not isinstance(header, dict) or set(header) != HEADER_FIELDS or header['format'] != FORMAT or
        header['name_encoding'] != NAME_ENCODING or header['axiom_provenance'] != AXIOM_PROVENANCE):
        raise ValueError('invalid declaration record header; regenerate using the current exporter')
    selected, count = header['modules'], header['declarations']
    if (not isinstance(selected, list) or not selected or
        any(not isinstance(m, str) or not m for m in selected) or len(set(selected)) != len(selected)):
        raise ValueError('invalid or duplicate module selection')
    if type(count) is not int or count < 0:
        raise ValueError('invalid declaration count')
    return selected, count


def capture_records(package, modules, output):
    """Capture each owning module in a fresh Lean process, using existing oleans.

    Loaded Lean extensions may retain imported regions. Process isolation bounds
    their lifetime and keeps both axiom lookup and its cache module-specific.
    Publish the combined file only after every selected module has succeeded.
    """
    if (not isinstance(modules, list) or not modules or
        any(not isinstance(m, str) or not m for m in modules) or len(set(modules)) != len(modules)):
        raise ValueError('capture requires nonempty, unique module names')
    package, output = Path(package).resolve(), Path(output).resolve()
    emitter = Path(__file__).resolve().parents[1] / 'checks/MigrationRecords.lean'
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='migration-capture-', dir=output.parent) as temporary:
        temporary = Path(temporary)
        total = 0
        with (temporary / 'rows').open('w') as combined:
            for module in sorted(modules):
                path = temporary / 'module.jsonl'
                path.unlink(missing_ok=True)
                subprocess.run(['lake', 'env', 'lean', '--run', str(emitter), str(path), module],
                               cwd=package, env=os.environ | {'LEAN_NUM_THREADS': os.environ.get('LEAN_NUM_THREADS', '2')},
                               stdin=subprocess.DEVNULL, check=True)
                # Validate coverage and all identities before combining records.
                with path.open() as stream:
                    selected, count = read_header(stream)
                    if selected != [module]: raise ValueError('exporter selected the wrong module')
                    seen = set()
                    for line in stream:
                        row = json.loads(line)
                        validate_row(row, selected)
                        if row['name'] in seen: raise ValueError('duplicate stored declaration')
                        seen.add(row['name'])
                        combined.write(line)
                    if len(seen) != count: raise ValueError('declaration count mismatch')
                    total += count
        if not total: raise ValueError('selected modules own no stored declarations')
        with (temporary / 'complete.jsonl').open('w') as complete:
            complete.write(json.dumps(record_header(sorted(modules), total)) + '\n')
            with (temporary / 'rows').open() as rows:
                while chunk := rows.read(1024 * 1024): complete.write(chunk)
        (temporary / 'complete.jsonl').replace(output)
    return total


def name_key(components):
    """Encode explicit kernel components; strings and natural numbers are distinct.

    The anonymous root is the empty list. Never split a display name to recover
    identity: quoted strings, embedded dots and numeric components are ambiguous.
    """
    if not isinstance(components, list) or any(
        not isinstance(part, list) or len(part) != 2 or
        not ((part[0] == 'str' and isinstance(part[1], str)) or
             (part[0] == 'num' and type(part[1]) is int and part[1] >= 0))
        for part in components
    ):
        raise ValueError('invalid kernel name components')
    def string(value):
        # Match Lean.Json.compress, which uses \u0009/\u0008/\u000c
        # rather than Python's short escapes for tab/backspace/formfeed.
        escaped = []
        for char in value:
            if 0xD800 <= ord(char) <= 0xDFFF:
                raise ValueError('kernel names require Unicode scalar values')
            escaped.append({'"': '\\"', '\\': '\\\\', '\n': '\\n', '\r': '\\r'}.get(
                char, f'\\u{ord(char):04x}' if ord(char) < 32 else char))
        return '"' + ''.join(escaped) + '"'

    return '[' + ','.join('[' + string(tag) + ',' +
                          (string(value) if tag == 'str' else str(value)) + ']'
                          for tag, value in components) + ']'


def validate_name(value):
    if not isinstance(value, str):
        raise ValueError('invalid or noncanonical encoded kernel name')
    _validate_name_key(value)


@lru_cache(maxsize=65536)
def _validate_name_key(value):
    if name_key(json.loads(value)) != value:
        raise ValueError('invalid or noncanonical encoded kernel name')


def validate_row(row, selected):
    if (not isinstance(row, dict) or set(row) != FIELDS or row['module'] not in selected or
        not isinstance(row['display_name'], str)):
        raise ValueError('invalid or unselected declaration')
    validate_semantics(row)


def validate_semantics(row):
    """Validate every name position, including references outside selected modules."""
    def names(values):
        if not isinstance(values, list):
            raise ValueError('expected encoded name list')
        for value in values:
            validate_name(value)

    def tree(value):
        if not isinstance(value, list) or not value or not isinstance(value[0], str):
            raise ValueError('invalid semantic expression')
        tag, *args = value
        if tag in ('constant', 'projection', 'parameter', 'free', 'metavariable'):
            if not args: raise ValueError('missing semantic name')
            validate_name(args[0])
        if tag == 'constant' and len(args) == 2 and isinstance(args[1], list):
            for u in args[1]: tree(u)
        elif tag == 'projection' and len(args) == 3 and type(args[1]) is int and args[1] >= 0:
            tree(args[2])
        elif tag in ('parameter', 'free', 'metavariable') and len(args) == 1:
            pass
        elif tag in ('sort', 'succ') and len(args) == 1:
            tree(args[0])
        elif tag in ('application', 'max', 'imax') and len(args) == 2:
            for item in args: tree(item)
        elif tag in ('lambda', 'forall') and len(args) == 3 and args[0] in (
            'explicit', 'implicit', 'strict-implicit', 'instance'
        ):
            tree(args[1]); tree(args[2])
        elif tag == 'let' and len(args) == 4 and type(args[3]) is bool:
            for item in args[:3]: tree(item)
        elif tag in ('natural', 'bound', 'regular') and len(args) == 1 and type(args[0]) is int and args[0] >= 0:
            pass
        elif tag == 'string' and len(args) == 1 and isinstance(args[0], str):
            pass
        elif tag in ('zero', 'opaque', 'abbreviation') and not args:
            pass
        else:
            raise ValueError('unknown or malformed semantic expression')

    validate_name(row['name'])
    for field in ('universes', 'axioms', 'type_dependencies', 'body_dependencies'):
        names(row[field])
        if len(set(row[field])) != len(row[field]):
            raise ValueError(f'duplicate name in {field}')
    tree(row['type'])
    if row['body'] is not None: tree(row['body'])
    shape = row['shape']
    fields = {
        'inductive': {'parameters', 'indices', 'mutual', 'constructors', 'nested', 'recursive', 'unsafe', 'reflexive'},
        'constructor': {'inductive', 'index', 'parameters', 'fields', 'unsafe'},
        'recursor': {'mutual', 'parameters', 'indices', 'motives', 'minors', 'k', 'unsafe', 'rules'},
        'definition': {'safety', 'hints'}, 'opaque': {'unsafe'}, 'axiom': {'unsafe'},
        'theorem': None, 'quotient': None,
    }
    if row['kind'] not in fields or (fields[row['kind']] is None and shape is not None):
        raise ValueError('invalid declaration kind or shape')
    if fields[row['kind']] is not None:
        if not isinstance(shape, dict) or set(shape) != fields[row['kind']]:
            raise ValueError('invalid declaration shape fields')
        for key in ('mutual', 'constructors'):
            if key in shape: names(shape[key])
        if 'inductive' in shape: validate_name(shape['inductive'])
        if 'hints' in shape: tree(shape['hints'])
        for key in ('parameters', 'indices', 'nested', 'index', 'fields', 'motives', 'minors'):
            if key in shape and (type(shape[key]) is not int or shape[key] < 0):
                raise ValueError('invalid declaration shape count')
        for key in ('recursive', 'unsafe', 'reflexive', 'k'):
            if key in shape and type(shape[key]) is not bool:
                raise ValueError('invalid declaration shape flag')
        if 'safety' in shape and shape['safety'] not in (
            'Lean.DefinitionSafety.safe', 'Lean.DefinitionSafety.unsafe', 'Lean.DefinitionSafety.partial'
        ):
            raise ValueError('invalid declaration safety')
        if 'rules' in shape:
            if not isinstance(shape['rules'], list): raise ValueError('invalid recursor rules')
            for rule in shape['rules']:
                if not isinstance(rule, dict) or set(rule) != {'constructor', 'fields', 'rhs'}:
                    raise ValueError('invalid recursor rule')
                if type(rule['fields']) is not int or rule['fields'] < 0:
                    raise ValueError('invalid recursor field count')
                validate_name(rule['constructor']); tree(rule['rhs'])


def canonical(record, renames=None):
    """Alpha-normalize bound universes and apply an explicit declaration bijection.

    Only semantic name positions are rewritten. A string literal or an unknown
    universe is never renamed merely because its bytes match a declaration.
    """
    renames = {} if renames is None else renames
    parameters = {name: index for index, name in enumerate(record['universes'])}
    if len(parameters) != len(record['universes']):
        raise ValueError('duplicate universe binder')

    def expression(value):
        if not isinstance(value, list) or not value:
            return value
        tag = value[0]
        if tag == 'parameter' and len(value) == 2:
            return ['parameter-index', parameters[value[1]]] if value[1] in parameters else value
        if tag == 'constant' and len(value) == 3:
            return [tag, renames.get(value[1], value[1]), [expression(u) for u in value[2]]]
        if tag == 'projection' and len(value) == 4:
            return [tag, renames.get(value[1], value[1]), value[2], expression(value[3])]
        if tag in ('string', 'natural', 'bound', 'free', 'metavariable'):
            return value
        return [expression(item) for item in value]

    def shape(value):
        if value is None:
            return None
        result = dict(value)
        for key in ('inductive',):
            if key in result:
                result[key] = renames.get(result[key], result[key])
        for key in ('mutual', 'constructors'):
            if key in result:
                result[key] = [renames.get(name, name) for name in result[key]]
        if 'rules' in result:
            result['rules'] = [rule | {
                'constructor': renames.get(rule['constructor'], rule['constructor']),
                'rhs': expression(rule['rhs']),
            } for rule in result['rules']]
        return result

    return {'kind': record['kind'], 'universes': list(range(len(parameters))),
            'type': expression(record['type']), 'body': expression(record['body']),
            'shape': shape(record['shape']),
            'axioms': sorted(renames.get(name, name) for name in record['axioms'])}


def fingerprint(record, renames=None):
    return hashlib.sha256(json.dumps(canonical(record, renames), sort_keys=True,
                                     separators=(',', ':')).encode()).hexdigest()


@dataclass
class Records:
    modules: set[str]
    declarations: dict[tuple[str, str], dict]


def read_records(paths):
    modules, declarations = set(), {}
    for path in paths:
        with Path(path).open() as stream:
            selected, count = read_header(stream)
            if modules.intersection(selected):
                raise ValueError(f'{path}: duplicate module selection')
            found = 0
            for line in stream:
                row = json.loads(line)
                validate_row(row, selected)
                key = row['module'], row['name']
                if key in declarations:
                    raise ValueError(f'{path}: duplicate stored declaration {key}')
                declarations[key] = row
                found += 1
            if found != count:
                raise ValueError(f'{path}: declaration count mismatch')
            modules.update(selected)
    if not modules or not declarations:
        raise ValueError('no declaration records selected')
    return Records(modules, declarations)


def compare(before, after, moves=None, renames=None):
    """Map old modules to their exact allowed destination modules, including splits.

    Declaration renames require an explicit injective map whose sources and
    destinations occur in the selected records. No rename is inferred from a
    similar suffix. All references and definition bodies must still agree.
    """
    moves = {} if moves is None else moves
    renames = {} if renames is None else renames
    if not isinstance(moves, dict) or not isinstance(renames, dict):
        raise ValueError('migration maps must be JSON objects')
    for source, destination in renames.items():
        validate_name(source); validate_name(destination)
    before_names = {name for _, name in before.declarations}
    after_names = {name for _, name in after.declarations}
    if set(renames) - before_names or set(renames.values()) - after_names:
        raise ValueError('rename map names an unselected declaration')
    effective = [renames.get(name, name) for name in before_names]
    if len(set(effective)) != len(effective):
        raise ValueError('declaration rename map is not injective')
    if set(moves) - before.modules:
        raise ValueError('move map names an unselected baseline module')
    targets = {module: moves.get(module, [module]) for module in before.modules}
    if any(not isinstance(destinations, list) or not destinations or
           any(not isinstance(name, str) or not name for name in destinations) or
           len(set(destinations)) != len(destinations)
           for destinations in targets.values()):
        raise ValueError('every module needs explicit, nonempty, unique destinations')
    required = {module for destinations in targets.values() for module in destinations}
    missing_modules = sorted(required - after.modules)
    changes, seen = [], set()
    preserved = 0
    for (module, name), old in sorted(before.declarations.items()):
        renamed = renames.get(name, name)
        candidates = [(destination, renamed) for destination in targets[module]
                      if (destination, renamed) in after.declarations]
        if not candidates:
            changes.append({'module': module, 'name': name, 'display_name': old['display_name'], 'status': 'missing',
                            'expected_modules': targets[module], 'before': fingerprint(old, renames)})
            continue
        seen.update(candidates)
        exact = [key for key in candidates if fingerprint(old, renames) == fingerprint(after.declarations[key])]
        if exact and len(exact) == len(candidates):
            preserved += 1
            continue
        for key in candidates:
            current = after.declarations[key]
            previous, following = canonical(old, renames), canonical(current)
            fields = [field for field in SEMANTIC_FIELDS if previous[field] != following[field]]
            if fields:
                changes.append({'module': module, 'name': name, 'display_name': old['display_name'], 'status': 'changed',
                                'destination': key[0], 'fields': fields,
                                'before': fingerprint(old, renames), 'after': fingerprint(current)})
    return {'format': 'zkc.migration-comparison/0',
            'status': 'preserved' if not changes and not missing_modules else 'review-required',
            'baseline_declarations': len(before.declarations), 'preserved_declarations': preserved,
            'missing_modules': missing_modules, 'changes': changes,
            'declaration_renames': dict(sorted(renames.items())),
            'normalization': 'bound-universe alpha-equivalence and explicit declaration renaming only',
            'added_declarations': [{'module': module, 'name': name,
                                    'display_name': after.declarations[(module, name)]['display_name']}
                                   for module, name in sorted(set(after.declarations) - seen)],
            'meaning': 'exact selected types, definitions, universes, shapes and axiom sets; '
                       'intentional changes require separate checked correspondence and review; '
                       'new declarations remain subject to the ordinary dependency and axiom audit'}
