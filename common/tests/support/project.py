"""Write small authored project fixtures without a second TOML dependency."""
import json


def project_text(value):
    """Render string/bool/count values and nested tables used by schema controls."""
    lines = []

    def table(mapping, prefix=()):
        for name, item in mapping.items():
            if not isinstance(item, dict):
                lines.append(f'{json.dumps(name)} = {json.dumps(item)}')
        for name, item in mapping.items():
            if isinstance(item, dict):
                path = (*prefix, name)
                lines.extend(['', '[' + '.'.join(json.dumps(part) for part in path) + ']'])
                table(item, path)
    table(value)
    return '\n'.join(lines) + '\n'
