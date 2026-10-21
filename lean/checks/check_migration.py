"""Compare selected stored Lean declarations under explicit migration maps."""

import argparse
import json
from pathlib import Path
import sys
import subprocess

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support.migration import capture_records, compare, read_records  # noqa: E402


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--before', action='append', type=Path)
    parser.add_argument('--after', action='append', type=Path)
    parser.add_argument('--capture-from', type=Path, help='existing Lake package; performs no build')
    parser.add_argument('--capture-modules', type=Path, help='JSON list of exact modules to capture independently')
    parser.add_argument('--modules', type=Path, help='JSON object mapping old modules to destination lists')
    parser.add_argument('--declarations', type=Path,
                        help='JSON list of {before: [module, encoded name], after: [module, encoded name]}; '
                             'only selected stored identities may be mapped')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.capture_from is not None or args.capture_modules is not None:
            if (args.capture_from is None or args.capture_modules is None or
                args.before or args.after or args.modules or args.declarations):
                raise ValueError('capture requires --capture-from and --capture-modules without comparison arguments')
            count = capture_records(args.capture_from, json.loads(args.capture_modules.read_text()), args.output)
            print(f'captured {count} declarations in isolated owning-module environments')
            return 0
        if not args.before or not args.after:
            raise ValueError('comparison requires --before and --after')
        modules = json.loads(args.modules.read_text()) if args.modules else {}
        declarations = json.loads(args.declarations.read_text()) if args.declarations else []
        result = compare(read_records(args.before), read_records(args.after), modules, declarations)
    except (OSError, ValueError, TypeError, KeyError, IndexError, subprocess.CalledProcessError) as error:
        parser.exit(2, f'migration records refused: {error}\n')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(f"{result['status']}: {result['preserved_declarations']}/{result['baseline_declarations']} "
          f"declarations; {len(result['changes'])} changes; {len(result['missing_modules'])} missing modules")
    return 0 if result['status'] == 'preserved' else 1


if __name__ == '__main__':
    raise SystemExit(main())
