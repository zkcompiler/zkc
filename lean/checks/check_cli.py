#!/usr/bin/env python3
"""Independent CLI controls for retained research tools, without native drivers."""

import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'common/tests/support'))
from journal import Journal  # noqa: E402
from toolchain import reports_root  # noqa: E402


def main():
    output = reports_root() / 'lean/independent-cli'
    journal = Journal(output)
    output.mkdir(parents=True, exist_ok=True)
    for name, exists in [('missing-snapshot', False), ('nonexecutable-snapshot', True)]:
        snapshot = output / name
        if exists:
            snapshot.write_text('not executable')
        result = journal.attempt([sys.executable, ROOT / 'lean/checks/FrontendIdentity.py',
                                  '--baseline', snapshot])
        assert result.returncode == 2
        assert 'explicit baseline is not an executable file' in result.stderr
    binaries = ROOT / 'lean/.lake/build/bin'
    for name in ('table-protocol', 'vector-service', 'table-physical-reference'):
        report = journal.json([binaries / name], refuses=True)
        assert report['status'] == 'refused'
        assert report['code'].startswith(f'usage: {name} '), report
    assert journal.json([binaries / 'requirement-checker'], stdin='[]',
                        refuses='requirements-envelope') == ['refused', 'requirements-envelope']
    rows = journal.run([binaries / 'iteration-reference']).splitlines()
    (output / 'iteration.txt').write_text('\n'.join(rows) + '\n')
    assert len(rows) == 1326
    for row in ('2|2|0|false|pending|2|0,1', '2|3|0|false|returned:2|3|0,1,2',
                '5|8|3|true|reject|4|3'):
        assert row in rows
    for mode in ('whole', 'split'):
        assert f'resume|3|4|1|1|{mode}|pending:1|9|3,2' in rows
        assert f'resume|3|4|2|3|{mode}|returned:10|10|3,2,1,0' in rows
    for mode in ('close-whole', 'close-split'):
        assert f'resume|3|4|1|1|{mode}|exhausted|9|3,2' in rows
        assert f'resume|3|4|2|3|{mode}|returned:10|10|3,2,1,0' in rows
    for reason in ('reject', 'abort', 'exhausted', 'incomplete', 'refused'):
        for mode in ('prefix', 'close'):
            assert f'stop|{reason}|3|{mode}|{reason}|2|0,1' in rows
        assert f'stop|{reason}|1|prefix|pending|1|0' in rows
        assert f'stop|{reason}|1|close|exhausted|1|0' in rows
    report = {'status': 'pass', 'iteration_rows': len(rows), 'commands': journal.save(),
              'scope': 'independent research CLI checks; no current compiler correspondence'}
    journal.write('report.json', report)
    print(json.dumps(report))


if __name__ == '__main__':
    main()
