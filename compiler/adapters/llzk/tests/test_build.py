#!/usr/bin/env python3
"""Archive and prepared-source custody controls, without invoking a compiler."""

import importlib.util
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest

PATH = Path(__file__).resolve().parents[1] / 'build.py'
SPEC = importlib.util.spec_from_file_location('llzk_build', PATH)
BUILD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BUILD)


class Build(unittest.TestCase):
    def setUp(self):
        workspace = tempfile.TemporaryDirectory(prefix='zkc-llzk-build-')
        self.addCleanup(workspace.cleanup)
        self.root = Path(workspace.name)
        self.work = self.root / 'work'
        self.work.mkdir()
        self.archive = self.root / 'source.tar.gz'
        with tarfile.open(self.archive, 'w:gz') as archive:
            item = tarfile.TarInfo('llzk-lib-test/source.cpp')
            data = b'const int source = 1;\n'
            item.size = len(data)
            archive.addfile(item, io.BytesIO(data))
        self.pins = {'llzk-current': {'revision': 'test', 'sha256': BUILD.digest(self.archive)},
                     'llvm': {'version': '23.1.3'}, 'patches': []}

    def test_reuse_requires_matching_sources_and_pins(self):
        source = BUILD.prepare(self.archive, self.work, self.pins)
        self.assertEqual(BUILD.prepare(self.archive, self.work, self.pins), source)
        changed = json.loads(json.dumps(self.pins))
        changed['llvm']['version'] = 'other'
        with self.assertRaisesRegex(ValueError, 'different pins'):
            BUILD.prepare(self.archive, self.work, changed)
        (source / 'source.cpp').write_text('changed')
        with self.assertRaisesRegex(ValueError, 'source has changed'):
            BUILD.prepare(self.archive, self.work, self.pins)

    def test_rejects_archive_and_patch_digest_changes(self):
        changed = self.pins | {'patches': [{'path': 'toolchain.patch', 'sha256': 'wrong'}]}
        with self.assertRaisesRegex(ValueError, 'patch does not match'):
            BUILD.prepare(self.archive, self.work, changed)
        self.archive.write_bytes(self.archive.read_bytes() + b'changed')
        with self.assertRaisesRegex(ValueError, 'archive does not match'):
            BUILD.prepare(self.archive, self.work, self.pins)
        self.assertFalse((self.work / 'source').exists())

    def test_rejects_unmanifested_source_and_new_links(self):
        source = self.work / 'source'
        source.mkdir()
        with self.assertRaisesRegex(ValueError, 'no manifest'):
            BUILD.prepare(self.archive, self.work, self.pins)
        source.rmdir()
        BUILD.prepare(self.archive, self.work, self.pins)
        (source / 'linked.cpp').symlink_to(source / 'source.cpp')
        with self.assertRaisesRegex(ValueError, 'symbolic link'):
            BUILD.prepare(self.archive, self.work, self.pins)


if __name__ == '__main__':
    unittest.main()
