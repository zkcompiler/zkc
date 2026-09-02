from __future__ import annotations

import io
import json
from pathlib import Path
import sys
import tempfile
import unittest


PACKAGE_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PACKAGE_ROOT))

import run as runner  # noqa: E402


class AnalysisRunnerTelemetryTest(unittest.TestCase):
    def test_result_records_case_and_class_timings(self) -> None:
        class TelemetryFixture(unittest.TestCase):
            def test_pass(self) -> None:
                self.assertEqual(2, 1 + 1)

        suite = unittest.TestSuite((TelemetryFixture("test_pass"),))
        result = unittest.TextTestRunner(
            stream=io.StringIO(),
            verbosity=0,
            resultclass=runner.TimingTextTestResult,
        ).run(suite)

        self.assertTrue(result.wasSuccessful())
        self.assertEqual(len(result.timings), 1)
        self.assertEqual(result.timings[0]["status"], "pass")
        self.assertGreaterEqual(result.timings[0]["elapsed_seconds"], 0.0)
        classes = runner._class_timings(result.timings)
        self.assertEqual(classes[0]["test_count"], 1)
        self.assertEqual(classes[0]["statuses"], {"pass": 1})

    def test_telemetry_writer_produces_machine_readable_json(self) -> None:
        payload = {
            "schema_version": 1,
            "runner": "analysis-semantic-closure",
            "passed": True,
        }
        with tempfile.TemporaryDirectory() as raw_temp:
            path = Path(raw_temp) / "nested" / "telemetry.json"
            runner._write_telemetry(path, payload)
            self.assertEqual(
                json.loads(path.read_text(encoding="utf-8")),
                payload,
            )


if __name__ == "__main__":
    unittest.main()
