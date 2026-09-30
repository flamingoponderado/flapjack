"""Regression tests for the shard drift gate, semantic comparison, and cleanup."""

import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPTS = Path(__file__).resolve().parents[1]
LOADER = SCRIPTS / "hol_theorem_map.py"
GATE = SCRIPTS / "check-hol-theorem-map-shards.py"


def _load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


MODULE = _load(LOADER, "hol_theorem_map")


def record(
    lean_path: str,
    lean_name: str,
    hol_path: str | None,
    hol_name: str | None,
    *,
    status: str = "reviewed_exact",
    reviewer: str = "flapjack-ds9 review",
    **extra: object,
) -> dict:
    payload = {
        "hol_path": hol_path,
        "hol_name": hol_name,
        "lean_path": lean_path,
        "lean_name": lean_name,
        "statement_status": status,
        "reviewer": reviewer,
    }
    payload.update(extra)
    return payload


class CompareRecordsTest(unittest.TestCase):
    def test_identical_order_insensitive(self) -> None:
        first = record("Flapjack/A.lean", "aHOL", "cakeml/aScript.sml", "a_def")
        second = record(
            "Flapjack/B.lean",
            "bHOL",
            None,
            None,
            status="no_hol_reference_pending_classification",
        )
        diff = MODULE.compare_records([first, second], [second, first])
        self.assertTrue(diff.ok(), diff.messages())

    def test_detects_each_side_missing_and_changed(self) -> None:
        shared = record("Flapjack/A.lean", "aHOL", "cakeml/aScript.sml", "a_def")
        only_shard = record("Flapjack/C.lean", "cHOL", "cakeml/cScript.sml", "c_def")
        only_mono = record("Flapjack/B.lean", "bHOL", "cakeml/bScript.sml", "b_def")
        changed = record(
            "Flapjack/A.lean", "aHOL", "cakeml/aScript.sml", "a_def", hol_line=7
        )
        diff = MODULE.compare_records([shared, only_shard], [only_mono, changed])
        self.assertEqual(diff.missing_from_shards, ["Flapjack/B.lean:bHOL"])
        self.assertEqual(diff.missing_from_monolith, ["Flapjack/C.lean:cHOL"])
        self.assertEqual(diff.changed, ["Flapjack/A.lean:aHOL"])
        self.assertFalse(diff.ok())

    def test_detects_duplicate_keys_on_each_side(self) -> None:
        item = record("Flapjack/A.lean", "aHOL", "cakeml/aScript.sml", "a_def")
        other = record("Flapjack/A.lean", "aHOL", "cakeml/aScript.sml", "a_def")
        diff = MODULE.compare_records([item, other], [item, other])
        self.assertEqual(diff.duplicates_in_shards, ["Flapjack/A.lean:aHOL"])
        self.assertEqual(diff.duplicates_in_monolith, ["Flapjack/A.lean:aHOL"])
        self.assertFalse(diff.ok())


class StaleShardTest(unittest.TestCase):
    def _seed(self, root: Path) -> list[dict]:
        return [
            record("Flapjack/A.lean", "aHOL", "cakeml/aScript.sml", "a_def"),
            record("Flapjack/B.lean", "bHOL", "cakeml/bScript.sml", "b_def"),
        ]

    def test_write_with_cleanup_removes_stale_leftover(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "shards"
            records = self._seed(root)
            MODULE.write_shards(root, records)
            # Simulate a row moving shards: b now lives under cScript.
            moved = [
                records[0],
                record("Flapjack/B.lean", "bHOL", "cakeml/cScript.sml", "b_def"),
            ]
            MODULE.write_shards(root, moved, cleanup=True)
            self.assertFalse((root / "cakeml/bScript.sml.json").exists())
            self.assertTrue((root / "cakeml/cScript.sml.json").exists())
            self.assertEqual(
                MODULE.check_drift(root, self._monolith(tmp, moved)).ok(),
                True,
            )

    def test_remove_stale_prunes_empty_directories(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "shards"
            MODULE.write_shards(
                root,
                [record("Flapjack/A.lean", "aHOL", None, None,
                        status="no_hol_reference_pending_classification")],
            )
            no_hol = root / "no-hol" / "Flapjack"
            self.assertTrue(no_hol.is_dir())
            removed = MODULE.remove_stale_shards(root, [])
            self.assertIn("no-hol/Flapjack/A.lean.json", removed)
            self.assertFalse(no_hol.exists())

    def test_sync_shards_is_deterministic(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "shards"
            records = self._seed(root)
            MODULE.sync_shards(root, records)
            first = {
                p.relative_to(root).as_posix(): p.read_text(encoding="utf-8")
                for p in MODULE.shard_files(root)
            }
            MODULE.sync_shards(root, records)
            second = {
                p.relative_to(root).as_posix(): p.read_text(encoding="utf-8")
                for p in MODULE.shard_files(root)
            }
            self.assertEqual(first, second)
            self.assertTrue(MODULE.check_drift(root, self._monolith(tmp, records)).ok())

    def test_stale_shard_files_flags_extra_file(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "shards"
            records = self._seed(root)
            MODULE.write_shards(root, records)
            extra = root / "no-hol" / "Flapjack" / "Ghost.lean.json"
            extra.parent.mkdir(parents=True, exist_ok=True)
            extra.write_text(json.dumps(records[:1]), encoding="utf-8")
            self.assertIn(
                "no-hol/Flapjack/Ghost.lean.json",
                MODULE.stale_shard_files(root, records),
            )

    def test_stale_scan_rejects_escaping_symlink(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "shards"
            root.mkdir()
            outside = Path(tmp) / "outside.json"
            outside.write_text("[]", encoding="utf-8")
            (root / "link.json").symlink_to(outside)
            with self.assertRaises(ValueError):
                MODULE.stale_shard_files(root, [])

    def _monolith(self, tmp: str, records: list[dict]) -> Path:
        path = Path(tmp) / "monolith.json"
        path.write_text(
            json.dumps(records, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
        )
        return path


class DriftGateTest(unittest.TestCase):
    def test_repo_shards_match_monolith(self) -> None:
        diff = MODULE.check_drift(MODULE.SHARD_DIR, MODULE.LEGACY_MANIFEST)
        self.assertTrue(diff.ok(), diff.messages())

    def test_gate_cli_passes_on_repo(self) -> None:
        result = subprocess.run(
            [sys.executable, str(GATE)],
            capture_output=True,
            text=True,
            cwd=str(SCRIPTS.parent),
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("match", result.stdout)

    def test_gate_cli_fails_on_perturbed_shard(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            shard_root = Path(tmp) / "shards"
            MODULE.sync_shards(shard_root, MODULE.load_manifest(MODULE.LEGACY_MANIFEST))
            target = sorted(shard_root.rglob("*.json"))[0]
            payload = json.loads(target.read_text(encoding="utf-8"))
            payload[0]["reviewer"] = payload[0]["reviewer"] + " PERTURBED"
            target.write_text(
                json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
                encoding="utf-8",
            )
            result = subprocess.run(
                [sys.executable, str(GATE), "--shard-dir", str(shard_root)],
                capture_output=True,
                text=True,
                cwd=str(SCRIPTS.parent),
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("differs", result.stderr)

    def test_gate_cli_fails_on_stale_shard(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            shard_root = Path(tmp) / "shards"
            MODULE.sync_shards(shard_root, MODULE.load_manifest(MODULE.LEGACY_MANIFEST))
            stale = shard_root / "no-hol" / "Ghost.lean.json"
            stale.parent.mkdir(parents=True, exist_ok=True)
            stale.write_text("[]", encoding="utf-8")
            result = subprocess.run(
                [sys.executable, str(GATE), "--shard-dir", str(shard_root)],
                capture_output=True,
                text=True,
                cwd=str(SCRIPTS.parent),
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("stale/extra shard file", result.stderr)


class CompatWorkflowTest(unittest.TestCase):
    def _seed(self) -> list[dict]:
        return [
            record("Flapjack/A.lean", "aHOL", "cakeml/aScript.sml", "a_def"),
            record("Flapjack/B.lean", "bHOL", "cakeml/bScript.sml", "b_def"),
        ]

    def _run(self, *extra: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            [sys.executable, str(GATE), *extra],
            capture_output=True,
            text=True,
            cwd=str(SCRIPTS.parent),
        )

    def test_sync_compat_generates_view_from_canonical_shards(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            shard_root = Path(tmp) / "shards"
            compat = Path(tmp) / "HOL-THEOREM-MAP.json"
            MODULE.sync_shards(shard_root, self._seed())
            self.assertFalse(compat.exists())
            result = self._run(
                "--shard-dir", str(shard_root), "--manifest", str(compat),
                "--sync-compat",
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue(compat.exists())
            result = self._run("--shard-dir", str(shard_root), "--manifest", str(compat))
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("match", result.stdout)

    def test_gate_fails_when_compat_view_is_mutated(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            shard_root = Path(tmp) / "shards"
            compat = Path(tmp) / "HOL-THEOREM-MAP.json"
            MODULE.sync_shards(shard_root, self._seed())
            result = self._run(
                "--shard-dir", str(shard_root), "--manifest", str(compat),
                "--sync-compat",
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            payload = json.loads(compat.read_text(encoding="utf-8"))
            payload[0]["reviewer"] = payload[0]["reviewer"] + " PERTURBED"
            compat.write_text(
                json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
                encoding="utf-8",
            )
            result = self._run("--shard-dir", str(shard_root), "--manifest", str(compat))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("differs", result.stderr)

    def test_contributor_edit_shard_then_regenerate_compat(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            shard_root = Path(tmp) / "shards"
            compat = Path(tmp) / "HOL-THEOREM-MAP.json"
            MODULE.sync_shards(shard_root, self._seed())
            self.assertEqual(
                self._run(
                    "--shard-dir", str(shard_root), "--manifest", str(compat),
                    "--sync-compat",
                ).returncode,
                0,
            )
            # A contributor edits a canonical shard record.
            target = shard_root / "cakeml" / "aScript.sml.json"
            payload = json.loads(target.read_text(encoding="utf-8"))
            payload[0]["hol_line"] = 42
            target.write_text(
                json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
                encoding="utf-8",
            )
            drift = self._run("--shard-dir", str(shard_root), "--manifest", str(compat))
            self.assertNotEqual(drift.returncode, 0)
            self.assertIn("differs", drift.stderr)
            # Regenerating the compatibility view from the shards clears drift.
            self.assertEqual(
                self._run(
                    "--shard-dir", str(shard_root), "--manifest", str(compat),
                    "--sync-compat",
                ).returncode,
                0,
            )
            self.assertEqual(
                self._run(
                    "--shard-dir", str(shard_root), "--manifest", str(compat)
                ).returncode,
                0,
            )

    def test_skip_compat_checks_only_shard_internals(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            shard_root = Path(tmp) / "shards"
            MODULE.sync_shards(shard_root, self._seed())
            result = self._run("--shard-dir", str(shard_root), "--skip-compat")
            self.assertEqual(result.returncode, 0, result.stderr)
            stale = shard_root / "no-hol" / "Ghost.lean.json"
            stale.parent.mkdir(parents=True, exist_ok=True)
            stale.write_text("[]", encoding="utf-8")
            result = self._run("--shard-dir", str(shard_root), "--skip-compat")
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("stale/extra shard file", result.stderr)


if __name__ == "__main__":
    unittest.main()
