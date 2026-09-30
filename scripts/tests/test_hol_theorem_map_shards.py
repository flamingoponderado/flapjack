"""Regression tests for the sharded HOL-theorem-map loader and writer."""

import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "hol_theorem_map.py"
SPEC = importlib.util.spec_from_file_location("hol_theorem_map", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules["hol_theorem_map"] = MODULE
SPEC.loader.exec_module(MODULE)


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


class ShardPathTest(unittest.TestCase):
    def test_hol_script_backed_record_uses_hol_path(self) -> None:
        item = record(
            "Flapjack/Pancake/PanLang.lean",
            "shapeToStringHOL",
            "cakeml/pancake/panLangScript.sml",
            "shape_to_str_def",
        )
        self.assertEqual(
            MODULE.shard_relpath(item),
            "cakeml/pancake/panLangScript.sml.json",
        )

    def test_null_hol_path_groups_under_no_hol(self) -> None:
        item = record(
            "Flapjack/Pancake/Proofs/PanSimp.lean",
            "panSimpHOL",
            None,
            None,
            status="no_hol_reference_pending_classification",
        )
        self.assertEqual(
            MODULE.shard_relpath(item),
            "no-hol/Flapjack/Pancake/Proofs/PanSimp.lean.json",
        )


class LoadManifestTest(unittest.TestCase):
    def test_directory_and_legacy_file_load_equivalently(self) -> None:
        records = [
            record(
                "Flapjack/A.lean",
                "aHOL",
                "cakeml/pancake/aScript.sml",
                "a_def",
            ),
            record(
                "Flapjack/B.lean",
                "bHOL",
                None,
                None,
                status="no_hol_reference_pending_classification",
            ),
        ]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            MODULE.write_shards(root / "shards", records)
            legacy = root / "legacy.json"
            legacy.write_text(
                json.dumps(records, indent=2, ensure_ascii=False) + "\n",
                encoding="utf-8",
            )
            from_dir = MODULE.load_manifest(root / "shards")
            from_file = MODULE.load_manifest(legacy)
        self.assertEqual(from_dir, from_file)
        self.assertEqual(len(from_dir), 2)

    def test_load_rejects_non_array_legacy_root(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "bad.json"
            path.write_text("{}", encoding="utf-8")
            with self.assertRaises(ValueError):
                MODULE.load_manifest(path)

    def test_load_rejects_duplicate_keys_across_shards(self) -> None:
        first = record(
            "Flapjack/A.lean", "aHOL", "cakeml/pancake/aScript.sml", "a_def"
        )
        duplicate = record(
            "Flapjack/A.lean", "aHOL", "cakeml/pancake/bScript.sml", "b_def"
        )
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "one.json").write_text(
                json.dumps([first]), encoding="utf-8"
            )
            (root / "two.json").write_text(
                json.dumps([duplicate]), encoding="utf-8"
            )
            with self.assertRaisesRegex(ValueError, "duplicate manifest entry"):
                MODULE.load_manifest(root)


class ValidationTest(unittest.TestCase):
    def test_requires_every_required_field(self) -> None:
        item = record("Flapjack/A.lean", "aHOL", None, None)
        del item["reviewer"]
        with self.assertRaisesRegex(ValueError, "missing fields"):
            MODULE.validate_records([item])

    def test_rejects_unknown_field(self) -> None:
        item = record("Flapjack/A.lean", "aHOL", None, None)
        item["typo_field"] = True
        with self.assertRaisesRegex(ValueError, "unknown fields"):
            MODULE.validate_records([item])

    def test_rejects_invalid_status(self) -> None:
        item = record(
            "Flapjack/A.lean", "aHOL", None, None, status="reviewed_maybe"
        )
        with self.assertRaisesRegex(ValueError, "invalid statement_status"):
            MODULE.validate_records([item])

    def test_rejects_empty_reviewer(self) -> None:
        item = record("Flapjack/A.lean", "aHOL", None, None, reviewer="  ")
        with self.assertRaisesRegex(ValueError, "reviewer metadata is required"):
            MODULE.validate_records([item])

    def test_rejects_non_bool_words_flag(self) -> None:
        item = record(
            "Flapjack/A.lean",
            "aHOL",
            None,
            None,
            words_as_type_indexed_bitvec="yes",
        )
        with self.assertRaisesRegex(ValueError, "must be a bool"):
            MODULE.validate_records([item])

    def test_allows_null_hol_fields_for_no_hol_entries(self) -> None:
        item = record(
            "Flapjack/A.lean",
            "aHOL",
            None,
            None,
            status="no_hol_reference_pending_classification",
        )
        self.assertEqual(MODULE.validate_records([item]), [item])


class RenderTest(unittest.TestCase):
    def test_render_is_deterministic_and_sorted(self) -> None:
        records = [
            record(
                "Flapjack/B.lean",
                "bHOL",
                "cakeml/pancake/aScript.sml",
                "z_def",
            ),
            record(
                "Flapjack/A.lean",
                "aHOL",
                "cakeml/pancake/aScript.sml",
                "a_def",
            ),
        ]
        rendered = MODULE.render_shards(records)
        self.assertEqual(list(rendered), ["cakeml/pancake/aScript.sml.json"])
        payload = json.loads(rendered["cakeml/pancake/aScript.sml.json"])
        self.assertEqual([item["hol_name"] for item in payload], ["a_def", "z_def"])
        self.assertEqual(MODULE.render_shards(records), rendered)

    def test_canonical_record_order_is_fixed(self) -> None:
        item = record(
            "Flapjack/A.lean",
            "aHOL",
            "cakeml/pancake/aScript.sml",
            "a_def",
            words_as_type_indexed_bitvec=True,
        )
        shuffled = {key: item[key] for key in reversed(list(item))}
        self.assertEqual(
            list(MODULE.canonical_record(shuffled)),
            list(MODULE.canonical_record(item)),
        )
        self.assertEqual(list(MODULE.canonical_record(item))[-1], "reviewer")

    def test_write_and_reload_round_trips(self) -> None:
        records = [
            record(
                "Flapjack/A.lean",
                "aHOL",
                "cakeml/pancake/aScript.sml",
                "a_def",
                fmap_as_finite_support=["globals"],
                hol_line=12,
            ),
            record(
                "Flapjack/B.lean",
                "bHOL",
                None,
                None,
                status="documented_mismatch",
            ),
        ]
        with tempfile.TemporaryDirectory() as tmp:
            written = MODULE.write_shards(tmp, records)
            reloaded = MODULE.load_manifest(tmp)
        self.assertEqual(
            written,
            [
                "cakeml/pancake/aScript.sml.json",
                "no-hol/Flapjack/B.lean.json",
            ],
        )
        self.assertEqual(
            [item["lean_name"] for item in reloaded], ["bHOL", "aHOL"]
        )


class CompatViewTest(unittest.TestCase):
    def _records(self) -> list[dict]:
        return [
            record(
                "Flapjack/B.lean",
                "bHOL",
                "cakeml/pancake/aScript.sml",
                "z_def",
                status="reviewed_words_as_type_indexed_bitvec",
                words_as_type_indexed_bitvec=True,
            ),
            record(
                "Flapjack/A.lean",
                "aHOL",
                "cakeml/pancake/aScript.sml",
                "a_def",
                words_as_type_indexed_bitvec=True,
            ),
            record(
                "Flapjack/C.lean",
                "cHOL",
                None,
                None,
                status="documented_mismatch",
            ),
        ]

    def test_render_compat_is_deterministic_and_order_insensitive(self) -> None:
        records = self._records()
        first = MODULE.render_compat(records)
        self.assertEqual(MODULE.render_compat(records), first)
        self.assertEqual(MODULE.render_compat(list(reversed(records))), first)
        payload = json.loads(first)
        self.assertEqual(len(payload), 3)
        self.assertTrue(first.endswith("\n"))

    def test_write_compat_round_trips_all_records(self) -> None:
        records = self._records()
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "HOL-THEOREM-MAP.json"
            MODULE.write_compat(path, records)
            first = path.read_bytes()
            MODULE.write_compat(path, list(reversed(records)))
            self.assertEqual(path.read_bytes(), first)
            reloaded = MODULE.load_manifest(path)
        self.assertEqual(
            {item["lean_name"] for item in reloaded},
            {item["lean_name"] for item in records},
        )
        self.assertEqual(
            {item["statement_status"] for item in reloaded},
            {"reviewed_exact", "reviewed_words_as_type_indexed_bitvec", "documented_mismatch"},
        )


class PathSafetyTest(unittest.TestCase):
    def test_rejects_absolute_hol_path(self) -> None:
        item = record("Flapjack/A.lean", "aHOL", "/etc/passwd", "x")
        with self.assertRaises(ValueError):
            MODULE.shard_relpath(item)

    def test_rejects_traversal_hol_path(self) -> None:
        item = record("Flapjack/A.lean", "aHOL", "../../etc/passwd", "x")
        with self.assertRaises(ValueError):
            MODULE.shard_relpath(item)

    def test_rejects_backslash_hol_path(self) -> None:
        item = record("Flapjack/A.lean", "aHOL", "cakeml\\x.sml", "x")
        with self.assertRaises(ValueError):
            MODULE.shard_relpath(item)

    def test_rejects_traversal_lean_path_for_no_hol_record(self) -> None:
        item = record(
            "../Flapjack/A.lean",
            "aHOL",
            None,
            None,
            status="no_hol_reference_pending_classification",
        )
        with self.assertRaises(ValueError):
            MODULE.shard_relpath(item)

    def test_write_shards_rejects_before_creating_any_file(self) -> None:
        unsafe = record("Flapjack/A.lean", "aHOL", "/etc/passwd", "x")
        duplicate = record("Flapjack/A.lean", "aHOL", "cakeml/a.sml", "x")
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "shards"
            with self.assertRaises(ValueError):
                MODULE.write_shards(root, [unsafe])
            self.assertFalse(root.exists())
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "shards"
            with self.assertRaises(ValueError):
                MODULE.write_shards(root, [duplicate, duplicate])
            self.assertFalse(root.exists())

    def test_valid_statuses_extracted_without_executing_checker(self) -> None:
        self.assertIn("reviewed_exact", MODULE.VALID_STATUSES)
        self.assertIn(
            "no_hol_reference_pending_classification", MODULE.VALID_STATUSES
        )
        # The checker is parsed, not executed (no circular runpy import).
        self.assertFalse(hasattr(MODULE, "runpy"))
        self.assertFalse(hasattr(MODULE, "_STATUS_MODULE"))

    def test_write_shards_rejects_escaping_symlink_and_writes_nothing(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "shards"
            root.mkdir()
            outside = Path(tmp) / "outside"
            outside.mkdir()
            (root / "cakeml").symlink_to(outside, target_is_directory=True)
            item = record("Flapjack/A.lean", "aHOL", "cakeml/aScript.sml", "a_def")
            with self.assertRaises(ValueError):
                MODULE.write_shards(root, [item])
            self.assertEqual(list(outside.iterdir()), [])

    def test_write_shards_rejects_escaping_file_symlink(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "shards"
            (root / "cakeml").mkdir(parents=True)
            outside = Path(tmp) / "outside.json"
            outside.write_text("ORIGINAL", encoding="utf-8")
            (root / "cakeml" / "aScript.sml.json").symlink_to(outside)
            item = record("Flapjack/A.lean", "aHOL", "cakeml/aScript.sml", "a_def")
            with self.assertRaises(ValueError):
                MODULE.write_shards(root, [item])
            self.assertEqual(outside.read_text(encoding="utf-8"), "ORIGINAL")

    def test_write_compat_rejects_escaping_symlink(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            parent = Path(tmp) / "docs"
            parent.mkdir()
            outside = Path(tmp) / "outside.json"
            outside.write_text("[]", encoding="utf-8")
            link = parent / "HOL-THEOREM-MAP.json"
            link.symlink_to(outside)
            item = record("Flapjack/A.lean", "aHOL", "cakeml/aScript.sml", "a_def")
            with self.assertRaises(ValueError):
                MODULE.write_compat(link, [item])
            self.assertEqual(outside.read_text(encoding="utf-8"), "[]")


if __name__ == "__main__":
    unittest.main()
