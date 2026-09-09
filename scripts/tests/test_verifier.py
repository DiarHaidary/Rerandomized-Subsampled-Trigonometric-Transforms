"""Regression checks for the verifier's rejection paths and clean source copy."""
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
from sandbox_preflight import preflight
from validate_comparator import validate
from verify_comparator import fresh_source


class VerifierTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name) / "package"
        self.root.mkdir()
        original = SCRIPTS.parent
        for name in ("comparator.json", "Challenge.lean", "Solution.lean", "lean-toolchain", "lake-manifest.json", "lakefile.lean"):
            shutil.copyfile(original / name, self.root / name)
        (self.root / "scripts").mkdir()
        shutil.copyfile(SCRIPTS / "tool-pins.json", self.root / "scripts/tool-pins.json")

    def tearDown(self):
        self.temporary.cleanup()

    def mutate_config(self, change):
        path = self.root / "comparator.json"
        value = json.loads(path.read_text())
        change(value)
        path.write_text(json.dumps(value))

    def test_valid_imported_theorems_need_no_local_solution_stubs(self):
        (self.root / "Solution.lean").write_text("import SRHT.Main\n")
        self.assertEqual(validate(self.root)["status"], "passed")

    def test_reject_disabled_nanoda(self):
        self.mutate_config(lambda x: x.update(enable_nanoda=False))
        with self.assertRaisesRegex(ValueError, "NanoDa"):
            validate(self.root)

    def test_reject_additional_axiom(self):
        self.mutate_config(lambda x: x["permitted_axioms"].append("sorryAx"))
        with self.assertRaisesRegex(ValueError, "standard axioms"):
            validate(self.root)

    def test_reject_unknown_keys(self):
        self.mutate_config(lambda x: x.update(external_kernels={}))
        with self.assertRaisesRegex(ValueError, "unknown"):
            validate(self.root)

    def test_reject_missing_target(self):
        self.mutate_config(lambda x: x["theorem_names"].pop())
        with self.assertRaisesRegex(ValueError, "target"):
            validate(self.root)

    def test_reject_fake_mathlib_prefix(self):
        with (self.root / "Challenge.lean").open("a") as out:
            out.write("\nimport Mathlibrary.Untrusted\n")
        with self.assertRaisesRegex(ValueError, "Mathlib modules"):
            validate(self.root)

    def test_reject_unpinned_dependency(self):
        path = self.root / "lake-manifest.json"
        manifest = json.loads(path.read_text())
        manifest["packages"][0]["rev"] = "main"
        path.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, "Unpinned dependency"):
            validate(self.root)

    def test_windows_is_fail_closed(self):
        with patch("sandbox_preflight.platform.system", return_value="Windows"):
            result = preflight(self.root)
        self.assertEqual(result["status"], "blocked")
        self.assertIn("native Windows", result["failures"][0])

    def test_snapshot_excludes_cached_oleans(self):
        (self.root / "SRHT").mkdir()
        (self.root / "SRHT/Example.lean").write_text("example : True := True.intro\n")
        (self.root / "SRHT/Example.olean").write_bytes(b"precompiled")
        (self.root / "vendor/sparse-fock/SparseFockFormal").mkdir(parents=True)
        (self.root / "vendor/sparse-fock/SparseFockFormal/Example.lean").write_text("example : True := True.intro\n")
        (self.root / ".lake").mkdir()
        (self.root / ".lake/Solution.olean").write_bytes(b"precompiled")
        work = Path(self.temporary.name) / "work"
        work.mkdir()
        source, hashes = fresh_source(self.root, work)
        self.assertFalse((source / ".lake").exists())
        self.assertFalse(list(source.rglob("*.olean")))
        self.assertIn("SRHT/Example.lean", hashes)
        self.assertIn("vendor/sparse-fock/SparseFockFormal/Example.lean", hashes)
        self.assertIn("lakefile.lean", hashes)

    def test_reject_ambiguous_lakefiles(self):
        (self.root / "lakefile.toml").write_text('name = "wrong"\n')
        with self.assertRaisesRegex(ValueError, "Exactly one"):
            validate(self.root)


if __name__ == "__main__":
    unittest.main()
