#!/usr/bin/env python3
"""Regression tests for import headers and restoring clumped modules."""

import contextlib
import io
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import clump


class ClumpTests(unittest.TestCase):
    def test_trailing_import_comments_remain_in_header(self):
        for modifiers, public, exotic in [
            ("", False, False),
            ("public ", True, False),
            ("private ", False, False),
            ("meta ", False, True),
            ("public meta ", True, True),
        ]:
            for all_modifier in ["", "all "]:
                with self.subTest(modifiers=modifiers, all_modifier=all_modifier):
                    header = (f"module\n\n{modifiers}import {all_modifier}A.B -- unfold π\n"
                              "import Next\n\n")
                    body = "@[expose] public section\ntheorem sample : True := trivial\n"
                    mod = clump.Module("Lemmata.A", "src/Lemmata/A.lean", header + body)
                    self.assertEqual(mod.imports, [("A.B", public), ("Next", False)])
                    self.assertEqual(mod.exotic, exotic or bool(all_modifier))
                    self.assertEqual(mod.header, header)
                    self.assertEqual(mod.body, body)

    def test_standalone_import_comments_remain_in_header(self):
        for modifier, exotic in [("public ", False), ("meta ", True)]:
            with self.subTest(modifier=modifier):
                header = ("-- module comment\nmodule\n\n-- dependency π\n"
                          f"{modifier}import Core\n  -- another dependency\nimport Next\n\n")
                body = "@[expose] public section\ntheorem sample : True := trivial\n"
                mod = clump.Module("Lemmata.A", "src/Lemmata/A.lean", header + body)
                self.assertEqual(mod.imports, [("Core", modifier == "public "), ("Next", False)])
                self.assertEqual(mod.exotic, exotic)
                self.assertEqual(mod.header, header)
                self.assertEqual(mod.body, body)

    def test_comments_after_the_last_import_stay_in_the_body(self):
        header = "module\n\n-- dependency\nimport Core\n\n"
        body = "-- about the first declaration\ntheorem sample : True := trivial\n"
        mod = clump.Module("Lemmata.A", "src/Lemmata/A.lean", header + body)
        self.assertEqual((mod.header, mod.body), (header, body))

    def test_comment_glued_to_an_import(self):
        mod = clump.Module("Lemmata.A", "src/Lemmata/A.lean", "module\nimport A.B--note\n\ndef a := 1\n")
        self.assertEqual(mod.imports, [("A.B", False)])

    def test_clump_records_are_not_part_of_the_header(self):
        """A caller's header is rebuilt from its imports by collapse_wrappers.py, so a clump
        file's marker and first member records must be in its body, or `unclump` skips it."""
        with tempfile.TemporaryDirectory() as root:
            root = Path(root)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            texts = {
                "L.A": "module\n\npublic import Mathlib.Init\n\ndef a := 1\n",
                "L.R": "module\n\npublic import L.A\n\ndef r := a\n",
            }
            for name, text in texts.items():
                path = root / "src" / (name.replace(".", "/") + ".lean")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text, encoding="utf-8")
            subprocess.run(["git", "-C", str(root), "add", "-A"], check=True)
            with contextlib.redirect_stdout(io.StringIO()):
                clump.apply(str(root), {"L.R": ["L.A", "L.R"]})
            text = (root / "src/L/R.lean").read_text(encoding="utf-8")
            mod = clump.Module("L.R", "src/L/R.lean", text)
            self.assertEqual(mod.header, "module\n\npublic import Mathlib.Init\n\n")
            self.assertTrue(mod.body.startswith(clump.CLUMP_MARK))
            self.assertEqual(mod.body.count(clump.SEAM_BEGIN), 2)
            self.assertEqual(mod.header + mod.body, text)

    def test_commented_import_all_still_prevents_clumping(self):
        texts = {
            "Lemmata.A": "module\nimport all External -- unfold a definition\n\ndef a := 1\n",
            "Lemmata.Root": "module\npublic import Lemmata.A\n\ndef root := a\n",
        }
        mods = {n: clump.Module(n, "src/" + n.replace(".", "/") + ".lean", text)
                for n, text in texts.items()}
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(clump.plan(mods, 2000), {})

    def test_unclump_recreates_absorbed_directories_byte_for_byte(self):
        with tempfile.TemporaryDirectory() as root:
            root = Path(root)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            originals = {
                "src/Lemmata/Only/Leaf.lean":
                    "module\n-- external dependency\npublic import Core\n\n"
                    "@[expose] public section\n-- π\ntheorem leaf : True := trivial",
                "src/Lemmata/Root.lean":
                    "module\npublic import Lemmata.Only.Leaf\n\n"
                    "@[expose] public section\ntheorem root : True := leaf\n",
            }
            for path, text in originals.items():
                (root / path).parent.mkdir(parents=True, exist_ok=True)
                (root / path).write_bytes(text.encode())
            subprocess.run(["git", "-C", str(root), "add", "src"], check=True)
            with contextlib.redirect_stderr(io.StringIO()):
                plan = clump.plan(clump.load(root), 2000)
            self.assertEqual(plan, {"Lemmata.Root": ["Lemmata.Only.Leaf", "Lemmata.Root"]})
            clump.apply(root, plan)
            combined = (root / "src/Lemmata/Root.lean").read_text()
            header, members = combined.split(clump.SEAM_BEGIN, 1)
            self.assertIn("public import Core\n", header)
            self.assertNotIn("\npublic import Core\n", members)
            self.assertTrue(clump.is_clump_file(
                clump.Module("Lemmata.Root", "src/Lemmata/Root.lean", combined)))
            # Git does not preserve the empty directory in a fresh checkout.
            (root / "src/Lemmata/Only").rmdir()
            with contextlib.redirect_stdout(io.StringIO()):
                clump.unclump(root)
            for path, text in originals.items():
                self.assertEqual((root / path).read_bytes(), text.encode())


if __name__ == "__main__":
    unittest.main()
