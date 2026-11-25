#!/usr/bin/env python3
"""Checks that every script that loads `github-rest.py` starts: `--help` exits cleanly. No network
calls.

The scripts load each other's files at startup (see `load` in `github-rest.py`), so a mistake there
stops a script before it reads its arguments, and only on some Python versions: a module missing
from `sys.modules` breaks a dataclass under `from __future__ import annotations` up to Python 3.14
but not on 3.15. The workflows run on `ubuntu-26.04`, whose `python3` is 3.14, so besides the
interpreter running the tests, each script is started with the interpreters in `OTHER_PYTHONS`
that exist on the machine, and one that doesn't is skipped.

The scripts are found by looking for `github-rest.py` in their text, so a new one is checked without
being listed here.
"""
from pathlib import Path
import subprocess
import sys
import unittest

SCRIPTS = Path(__file__).resolve().parents[1]
# Further interpreters to start the scripts with, besides the one running the tests, where they
# exist: on a runner `/usr/bin/python3` is the system's 3.14, and on a Mac these are Homebrew's
# 3.14 and the system's older Python.
OTHER_PYTHONS = ["/opt/homebrew/bin/python3.14", "/usr/bin/python3"]


def scripts():
    """The scripts that load `github-rest.py`, by file name."""
    return sorted(path for path in SCRIPTS.glob("*.py")
                  if path.name != "github-rest.py" and "github-rest.py" in path.read_text())


class ScriptsStart(unittest.TestCase):
    def test_scripts_are_found(self):
        names = {path.name for path in scripts()}
        self.assertIn("batch-queue-sync.py", names)
        self.assertIn("inbox-sync.py", names)

    def check(self, python):
        for script in scripts():
            with self.subTest(python=python, script=script.name):
                run = subprocess.run([python, str(script), "--help"], capture_output=True,
                                     text=True, timeout=60)
                self.assertEqual(run.returncode, 0, run.stderr)
                self.assertIn("usage:", run.stdout)

    def test_with_this_python(self):
        self.check(sys.executable)

    def test_with_other_pythons(self):
        for python in OTHER_PYTHONS:
            with self.subTest(python=python):
                if not Path(python).exists():
                    self.skipTest(python + " is not installed")
                self.check(python)


if __name__ == "__main__":
    unittest.main()
