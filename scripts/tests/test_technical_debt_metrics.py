#!/usr/bin/env python3
"""Technical debt counts on a throwaway git repository."""
import importlib.util
import os
from pathlib import Path
import subprocess
import tempfile
import time
import unittest
from unittest import mock

SCRIPT = Path(__file__).resolve().parents[1] / "technical-debt-metrics.py"
spec = importlib.util.spec_from_file_location("technical_debt_metrics", SCRIPT)
debt = importlib.util.module_from_spec(spec)
spec.loader.exec_module(debt)
STRONG, WEAK = debt.STRONG, debt.WEAK

BEFORE = """\
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem a : True := by erw [foo]; trivial
-- a removed comment that mentions erw [h]
set_option maxHeartbeats 400000 in
open Fin.NatCast Fin.CommRing in
theorem b : True := trivial
"""
AFTER = """\
set_option backward.isDefEq.respectTransparency.types false in
theorem a : True := by rw [foo]; trivial
set_option maxHeartbeats 400000 in
set_option linter.unusedSectionVars false in
set_option linter.overlappingInstances false
open scoped Fin.NatCast in
attribute [-instance] Foo.bar
local elab "exact_by_kernel " t:term : tactic => pure ()
theorem b : True := by run_tac pure (); dsimp +instances; trivial
"""


class CountLine(unittest.TestCase):
    def test_each_counter(self):
        def keys(line):
            return set(debt.count_line(line))
        self.assertEqual(keys("  erw [h]"), {(STRONG, "`erw`")})
        self.assertEqual(keys("  rw [h]"), set())
        self.assertEqual(keys("set_option synthInstance.maxHeartbeats 80000 in"),
                         {(STRONG, "`maxHeartbeats` modifications")})
        self.assertEqual(keys("set_option backward.isDefEq.respectTransparency false in"),
                         {(STRONG, "`backward.isDefEq.respectTransparency`")})
        self.assertEqual(keys("set_option linter.unusedVariables true"), set())
        self.assertEqual(keys("set_option linter.unusedVariables false in"),
                         {(WEAK, "disabled `linter.unusedVariables`")})
        self.assertEqual(keys("set_option linter.unusedSectionVars false in"),
                         {(STRONG, "disabled `linter.unusedSectionVars`")})
        self.assertEqual(keys("open Fin.NatCast Fin.CommRing in"),
                         {(STRONG, "`NatCast (Fin n)` instances"),
                          (STRONG, "`CommRing (Fin n)` instances")})
        self.assertEqual(keys("open Fin.NatCast.foo in"), set())
        self.assertEqual(keys("  simp +instances"), set())
        self.assertEqual(keys("  dsimp -zeta +instances [h]"), {(WEAK, "`dsimp +instances`")})
        self.assertEqual(keys("elab_rules : tactic"), {(STRONG, "tactics defined with `elab`")})
        self.assertEqual(keys("elab \"foo\" : term => bar"), set())

    def test_no_catastrophic_backtracking(self):
        start = time.monotonic()
        self.assertEqual(debt.count_line("dsimp " + "+" * 5000 + " instances"), [])
        self.assertLess(time.monotonic() - start, 1)


class Repository(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.cwd = os.getcwd()
        os.chdir(self.tmp.name)
        self.addCleanup(os.chdir, self.cwd)
        self.git("init", "-q")
        self.base = self.commit(BEFORE)
        self.head = self.commit(AFTER)

    def git(self, *args):
        return subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", *args],
                              check=True, capture_output=True, text=True).stdout.strip()

    def commit(self, text):
        Path("src").mkdir(exist_ok=True)
        Path("src/A.lean").write_text(text)
        Path("README.md").write_text(text)  # outside src/, so never counted
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "x")
        return self.git("rev-parse", "HEAD")

    def totals(self, commit):
        empty_tree = self.git("hash-object", "-t", "tree", "/dev/null")
        return debt.count_diff(empty_tree, commit)[0]

    def test_change_matches_totals(self):
        before, after = self.totals(self.base), self.totals(self.head)
        expected = {key: after[key] - before[key] for key in before.keys() | after.keys()}
        self.assertEqual(debt.change(self.base, self.head),
                         {key: n for key, n in expected.items() if n})
        self.assertEqual(before[STRONG, "`maxHeartbeats` modifications"], 1)

    def test_pr_summary(self):
        output = Path("output")
        with mock.patch.dict(os.environ, {"GITHUB_OUTPUT": str(output)}):
            summary = debt.pr_summary(self.base, self.head)
            unchanged = debt.pr_summary(self.head, self.head)
        self.assertIn("Changes to strong tech debt", summary)
        self.assertIn("|-2|`erw`|", summary)
        self.assertIn("|+1|disabled `linter.unusedSectionVars`|", summary)
        self.assertIn("Increase in weak tech debt", summary)
        self.assertIn("No changes to strong technical debt.", unchanged)
        self.assertEqual(output.read_text(), "changed=true\nchanged=false\n")


if __name__ == "__main__":
    unittest.main()
