#!/usr/bin/env python3
"""Checks that the label names written in the workflows are the ones the scripts use; no network
calls.

A workflow's `if:` cannot read `scripts/batch-labels.py`, so the workflows name labels themselves,
and a label renamed in one place but not the other would quietly stop a workflow from running.
The names are found with regular expressions over the text, in the places a workflow names a
label: `contains(... labels.*.name, '...')`, `label.name == '...'` (or `!=`) and an `env:` entry
named after a constant of `batch-labels.py`, such as `PRIORITY: priority`.
"""
import importlib.util
from pathlib import Path
import re
import shlex
import unittest

SCRIPTS = Path(__file__).resolve().parents[1]
ROOT = SCRIPTS.parent
WORKFLOWS = ROOT / ".github" / "workflows"


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


labels = load("batch_labels_for_names", "batch-labels.py")
inbox = load("inbox_sync_for_names", "inbox-sync.py")

# The constants of `batch-labels.py` that name labels, by constant: every upper-case string but
# the branch prefix.
CONSTANTS = {name: value for name, value in vars(labels).items()
             if name.isupper() and isinstance(value, str) and name != "PREFIX"}
BATCH_LABELS = set(CONSTANTS.values())
# `env:` names that stand for a constant of another name.
ENV_ALIASES = {"LABEL": "QUEUED"}
# Labels the workflows use that are not batch labels: the inbox's own.
OTHER = {inbox.INBOX}

CONTAINS = re.compile(r"labels\.\*\.name\s*,\s*'([^']*)'")
COMPARED = re.compile(r"label\.name\s*[!=]=\s*'([^']*)'")
ENV = re.compile(r"^\s+([A-Z][A-Z_]*):[ \t]*(.*?)[ \t]*$", re.MULTILINE)
# What `label-pr.yml` sets: a path label for each `flag <name> "$paths"` line, and the size labels
# that its `for label in ...; do` loop goes through.
FLAG = re.compile(r"^\s*flag\s+([\w-]+)\s+\"", re.MULTILINE)
SIZES = re.compile(r"^\s*for label in ((?:'[^'$]+'|[\w-]+)(?:\s+(?:'[^'$]+'|[\w-]+))*); do$", re.MULTILINE)


def label_pr():
    """The labels `label-pr.yml` puts on pull requests."""
    text = (WORKFLOWS / "label-pr.yml").read_text()
    return set(FLAG.findall(text)) | {name for found in SIZES.findall(text) for name in shlex.split(found)}


def named(text):
    """The label names a workflow writes, as [(where, name)]."""
    found = [("contains", name) for name in CONTAINS.findall(text)]
    found += [("label.name", name) for name in COMPARED.findall(text)]
    for key, value in ENV.findall(text):
        constant = ENV_ALIASES.get(key, key)
        if constant in CONSTANTS and not value.startswith("${{"):
            found.append((f"env {key}", value.strip("'\"")))
    return found


class Workflows(unittest.TestCase):
    def test_every_label_a_workflow_names_is_known(self):
        known = BATCH_LABELS | OTHER | label_pr()
        seen = set()
        for path in sorted(WORKFLOWS.glob("*.yml")):
            for where, name in named(path.read_text()):
                seen.add(where.split()[0])
                with self.subTest(workflow=path.name, where=where):
                    self.assertIn(name, known)
        # Each kind of place is found, so that a change in how the workflows are written does not
        # leave this test checking nothing.
        self.assertEqual(seen, {"contains", "label.name", "env"})

    def test_an_env_entry_named_after_a_constant_holds_its_name(self):
        for path in sorted(WORKFLOWS.glob("*.yml")):
            for key, value in ENV.findall(path.read_text()):
                constant = ENV_ALIASES.get(key, key)
                if constant in CONSTANTS and not value.startswith("${{"):
                    with self.subTest(workflow=path.name, key=key):
                        self.assertEqual(value.strip("'\""), CONSTANTS[constant])

    def test_the_inbox_ignores_exactly_the_labels_label_pr_sets(self):
        found = label_pr()
        self.assertTrue(found)
        self.assertEqual(set(inbox.AUTOMATIC), found)


# A later pull request adds `verification/BATCHES.md`, whose "Labels at a glance" table lists the
# labels of `batch-labels.py`, and with it a check here that the table lists exactly those.


if __name__ == "__main__":
    unittest.main()
