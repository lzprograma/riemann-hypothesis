"""GitHub's API through `gh`, as the workflows that label pull requests use it, in one place.

`batch-queue-sync.py` and `inbox-sync.py` load this file, and load the other files they share
through its `load`. Each keeps a subclass of `GitHub` with what only it needs, such as the GraphQL queries
that read its pull requests.

The workflows' token has an hourly allowance of REST requests, shared with every other workflow
here. GitHub says in each answer how many are left, and a run's log ends with that count. So `call`
remembers how many GitHub says are left, `short` says when that is nearly used up, and
`write` spaces requests that change something a second apart and stops the run when GitHub refuses
one for going too fast. GraphQL has an allowance of its own.
"""
from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time
from urllib.parse import quote

# Stop early when fewer REST requests than this are left for the hour, so other workflows keep
# working.
RESERVE = 150
# Seconds between two requests that change something. GitHub allows no more than 80 requests
# that create content a minute, and asks for a pause of a second between those that change
# anything.
PACE = 1.0


def load(filename):
    """Load another file of this directory as a module, such as `batch-labels.py`. Its name is
    `rh_` and the file's name without `.py`, with `_` for `-`: `rh_batch_labels`. Each call loads
    a fresh copy, and registers it in `sys.modules` under that name.

    The module must be in `sys.modules` while it runs: up to Python 3.14, a dataclass in a file
    with `from __future__ import annotations` looks its module up there, and fails at import
    with `AttributeError: 'NoneType' object has no attribute '__dict__'` if it is missing.
    `tests/test_scripts_start.py` checks that every script that loads files this way starts."""
    path = Path(__file__).with_name(filename)
    name = "rh_" + path.stem.replace("-", "_")
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


class Refused(Exception):
    """GitHub would not do something, or something is wrong with the repository, that the run
    should not paper over. It stops the run, and the next one carries on."""


def quoted(name):
    """A label's name as it goes into a path or a query string."""
    return quote(name, safe="")


class GitHub:
    """The repository through `gh api`. With `dry_run`, writes are printed, not sent.

    `calls` counts REST requests and `queries` GraphQL ones. `remaining` is how many REST requests
    GitHub last said were left this hour, or None before it has said. A script sets `failed` when
    something went wrong that did not stop the run.
    """

    def __init__(self, repo, dry_run=False):
        self.repo, self.dry_run = repo, dry_run
        self.owner, _, self.name = repo.partition("/")
        self.calls, self.queries = 0, 0
        self.remaining, self.changed, self.failed = None, None, False
        # Whether each label looked up exists, by name.
        self.known_labels = {}

    def run(self, args, payload=None):
        data = json.dumps(payload).encode() if payload is not None else None
        return subprocess.run(["gh", "api", *args], input=data, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def call(self, method, path, payload=None):
        """One REST request, to `path` in the repository. Returns (HTTP status, decoded body or
        None). Requests that change something are spaced PACE seconds apart."""
        if method != "GET":
            if self.changed is not None:
                time.sleep(max(0.0, self.changed + PACE - time.monotonic()))
            self.changed = time.monotonic()
        args = ["--include", "--method", method, f"repos/{self.repo}/{path}".rstrip("/")]
        if payload is not None:
            args += ["--input", "-"]
        done = self.run(args, payload)
        self.calls += 1
        head, _, body = done.stdout.decode("utf-8", "replace").replace("\r\n", "\n").partition("\n\n")
        try:
            status = int(head.split()[1])
        except (IndexError, ValueError):
            sys.stderr.write(done.stderr.decode("utf-8", "replace"))
            raise RuntimeError(f"no answer from GitHub for {method} {path}") from None
        for line in head.splitlines()[1:]:
            name, _, value = line.partition(":")
            if name.strip().lower() == "x-ratelimit-remaining" and value.strip().isdigit():
                self.remaining = int(value)
        # An error page that is not JSON still has a status to go by.
        try:
            return status, (json.loads(body) if body.strip() else None)
        except json.JSONDecodeError:
            return status, None

    def get(self, path):
        status, data = self.call("GET", path)
        if status != 200:
            raise RuntimeError(f"GET {path} answered {status}")
        return data

    def pages(self, path):
        """Every item of a paginated list."""
        items, page = [], 1
        while True:
            batch = self.get(f"{path}{'&' if '?' in path else '?'}per_page=100&page={page}")
            items += batch
            if len(batch) < 100:
                return items
            page += 1

    def write(self, method, path, payload=None):
        """A request that changes something. Returns (HTTP status, decoded body or None), or with
        `dry_run` prints the line saying what it would be and returns (0, None): 0 says that
        nothing was sent.

        A refusal for going too fast stops the run: every write after it would be refused too, on
        the allowance the other workflows share. Each script records what it does as it does it,
        so the next run carries on.
        """
        if self.dry_run:
            print(f"would {method} {path} {json.dumps(payload) if payload else ''}".rstrip())
            return 0, None
        status, data = self.call(method, path, payload)
        if status == 429 or (status == 403 and "rate limit" in str((data or {}).get("message", "")).lower()):
            raise Refused(f"GitHub's rate limit refused {method} {path}: the next run carries on.")
        return status, data

    def graphql(self, query, **variables):
        """A GraphQL query's data. An answer with errors, or without data, is an error."""
        done = self.run(["graphql", "--input", "-"], {"query": query, "variables": variables})
        self.queries += 1
        try:
            answer = json.loads(done.stdout)
        except json.JSONDecodeError:
            answer = None
        errors = answer.get("errors") if isinstance(answer, dict) else None
        if not isinstance(answer, dict) or not answer.get("data") or errors or done.returncode != 0:
            sys.stderr.write(done.stderr.decode("utf-8", "replace"))
            raise RuntimeError(f"GraphQL query failed: {json.dumps(errors) if errors else 'no answer'}")
        return answer["data"]

    def short(self):
        """Whether the hour's allowance is nearly used up."""
        return self.remaining is not None and self.remaining < RESERVE

    def label_exists(self, name):
        """Whether the label `name` exists, asked once a run. Adding a label that does not exist
        would create it, and a label renamed on GitHub should be noticed, not started again under
        the old name: the caller decides what a missing one means."""
        if name not in self.known_labels:
            status, _ = self.call("GET", f"labels/{quoted(name)}")
            if status not in (200, 404):
                raise RuntimeError(f"GET labels/{name} answered {status}")
            self.known_labels[name] = status == 200
        return self.known_labels[name]
