"""The labels the batch-queue and inbox workflows give pull requests, and which pull requests hold a
batch, in one place.

`batch-queue-sync.py`, `batch-queue-conflicts.py` and `inbox-sync.py` read the names from here,
and use `holds_batch`.
A workflow's `if:` cannot read this file, so the workflows in `.github/workflows` name some of them
too, in `if:` and `env:`: rename a label there as well, and on GitHub before either change lands.
`tests/test_label_names.py` checks that every label name a workflow writes is one of these or
another label the workflows know.
"""

# Wanted in an upcoming batch: a maintainer commented `batch` on the pull request.
QUEUED = "batch queue"
# A queued pull request that goes into a batch before the others.
PRIORITY = "priority"
# Paused by a maintainer; must not be added to a batch while this label is present.
DEFERRED = "deferred"
# On the pull request of a batch assembled by hand that is being built, and on each open pull
# request whose head commit is in that batch.
BUILDING = "building"
# On the pull request of a batch assembled by hand that is being built and that no other such
# batch is stacked on: the outermost batch of its stack.
LATEST = "latest batch"
# Handed back to the pull request's author.
WAITING = "awaiting-author"

# The start of the name of a branch that holds a batch.
PREFIX = "batch/"


def holds_batch(repo, home, ref):
    """Whether a pull request holds a batch: its head branch `ref` is in `repo`, this repository,
    and its name starts with `batch/`. `home` is the repository the branch is in, as `owner/name`,
    or None when GitHub no longer knows it. A `batch/...` branch of a fork is not a batch: only
    those who can push to this repository can make one. Repository names are compared ignoring
    letter case, as GitHub does."""
    return bool(home) and home.lower() == repo.lower() and ref.startswith(PREFIX)
