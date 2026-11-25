#!/usr/bin/env python3
"""Keep the labels of the batch queue in step with the batches being built.

The batch-queue workflow runs this from its trusted checkout. Everything goes through GitHub's
API: GitHub performs the merges, and nothing from a pull request is checked out or run here.

The batch queue is a list of approvals, and maintainers assemble batches from it by hand. This
script assembles no batch of its own: the code that does is kept, switched off by `ASSEMBLE`, in
case we want a batch assembled by the queue again, and the comment there says what that needs.
What follows about the batch being assembled, the order queued commits go in and the note in its
pull request describes that code as it works with `ASSEMBLE` on. With it off, a branch this
script started is removed once its pull request is merged or closed, as before, and one without a
pull request, such as `batch/2026-11-24-142233`, is left alone.

Which commit goes into a batch. A maintainer queues one commit of a pull request by commenting
`batch`: the commit that was its head when the comment was posted, or one named in the comment.
The workflow's label job records that commit in a comment of its own, and it is the only one a
batch takes. The `batch queue` label alone queues nothing, and commits pushed afterwards wait
for another `batch`.

A batch is a branch of this repository that this script started, normally with an open pull
request. Its name is `batch/` and the time it was started, such as `batch/2026-11-23-041230`,
with `-2` and so on after it when that name was taken. Other `batch/...` branches of this
repository, such as one a maintainer assembled by hand, are batches assembled by hand: nothing
is merged into them, their pull requests' text is left alone, and they are never deleted.

The batch being assembled takes each queued commit for as long as its pull request is open, and
a pull request that GitHub cannot merge into it is told so in a comment. Once the batch's pull
request is merged or closed, its branch is removed. What it contained and is still open stays
queued, and the next run starts a new batch with it.

Queued commits are merged in pull request number order, except that those of pull requests
labelled `priority` go first: when one of them and another pull request cannot both be merged,
the other one is left out. The order counts when a batch is started or rebuilt. After that, a
newly queued commit is merged on top of what is already there, and one that was left out stays
out until the batch is rebuilt or a new commit of it is queued, labelled `priority` or not.

A batch assembled by hand is being built for as long as its pull request is open and its branch
holds the head commit of an open pull request, and this script labels its pull request
`building` to say so. One that is labelled `batch queue` itself waits in the queue like any
other pull request instead.

Batches assembled by hand can be stacked: the branch of the upper batch merges the branch of the
one it is stacked on, so it holds that batch's commits too, and it is to be merged right after
it. A batch says which batch it is stacked on with a line of its description such as

    - [ ] depends on: #1739

the same `depends on` line any pull request uses (read by `pr-dependencies.py`), ticked or not.
Until its description has one that names an open batch that is being built, its branch name is
read instead: `batch/<anything>-on-<number>`, such as `batch/b11-on-1739`, is stacked on that
number if it is such a batch. A batch can be stacked on more than one. Batches that say they are
stacked on each other in a circle are taken to be stacked on none. Only git checks the claim:
when a batch's branch shares no commit beyond main with the branch of a batch it says it is
stacked on, the run warns about it. Batches whose branches are at the same commit contain the
same pull requests, so whatever they say about each other, each is taken to be stacked on the one
with the next lower number: the lowest holds what they contain, and the highest is the
outermost. The run warns about them every time it sees them.

What a batch contains of its own is every open pull request whose head commit is in its branch,
queued or not, into main or into another branch, unless a batch it is stacked on, directly or
not, contains it: a pull request belongs to the lowest batch of a stack that holds it. A pull
request that holds a batch is never part of another batch. Everything a batch contains is
labelled `building`, in place of `batch queue` for those that had it, whichever batch of a stack
it is in. This script records what each batch contains of its own in a comment of its own on the
batch's pull request, and looks through the branch again when its head moves, or when a batch
under it moves or the batches under it change. A pull request that has left the branch by then
loses `building` unless another batch holds it, and so does everything in it once the batch is
merged or closed. Those that had `batch queue` before get it back, unless the batch was merged.

The outermost batch of each stack, the one that no other open batch assembled by hand is stacked
on, is labelled `latest batch` as well. A batch that is stacked on nothing and has nothing
stacked on it is a stack of its own. The label comes off when another batch is stacked on it, or
when it is merged or closed.

When the batch underneath is merged, GitHub marks what it contained as merged, and the batch on
top simply stops being stacked on it. When it is closed without being merged, the batch on top is
told so once, in a comment: its branch still carries the commits of the closed batch, so the open
pull requests among them are now its own and stay `building`, and whoever assembles it should
rebuild it on main or on another batch and change its `depends on` line or branch name to match.

The batch being assembled is built on top of the batch assembled by hand labelled `latest batch`,
when exactly one into main is: its branch starts at that batch's head, and its pull request is
to be merged after that batch's. When the batch underneath moves on, its new head is merged in.
When it is rebuilt, closed without being merged, or replaced by another, the batch being
assembled is rebuilt as well: its branch is reset to the new base, or to main, and every queued
commit is merged in again. Once the batch underneath has landed on main there is nothing to do.

A batch assembled by hand that was merged or closed is found by its pull request, which keeps
`building` until this script has tidied up after it. Its branch may already have been deleted by
then.

Taking a pull request out of the queue never changes a batch. Commits already merged into one
stay there, and the batch's description says so. No batch is rebuilt for that.

A pull request that is closed, whether merged or not, loses `batch queue` and `building`: it is
neither waiting for a build nor in one any more. The pull request of a batch assembled by hand
is the exception, because it keeps `building` until it has been tidied up after. When a pull
request is reopened, `batch queue` comes back if this workflow was the last to take a label off,
and the pull request was not taken out of the queue with `-batch` meanwhile. A label a person
took off stays off.

The workflow's token has an hourly allowance of requests, shared with every other workflow here
(see `github-rest.py`). A note in each batch pull request's text therefore remembers what was merged and which pull
requests were already looked at. The note is a cache: it is used only while the batch's head
and each pull request's update time are what they were, and everything in it can be read again
from the branch and the comments.
"""
from __future__ import annotations

import argparse
import datetime
import importlib.util
import json
from pathlib import Path
import re
import sys

_REST_SPEC = importlib.util.spec_from_file_location("rh_github_rest", Path(__file__).with_name("github-rest.py"))
_rest = importlib.util.module_from_spec(_REST_SPEC)
_REST_SPEC.loader.exec_module(_rest)
_labels = _rest.load("batch-labels.py")
_deps = _rest.load("pr-dependencies.py")

QUEUED, BUILDING, LATEST = _labels.QUEUED, _labels.BUILDING, _labels.LATEST
# A maintainer's label: pull requests that carry it go into a batch before the others.
PRIORITY = _labels.PRIORITY
PREFIX = _labels.PREFIX
# The name `start` gives a batch branch. Any other `batch/...` branch is not this script's.
OWN_BATCH = re.compile(r"batch/[0-9]{4}-[0-9]{2}-[0-9]{2}-[0-9]{6}(?:-[0-9]+)?")
# The name of a batch assembled by hand that says which batch it is stacked on, such as
# `batch/b11-on-1739`, when its description does not say so in a `depends on` line.
ON_BATCH = re.compile(r"batch/.+-on-([0-9]+)")
BOT = "github-actions[bot]"
# Stop early when fewer requests than this are left for the hour (see `github-rest.py`).
RESERVE = _rest.RESERVE
# What was read from a pull request is remembered only once the pull request has been quiet for
# this long. GitHub's update times are whole seconds, so two changes in one second look like one.
SETTLE = datetime.timedelta(seconds=120)

# Whether the sync assembles a batch of its own from the queue: starts a `batch/<date-time>`
# branch, merges each queued commit into it, opens and describes its pull request, and rebuilds it
# on top of a batch assembled by hand (`start`, `recall`, `restack`, `publish` and the end of
# `sync`). It does not: the queue is a list of approvals, which maintainers assemble batches from
# by hand. The code is kept, and tested with this on, in case we want a batch assembled by the
# queue again. Running it taught us what that needs:
#
# - GitHub Actions may not create pull requests in this repository. That is a repository setting:
#   Settings > Actions > General > "Allow GitHub Actions to create and approve pull requests". So
#   the queue's branch `batch/2026-11-24-142233` never got a pull request, and every sync run
#   ended in `Refused` at `publish`: the job failed, its summary showed only the refusal, and
#   anything that runs after `publish` would not run. Run 45503694341 shows it.
# - The batches maintainers assemble by hand already take every open pull request that is not a
#   draft, touches `src/` and merges cleanly, queued or not, so a second batch assembled from the
#   queue largely builds them again.
# - Batches assembled by hand are stacked: #1739 (`batch/b10b-on-1410`) is built on #1410, and
#   takes each new head of #1410 while #1410 is being repaired. A batch of the queue would have
#   to go on the outermost of them and be rebuilt whenever a batch below it moves. `restack`
#   now follows the batch labelled `latest batch` when a single one into main is, and goes back
#   to main when there are more.
# - Requests: a sync run that assembled cost about 300 REST requests. Run 45503694341 ended with
#   "304 requests to GitHub; 4721 left this hour".
#
# To revive it: allow GitHub Actions to create pull requests, check that going on the
# `latest batch` is still what we want, and set this back to True.
ASSEMBLE = False

# Comments the workflow's label job leaves when a maintainer queues or unqueues a pull request.
# They count only at the very start of a comment written by the workflow itself.
APPROVED = re.compile(r"<!-- batch-queue-approved ([0-9a-f]{40}) -->")
WITHDRAWN = "<!-- batch-queue-withdrawn -->"
# Comments this script leaves on a pull request, each once.
REFUSAL = "<!-- batch-queue-refused {branch} {sha} -->"
REFUSAL_ON = "<!-- batch-queue-refused {branch} {sha} on #{base} -->"
MOVED = "<!-- batch-queue-moved {sha} -->"
STAYS = "<!-- batch-queue-stays {branch} -->"
# On a batch assembled by hand, when a batch it is stacked on is closed without being merged.
STRANDED = "<!-- batch-queue-stranded {number} -->"
# The comment on a batch assembled by hand that records what it contains.
BY_HAND = re.compile(r"<!-- batch-queue-by-hand (\{.*\}) -->")
# In a batch pull request's text: the part this script writes, and its note to itself.
BODY = "<!-- batch-queue -->"
STATE = re.compile(r"<!-- batch-queue-state (\{.*\}) -->")
# The merge commit that adds a pull request to a batch, and the one that brings the batch
# underneath up to date.
ADDED = re.compile(r"Add #(\d+) to the batch\n\nMerged at ([0-9a-f]{40})\.")
UPDATED = "Bring #{number} up to date\n\nMerged at {sha}."


Refused = _rest.Refused
quoted = _rest.quoted


class GitHub(_rest.GitHub):
    """The repository's REST API through `gh` (see `github-rest.py`), with a clock that the tests
    can set."""

    def __init__(self, repo, dry_run=False):
        super().__init__(repo, dry_run)
        # Lines saying which label changes GitHub refused (see `relabel`).
        self.refused = []

    def now(self):
        return datetime.datetime.now(datetime.timezone.utc)


def open_pulls(gh):
    """Every open pull request, by number. Two requests cover a couple of hundred of them."""
    found = {}
    for info in gh.pages("pulls?state=open"):
        found[info["number"]] = {
            "number": info["number"], "sha": info["head"]["sha"], "ref": info["head"]["ref"],
            "batch": holds_batch(gh, info), "base": info["base"]["ref"],
            "labels": {label["name"] for label in info["labels"]},
            "updated": info["updated_at"], "body": info.get("body") or ""}
    return found


def holds_batch(gh, info):
    """Whether a pull request, as GitHub's REST API gives it, holds a batch (see `batch-labels.py`)."""
    head = info["head"]
    return _labels.holds_batch(gh.repo, (head.get("repo") or {}).get("full_name"), head["ref"])


def own_batch(ref):
    """Whether a branch name is one `start` gives a batch."""
    return OWN_BATCH.fullmatch(ref) is not None


def is_batch(pr):
    """Whether a pull request holds a batch that `start` began."""
    return pr["batch"] and own_batch(pr["ref"])


def by_hand(pr):
    """Whether a pull request holds a batch assembled by hand: a `batch/...` branch of this
    repository under another name than the ones `start` gives."""
    return pr["batch"] and not own_batch(pr["ref"])


def relabel(gh, pr_or_number, add=None, remove=None):
    """Change labels on GitHub, and on our own copy of the pull request when we hold one.

    Returns whether GitHub took every change. A change it refused, other than for the rate limit,
    which stops the run, is added to `gh.refused`: the run's log ends with those lines, since the
    line its caller logs says the label changed.
    """
    number = pr_or_number["number"] if isinstance(pr_or_number, dict) else pr_or_number
    done = True
    if add:
        status = gh.write("POST", f"issues/{number}/labels", {"labels": [add]})[0]
        if status not in (0, 200):
            gh.refused.append(f"#{number}: GitHub answered {status} to adding `{add}`, so it was not added")
            done, add = False, None
    if remove:
        # A label that is not there any more answers 404, which is what was wanted.
        status = gh.write("DELETE", f"issues/{number}/labels/{quoted(remove)}")[0]
        if status not in (0, 200, 404):
            gh.refused.append(f"#{number}: GitHub answered {status} to removing `{remove}`, so it is still on")
            done, remove = False, None
    if isinstance(pr_or_number, dict):
        pr_or_number["labels"] = (pr_or_number["labels"] | ({add} if add else set())) - {remove}
    return done


def by_workflow(comment):
    return (comment.get("user") or {}).get("login") == BOT


def look(gh, pr, seen):
    """What a maintainer queued on a pull request: (commit or None, its comments or None).

    The comments are read only if the pull request has changed since it was last looked at.
    When it has not, the earlier answer stands, there is nothing new to say to it, and None is
    returned in place of the comments.
    """
    key = str(pr["number"])
    if key in seen and seen[key][0] == pr["updated"]:
        return seen[key][1] or None, None
    comments = gh.pages(f"issues/{pr['number']}/comments")
    sha = None
    for comment in comments:
        body = comment.get("body") or ""
        if not by_workflow(comment):
            continue
        match = APPROVED.match(body)
        if match:
            sha = match.group(1)
        elif body.startswith(WITHDRAWN):
            sha = None
    if settled(gh, pr["updated"]):
        seen[key] = [pr["updated"], sha or ""]
    else:
        seen.pop(key, None)
    return sha, comments


def settled(gh, updated):
    """Whether a pull request has been left alone long enough for its update time to be trusted."""
    try:
        when = datetime.datetime.strptime(updated, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=datetime.timezone.utc)
    except (TypeError, ValueError):
        return False
    return gh.now() - when >= SETTLE


def tell(gh, number, comments, marker, text):
    """Leave a comment on a pull request, unless the workflow has left that one before."""
    if comments is None:
        comments = gh.pages(f"issues/{number}/comments")
    if any(marker in (comment.get("body") or "") for comment in comments if by_workflow(comment)):
        return False
    gh.write("POST", f"issues/{number}/comments", {"body": f"{marker}\n{text}\n"})
    return True


# ---------------------------------------------------------------------------------------------
# Batches.


def batches(gh, pulls):
    """The batches that can still be merged, as {ref, sha, number, body}, and the batch branches
    left behind by a pull request that was merged or closed, as {ref, sha, pull}, with that pull
    request as GitHub gives it.

    `number` is None for a branch whose pull request has not been opened yet. A `batch/...`
    branch under any other name than the ones `start` gives is not looked at.
    """
    owner = gh.repo.split("/")[0]
    live = {pr["ref"]: pr for pr in pulls.values() if is_batch(pr)}
    found, leftover = [], []
    for ref in gh.get(f"git/matching-refs/heads/{PREFIX}"):
        name = ref["ref"][len("refs/heads/"):]
        if not own_batch(name):
            continue
        batch = {"ref": name, "sha": ref["object"]["sha"], "number": None, "body": ""}
        if name in live:
            pr = live[name]
            batch.update(number=pr["number"], body=pr["body"])
        else:
            closed = gh.get(f"pulls?state=all&head={owner}:{name}")
            if closed:
                leftover.append({"ref": name, "sha": batch["sha"], "pull": closed[0]})
                continue
        found.append(batch)
    return found, leftover


def finished(gh, closed_building, known):
    """Batches assembled by hand that were merged or closed and not yet tidied up after, with a
    `fate`, the pull requests they contained as `members`, {number: commit}, those of them that
    were labelled `batch queue` before as `queued`, and their own `labels`.

    They are found by their pull requests, which keep `building` until `finish` is done with
    them. That works whether or not someone has already deleted the branch. `closed_building`
    is every closed issue or pull request that still carries `building`.

    Telling a batch assembled by hand from any other pull request takes a request, so `known`,
    the pull requests some open batch is known to contain, are not asked about. Neither is what
    a batch just found contained, and the newest are looked at first, because a batch is opened
    after what it contains.
    """
    found, known = [], set(known)
    for item in sorted(closed_building, key=lambda item: -item["number"]):
        if "pull_request" not in item or str(item["number"]) in known:
            continue
        info = gh.get(f"pulls/{item['number']}")
        if not holds_batch(gh, info) or own_batch(info["head"]["ref"]):
            continue
        note = read_record(gh, info["number"])[1]
        batch = {"number": info["number"], "fate": "merged" if info.get("merged") else "closed",
                 "members": members(note), "queued": queued_before(note),
                 "labels": {label["name"] for label in info["labels"]}}
        known |= set(batch["members"])
        found.append(batch)
    return found


def added(gh, batch, main_sha, stop=None, limit=400):
    """What this workflow merged into a batch, as {number: commit}, read from the branch itself.

    Follows first parents from the batch's head back to main, or to `stop`, the commit the
    branch was started from when it was started on top of another batch: the walk would
    otherwise go on through every commit of that one. Commits a maintainer pushed on top are
    stepped over.
    """
    merged, sha = {}, batch["sha"]
    for _ in range(limit):
        if sha == stop:
            break
        commit = gh.get(f"git/commits/{sha}")
        match = ADDED.match(commit["message"])
        if match and len(commit["parents"]) == 2:
            merged.setdefault(match.group(1), match.group(2))
        elif not commit["parents"] or gh.get(f"compare/{main_sha}...{sha}?per_page=1")["ahead_by"] == 0:
            break
        sha = commit["parents"][0]["sha"]
    return merged


def recall(gh, batch, main_sha, under=None):
    """What is known about a batch: {"merged": {number: commit}, "refused": {...}, "seen": {...},
    "base": ...}.

    `merged` and `refused` come from the note in the pull request's text when the note was
    written for the batch's present head. Otherwise `merged` is read again from the branch.
    `base` is the batch it is built on, as {number, sha, start}: the head of that batch it was
    last brought up to date with, and the commit its own branch was started from. It is None
    for a batch built on main. Without a note, as while the batch has no pull request, the walk
    back through the branch stops at `under` instead, the head of the batch it should be built
    on, in case it was started there.
    """
    state = {"merged": {}, "refused": {}, "seen": {}, "base": None}
    match = STATE.search(batch["body"])
    try:
        note = json.loads(match.group(1)) if match else {}
    except ValueError:
        note = {}
    if isinstance(note.get("seen"), dict):
        state["seen"] = note["seen"]
    if isinstance(note.get("base"), dict):
        state["base"] = note["base"]
    if note.get("head") == batch["sha"] and isinstance(note.get("merged"), dict):
        state["merged"], state["refused"] = note["merged"], dict(note.get("refused") or {})
    else:
        state["merged"] = added(gh, batch, main_sha, (state["base"] or {}).get("start") or under)
    return state


def describe(batch, state, members, also=(), refused=(), unapproved=(), stack=()):
    """The text of a batch pull request. `stack` is what to say about the batch it is built on."""
    lines = [BODY, "The batch-queue workflow assembles this pull request. When a maintainer comments "
             "`batch` on a pull request, the commit that was its head at that moment is merged in here."]
    if stack:
        lines += [""] + list(stack)
    lines += ["", "In this batch:", ""]
    lines += [f"- #{number} at `{sha[:10]}`" for number, sha in members] or ["- nothing yet"]
    if also:
        lines += ["", "Also in this branch:", ""] + [f"- #{number}, {why}" for number, why in also]
    if refused:
        lines += ["", "Left out, because GitHub could not merge them into this branch: "
                  + ", ".join(f"#{number}" for number in refused) + "."]
    if unapproved:
        lines += ["", f"Labelled `{QUEUED}` but not queued, because no maintainer has commented `batch` on them: "
                  + ", ".join(f"#{number}" for number in unapproved) + "."]
    lines += ["", "Merge this with a merge commit, not a squash, so that GitHub marks the pull "
              "requests above as merged."]
    note = {"head": batch["sha"], "merged": state["merged"], "refused": state["refused"], "seen": state["seen"]}
    if state.get("base"):
        note["base"] = state["base"]
    lines += ["", f"<!-- batch-queue-state {json.dumps(note, sort_keys=True)} -->"]
    return "\n".join(lines) + "\n"


def publish(gh, batch, main, text):
    """Open the batch's pull request if it has none, and bring its text up to date."""
    if batch["number"]:
        if text != batch["body"]:
            gh.write("PATCH", f"pulls/{batch['number']}", {"body": text})
        return
    title = "Batch " + batch["ref"][len(PREFIX):]
    status, data = gh.write("POST", "pulls", {"title": title, "head": batch["ref"], "base": main, "body": text})
    if status == 201:
        batch["number"] = data["number"]
    elif status:
        raise Refused(
            f"GitHub would not let this workflow open a pull request for `{batch['ref']}` "
            f"({status}: {(data or {}).get('message', 'no reason given')}). The branch is ready. Open the pull "
            f"request by hand at https://github.com/{gh.repo}/compare/{main}...{batch['ref']}?expand=1 and it "
            "will be picked up, or allow GitHub Actions to create pull requests in the repository settings.")


def start(gh, main, head, now, log, on=None):
    """Create the branch for a new batch at `head`, under a name no other batch has. `on` is the
    number of the batch whose head that is, when it is not main's."""
    stamp = (now or datetime.datetime.now(datetime.timezone.utc)).strftime("%Y-%m-%d-%H%M%S")
    status, data = None, None
    for name in [PREFIX + stamp] + [f"{PREFIX}{stamp}-{count}" for count in range(2, 6)]:
        status, data = gh.write("POST", "git/refs", {"ref": f"refs/heads/{name}", "sha": head})
        if status in (0, 201):
            log.append(f"started `{name}` on top of #{on}" if on else f"started `{name}` from `{main}`")
            return {"ref": name, "sha": head, "number": None, "body": ""}
        if status != 422:
            break
    raise Refused(f"GitHub would not create a batch branch ({status}: {(data or {}).get('message', 'no reason given')}).")


# ---------------------------------------------------------------------------------------------
# Batches assembled by hand.


def read_record(gh, number):
    """This script's comment on a batch assembled by hand, as (comment, note). The comment is
    None, and the note empty, until there is one."""
    for comment in gh.pages(f"issues/{number}/comments"):
        match = BY_HAND.match(comment.get("body") or "") if by_workflow(comment) else None
        if match:
            return comment, load_note(match.group(1))
    return None, {}


# The note of a batch assembled by hand: what `look_through` remembers from one run to the next.
# `keep_in_step` writes it into this script's record comment on the batch's pull request, with
# `dump_note`, and `read_record` reads it back, with `load_note`. In memory, numbers are strings,
# and a key may be missing from a note written before it was:
#
#   head      the branch's head when `members` was found.
#   members   what the batch contains of its own, as {number: the commit of it that is in the
#             branch}: not what a batch it is stacked on contains.
#   queued    the members that were labelled `batch queue` before the batch took them. They go
#             back to the queue if the batch is closed without being merged. A note without it
#             is from before it was written down, and held only queued pull requests.
#   below     the batches this one is stacked on, directly or not, as {number: the head of that
#             batch when its own members were found}. Missing when there are none. When it
#             changes, the branch is looked through again, because what this batch contains of
#             its own changes with it.
#
# On GitHub, where a comment holds at most 65,536 characters, the note is compact JSON, and
# `queued` is kept as a list of numbers or as the list of the members it leaves out (`unqueued`),
# whichever is shorter. `load_note` also reads notes written before `dump_note`, which kept every
# key as it is in memory.


def dump_note(note):
    """A note as it is kept on GitHub: compact JSON, with only the keys the note has."""
    found = note.get("members") or {}
    kept = {name: note[name] for name in ("head", "members") if name in note}
    if note.get("below"):
        kept["below"] = note["below"]
    if "queued" in note:
        queued = {key for key in note["queued"] if key in found}
        rest = {key for key in found if key not in queued}
        if len(rest) < len(queued):
            kept["unqueued"] = sorted(int(key) for key in rest)
        else:
            kept["queued"] = sorted(int(key) for key in queued)
    return json.dumps(kept, sort_keys=True, separators=(",", ":"))


def load_note(text):
    """A note as `dump_note` wrote it, or as notes were written before it, in memory. Anything
    that is not a note reads as an empty one."""
    try:
        kept = json.loads(text)
    except ValueError:
        return {}
    if not isinstance(kept, dict):
        return {}
    note = {"head": kept["head"]} if "head" in kept else {}
    if isinstance(kept.get("members"), dict):
        note["members"] = {str(key): value for key, value in kept["members"].items()}
    found = note.get("members", {})
    if isinstance(kept.get("unqueued"), list):
        rest = {str(key) for key in kept["unqueued"]}
        note["queued"] = sorted((key for key in found if key not in rest), key=int)
    elif isinstance(kept.get("queued"), list):
        note["queued"] = sorted({str(key) for key in kept["queued"]}, key=int)
    if isinstance(kept.get("below"), dict) and kept["below"]:
        note["below"] = {str(key): value for key, value in kept["below"].items()}
    return note


def members(note):
    """What a note says a batch assembled by hand contains, as {number: commit}."""
    found = note.get("members")
    return dict(found) if isinstance(found, dict) else {}


def queued_before(note):
    """Which of those were labelled `batch queue` before they were labelled `building`. A note
    from before this was written down holds only queued pull requests."""
    if isinstance(note.get("queued"), list):
        return {str(key) for key in note["queued"]}
    return set(members(note))


def branch_commits(gh, base, head, pages=20):
    """The commits of a branch whose head is `head` that `base` does not have, or None if GitHub
    did not list them all. A request for each hundred of them."""
    found = set()
    for page in range(1, pages + 1):
        status, data = gh.call("GET", f"compare/{base}...{head}?per_page=100&page={page}")
        if status != 200 or not isinstance(data, dict) or not isinstance(data.get("commits"), list):
            return None
        found |= {commit["sha"] for commit in data["commits"]}
        if len(found) >= data.get("total_commits", 0):
            return found
        if len(data["commits"]) < 100:
            return None
    return None


def inside(batch, pulls, commits):
    """The open pull requests whose head commit is one of a batch's `commits`, as {number: commit}.
    No pull request that holds a batch is ever in another batch: one batch is stacked on another
    instead (see `stack`). A pull request into another branch counts too: it is built along with
    the batch, even though GitHub will not mark it merged when the batch is."""
    return {str(pr["number"]): pr["sha"] for pr in pulls.values() if not pr["batch"] and pr["sha"] in commits}


def built_by_hand(gh, pulls, log):
    """The open batches assembled by hand that are being built, as {ref, sha, number, base,
    comment, note, commits}.

    One labelled `building` is being built. One that is not is looked through, at a request or
    so, and labelled `building` once its branch holds the head commit of an open pull request:
    the label is how it is found again after it is closed. One labelled `batch queue` and not
    `building` is waiting in the queue like any other pull request, and is not looked at.
    Reading the note costs a request for each. `commits` is what the branch was found to hold,
    or None when it was not looked through.
    """
    found = []
    for pr in sorted(pulls.values(), key=lambda pr: pr["number"]):
        if not by_hand(pr) or (QUEUED in pr["labels"] and BUILDING not in pr["labels"]):
            continue
        commits = None
        if BUILDING not in pr["labels"]:
            if gh.short():
                log.append(f"only {gh.remaining} requests left this hour: did not look through the batch "
                           f"#{pr['number']}, and the next run does")
                continue
            commits = branch_commits(gh, pr["base"], pr["sha"])
            if commits is None:
                log.append(f"GitHub did not list every commit of the batch #{pr['number']}: the next run looks again")
                continue
            if not inside(pr, pulls, commits):
                continue
            relabel(gh, pr, add=BUILDING)
            log.append(f"#{pr['number']} is a batch assembled by hand with open pull requests in it: now `{BUILDING}`")
        comment, note = read_record(gh, pr["number"])
        found.append({"ref": pr["ref"], "sha": pr["sha"], "number": pr["number"], "base": pr["base"],
                      "comment": comment, "note": note, "commits": commits})
    return found


def stacked_on(gh, pr, batches):
    """Which of `batches`, a set of numbers, the batch held by `pr` says it is stacked on, and
    where it says so: (set of numbers, "a `depends on` line" or "its branch name" or None).

    A `depends on` line of its description that names one of them counts, ticked or not (see
    `pr-dependencies.py`). When none does, a branch named `batch/<anything>-on-<number>` is
    stacked on that number, if it is one of them. A batch is never stacked on itself.
    """
    others = set(batches) - {pr["number"]}
    named = _deps.dependencies(pr["body"], gh.repo) & others
    if named:
        return named, "a `depends on` line"
    match = ON_BATCH.fullmatch(pr["ref"])
    if match and int(match.group(1)) in others:
        return {int(match.group(1))}, "its branch name"
    return set(), None


def twins(hand, log):
    """Stack batches whose branches are at the same commit on one another, in number order.

    Two such batches contain the same pull requests, and so does a branch that contains another's
    head while the other contains its head: the two heads are one commit. Whatever they say about
    each other, each is taken to be stacked on the one with the next lower number, which holds
    what they share, and the one with the highest number is the outermost. What they say about
    other batches still counts. Sets `same` on each batch, the batch it is stacked on for that
    reason, and warns on every run that sees such batches.
    """
    for batch in hand:
        batch["same"] = set()
    heads = {}
    for batch in hand:
        heads.setdefault(batch["sha"], []).append(batch)
    for head, group in sorted(heads.items(), key=lambda item: min(batch["number"] for batch in item[1])):
        if len(group) < 2:
            continue
        group.sort(key=lambda batch: batch["number"])
        numbers = {batch["number"] for batch in group}
        for lower, upper in zip(group, group[1:]):
            upper["same"] = {lower["number"]}
        for batch in group:
            batch["under"] = (batch["under"] - numbers) | batch["same"]
            if not batch["under"] - batch["same"]:
                batch["how"] = None
        names = ", ".join(f"#{batch['number']}" for batch in group)
        order = ", ".join(f"#{upper['number']} on #{lower['number']}" for lower, upper in zip(group, group[1:]))
        log.append(f"warning: the batches {names} are at the same commit `{head[:10]}`: whatever they say about "
                   f"each other, each is taken to be stacked on the one with the next lower number ({order})")


def stacking(batch):
    """Which batches a batch is stacked on directly, and why, in words, or "" when it is stacked on
    none: "#1018, as its branch name says"."""
    same = batch.get("same", set())
    claimed = sorted(set(batch.get("under", ())) - same)
    parts = []
    if claimed:
        parts.append(", ".join(f"#{number}" for number in claimed) + f", as {batch['how']} says")
    if same:
        parts.append(", ".join(f"#{number}" for number in sorted(same))
                     + ", whose branch is at the same commit and whose number is lower")
    return ", and on ".join(parts)


def stack(gh, hand, pulls, log):
    """Put the open batches assembled by hand that are being built in order, the lowest first.

    Sets on each `under`, the batches it is stacked on directly, `how`, where it says so, `same`,
    those of them it is stacked on because their branches are at the same commit (see `twins`),
    and `below`, every batch under it, directly or not, all as numbers of batches in `hand`.
    Batches that say they are stacked on each other in a circle are taken to be stacked on none,
    except for `same`, and the run says so. Each batch comes after every batch under it.
    """
    numbers = {batch["number"] for batch in hand}
    by = {batch["number"]: batch for batch in hand}
    for batch in hand:
        batch["under"], batch["how"] = stacked_on(gh, pulls[batch["number"]], numbers)
    twins(hand, log)

    def close():
        for batch in hand:
            seen, todo = set(), list(batch["under"])
            while todo:
                number = todo.pop()
                if number not in seen:
                    seen.add(number)
                    todo += by[number]["under"]
            batch["below"] = seen

    close()
    circle = sorted(batch["number"] for batch in hand if batch["number"] in batch["below"])
    if circle:
        # What `twins` stacks never makes a circle by itself, so none is left once the rest goes.
        log.append("the batches " + ", ".join(f"#{number}" for number in circle) + " say they are stacked on "
                   "each other in a circle: none of them is taken to be stacked on another batch"
                   + (", except one at the same commit" if any(by[number]["same"] for number in circle) else ""))
        for number in circle:
            by[number]["under"], by[number]["how"] = set(by[number]["same"]), None
        close()
    # A batch has more batches under it than any batch under it has.
    return sorted(hand, key=lambda batch: (len(batch["below"]), batch["number"]))


def outermost(hand):
    """The numbers of the batches in `hand`, put in order by `stack`, that no other is stacked on."""
    return {batch["number"] for batch in hand} - set().union(*(batch["under"] for batch in hand))


def holders(hand):
    """Which batches assembled by hand contain each pull request, as {number: {batch numbers}}."""
    held = {}
    for batch in hand:
        for key in members(batch["note"]):
            held.setdefault(key, set()).add(batch["number"])
    return held


def contains(gh, head, commit):
    """Whether a branch whose head is `head` has `commit` in it, or None if GitHub did not say."""
    status, data = gh.call("GET", f"compare/{head}...{commit}?per_page=1")
    if status != 200 or not isinstance(data, dict) or "ahead_by" not in data:
        return None
    return data["ahead_by"] == 0


def merge_base(gh, one, other):
    """The commit that GitHub takes as the merge base of two commits, or None if it did not say."""
    status, data = gh.call("GET", f"compare/{one}...{other}?per_page=1")
    if status != 200 or not isinstance(data, dict):
        return None
    return (data.get("merge_base_commit") or {}).get("sha")


def shares(gh, batch, other, by, commits):
    """Whether a batch, whose branch holds `commits` beyond main, shares a commit beyond main with
    the batch `other` that it says it is stacked on. Usually it holds the head of `other`, or the
    commit of a pull request that `other` or a batch under it contains. Otherwise GitHub is asked
    for the merge base of the two. When GitHub does not say, they are taken to share one."""
    if other["sha"] in commits:
        return True
    for number in other["below"] | {other["number"]}:
        if any(commit in commits for commit in members(by[number]["note"]).values()):
            return True
    base = merge_base(gh, other["sha"], batch["sha"])
    return base is None or base in commits


def look_through(gh, batch, by, pulls, before, log):
    """Find what a batch assembled by hand contains of its own.

    It contains each open pull request whose head commit is in its branch, queued or not, that
    no batch under it contains: a pull request in several batches of one stack belongs to the
    lowest. `by` is the batches being built, by number; those under this one have been looked
    through already. When the branch's head, or a batch under it, has moved since the note was
    written, the branch's commits are listed again, a request for each hundred of them. What has
    arrived is added. What was found before stays as long as the commit it was found at is still
    there, even after its author has pushed again. `before` is the pull requests that some note
    says were labelled `batch queue` before a batch took them.

    Sets the batch's new `note`, and `old`, the note it had. Nothing is set when the branch could
    not be listed: the note keeps its old head, so the next run looks again. The note's keys are
    described above `dump_note`.
    """
    note, number = batch["note"], batch["number"]
    found, queued = members(note), queued_before(note)
    below = {str(other): by[other]["note"].get("head", "") for other in sorted(batch["below"])}
    taken = set().union(*(members(by[other]["note"]) for other in batch["below"]))
    if note.get("head") != batch["sha"] or note.get("below", {}) != below:
        commits = batch.get("commits")
        if commits is None:
            if gh.short():
                log.append(f"only {gh.remaining} requests left this hour: did not look through the batch #{number}, "
                           "and the next run does")
                return
            commits = branch_commits(gh, batch["base"], batch["sha"])
        if commits is None:
            log.append(f"GitHub did not list every commit of the batch #{number}: the next run looks again")
            return
        now = {key: commit for key, commit in found.items() if commit in commits}
        for key, commit in inside(batch, pulls, commits).items():
            now.setdefault(key, commit)
        found = now
        if set(below) != set(note.get("below", {})):
            log.append(f"#{number} is stacked on {stacking(batch)}" if batch["under"] else
                       f"#{number} is no longer stacked on another batch")
        for other in sorted(batch["under"] - batch.get("same", set())):
            if not shares(gh, batch, by[other], by, commits):
                log.append(f"warning: #{number} says in {batch['how']} that it is stacked on #{other}, but its branch "
                           f"shares no commit with that of #{other} beyond `main`")
    found = {key: commit for key, commit in found.items()
             if key not in taken and not (pulls.get(int(key)) or {}).get("batch")}
    queued = {key for key in found
              if key in queued or key in before or QUEUED in (pulls.get(int(key)) or {}).get("labels", ())}
    batch["old"] = note
    batch["note"] = {"head": batch["sha"], "members": found, "queued": sorted(queued, key=int)}
    if below:
        batch["note"]["below"] = below


def keep_in_step(gh, batch, pulls, held, log):
    """Record what `look_through` found in a batch assembled by hand, and label it `building`.

    Whatever has left the batch loses `building` unless another batch contains it, and goes back
    to `batch queue` if it was queued before. `held` says, for each pull request, which batches
    contain it now. Returns whether anything was queued again.
    """
    if "old" not in batch:
        return False
    number, requeued = batch["number"], False
    old, found = members(batch["old"]), batch["note"]["members"]
    queued = queued_before(batch["old"])
    for key in sorted(set(old) - set(found), key=int):
        pr = pulls.get(int(key))
        # A batch that a note written before batches were stacked lists as a member carries
        # `building` for being built itself.
        if pr and BUILDING in pr["labels"] and not held.get(key) and not pr["batch"]:
            back = key in queued
            relabel(gh, pr, add=QUEUED if back else None, remove=BUILDING)
            requeued |= back
            log.append(f"#{key} is no longer in the batch #{number}: "
                       + (f"`{QUEUED}` again" if back else f"no longer `{BUILDING}`"))

    # The record first and the labels second, so that whatever carries `building` because of
    # this batch is in the record when the batch is finished with. A label taken off by hand is
    # not put back, except that a pull request queued again swaps `batch queue` for it.
    text = describe_by_hand(batch["note"], stacking(batch))
    if batch["comment"] is None:
        gh.write("POST", f"issues/{number}/comments", {"body": text})
    elif text != batch["comment"].get("body"):
        gh.write("PATCH", f"issues/comments/{batch['comment']['id']}", {"body": text})
    for key in sorted(found, key=int):
        pr = pulls.get(int(key))
        if pr and QUEUED in pr["labels"]:
            relabel(gh, pr, add=BUILDING, remove=QUEUED)
        elif pr and key not in old and BUILDING not in pr["labels"]:
            relabel(gh, pr, add=BUILDING)
        else:
            continue
        log.append(f"#{key} is in the batch #{number}: now `{BUILDING}`")
    return requeued


def describe_by_hand(note, under=""):
    """The comment that records what a batch assembled by hand contains. `under` says which
    batches it is stacked on directly, and why, as `stacking` puts it."""
    listed = ", ".join(f"#{key}" for key in sorted(note["members"], key=int)) or "nothing yet"
    stacked = ""
    if under:
        stacked = (f"This batch is stacked on {under}. A pull request that a batch under this one "
                   "contains is listed there, not here.\n\n")
    return (f"<!-- batch-queue-by-hand {dump_note(note)} -->\n"
            "While this pull request is open, the batch-queue workflow takes it to be a batch that is being built. "
            "It adds nothing to a batch assembled by hand and leaves its description alone, but it keeps the labels "
            f"in step: each open pull request whose head commit is in this branch, and in no batch this one is "
            f"stacked on, is now `{BUILDING}`, in place of `{QUEUED}` if it had that. When this is merged they lose "
            f"`{BUILDING}`. If it is closed without being merged they lose it too, and the ones that were queued go "
            f"back to `{QUEUED}`, except those that a batch stacked on this one still holds.\n\n"
            f"{stacked}In this batch: {listed}.\n")


def stranded(gh, done, hand, pulls, log):
    """Tell each open batch assembled by hand that is stacked on a batch closed without being
    merged, once. Its branch still carries the commits of that batch, whose pull requests are now
    its own (see `look_through`), and whoever assembles it should rebuild it."""
    open_ = {batch["number"] for batch in hand}
    for gone in done:
        if gone["fate"] != "closed":
            continue
        for batch in hand:
            claimed, how = stacked_on(gh, pulls[batch["number"]], open_ | {gone["number"]})
            if gone["number"] not in claimed:
                continue
            if tell(gh, batch["number"], None, STRANDED.format(number=gone["number"]),
                    f"#{gone['number']}, which this batch is stacked on as {how} says, was closed without being "
                    f"merged. This batch's branch still carries the commits of #{gone['number']}, so the open pull "
                    f"requests of #{gone['number']} whose head commit is in this branch now count as part of this "
                    f"batch and stay `{BUILDING}`.\n\n"
                    "Whoever assembles this batch should rebuild it on `main` or on another batch, and update its "
                    "`depends on` line or its branch name to match."):
                log.append(f"told #{batch['number']} that #{gone['number']}, which it is stacked on, was closed "
                           "without merging")


def unsettled(gh, done, hand, pulls):
    """The batches among `done` closed without being merged that an open batch says it is stacked
    on, when that open batch could not be looked through in this run (see `look_through`). What
    such a batch contained may be held by the one stacked on it, which is not known yet: taking
    `building` off its members now would only see the next run put it back. They are left as
    they are, the closed batch keeping `building` itself, and the next run settles them."""
    open_ = {batch["number"] for batch in hand}
    return {gone["number"] for gone in done if gone["fate"] == "closed"
            for batch in hand
            if "old" not in batch and gone["number"] in stacked_on(gh, pulls[batch["number"]], open_ | {gone["number"]})[0]}


def mark_latest(gh, hand, pulls, log):
    """Label `latest batch` the outermost batch of each stack, and take the label off every
    other open pull request. A batch that was merged or closed loses it in `finish`."""
    tops = outermost(hand)
    for number in sorted(tops):
        pr = pulls[number]
        if LATEST in pr["labels"]:
            continue
        if not gh.label_exists(LATEST):
            log.append(f"there is no `{LATEST}` label in this repository: was it renamed?")
            break
        relabel(gh, pr, add=LATEST)
        log.append(f"#{number} is the outermost batch of its stack: now `{LATEST}`")
    for pr in sorted(pulls.values(), key=lambda pr: pr["number"]):
        if LATEST in pr["labels"] and pr["number"] not in tops:
            relabel(gh, pr, remove=LATEST)
            log.append(f"#{pr['number']} is not the outermost batch of a stack: `{LATEST}` removed")


# ---------------------------------------------------------------------------------------------
# Building on a batch assembled by hand.


def restack(gh, batch, state, base, main_sha, log):
    """Keep the batch being assembled on top of `base`, {number, sha}, or on main when it is None.

    When the batch underneath has moved on from what this one was last brought up to date with,
    its new head is merged in. When it was rebuilt, or when this one should now sit on another
    batch or on main, this one is rebuilt: its branch is reset, and what it held is forgotten,
    so that every queued commit is merged in again. A batch underneath that has landed on main
    is already in this one, and needs nothing. Nothing is done when GitHub does not say whether
    one commit is in another.

    A batch with no note, as while it has no pull request, whose branch already holds the head
    of `base` is taken to have been started there.
    """
    have = state.get("base")
    if base is None and have is None:
        return
    if base and have is None and contains(gh, batch["sha"], base["sha"]):
        state["base"] = {"number": base["number"], "sha": base["sha"], "start": base["sha"]}
        return
    if base and have and base["number"] == have.get("number"):
        if base["sha"] == have.get("sha"):
            return
        ahead = contains(gh, base["sha"], have.get("sha"))
        if ahead is None:
            return
        if ahead:
            message = UPDATED.format(number=base["number"], sha=base["sha"])
            status, data = gh.write("POST", "merges", {"base": batch["ref"], "head": base["sha"], "commit_message": message})
            if status in (0, 201, 204):
                if status == 201:
                    batch["sha"] = data["sha"]
                have["sha"] = base["sha"]
                log.append(f"brought `{batch['ref']}` up to date with #{base['number']} at `{base['sha'][:10]}`")
                return
            log.append(f"GitHub could not merge the new head of #{base['number']} into `{batch['ref']}` ({status})")
    elif base is None:
        landed = contains(gh, main_sha, have.get("sha"))
        if landed is None:
            return
        if landed:
            state["base"] = None
            log.append(f"#{have.get('number')}, which `{batch['ref']}` was built on, has landed on main")
            return
    head = base["sha"] if base else main_sha
    status, data = gh.write("PATCH", f"git/refs/heads/{batch['ref']}", {"sha": head, "force": True})
    if status not in (0, 200):
        raise Refused(f"GitHub would not reset `{batch['ref']}` ({status}: {(data or {}).get('message', 'no reason given')}).")
    batch["sha"] = head
    state["merged"], state["refused"] = {}, {}
    state["base"] = {"number": base["number"], "sha": head, "start": head} if base else None
    log.append(f"rebuilt `{batch['ref']}` " + (f"on top of #{base['number']} at `{head[:10]}`" if base else "on main"))


def on_top(state, crowded=()):
    """What a batch's description says about the batch it is built on. `crowded` lists the
    outermost batches assembled by hand into main, when there are too many to choose one."""
    base = state.get("base")
    if not base:
        if crowded:
            return [f"Built on `main`, because more than one batch assembled by hand into `main` is `{LATEST}`: "
                    + ", ".join(f"#{number}" for number in crowded) + "."]
        return []
    number = base["number"]
    return [f"Built on top of #{number} at `{base['sha'][:10]}`. Merge it after #{number}: merging it first "
            f"lands the pull requests of #{number} too."]


# ---------------------------------------------------------------------------------------------
# One run.


def finish(gh, pulls, held, leftover, main_sha, done, log):
    """Tidy up after batches that were merged or closed. `done` is the batches assembled by hand
    among them, as `finished` gives them. `held` is what the open batches assembled by hand
    contain, and a pull request one of them contains keeps `building`. That includes what a
    batch closed without being merged contained, when a batch stacked on it still holds it.

    The branch of a batch this script assembled is removed once its pull request is merged or
    closed. When it was merged, GitHub marks what it contained as merged too, except a pull
    request pushed to after it was queued. That one loses `batch queue` here if the commit that
    landed is the one queued, since nothing is left of it to build.

    Returns whether anything was queued again, and the numbers whose `building` was taken off.
    """
    requeued, cleared = False, set()
    for batch in done:
        cleared.add(batch["number"])
        for key in batch["members"]:
            pr = pulls.get(int(key))
            if pr and pr["batch"]:
                # Listed by a note written before batches were stacked: an open batch keeps
                # `building` for being built itself.
                continue
            if batch["fate"] == "merged":
                # A pull request that GitHub marked as merged is no longer in `pulls`.
                if pr is None or (BUILDING in pr["labels"] and key not in held):
                    relabel(gh, pr or int(key), remove=BUILDING)
                    cleared.add(int(key))
                    log.append(f"#{key} landed with batch #{batch['number']}: `{BUILDING}` removed")
            elif pr and BUILDING in pr["labels"] and key not in held:
                back = key in batch["queued"]
                relabel(gh, pr, add=QUEUED if back else None, remove=BUILDING)
                requeued |= back
                log.append(f"batch #{batch['number']} was closed without merging: #{key} is "
                           + (f"`{QUEUED}` again" if back else f"no longer `{BUILDING}`"))
        if LATEST in batch["labels"]:
            relabel(gh, batch["number"], remove=LATEST)
        # Taking the label off the batch itself marks it as dealt with.
        relabel(gh, batch["number"], remove=BUILDING)
        log.append(f"tidied up after batch #{batch['number']}, which was assembled by hand")
    for item in leftover:
        info = item["pull"]
        if info.get("merged_at"):
            merged = recall(gh, {"sha": item["sha"], "body": info.get("body") or ""}, main_sha)["merged"]
            for key, commit in sorted(merged.items(), key=lambda entry: int(entry[0])):
                pr = pulls.get(int(key))
                if pr and QUEUED in pr["labels"] and look(gh, pr, {})[0] == commit:
                    relabel(gh, pr, remove=QUEUED)
                    log.append(f"#{key} landed with batch #{info['number']} at the commit that was queued: "
                               f"`{QUEUED}` removed")
        gh.write("DELETE", f"git/refs/heads/{item['ref']}")
        log.append(f"removed the branch `{item['ref']}`")
    return requeued, cleared


def unlabel_closed(gh, closed_building, cleared, log):
    """Take `batch queue` and `building` off pull requests that were closed, merged or not.

    `finish` has already taken `building` off the batches assembled by hand it tidied up after,
    and off what they contained. Those are skipped.
    """
    closed_queued = gh.pages(f"issues?state=closed&labels={quoted(QUEUED)}")
    for label, items in ((QUEUED, closed_queued), (BUILDING, closed_building)):
        for item in items:
            number = item["number"]
            if "pull_request" not in item:
                continue
            if label == BUILDING and number in cleared:
                continue
            relabel(gh, number, remove=label)
            log.append(f"#{number} is closed: `{label}` removed")


def reopened(gh, number):
    """Put `batch queue` back on a reopened pull request that lost it when it was closed.

    Only if this workflow was the last to take `batch queue` or `building` off, after the pull
    request was last closed, and no maintainer has taken it out of the queue with `-batch` since
    it was last queued. A label a person took off stays off. Whether the pull request then becomes
    `building` again is decided by the next sync, as for any other queued pull request.
    """
    info = gh.get(f"pulls/{number}")
    if info["state"] != "open":
        return [f"#{number} is not open: nothing to put back"]
    if holds_batch(gh, info):
        return [f"#{number} holds a batch: nothing to put back"]
    if {label["name"] for label in info["labels"]} & {QUEUED, BUILDING}:
        return [f"#{number} already carries `{QUEUED}` or `{BUILDING}`"]
    events = gh.pages(f"issues/{number}/events")
    closed = [event["created_at"] for event in events if event.get("event") == "closed"]
    removed = [event for event in events if event.get("event") == "unlabeled"
               and (event.get("label") or {}).get("name") in (QUEUED, BUILDING)]
    if not closed or not removed or removed[-1]["created_at"] < closed[-1]:
        return [f"#{number} had no label taken off when it was closed: nothing to put back"]
    last = removed[-1]
    who = (last.get("actor") or {}).get("login") or "someone"
    if who != BOT:
        return [f"#{number}: `{last['label']['name']}` was taken off by {who}, so it stays off"]
    record = None
    for comment in gh.pages(f"issues/{number}/comments"):
        body = comment.get("body") or ""
        if by_workflow(comment):
            if APPROVED.match(body):
                record = "queued"
            elif body.startswith(WITHDRAWN):
                record = "withdrawn"
    if record == "withdrawn":
        return [f"#{number} was taken out of the queue with `-batch`: `{QUEUED}` stays off"]
    relabel(gh, number, add=QUEUED)
    return [f"#{number} was reopened: `{QUEUED}` put back"]


def sync(gh, now=None):
    """Bring batches and labels up to date. Returns lines saying what was done."""
    log = []
    main = gh.get("")["default_branch"]
    main_sha = gh.get(f"git/ref/heads/{main}")["object"]["sha"]
    pulls = open_pulls(gh)
    found, leftover = batches(gh, pulls)
    hand = built_by_hand(gh, pulls, log)
    closed_building = gh.pages(f"issues?state=closed&labels={quoted(BUILDING)}")
    done = finished(gh, closed_building, holders(hand))
    # The lowest batch first, so that what a batch contains of its own is found after what the
    # batches under it contain. A batch stacked on one closed just now takes over what that one
    # contained and its branch still holds, and the labels are changed once all are known.
    hand = stack(gh, hand, pulls, log)
    before = set().union(*(queued_before(batch["note"]) for batch in hand), *(batch["queued"] for batch in done))
    by = {batch["number"]: batch for batch in hand}
    for batch in hand:
        look_through(gh, batch, by, pulls, before, log)
    held = holders(hand)
    requeued = False
    for batch in hand:
        requeued |= keep_in_step(gh, batch, pulls, held, log)
    unsure = unsettled(gh, done, hand, pulls)
    for number in sorted(unsure):
        log.append(f"batch #{number} was closed without merging, and a batch stacked on it could not be looked "
                   "through: its pull requests keep their labels, and the next run settles them")
    more, cleared = finish(gh, pulls, held, leftover, main_sha,
                           [batch for batch in done if batch["number"] not in unsure], log)
    # `unlabel_closed` leaves these alone too.
    cleared |= unsure
    requeued |= more
    unlabel_closed(gh, closed_building, cleared, log)
    stranded(gh, done, hand, pulls, log)
    mark_latest(gh, hand, pulls, log)

    if not ASSEMBLE:
        # A batch of this script's own whose pull request was merged or closed was tidied up
        # after above. One that has none is left alone (see `ASSEMBLE`).
        return log or ["nothing to do"]
    if requeued:
        # Leave time to take the pull request that broke the build out of the queue first.
        log.append("not starting a new batch in this run: the next `batch` or `-batch` comment does")
        return log

    # The batch being assembled goes on top of the outermost batch assembled by hand, the one
    # labelled `latest batch`, when just one into main is. With more than one it is not clear
    # which comes first, so it goes on main.
    tops = outermost(hand)
    under = [item for item in hand if item["number"] in tops and item["base"] == main]
    base = {"number": under[0]["number"], "sha": under[0]["sha"]} if len(under) == 1 else None
    crowded = sorted(item["number"] for item in under) if len(under) > 1 else []

    # The batch being assembled takes each commit a maintainer queued.
    assembling = sorted(found, key=lambda item: item["ref"])
    batch = assembling[-1] if assembling else None
    state = recall(gh, batch, main_sha, base and base["sha"]) if batch else {"merged": {}, "refused": {}, "seen": {}, "base": None}
    members, refused, unapproved, stopped, before = [], [], [], False, len(log)
    if batch:
        restack(gh, batch, state, base, main_sha, log)
    queued = sorted((pr for pr in pulls.values() if QUEUED in pr["labels"] and not is_batch(pr) and pr["base"] == main),
                    key=lambda pr: (PRIORITY not in pr["labels"], pr["number"]))
    for pr in queued:
        number, key = pr["number"], str(pr["number"])
        sha, comments = look(gh, pr, state["seen"])
        if sha is None:
            unapproved.append(number)
            continue
        if sha != pr["sha"] and comments is not None and tell(
                gh, number, comments, MOVED.format(sha=sha),
                f"This pull request was queued at `{sha[:10]}` and its head is now `{pr['sha'][:10]}`. A batch takes "
                "only the commit that was queued. Comment `batch` again to queue the new one."):
            log.append(f"told #{number} that its head has moved since it was queued")
        if state["merged"].get(key) == sha:
            members.append((number, sha))
            continue
        if state["refused"].get(key) == sha:
            refused.append(number)
            continue
        if stopped:
            continue
        if gh.short():
            log.append(f"only {gh.remaining} requests left this hour: stopped merging, and the next run carries on")
            stopped = True
            continue
        if batch is None:
            batch = start(gh, main, base["sha"] if base else main_sha, now, log, on=base and base["number"])
            if base:
                state["base"] = {"number": base["number"], "sha": base["sha"], "start": base["sha"]}
        message = f"Add #{number} to the batch\n\nMerged at {sha}."
        status, data = gh.write("POST", "merges", {"base": batch["ref"], "head": sha, "commit_message": message})
        if status == 201:
            batch["sha"] = data["sha"]
        if status in (0, 201, 204):
            state["merged"][key] = sha
            members.append((number, sha))
            log.append(f"{'would add' if gh.dry_run else 'added'} #{number} at `{sha[:10]}` to `{batch['ref']}`")
            continue
        on = (state["base"] or {}).get("number")
        if status != 409:
            reason = f"GitHub refused the merge ({status}: `{(data or {}).get('message', 'no reason given')}`)."
        elif on:
            reason = (f"GitHub could not merge it with what is already there: #{on}, which this batch is built on, "
                      "and the pull requests added before it.")
        else:
            reason = "GitHub could not merge it with what is already there."
        link = f"#{batch['number']}" if batch["number"] else f"`{batch['ref']}`"
        marker = REFUSAL_ON.format(branch=batch["ref"], sha=sha, base=on) if on else REFUSAL.format(branch=batch["ref"], sha=sha)
        tell(gh, number, comments, marker,
             f"The commit `{sha[:10]}` of this pull request was not added to the batch {link}: {reason}\n\n"
             f"It keeps its `{QUEUED}` label. It is tried again when a maintainer queues a new commit, "
             "or when the next batch starts.")
        state["refused"][key] = sha
        refused.append(number)
        log.append(f"left #{number} out of `{batch['ref']}`: {reason}")

    if batch is None:
        if unapproved:
            log.append(f"labelled `{QUEUED}` but no commit of them is queued: "
                       + ", ".join(f"#{number}" for number in unapproved))
        return log or ["nothing to do"]

    # What the branch holds that the list above does not account for.
    listed, also = {number for number, _ in members}, []
    for key in sorted(state["merged"], key=int):
        number, pr = int(key), pulls.get(int(key))
        if number in listed:
            continue
        if pr is None:
            also.append((number, "closed since it was merged in"))
        elif QUEUED in pr["labels"]:
            also.append((number, "at an earlier commit than the one now queued"))
        elif BUILDING in pr["labels"] and held.get(key):
            # Being built in another batch: nothing to tell it.
            also.append((number, "being built in " + ", ".join(f"#{other}" for other in sorted(held[key]))))
        else:
            also.append((number, "no longer queued"))
            _, comments = look(gh, pr, state["seen"])
            if batch["number"] and comments is not None and tell(
                    gh, number, comments, STAYS.format(branch=batch["ref"]),
                    f"`{QUEUED}` was removed from this pull request, but its commits were already merged into "
                    f"the batch #{batch['number']} and are still there. That batch was not changed.\n\n"
                    f"To build without them, close #{batch['number']}. The next `batch` comment then assembles a "
                    "new batch from what is still queued."):
                log.append(f"told #{number} that its commits stay in batch #{batch['number']}")
    if members or batch["number"]:
        publish(gh, batch, main, describe(batch, state, members, also, refused, unapproved,
                                          on_top(state, crowded)))
        if len(log) > before:
            log.append(f"batch pull request #{batch['number']} lists {len(members)} pull request(s)"
                       if batch["number"] else f"`{batch['ref']}` has no pull request yet")
    return log or ["nothing to do"]


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", required=True, help="owner/name")
    parser.add_argument("--dry-run", action="store_true", help="read everything, change nothing")
    parser.add_argument("--summary", type=Path, help="append what was done to this file")
    parser.add_argument("--reopened", type=int, metavar="NUMBER",
                        help="only put `batch queue` back on this reopened pull request if it lost it when closed")
    args = parser.parse_args()

    gh = GitHub(args.repo, args.dry_run)
    failure = None
    try:
        log = reopened(gh, args.reopened) if args.reopened else sync(gh)
    except Refused as error:
        log, failure = [str(error)], 1
    log += gh.refused
    failure = failure or (1 if gh.refused else None)
    left = f"; {gh.remaining} left this hour" if gh.remaining is not None else ""
    log.append(f"{gh.calls} requests to GitHub{left}")
    text = "".join(f"- {line}\n" for line in log)
    sys.stdout.write(text)
    if args.summary:
        with args.summary.open("a") as handle:
            handle.write(text)
    sys.exit(failure)


if __name__ == "__main__":
    main()
