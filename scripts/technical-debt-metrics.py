#!/usr/bin/env python3
"""Count how a pull request changes the technical debt in `src/`.

This is the technical debt part of Mathlib's PR summary comment, adapted to this repository.
Mathlib's version is `scripts/reporting/technical-debt-metrics.py` in
leanprover-community/mathlib-ci. This one differs from it in three ways.

* It keeps only the counters that are not already zero here, and adds the patterns that
  AGENTS.md asks contributors not to add (`attribute [-instance]`, goal-closing tactics
  written with `elab` or `run_tac`, and disabled linters such as `unusedSectionVars`). It also
  drops "exposed public sections", which are not zero: nearly every file opens two, so the
  counter would only count files, and go up with every new one.
* It counts the lines `git diff` adds and removes rather than checking out both commits, so in
  a blobless clone it only downloads the files the pull request changes. It therefore reports
  the change in each counter but not its total.
* Counters are split into strong debt, which a pull request should rarely increase, and weak
  debt, which it may, as in Mathlib.

Usage, from a clone of this repository:

  scripts/technical-debt-metrics.py pr_summary [BASE [HEAD]]

prints the change in each counter from BASE...HEAD (default origin/main...HEAD). If
GITHUB_OUTPUT is set, it also writes the output `changed` ("true" or "false") to it.
"""
from collections import Counter
import os
import re
import subprocess
import sys

STRONG, WEAK = 'strong', 'weak'
PATHS = ['src']

# Disabling these linters is strong debt: the first two as in Mathlib, `unusedSectionVars` because
# AGENTS.md asks contributors not to, and `all` because it disables that one too. Disabling any
# other linter is weak debt.
STRONG_LINTERS = {'linter.deprecated', 'linter.auxLemma', 'linter.unusedSectionVars', 'linter.all'}

# Each fixed counter counts the lines matching its regular expression.
FIXED = [
    (STRONG, '`erw`', re.compile(r'\berw \[')),
    (STRONG, '`maxHeartbeats` modifications', re.compile(r'^ *set_option .*maxHeartbeats.* [0-9]')),
    (STRONG, '`attribute [-instance]`', re.compile(r'attribute \[-instance\]')),
    (STRONG, 'tactics defined with `elab`',
     re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:local |scoped )?elab(?:_rules)?\b.*:\s*tactic\b')),
    (STRONG, '`run_tac`', re.compile(r'\brun_tac\b')),
    (STRONG, '`CommRing (Fin n)` instances', re.compile(r'^open\b.*\bFin\.CommRing\b(?!\.)')),
    (STRONG, '`NatCast (Fin n)` instances', re.compile(r'^open\b.*\bFin\.NatCast\b(?!\.)')),
    (WEAK, '`dsimp +instances`', re.compile(r'\bdsimp (?:[+-]\S* +)*\+instances')),
]
# These count each option separately: a line counts once for every option it names.
BACKWARD = re.compile(r'set_option (backward\.[\w.]+)')
LINTER = re.compile(r'set_option (linter\.[\w.]+) false')
# A line that matches none of these cannot match any counter.
PREFILTER = re.compile(r'set_option|erw|attribute|elab|run_tac|Fin\.|instances')


def git(*args):
    return subprocess.run(['git', *args], capture_output=True, encoding='utf-8',
                          check=True).stdout.strip()


def count_line(line):
    """The counters that one line of Lean adds to, as (level, name) pairs."""
    if not PREFILTER.search(line):
        return []
    keys = [(level, name) for level, name, regex in FIXED if regex.search(line)]
    keys += [(STRONG, f'`{option}`') for option in sorted(set(BACKWARD.findall(line)))]
    keys += [(STRONG if option in STRONG_LINTERS else WEAK, f'disabled `{option}`')
             for option in sorted(set(LINTER.findall(line)))]
    return keys


def count_diff(old, new):
    """Return (added, removed): the counts over the lines `git diff old new` adds and removes."""
    added, removed = Counter(), Counter()
    # Without rename detection a moved file is removed and added in full, so its counts cancel.
    with subprocess.Popen(['git', 'diff', '--no-renames', '--no-ext-diff', '--no-color',
                           '--no-textconv', '-U0', old, new, '--', *PATHS],
                          stdout=subprocess.PIPE, encoding='utf-8', errors='replace') as proc:
        in_hunk = False
        for line in proc.stdout:
            # File headers such as `--- a/…` come between `diff --git` and the first `@@`,
            # so a removed line that starts with `--` is never mistaken for one.
            if line.startswith('diff --git '):
                in_hunk = False
            elif line.startswith('@@'):
                in_hunk = True
            elif in_hunk and line[:1] == '+':
                added.update(count_line(line[1:]))
            elif in_hunk and line[:1] == '-':
                removed.update(count_line(line[1:]))
    if proc.returncode:
        raise subprocess.CalledProcessError(proc.returncode, proc.args)
    return added, removed


def change(old, new):
    """The change in each counter between two commits."""
    added, removed = count_diff(old, new)
    return {key: added[key] - removed[key] for key in added.keys() | removed.keys()
            if added[key] != removed[key]}


def table(headers, align, rows):
    lines = ['|' + '|'.join(headers) + '|',
             '|' + '|'.join({'l': ':-', 'r': '-:'}[a] for a in align) + '|']
    lines += ['|' + '|'.join(map(str, row)) + '|' for row in rows]
    return '\n'.join(lines)


def ordered(keys, level):
    """The counters of one level: the fixed ones first, in the order of FIXED."""
    rank = {name: i for i, (_, name, _) in enumerate(FIXED)}
    return sorted((name for lvl, name in keys if lvl == level),
                  key=lambda name: (rank.get(name, len(rank)), name))


def pr_summary(base, head):
    diff = change(base, head)
    sections = []
    for level in (STRONG, WEAK):
        names = ordered(diff, level)
        if not names:
            sections.append(f'No changes to {level} technical debt.')
            continue
        deltas = [diff[level, name] for name in names]
        if all(d > 0 for d in deltas):
            headline = f'Increase in {level} tech debt'
        elif all(d < 0 for d in deltas):
            headline = f'Decrease in {level} tech debt'
        else:
            headline = f'Changes to {level} tech debt'
        rows = [(f'{diff[level, name]:+d}', name) for name in names]
        sections.append(f'<details><summary>{headline}</summary>\n\n'
                        f'{table(["Change", f"Type ({level})"], "rl", rows)}\n</details>')
    output = os.environ.get('GITHUB_OUTPUT')
    if output:
        with open(output, 'a', encoding='utf-8') as f:
            f.write(f'changed={str(bool(diff)).lower()}\n')
    return '\n\n'.join(sections) + f'\n\nBase {base[:10]}, head {head[:10]}.\n'


def main(argv):
    mode, *args = argv or ['']
    if mode != 'pr_summary' or len(args) > 2:
        sys.exit(__doc__)
    head = git('rev-parse', args[1] if len(args) > 1 else 'HEAD')
    base = git('merge-base', args[0] if args else 'origin/main', head)
    print(pr_summary(base, head))


if __name__ == '__main__':
    main(sys.argv[1:])
