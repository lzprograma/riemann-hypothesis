#!/usr/bin/env python3
"""Checks of the parser for the `depends on` lines of a description; no network calls."""
import importlib.util
from pathlib import Path
import unittest

SCRIPTS = Path(__file__).resolve().parents[1]


# `pr-dependencies.py` is loaded the way the scripts load it, through `load` in `github-rest.py`,
# which registers it in `sys.modules`: its dataclass needs that up to Python 3.14.
spec = importlib.util.spec_from_file_location("github_rest", SCRIPTS / "github-rest.py")
rest = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rest)
deps = rest.load("pr-dependencies.py")

REPO = "o/r"


class Dependencies(unittest.TestCase):
    def read(self, body):
        return deps.dependencies(body, REPO)

    def test_the_line_agents_md_asks_for(self):
        self.assertEqual(self.read("Some text.\n\n---\n\n- [ ] depends on: #123\n"), {123})

    def test_every_wording_and_task_box(self):
        for line in ("- [ ] depends on: #7", "- [x] depends on: #7", "- [X] Depends on #7", "depends on #7",
                     "Depend on: #7", "* [ ] depends upon #7", "  - depends on: #7", "DEPENDS ON #7",
                     "depend upon #7", "+ depends on #7"):
            with self.subTest(line=line):
                self.assertEqual(self.read(line), {7})

    def test_other_common_wordings(self):
        for line in ("- blocked by #7", "- [ ] Blocked by: #7", "* requires #7", "+ Requires: #7", "[ ] needs #7",
                     "- [x] needs: #7", "> depends on #7", "> - [ ] blocked by #7", "-depends on #7",
                     "[ ] depends on #7", "[] depends on #7", "**Depends on** #7", "depends\ton\t#7",
                     "- [ ]depends on #7", "  -\tneeds #7", "[x]requires #7"):
            with self.subTest(line=line):
                self.assertEqual(self.read(line), {7})

    def test_needs_requires_and_blocked_by_only_on_a_list_or_task_line(self):
        for line in ("Needs review from the authors of #1234.", "needs #7", "Requires: #7", "blocked by #7",
                     "> blocked by #7", "-needs #7", "**Needs** #7", "*requires #7"):
            with self.subTest(line=line):
                self.assertEqual(self.read(line), set())

    def test_code_indented_by_four_spaces_is_not_read(self):
        self.assertEqual(self.read("Text.\n\n    depends on #1\n    - [ ] needs #2\n\ndepends on #3\n"), {3})
        self.assertEqual(self.read("    depends on #1\n\tdepends on #2\n"), set())
        # Blank lines inside the block keep it going.
        self.assertEqual(self.read("\n    x = 1\n\n    depends on #1\ndepends on #2\n"), {2})

    def test_indented_lines_that_are_not_code_are_read(self):
        # A paragraph's next line, however far it is indented, continues the paragraph.
        self.assertEqual(self.read("Some text\n    depends on #1\n"), {1})
        # Within a list, indenting nests a list item or continues one.
        self.assertEqual(self.read("- [ ] depends on #1\n\n    - [ ] depends on #2\n"), {1, 2})
        self.assertEqual(self.read("1. First\n\n    depends on #3\n"), {3})

    def test_several_on_one_line_and_several_lines(self):
        self.assertEqual(self.read("- [ ] depends on: #1, #2\n- [x] depends on: #3\n"), {1, 2, 3})

    def test_addresses_and_references_to_this_repository_only(self):
        body = ("depends on https://github.com/o/r/pull/11\n"
                "depends on https://github.com/other/r/pull/12\n"
                "depends on o/r#13 and other/r#14\n"
                "depends on http://github.com/O/R/pull/15/files\n")
        self.assertEqual(self.read(body), {11, 13, 15})

    def test_only_at_the_start_of_a_line(self):
        self.assertEqual(self.read("This depends on #5.\n- see #6, which depends on #7\n"), set())

    def test_other_words_are_not_dependencies(self):
        self.assertEqual(self.read("dependson #1\ndepends #2\ndepends-on #3\n- [ ] closes #4\n"
                                   "needed by #5\nrequired #6\nblocked #7\n"), set())

    def test_a_sentence_after_a_number_is_not_read(self):
        self.assertEqual(self.read("depends on #12. See also #99 for context.\n"), {12})
        self.assertEqual(self.read("depends on #12; #13 is related\n"), {12})
        self.assertEqual(self.read("depends on #1, #2.\n"), {1, 2})

    def test_comments_and_code_blocks_are_not_read(self):
        body = ("<!-- - [ ] depends on: #1 -->\n<!--\ndepends on #2\n-->\n"
                "```\n- [ ] depends on: #3\n```\n~~~md\ndepends on #4\n~~~\ndepends on #5\n")
        self.assertEqual(self.read(body), {5})

    def test_a_fence_closes_only_with_its_own_kind(self):
        body = "````\n```\ndepends on #1\n```\ndepends on #2\n````\n~~~\n```\ndepends on #3\n~~~\ndepends on #4\n"
        self.assertEqual(self.read(body), {4})

    def test_an_unclosed_fence_or_comment_runs_to_the_end(self):
        self.assertEqual(self.read("depends on #1\n```\ndepends on #2\n"), {1})
        self.assertEqual(self.read("depends on #1\n<!-- draft\ndepends on #2\n"), {1})

    def test_code_spans_are_not_read(self):
        self.assertEqual(self.read("depends on `#5`\n"), set())
        self.assertEqual(self.read("`depends on #5`\n"), set())
        self.assertEqual(self.read("depends on ``#5`` and #6\n"), {6})
        self.assertEqual(self.read("depends on ```#5``` and #6\n"), {6})
        # A lone backtick opens nothing.
        self.assertEqual(self.read("depends on #5 ` and #6\n"), {5, 6})

    def test_a_comment_before_the_line_is_not_in_the_way(self):
        self.assertEqual(self.read("<!-- note --> - [ ] depends on #5\n<!-- a\nlonger note --> - needs #6\n"), {5, 6})

    def test_windows_line_ends(self):
        self.assertEqual(self.read("text\r\n- [ ] depends on: #9\r\n```\r\ndepends on #10\r\n```\r\n"), {9})

    def test_a_number_must_stand_alone(self):
        self.assertEqual(self.read("depends on #14 and #12abc and &#13;\n"), {14})


class Declarations(unittest.TestCase):
    def test_what_each_line_says(self):
        body = ("Text.\n- [ ] depends on: #3, #1, #3\n- [x] needs #2\n* blocked by #4\n- requires Lean\n[] needs #5\n"
                "requires #6\n")
        found = deps.declarations(body, REPO)
        self.assertEqual([(line.index, line.box, line.numbers) for line in found],
                         [(1, " ", (3, 1)), (2, "x", (2,)), (3, None, (4,)), (4, None, ()), (5, "", (5,))])
        first = found[0]
        self.assertEqual(body[first.start:first.end], "- [ ] depends on: #3, #1, #3")
        self.assertEqual(body[first.box_at], " ")
        self.assertEqual(body[first.box_at - 1:first.box_at + 2], "[ ]")
        self.assertEqual([(line.tickable, line.ticked) for line in found[:3]], [(True, False), (False, True), (False, False)])
        self.assertIsNone(found[2].box_at)

    def test_lines_end_before_a_carriage_return(self):
        body = "a\r\n- [ ] depends on #1\r\nb"
        line, = deps.declarations(body, REPO)
        self.assertEqual((line.index, body[line.start:line.end]), (1, "- [ ] depends on #1"))

    def test_the_box_after_a_comment_is_found_where_it_is(self):
        body = "<!-- x --> - [ ] depends on #5\n"
        line, = deps.declarations(body, REPO)
        self.assertEqual(body[line.box_at - 1:line.box_at + 2], "[ ]")


class Tick(unittest.TestCase):
    def test_only_lines_whose_pull_requests_have_all_landed(self):
        body = "- [ ] depends on: #1, #2\n- [ ] depends on: #1\n- [ ] depends on: #3\n"
        new, ticked = deps.tick(body, REPO, {1, 3})
        self.assertEqual(new, "- [ ] depends on: #1, #2\n- [x] depends on: #1\n- [x] depends on: #3\n")
        self.assertEqual([line.index for line in ticked], [1, 2])
        self.assertEqual(deps.tick(body, REPO, {1, 2, 3})[0].count("[x]"), 3)

    def test_byte_for_byte_with_windows_line_ends(self):
        body = ("Intro with é and 🤖 and trailing spaces   \r\n\r\n---\r\n\r\n- [ ] depends on: #12\r\n"
                "- [ ] depends on: #13\r\n<!-- - [ ] depends on: #12 -->\r\n```\r\n- [ ] depends on: #12\r\n```\r\nend")
        new, ticked = deps.tick(body, REPO, {12})
        at = body.index("- [ ] depends on: #12") + 3
        self.assertEqual(new, body[:at] + "x" + body[at + 1:])
        self.assertEqual(len(ticked), 1)
        self.assertEqual(new.encode().count(b"\r\n"), body.encode().count(b"\r\n"))

    def test_nothing_else_is_touched(self):
        body = ("- [x] depends on: #1\n- [X] depends on: #1\n- depends on: #1\n[] depends on #1\n"
                "- [ ] depends on: other/r#1\n- [ ] depends on: `#1`\n- [ ] requires Lean 4\n"
                "<!--\n- [ ] depends on: #1\n-->\n~~~\n- [ ] depends on: #1\n~~~\n")
        new, ticked = deps.tick(body, REPO, {1})
        self.assertEqual((new, ticked), (body, []))

    def test_never_unticks(self):
        body = "- [x] depends on: #1\n"
        self.assertEqual(deps.tick(body, REPO, set()), (body, []))


if __name__ == "__main__":
    unittest.main()
