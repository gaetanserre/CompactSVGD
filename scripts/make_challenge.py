#!/usr/bin/env python3
"""Generate the comparator challenge `CompactSVGDChallenge/Paper.lean` from `CompactSVGD/Paper.lean`.

The challenge is the solution with the proof of every theorem replaced by `sorry`. The
definitions, structures, notations, variables and docstrings are copied as is, so that the
statements and the definitions of the challenge are exactly those of the solution. Only the
public imports of the solution are kept, so that the challenge trusts as few modules as possible.
This requires that the definitions of the solution contain no proof using a private import.

Usage: `python3 scripts/make_challenge.py`. It also writes `comparator.json`, the configuration of
`lake comparator`, with the list of the (non-private) theorems to check. Then run
`lake comparator` (on Linux, with `bubblewrap` installed) from a clean build of the project.
"""

import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SOLUTION = ROOT / "CompactSVGD" / "Paper.lean"
CHALLENGE = ROOT / "CompactSVGDChallenge" / "Paper.lean"
CONFIG = ROOT / "comparator.json"

THEOREM_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?((?:(?:protected|private|nonrec|noncomputable) )*)(?:theorem|lemma) (\S+)")
COMMAND_RE = re.compile(
    r"^(?:theorem|lemma|def|abbrev|structure|class|instance|inductive|variable|omit|include|end|"
    r"namespace|section|open|notation|scoped|local|private|protected|noncomputable|nonrec|"
    r"set_option|attribute|example|/--|/-!|@\[)")
NAMESPACE_RE = re.compile(r"^namespace (\S+)")
SECTION_RE = re.compile(r"^(?:noncomputable )?section(?: (\S+))?\s*$")
END_RE = re.compile(r"^end(?: (\S+))?\s*$")
IMPORT_RE = re.compile(r"^(public )?(?:meta )?import (\S+)")
OPEN_BRACKETS = {"(": ")", "[": "]", "{": "}", "⟨": "⟩", "⦃": "⦄"}
CLOSE_BRACKETS = set(OPEN_BRACKETS.values())


def fail(msg: str) -> None:
    sys.exit(f"make_challenge.py: {msg}")


def comment_delta(line: str, depth: int) -> int:
    """The nesting depth of block comments after `line`, starting from `depth`."""
    i = 0
    while i < len(line):
        if depth == 0 and line.startswith("--", i):
            break
        if line.startswith("/-", i):
            depth += 1
            i += 2
        elif depth > 0 and line.startswith("-/", i):
            depth -= 1
            i += 2
        else:
            i += 1
    return depth


def statement_end(lines: list[str], start: int) -> tuple[int, int]:
    """Position (line, column) of the first `:=` at bracket depth 0 from line `start`."""
    depth = 0
    for j in range(start, len(lines)):
        line = lines[j]
        k = 0
        while k < len(line):
            if line.startswith("--", k):
                break
            c = line[k]
            if c in OPEN_BRACKETS:
                depth += 1
            elif c in CLOSE_BRACKETS:
                depth -= 1
            elif depth == 0 and line.startswith(":=", k):
                return j, k
            k += 1
    fail(f"no `:=` after line {start + 1}")
    raise AssertionError


def main() -> None:
    lines = SOLUTION.read_text().split("\n")
    out: list[str] = []
    names: list[str] = []
    theorem_lines = 0
    scopes: list[tuple[str, str]] = []  # ("namespace" | "section", name)
    comment = 0
    in_header = True
    i = 0
    while i < len(lines):
        line = lines[i]
        if comment == 0 and in_header and IMPORT_RE.match(line):
            # The import block: keep the public imports.
            public = []
            while i < len(lines) and (IMPORT_RE.match(lines[i]) or not lines[i].strip()):
                if (m := IMPORT_RE.match(lines[i])) and m.group(1):
                    public.append(lines[i])
                i += 1
            out.extend(public + [""])
            continue
        if comment == 0 and line.startswith("/-!"):
            in_header = False
        if comment == 0:
            if m := NAMESPACE_RE.match(line):
                scopes.append(("namespace", m.group(1)))
            elif m := SECTION_RE.match(line):
                scopes.append(("section", m.group(1) or ""))
            elif (m := END_RE.match(line)) and scopes:
                scopes.pop()
            if m := THEOREM_RE.match(line):
                theorem_lines += 1
                private = "private" in m.group(1)
                if not private:
                    prefix = [n for kind, n in scopes if kind == "namespace"]
                    names.append(".".join(prefix + [m.group(2)]))
                j, k = statement_end(lines, i)
                out.extend(lines[i:j])
                out.append(lines[j][:k].rstrip() + " :=")
                out.append("  sorry")
                # The proof ends at the next blank line or command at column 0, outside comments.
                i = j + 1
                proof_comment = comment_delta(lines[j][k:], 0)
                while i < len(lines):
                    nxt = lines[i]
                    if proof_comment == 0 and (not nxt.strip() or COMMAND_RE.match(nxt)):
                        break
                    proof_comment = comment_delta(nxt, proof_comment)
                    i += 1
                continue
        out.append(line)
        comment = comment_delta(line, comment)
        i += 1
    top_level = sum(1 for n in names) + sum(
        1 for line in lines if re.match(r"^(?:@\[[^\]]*\]\s*)?private (?:theorem|lemma) ", line))
    if top_level != theorem_lines:
        fail(f"found {theorem_lines} theorems but extracted {top_level}")
    CHALLENGE.parent.mkdir(exist_ok=True)
    CHALLENGE.write_text("\n".join(out))
    CONFIG.write_text(json.dumps({
        "challenge_module": "CompactSVGDChallenge.Paper",
        "solution_module": "CompactSVGD.Paper",
        "theorem_names": names,
        "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
    }, indent=2, ensure_ascii=False) + "\n")
    print(f"{CHALLENGE.relative_to(ROOT)}: {len(names)} theorems to check")


if __name__ == "__main__":
    main()
